#![allow(clippy::too_many_arguments)]

//! Peer-oriented edaBits / A2B flow built on top of the repository's VOLE/tag
//! machinery with explicit authenticated secret shares.
//!
//! Correspondence with the ZK-oriented code:
//! - [`crate::mpc_homcom`] mirrors [`crate::homcom`] with bidirectional,
//!   peer-facing initialization.
//! - [`crate::mpc_conv`] adds `private_edabits` and `global_edabits` on top of
//!   the owner/checker proof views from [`crate::conv`].
//! - This module mirrors [`crate::edabits`] at the orchestration level, but the
//!   output is now the final combined authenticated secret-shared
//!   `global_edabits` rather than separate owner/checker views.
//!
//! The current combine step is a 2-party masked adder: it uses the clear local
//! private contributions from each peer to derive fresh secret shares of the
//! global output, while the per-party `private_edabits` still exist as real
//! authenticated secret-share contributions for future generalization.

use crate::conv::{ConvProverT, ConvVerifierT};
use crate::edabits::{ProverConv, VerifierConv};
use crate::mpc_conv::{
    AuthenticatedShare, GlobalEdabit, PrivateEdabit, PrivateEdabitState, SharedEdabit,
};
use crate::mpc_homcom::{PeerFieldMacs, PeerRole};
use eyre::{eyre, Result};
use fancy_garbling::{
    twopac::semihonest::{Evaluator, Garbler},
    BinaryBundle, BinaryGadgets, Fancy, FancyBinary, FancyInput, WireMod2,
};
use ocelot::{
    ot::{AlszReceiver as OtReceiver, AlszSender as OtSender},
    svole::wykw::LpnParams,
};
use rand::{CryptoRng, Rng, SeedableRng};
use scuttlebutt::{
    field::{F40b, FiniteField, F2},
    ring::FiniteRing,
    AbstractChannel, AesRng, Block,
};

/// Select the cut-and-choose parameters used by the MPC-facing wrapper.
///
/// This matches the policy in [`crate::edabits`] so the MPC and ZK paths remain
/// easy to compare side-by-side.
pub fn select_cut_and_choose_parameters(num_edabits: usize) -> (usize, usize) {
    assert!(num_edabits >= 1024);
    let num_buckets = if num_edabits < 10322 {
        5
    } else if num_edabits < 1048576 {
        4
    } else {
        3
    };
    (num_buckets, num_buckets)
}

fn f2_to_fe<FE: FiniteField>(bit: F2) -> FE::PrimeField {
    if bit == F2::ZERO {
        FE::PrimeField::ZERO
    } else {
        FE::PrimeField::ONE
    }
}

fn convert_bits_to_field<FE: FiniteField>(bits: &[F2]) -> FE::PrimeField {
    let mut out = FE::PrimeField::ZERO;
    for bit in bits.iter().rev() {
        out += out;
        out += f2_to_fe::<FE>(*bit);
    }
    out
}

fn power_two<FE: FiniteField>(power: usize) -> FE::PrimeField {
    let mut out = FE::PrimeField::ONE;
    for _ in 0..power {
        out += out;
    }
    out
}

fn flatten_bits(bit_vectors: &[Vec<F2>]) -> Vec<F2> {
    let total: usize = bit_vectors.iter().map(Vec::len).sum();
    let mut out = Vec::with_capacity(total);
    for bits in bit_vectors {
        out.extend_from_slice(bits);
    }
    out
}

fn flatten_bits_u16(bit_vectors: &[Vec<F2>]) -> Vec<u16> {
    flatten_bits(bit_vectors)
        .into_iter()
        .map(|bit| u16::from(u8::from(bit)))
        .collect()
}

fn split_bits(flat: &[F2], chunk_size: usize) -> Vec<Vec<F2>> {
    flat.chunks(chunk_size)
        .map(|chunk| chunk.to_vec())
        .collect()
}

fn split_bits_u16(flat: &[u16], chunk_size: usize) -> Vec<Vec<F2>> {
    flat.chunks(chunk_size)
        .map(|chunk| {
            chunk
                .iter()
                .map(|bit| if *bit == 0 { F2::ZERO } else { F2::ONE })
                .collect()
        })
        .collect()
}

fn signed_bits_to_field<FE: FiniteField>(bits: &[F2]) -> FE::PrimeField {
    let raw = convert_bits_to_field::<FE>(bits);
    if bits.last().copied().unwrap_or(F2::ZERO) == F2::ZERO {
        raw
    } else {
        raw - power_two::<FE>(bits.len())
    }
}

fn build_masked_add_outputs<F: FancyBinary>(
    fancy: &mut F,
    bit_size: usize,
    lhs_bits: &[F::Item],
    rhs_bits: &[F::Item],
    output_mask_bits: &[F::Item],
    arithmetic_mask_bits: &[F::Item],
) -> Result<Vec<F::Item>, F::Error> {
    let num = lhs_bits.len() / bit_size;
    let zero = fancy.constant(0, 2)?;
    let mut outputs = Vec::with_capacity(num * (bit_size + bit_size + 1));

    for i in 0..num {
        let bit_base = i * bit_size;
        let arith_base = i * (bit_size + 1);

        let lhs = BinaryBundle::new(lhs_bits[bit_base..bit_base + bit_size].to_vec());
        let rhs = BinaryBundle::new(rhs_bits[bit_base..bit_base + bit_size].to_vec());
        let mask = BinaryBundle::new(output_mask_bits[bit_base..bit_base + bit_size].to_vec());
        let arithmetic_mask =
            BinaryBundle::new(arithmetic_mask_bits[arith_base..arith_base + bit_size + 1].to_vec());

        let (sum_bits, _) = fancy.bin_addition(&lhs, &rhs)?;
        let masked_bits = fancy.bin_xor(&sum_bits, &mask)?;
        outputs.extend(masked_bits.wires().iter().cloned());

        let mut sum_bits_extended = BinaryBundle::new(sum_bits.wires().to_vec());
        sum_bits_extended.push(zero.clone());
        let (diff_bits, _) = fancy.bin_subtraction(&sum_bits_extended, &arithmetic_mask)?;
        outputs.extend(diff_bits.wires().iter().cloned());
    }

    Ok(outputs)
}

fn open_authenticated_share<FE: FiniteField, C: AbstractChannel>(
    role: PeerRole,
    fcom: &PeerFieldMacs<FE>,
    channel: &mut C,
    share: &AuthenticatedShare<FE>,
) -> Result<FE::PrimeField> {
    let mut remote_value = Vec::with_capacity(1);
    if role.is_first() {
        fcom.local().get_refmut().open(channel, &[share.local])?;
        fcom.remote()
            .get_refmut()
            .open(channel, &[share.remote], &mut remote_value)?;
    } else {
        fcom.remote()
            .get_refmut()
            .open(channel, &[share.remote], &mut remote_value)?;
        fcom.local().get_refmut().open(channel, &[share.local])?;
    }
    Ok(share.local.value() + remote_value[0])
}

struct LocalPrivateEdabitBatch<FE: FiniteField> {
    private_edabits: Vec<PrivateEdabit<FE>>,
    proof_edabits: Vec<crate::conv::EdabitsProver<FE>>,
}

struct RemotePrivateEdabitBatch<FE: FiniteField> {
    peer_private_edabits: Vec<SharedEdabit<FE>>,
    peer_private_proof_edabits: Vec<crate::conv::EdabitsVerifier<FE>>,
}

/// MPC-facing peer that owns both directions of the A2B flow.
pub struct MpcEdabitsPeer<FE: FiniteField> {
    role: PeerRole,
    pub fcom_f2: PeerFieldMacs<F40b>,
    pub fcom_fe: PeerFieldMacs<FE>,
    local_conv: ProverConv<FE>,
    remote_conv: VerifierConv<FE>,
}

impl<FE: FiniteField<PrimeField = FE>> MpcEdabitsPeer<FE> {
    /// Initialize the bidirectional MPC-facing edaBits peer.
    pub fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        role: PeerRole,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
    ) -> Result<Self> {
        let fcom_f2 = PeerFieldMacs::init(channel, rng, role, lpn_setup, lpn_extend)?;
        let fcom_fe = PeerFieldMacs::init(channel, rng, role, lpn_setup, lpn_extend)?;
        let local_conv = ProverConv::init_zero(fcom_f2.local(), fcom_fe.local())?;
        let remote_conv = VerifierConv::init_zero(fcom_f2.remote(), fcom_fe.remote())?;
        Ok(Self {
            role,
            fcom_f2,
            fcom_fe,
            local_conv,
            remote_conv,
        })
    }

    fn sample_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<LocalPrivateEdabitBatch<FE>> {
        let proof_edabits = self
            .local_conv
            .random_edabits(channel, rng, bit_size, num)?;

        let mut clear_bits = Vec::with_capacity(num);
        let mut clear_values = Vec::with_capacity(num);
        let mut local_bit_shares = Vec::with_capacity(num);
        let mut remote_bit_shares = Vec::with_capacity(num);
        let mut local_value_shares = Vec::with_capacity(num);
        let mut remote_value_shares = Vec::with_capacity(num);

        for proof in &proof_edabits {
            let proof_bits: Vec<F2> = proof.bits.iter().map(|bit| bit.value()).collect();
            let proof_value = proof.value.value();

            let mut local_bits = Vec::with_capacity(bit_size);
            let mut remote_bits = Vec::with_capacity(bit_size);
            for bit in &proof_bits {
                let local_bit = F2::random(rng);
                local_bits.push(local_bit);
                remote_bits.push(*bit + local_bit);
            }

            let local_value = FE::random(rng);
            let remote_value = proof_value - local_value;

            clear_bits.push(proof_bits);
            clear_values.push(proof_value);
            local_bit_shares.push(local_bits);
            remote_bit_shares.push(remote_bits);
            local_value_shares.push(local_value);
            remote_value_shares.push(remote_value);
        }

        let flat_local_bits = flatten_bits(&local_bit_shares);
        let local_bit_macs =
            self.fcom_f2
                .local()
                .get_refmut()
                .input(channel, rng, &flat_local_bits)?;
        let local_value_macs =
            self.fcom_fe
                .local()
                .get_refmut()
                .input(channel, rng, &local_value_shares)?;

        channel.write_serializable_seq::<F2>(&flatten_bits(&remote_bit_shares))?;
        channel.write_serializable_seq::<FE>(&remote_value_shares)?;
        channel.flush()?;

        let remote_bit_auth =
            self.fcom_f2
                .remote()
                .get_refmut()
                .input(channel, rng, flat_local_bits.len())?;
        let remote_value_auth = self
            .fcom_fe
            .remote()
            .get_refmut()
            .input(channel, rng, num)?;

        let mut private_edabits = Vec::with_capacity(num);
        let mut bit_mac_offset = 0;
        for i in 0..num {
            let mut shared_bits = Vec::with_capacity(bit_size);
            for j in 0..bit_size {
                let local_idx = bit_mac_offset + j;
                shared_bits.push(AuthenticatedShare::new(
                    crate::homcom::MacProver::new(
                        local_bit_shares[i][j],
                        local_bit_macs[local_idx],
                    ),
                    remote_bit_auth[local_idx],
                ));
            }
            bit_mac_offset += bit_size;

            private_edabits.push(PrivateEdabit {
                clear_bits: clear_bits[i].clone(),
                clear_value: clear_values[i],
                shared: SharedEdabit {
                    bits: shared_bits,
                    value: AuthenticatedShare::new(
                        crate::homcom::MacProver::new(local_value_shares[i], local_value_macs[i]),
                        remote_value_auth[i],
                    ),
                },
            });
        }

        Ok(LocalPrivateEdabitBatch {
            private_edabits,
            proof_edabits,
        })
    }

    fn receive_peer_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<RemotePrivateEdabitBatch<FE>> {
        let peer_private_proof_edabits = self
            .remote_conv
            .random_edabits(channel, rng, bit_size, num)?;

        let remote_bit_auth =
            self.fcom_f2
                .remote()
                .get_refmut()
                .input(channel, rng, num * bit_size)?;
        let remote_value_auth = self
            .fcom_fe
            .remote()
            .get_refmut()
            .input(channel, rng, num)?;

        let remote_bit_shares = channel.read_serializable_seq::<F2>(num * bit_size)?;
        let remote_value_shares = channel.read_serializable_seq::<FE>(num)?;

        let local_bit_macs =
            self.fcom_f2
                .local()
                .get_refmut()
                .input(channel, rng, &remote_bit_shares)?;
        let local_value_macs =
            self.fcom_fe
                .local()
                .get_refmut()
                .input(channel, rng, &remote_value_shares)?;

        let remote_bit_chunks = split_bits(&remote_bit_shares, bit_size);
        let mut peer_private_edabits = Vec::with_capacity(num);
        let mut bit_mac_offset = 0;
        for i in 0..num {
            let mut shared_bits = Vec::with_capacity(bit_size);
            for j in 0..bit_size {
                let local_idx = bit_mac_offset + j;
                shared_bits.push(AuthenticatedShare::new(
                    crate::homcom::MacProver::new(
                        remote_bit_chunks[i][j],
                        local_bit_macs[local_idx],
                    ),
                    remote_bit_auth[local_idx],
                ));
            }
            bit_mac_offset += bit_size;

            peer_private_edabits.push(SharedEdabit {
                bits: shared_bits,
                value: AuthenticatedShare::new(
                    crate::homcom::MacProver::new(remote_value_shares[i], local_value_macs[i]),
                    remote_value_auth[i],
                ),
            });
        }

        Ok(RemotePrivateEdabitBatch {
            peer_private_edabits,
            peer_private_proof_edabits,
        })
    }

    /// Sampling/input plus sharing/authentication stage for `private_edabits`.
    pub fn sample_and_share_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<PrivateEdabitState<FE>> {
        let (local, remote) = if self.role.is_first() {
            (
                self.sample_private_edabits(channel, rng, bit_size, num)?,
                self.receive_peer_private_edabits(channel, rng, bit_size, num)?,
            )
        } else {
            let remote = self.receive_peer_private_edabits(channel, rng, bit_size, num)?;
            let local = self.sample_private_edabits(channel, rng, bit_size, num)?;
            (local, remote)
        };

        Ok(PrivateEdabitState {
            private_edabits: local.private_edabits,
            peer_private_edabits: remote.peer_private_edabits,
            private_proof_edabits: local.proof_edabits,
            peer_private_proof_edabits: remote.peer_private_proof_edabits,
        })
    }

    fn cut_and_choose_private<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num_bucket: usize,
        num_cut: usize,
        state: &PrivateEdabitState<FE>,
    ) -> Result<()> {
        if self.role.is_first() {
            self.local_conv.conv(
                channel,
                rng,
                num_bucket,
                num_cut,
                &state.private_proof_edabits,
                None,
            )?;
            self.remote_conv.conv(
                channel,
                rng,
                num_bucket,
                num_cut,
                &state.peer_private_proof_edabits,
                None,
            )?;
        } else {
            self.remote_conv.conv(
                channel,
                rng,
                num_bucket,
                num_cut,
                &state.peer_private_proof_edabits,
                None,
            )?;
            self.local_conv.conv(
                channel,
                rng,
                num_bucket,
                num_cut,
                &state.private_proof_edabits,
                None,
            )?;
        }
        Ok(())
    }

    fn garbler_global_share_masks<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        private_edabits: &[PrivateEdabit<FE>],
    ) -> Result<(Vec<Vec<F2>>, Vec<FE>)> {
        let bit_size = private_edabits[0].clear_bits.len();
        let num = private_edabits.len();

        let mut output_mask_bits = Vec::with_capacity(num);
        let mut arithmetic_mask_bits = Vec::with_capacity(num);
        for _ in 0..num {
            let mut bit_mask = Vec::with_capacity(bit_size);
            let mut value_mask = Vec::with_capacity(bit_size + 1);
            for _ in 0..bit_size {
                bit_mask.push(F2::random(rng));
                value_mask.push(F2::random(rng));
            }
            value_mask.push(F2::ZERO);
            output_mask_bits.push(bit_mask);
            arithmetic_mask_bits.push(value_mask);
        }

        let my_inputs = flatten_bits_u16(
            &private_edabits
                .iter()
                .map(|edabit| edabit.clear_bits.clone())
                .collect::<Vec<_>>(),
        );
        let mask_inputs = flatten_bits_u16(&output_mask_bits);
        let arithmetic_mask_inputs = flatten_bits_u16(&arithmetic_mask_bits);

        let mut gc = Garbler::<C, AesRng, OtSender, WireMod2>::new(
            channel.clone(),
            AesRng::from_seed(rng.gen::<Block>()),
        )
        .map_err(|err| eyre!("{err}"))?;

        let my_wires = gc
            .encode_many(&my_inputs, &vec![2; my_inputs.len()])
            .map_err(|err| eyre!("{err}"))?;
        let mask_wires = gc
            .encode_many(&mask_inputs, &vec![2; mask_inputs.len()])
            .map_err(|err| eyre!("{err}"))?;
        let arithmetic_mask_wires = gc
            .encode_many(
                &arithmetic_mask_inputs,
                &vec![2; arithmetic_mask_inputs.len()],
            )
            .map_err(|err| eyre!("{err}"))?;
        let peer_wires = gc
            .receive_many(&vec![2; my_inputs.len()])
            .map_err(|err| eyre!("{err}"))?;

        let output_wires = build_masked_add_outputs(
            &mut gc,
            bit_size,
            &my_wires,
            &peer_wires,
            &mask_wires,
            &arithmetic_mask_wires,
        )
        .map_err(|err| eyre!("{err}"))?;
        gc.outputs(&output_wires).map_err(|err| eyre!("{err}"))?;

        let arithmetic_masks = arithmetic_mask_bits
            .iter()
            .map(|bits| convert_bits_to_field::<FE>(&bits[..bit_size]))
            .collect();
        Ok((output_mask_bits, arithmetic_masks))
    }

    fn evaluator_global_share_masks<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        private_edabits: &[PrivateEdabit<FE>],
    ) -> Result<(Vec<Vec<F2>>, Vec<FE>)> {
        let bit_size = private_edabits[0].clear_bits.len();
        let my_inputs = flatten_bits_u16(
            &private_edabits
                .iter()
                .map(|edabit| edabit.clear_bits.clone())
                .collect::<Vec<_>>(),
        );

        let mut gc = Evaluator::<C, AesRng, OtReceiver, WireMod2>::new(
            channel.clone(),
            AesRng::from_seed(rng.gen::<Block>()),
        )
        .map_err(|err| eyre!("{err}"))?;

        let peer_wires = gc
            .receive_many(&vec![2; my_inputs.len()])
            .map_err(|err| eyre!("{err}"))?;
        let mask_wires = gc
            .receive_many(&vec![2; my_inputs.len()])
            .map_err(|err| eyre!("{err}"))?;
        let arithmetic_mask_wires = gc
            .receive_many(&vec![2; private_edabits.len() * (bit_size + 1)])
            .map_err(|err| eyre!("{err}"))?;
        let my_wires = gc
            .encode_many(&my_inputs, &vec![2; my_inputs.len()])
            .map_err(|err| eyre!("{err}"))?;

        let outputs = build_masked_add_outputs(
            &mut gc,
            bit_size,
            &peer_wires,
            &my_wires,
            &mask_wires,
            &arithmetic_mask_wires,
        )
        .map_err(|err| eyre!("{err}"))?;
        let revealed = gc
            .outputs(&outputs)
            .map_err(|err| eyre!("{err}"))?
            .ok_or_else(|| eyre!("masked global share outputs were not delivered"))?;

        let chunk_size = bit_size + bit_size + 1;
        let mut global_bit_shares = Vec::with_capacity(private_edabits.len());
        let mut global_value_shares = Vec::with_capacity(private_edabits.len());
        for chunk in revealed.chunks(chunk_size) {
            let bit_share = split_bits_u16(&chunk[..bit_size], bit_size)
                .into_iter()
                .next()
                .unwrap_or_default();
            let signed_bits = split_bits_u16(&chunk[bit_size..], bit_size + 1)
                .into_iter()
                .next()
                .unwrap_or_default();
            global_bit_shares.push(bit_share);
            global_value_shares.push(signed_bits_to_field::<FE>(&signed_bits));
        }

        Ok((global_bit_shares, global_value_shares))
    }

    fn derive_global_share_values<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &PrivateEdabitState<FE>,
    ) -> Result<(Vec<Vec<F2>>, Vec<FE>)> {
        if state.private_edabits.is_empty() {
            return Ok((Vec::new(), Vec::new()));
        }
        channel.flush()?;
        if self.role.is_first() {
            self.garbler_global_share_masks(channel, rng, &state.private_edabits)
        } else {
            self.evaluator_global_share_masks(channel, rng, &state.private_edabits)
        }
    }

    fn authenticate_global_shares<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        global_bit_shares: &[Vec<F2>],
        global_value_shares: &[FE],
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        let bit_size = global_bit_shares.first().map_or(0, Vec::len);
        let flat_bits = flatten_bits(global_bit_shares);

        let (local_bit_macs, local_value_macs, remote_bit_auth, remote_value_auth) =
            if self.role.is_first() {
                let local_bit_macs = self
                    .fcom_f2
                    .local()
                    .get_refmut()
                    .input(channel, rng, &flat_bits)?;
                let local_value_macs =
                    self.fcom_fe
                        .local()
                        .get_refmut()
                        .input(channel, rng, global_value_shares)?;
                let remote_bit_auth =
                    self.fcom_f2
                        .remote()
                        .get_refmut()
                        .input(channel, rng, flat_bits.len())?;
                let remote_value_auth = self.fcom_fe.remote().get_refmut().input(
                    channel,
                    rng,
                    global_value_shares.len(),
                )?;
                (
                    local_bit_macs,
                    local_value_macs,
                    remote_bit_auth,
                    remote_value_auth,
                )
            } else {
                let remote_bit_auth =
                    self.fcom_f2
                        .remote()
                        .get_refmut()
                        .input(channel, rng, flat_bits.len())?;
                let remote_value_auth = self.fcom_fe.remote().get_refmut().input(
                    channel,
                    rng,
                    global_value_shares.len(),
                )?;
                let local_bit_macs = self
                    .fcom_f2
                    .local()
                    .get_refmut()
                    .input(channel, rng, &flat_bits)?;
                let local_value_macs =
                    self.fcom_fe
                        .local()
                        .get_refmut()
                        .input(channel, rng, global_value_shares)?;
                (
                    local_bit_macs,
                    local_value_macs,
                    remote_bit_auth,
                    remote_value_auth,
                )
            };

        let mut global_edabits = Vec::with_capacity(global_value_shares.len());
        let mut bit_offset = 0;
        for i in 0..global_value_shares.len() {
            let mut bits = Vec::with_capacity(bit_size);
            for j in 0..bit_size {
                let idx = bit_offset + j;
                bits.push(AuthenticatedShare::new(
                    crate::homcom::MacProver::new(global_bit_shares[i][j], local_bit_macs[idx]),
                    remote_bit_auth[idx],
                ));
            }
            bit_offset += bit_size;

            global_edabits.push(SharedEdabit {
                bits,
                value: AuthenticatedShare::new(
                    crate::homcom::MacProver::new(global_value_shares[i], local_value_macs[i]),
                    remote_value_auth[i],
                ),
            });
        }
        Ok(global_edabits)
    }

    /// Combine the authenticated-share `private_edabits` into final
    /// authenticated-share `global_edabits`.
    pub fn combine_private_into_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &PrivateEdabitState<FE>,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        let (global_bit_shares, global_value_shares) =
            self.derive_global_share_values(channel, rng, state)?;
        self.authenticate_global_shares(channel, rng, &global_bit_shares, &global_value_shares)
    }

    /// Full MPC flow:
    /// 1. sample owner-known private contributions
    /// 2. distribute them as authenticated secret-shared `private_edabits`
    /// 3. run cut-and-choose plus QuickSilver-backed consistency on the proof views
    /// 4. combine the private contributions into authenticated secret-shared
    ///    `global_edabits`
    pub fn generate_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        let (num_bucket, num_cut) = select_cut_and_choose_parameters(num);
        let state = self.sample_and_share_private_edabits(channel, rng, bit_size, num)?;
        self.cut_and_choose_private(channel, rng, num_bucket, num_cut, &state)?;
        self.combine_private_into_global_edabits(channel, rng, &state)
    }

    /// Backwards-compatible alias for the new final `global_edabits` output.
    pub fn generate_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        self.generate_global_edabits(channel, rng, bit_size, num)
    }

    /// Open the final shared `global_edabits`.
    pub fn open_global_edabits<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        global_edabits: &[GlobalEdabit<FE>],
    ) -> Result<Vec<(Vec<F2>, FE)>> {
        let mut opened = Vec::with_capacity(global_edabits.len());
        for edabit in global_edabits {
            let mut bits = Vec::with_capacity(edabit.bits.len());
            for bit in &edabit.bits {
                bits.push(open_authenticated_share(
                    self.role,
                    &self.fcom_f2,
                    channel,
                    bit,
                )?);
            }
            let value = open_authenticated_share(self.role, &self.fcom_fe, channel, &edabit.value)?;
            opened.push((bits, value));
        }
        Ok(opened)
    }

    /// Aggregate VOLE estimate for the full peer-facing flow.
    ///
    /// The additional VOLE cost covers:
    /// - distributing the secret-shared `private_edabits`
    /// - authenticating the final `global_edabits`
    ///
    /// The masked 2-party add used in the current global combine step consumes
    /// OT, not VOLE, so it is intentionally not included here.
    pub fn estimate_voles(num: usize, bit_size: u32) -> (usize, usize) {
        let (proof_f2_local, proof_fe_local) = ProverConv::<FE>::estimate_voles(num, bit_size);
        let (proof_f2_remote, proof_fe_remote) = VerifierConv::<FE>::estimate_voles(num, bit_size);
        let share_f2 = 4 * num * bit_size as usize;
        let share_fe = 4 * num;
        (
            proof_f2_local + proof_f2_remote + share_f2,
            proof_fe_local + proof_fe_remote + share_fe,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ocelot::svole::wykw::{LPN_EXTEND_SMALL, LPN_SETUP_SMALL};
    use rand::SeedableRng;
    use scuttlebutt::{field::F61p, AesRng, Channel};
    use std::{
        io::{BufReader, BufWriter},
        os::unix::net::UnixStream,
    };

    #[test]
    fn test_mpc_global_edabits_roundtrip() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = MpcEdabitsPeer::<F61p>::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            let global_edabits = peer
                .generate_global_edabits(&mut channel, &mut rng, 8, 1024)
                .unwrap();
            assert_eq!(global_edabits.len(), 1024);

            let opened = peer
                .open_global_edabits(&mut channel, &global_edabits)
                .unwrap();
            for (bits, value) in opened {
                assert_eq!(bits.len(), 8);
                assert_eq!(convert_bits_to_field::<F61p>(&bits), value);
            }
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(right.try_clone().unwrap());
        let writer = BufWriter::new(right);
        let mut channel = Channel::new(reader, writer);
        let mut peer = MpcEdabitsPeer::<F61p>::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        let global_edabits = peer
            .generate_global_edabits(&mut channel, &mut rng, 8, 1024)
            .unwrap();
        assert_eq!(global_edabits.len(), 1024);

        let opened = peer
            .open_global_edabits(&mut channel, &global_edabits)
            .unwrap();
        for (bits, value) in opened {
            assert_eq!(bits.len(), 8);
            assert_eq!(convert_bits_to_field::<F61p>(&bits), value);
        }

        handle.join().unwrap();
    }
}
