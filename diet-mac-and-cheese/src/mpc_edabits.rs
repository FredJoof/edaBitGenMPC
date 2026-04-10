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
//! The global-combine step follows the paper's Figure 3 structure in 2-party
//! form:
//! - add the private bit contributions with a ripple-carry adder directly over
//!   authenticated secret-shared bits
//! - use QuickSilver-checked shared bit triples for the carry ANDs
//! - convert the overflow carry bits to authenticated field shares with shared
//!   dabits
//! - subtract the `2^m` overflow correction from the summed arithmetic shares

use crate::conv::{ConvProverT, ConvVerifierT};
use crate::edabits::{DabitProver, DabitVerifier, ProverConv, VerifierConv};
use crate::homcom::{MacProver, MacVerifier};
use crate::mpc_conv::{
    AuthenticatedShare, GlobalEdabit, PrivateEdabit, PrivateEdabitState, SharedEdabit,
};
use crate::mpc_homcom::{PeerFieldMacs, PeerRole};
use eyre::Result;
use generic_array::typenum::Unsigned;
use ocelot::svole::wykw::LpnParams;
use rand::{CryptoRng, Rng};
use scuttlebutt::{
    field::{Degree, F40b, FiniteField, F2},
    ring::FiniteRing,
    AbstractChannel,
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

#[cfg(test)]
fn f2_to_fe<FE: FiniteField>(bit: F2) -> FE::PrimeField {
    if bit == F2::ZERO {
        FE::PrimeField::ZERO
    } else {
        FE::PrimeField::ONE
    }
}

#[cfg(test)]
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

fn split_bits(flat: &[F2], chunk_size: usize) -> Vec<Vec<F2>> {
    flat.chunks(chunk_size)
        .map(|chunk| chunk.to_vec())
        .collect()
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

#[derive(Clone, Copy, Debug)]
struct SharedBitTriple {
    a: AuthenticatedShare<F40b>,
    b: AuthenticatedShare<F40b>,
    c: AuthenticatedShare<F40b>,
}

#[derive(Clone, Copy, Debug)]
struct SharedDabit<FE: FiniteField> {
    bit: AuthenticatedShare<F40b>,
    value: AuthenticatedShare<FE>,
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

    fn zero_bit_share(&self) -> AuthenticatedShare<F40b> {
        AuthenticatedShare::new(
            MacProver::new(F2::ZERO, F40b::ZERO),
            MacVerifier::new(F40b::ZERO),
        )
    }

    fn add_bit_shares(
        &mut self,
        lhs: AuthenticatedShare<F40b>,
        rhs: AuthenticatedShare<F40b>,
    ) -> AuthenticatedShare<F40b> {
        AuthenticatedShare::new(
            self.fcom_f2.local().get_refmut().add(lhs.local, rhs.local),
            self.fcom_f2
                .remote()
                .get_refmut()
                .add(lhs.remote, rhs.remote),
        )
    }

    fn add_bit_const(
        &mut self,
        share: AuthenticatedShare<F40b>,
        cst: F2,
    ) -> AuthenticatedShare<F40b> {
        if cst == F2::ZERO {
            share
        } else if self.role.is_first() {
            AuthenticatedShare::new(
                self.fcom_f2
                    .local()
                    .get_refmut()
                    .affine_add_cst(cst, share.local),
                share.remote,
            )
        } else {
            AuthenticatedShare::new(
                share.local,
                self.fcom_f2
                    .remote()
                    .get_refmut()
                    .affine_add_cst(cst, share.remote),
            )
        }
    }

    fn negate_field_share(&mut self, share: AuthenticatedShare<FE>) -> AuthenticatedShare<FE> {
        AuthenticatedShare::new(
            self.fcom_fe.local().get_refmut().neg(share.local),
            self.fcom_fe.remote().get_refmut().neg(share.remote),
        )
    }

    fn add_field_const(
        &mut self,
        share: AuthenticatedShare<FE>,
        cst: FE::PrimeField,
    ) -> AuthenticatedShare<FE> {
        if cst == FE::PrimeField::ZERO {
            share
        } else if self.role.is_first() {
            AuthenticatedShare::new(
                self.fcom_fe
                    .local()
                    .get_refmut()
                    .affine_add_cst(cst, share.local),
                share.remote,
            )
        } else {
            AuthenticatedShare::new(
                share.local,
                self.fcom_fe
                    .remote()
                    .get_refmut()
                    .affine_add_cst(cst, share.remote),
            )
        }
    }

    fn open_shared_bit_batch<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        shares: &[AuthenticatedShare<F40b>],
    ) -> Result<Vec<F2>> {
        if shares.is_empty() {
            return Ok(Vec::new());
        }

        let local_batch: Vec<_> = shares.iter().map(|share| share.local).collect();
        let remote_batch: Vec<_> = shares.iter().map(|share| share.remote).collect();
        let mut remote_values = Vec::with_capacity(shares.len());
        if self.role.is_first() {
            self.fcom_f2
                .local()
                .get_refmut()
                .open(channel, &local_batch)?;
            self.fcom_f2
                .remote()
                .get_refmut()
                .open(channel, &remote_batch, &mut remote_values)?;
        } else {
            self.fcom_f2
                .remote()
                .get_refmut()
                .open(channel, &remote_batch, &mut remote_values)?;
            self.fcom_f2
                .local()
                .get_refmut()
                .open(channel, &local_batch)?;
        }

        Ok(local_batch
            .iter()
            .zip(remote_values.into_iter())
            .map(|(local, remote)| local.value() + remote)
            .collect())
    }

    fn share_owned_f2_values<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        values: &[F2],
    ) -> Result<Vec<AuthenticatedShare<F40b>>> {
        let mut local_shares = Vec::with_capacity(values.len());
        let mut remote_shares = Vec::with_capacity(values.len());
        for value in values {
            let local_share = F2::random(rng);
            local_shares.push(local_share);
            remote_shares.push(*value + local_share);
        }

        let local_macs = self
            .fcom_f2
            .local()
            .get_refmut()
            .input(channel, rng, &local_shares)?;
        channel.write_serializable_seq::<F2>(&remote_shares)?;
        channel.flush()?;
        let remote_auth = self
            .fcom_f2
            .remote()
            .get_refmut()
            .input(channel, rng, values.len())?;

        Ok(local_shares
            .into_iter()
            .zip(local_macs.into_iter())
            .zip(remote_auth.into_iter())
            .map(|((share, mac), auth)| AuthenticatedShare::new(MacProver::new(share, mac), auth))
            .collect())
    }

    fn receive_shared_f2_values<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num: usize,
    ) -> Result<Vec<AuthenticatedShare<F40b>>> {
        let remote_auth = self
            .fcom_f2
            .remote()
            .get_refmut()
            .input(channel, rng, num)?;
        let local_shares = channel.read_serializable_seq::<F2>(num)?;
        let local_macs = self
            .fcom_f2
            .local()
            .get_refmut()
            .input(channel, rng, &local_shares)?;
        channel.flush()?;

        Ok(local_shares
            .into_iter()
            .zip(local_macs.into_iter())
            .zip(remote_auth.into_iter())
            .map(|((share, mac), auth)| AuthenticatedShare::new(MacProver::new(share, mac), auth))
            .collect())
    }

    fn share_owned_fe_values<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        values: &[FE],
    ) -> Result<Vec<AuthenticatedShare<FE>>> {
        let mut local_shares = Vec::with_capacity(values.len());
        let mut remote_shares = Vec::with_capacity(values.len());
        for value in values {
            let local_share = FE::random(rng);
            local_shares.push(local_share);
            remote_shares.push(*value - local_share);
        }

        let local_macs = self
            .fcom_fe
            .local()
            .get_refmut()
            .input(channel, rng, &local_shares)?;
        channel.write_serializable_seq::<FE>(&remote_shares)?;
        channel.flush()?;
        let remote_auth = self
            .fcom_fe
            .remote()
            .get_refmut()
            .input(channel, rng, values.len())?;

        Ok(local_shares
            .into_iter()
            .zip(local_macs.into_iter())
            .zip(remote_auth.into_iter())
            .map(|((share, mac), auth)| AuthenticatedShare::new(MacProver::new(share, mac), auth))
            .collect())
    }

    fn receive_shared_fe_values<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num: usize,
    ) -> Result<Vec<AuthenticatedShare<FE>>> {
        let remote_auth = self
            .fcom_fe
            .remote()
            .get_refmut()
            .input(channel, rng, num)?;
        let local_shares = channel.read_serializable_seq::<FE>(num)?;
        let local_macs = self
            .fcom_fe
            .local()
            .get_refmut()
            .input(channel, rng, &local_shares)?;
        channel.flush()?;

        Ok(local_shares
            .into_iter()
            .zip(local_macs.into_iter())
            .zip(remote_auth.into_iter())
            .map(|((share, mac), auth)| AuthenticatedShare::new(MacProver::new(share, mac), auth))
            .collect())
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

    fn generate_checked_shared_bit_triples<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num: usize,
    ) -> Result<Vec<SharedBitTriple>> {
        if num == 0 {
            return Ok(Vec::new());
        }

        if self.role.is_first() {
            let mut triples = Vec::with_capacity(num);
            self.local_conv
                .random_triples(channel, rng, num, &mut triples)?;
            self.fcom_f2
                .local()
                .get_refmut()
                .quicksilver_check_multiply(channel, rng, &triples)?;

            let a_values: Vec<_> = triples.iter().map(|(a, _, _)| a.value()).collect();
            let b_values: Vec<_> = triples.iter().map(|(_, b, _)| b.value()).collect();
            let c_values: Vec<_> = triples.iter().map(|(_, _, c)| c.value()).collect();
            let a_shared = self.share_owned_f2_values(channel, rng, &a_values)?;
            let b_shared = self.share_owned_f2_values(channel, rng, &b_values)?;
            let c_shared = self.share_owned_f2_values(channel, rng, &c_values)?;

            Ok(a_shared
                .into_iter()
                .zip(b_shared.into_iter())
                .zip(c_shared.into_iter())
                .map(|((a, b), c)| SharedBitTriple { a, b, c })
                .collect())
        } else {
            let mut triples = Vec::with_capacity(num);
            self.remote_conv
                .random_triples(channel, rng, num, &mut triples)?;
            self.fcom_f2
                .remote()
                .get_refmut()
                .quicksilver_check_multiply(channel, rng, &triples)?;

            let a_shared = self.receive_shared_f2_values(channel, rng, num)?;
            let b_shared = self.receive_shared_f2_values(channel, rng, num)?;
            let c_shared = self.receive_shared_f2_values(channel, rng, num)?;

            Ok(a_shared
                .into_iter()
                .zip(b_shared.into_iter())
                .zip(c_shared.into_iter())
                .map(|((a, b), c)| SharedBitTriple { a, b, c })
                .collect())
        }
    }

    fn generate_checked_shared_dabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num: usize,
    ) -> Result<Vec<SharedDabit<FE>>> {
        if num == 0 {
            return Ok(Vec::new());
        }

        if self.role.is_first() {
            let dabits: Vec<DabitProver<FE>> = self.local_conv.random_dabits(channel, rng, num)?;
            self.local_conv.fdabit(channel, rng, &dabits)?;

            let bit_values: Vec<_> = dabits.iter().map(|dabit| dabit.bit.value()).collect();
            let field_values: Vec<_> = dabits.iter().map(|dabit| dabit.value.value()).collect();
            let shared_bits = self.share_owned_f2_values(channel, rng, &bit_values)?;
            let shared_values = self.share_owned_fe_values(channel, rng, &field_values)?;

            Ok(shared_bits
                .into_iter()
                .zip(shared_values.into_iter())
                .map(|(bit, value)| SharedDabit { bit, value })
                .collect())
        } else {
            let dabits: Vec<DabitVerifier<FE>> =
                self.remote_conv.random_dabits(channel, rng, num)?;
            self.remote_conv.fdabit(channel, rng, &dabits)?;

            let shared_bits = self.receive_shared_f2_values(channel, rng, num)?;
            let shared_values = self.receive_shared_fe_values(channel, rng, num)?;

            Ok(shared_bits
                .into_iter()
                .zip(shared_values.into_iter())
                .map(|(bit, value)| SharedDabit { bit, value })
                .collect())
        }
    }

    fn multiply_shared_bits<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        lhs: &[AuthenticatedShare<F40b>],
        rhs: &[AuthenticatedShare<F40b>],
        triples: &[SharedBitTriple],
    ) -> Result<Vec<AuthenticatedShare<F40b>>> {
        let d_masks: Vec<_> = lhs
            .iter()
            .zip(triples.iter())
            .map(|(x, triple)| self.add_bit_shares(*x, triple.a))
            .collect();
        let e_masks: Vec<_> = rhs
            .iter()
            .zip(triples.iter())
            .map(|(y, triple)| self.add_bit_shares(*y, triple.b))
            .collect();
        let d_values = self.open_shared_bit_batch(channel, &d_masks)?;
        let e_values = self.open_shared_bit_batch(channel, &e_masks)?;

        Ok(triples
            .iter()
            .zip(d_values.into_iter().zip(e_values.into_iter()))
            .map(|(triple, (d, e))| {
                let mut product = triple.c;
                if d == F2::ONE {
                    product = self.add_bit_shares(product, triple.b);
                }
                if e == F2::ONE {
                    product = self.add_bit_shares(product, triple.a);
                }
                if d * e == F2::ONE {
                    product = self.add_bit_const(product, F2::ONE);
                }
                product
            })
            .collect())
    }

    fn add_private_bit_contributions<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        lhs: &[SharedEdabit<FE>],
        rhs: &[SharedEdabit<FE>],
        triples: &[SharedBitTriple],
    ) -> Result<(
        Vec<Vec<AuthenticatedShare<F40b>>>,
        Vec<AuthenticatedShare<F40b>>,
    )> {
        if lhs.is_empty() {
            return Ok((Vec::new(), Vec::new()));
        }

        let num = lhs.len();
        let bit_size = lhs[0].bit_len();
        let mut carry = vec![self.zero_bit_share(); num];
        let mut sums = vec![Vec::with_capacity(bit_size); num];
        let mut triple_offset = 0;

        for bit_idx in 0..bit_size {
            let mut and1_batch = Vec::with_capacity(num);
            let mut and2_batch = Vec::with_capacity(num);
            for row in 0..num {
                let and1 = self.add_bit_shares(lhs[row].bits[bit_idx], carry[row]);
                let and2 = self.add_bit_shares(rhs[row].bits[bit_idx], carry[row]);
                let sum = self.add_bit_shares(and1, rhs[row].bits[bit_idx]);
                sums[row].push(sum);
                and1_batch.push(and1);
                and2_batch.push(and2);
            }

            let and_results = self.multiply_shared_bits(
                channel,
                &and1_batch,
                &and2_batch,
                &triples[triple_offset..triple_offset + num],
            )?;
            triple_offset += num;
            for (carry_slot, and_result) in carry.iter_mut().zip(and_results.into_iter()) {
                *carry_slot = self.add_bit_shares(*carry_slot, and_result);
            }
        }

        Ok((sums, carry))
    }

    fn convert_shared_bits_to_field<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        bits: &[AuthenticatedShare<F40b>],
        dabits: &[SharedDabit<FE>],
    ) -> Result<Vec<AuthenticatedShare<FE>>> {
        let masked_bits: Vec<_> = bits
            .iter()
            .zip(dabits.iter())
            .map(|(bit, dabit)| self.add_bit_shares(*bit, dabit.bit))
            .collect();
        let opened_masks = self.open_shared_bit_batch(channel, &masked_bits)?;

        Ok(dabits
            .iter()
            .zip(opened_masks.into_iter())
            .map(|(dabit, mask)| {
                if mask == F2::ZERO {
                    dabit.value
                } else {
                    let negated = self.negate_field_share(dabit.value);
                    self.add_field_const(negated, FE::PrimeField::ONE)
                }
            })
            .collect())
    }

    fn sum_private_arithmetic_shares(
        &mut self,
        state: &PrivateEdabitState<FE>,
    ) -> Vec<AuthenticatedShare<FE>> {
        state
            .private_edabits
            .iter()
            .zip(state.peer_private_edabits.iter())
            .map(|(local, remote)| {
                AuthenticatedShare::new(
                    self.fcom_fe
                        .local()
                        .get_refmut()
                        .add(local.shared.value.local, remote.value.local),
                    self.fcom_fe
                        .remote()
                        .get_refmut()
                        .add(local.shared.value.remote, remote.value.remote),
                )
            })
            .collect()
    }

    fn apply_overflow_correction(
        &mut self,
        arithmetic_sums: &[AuthenticatedShare<FE>],
        carry_field_shares: &[AuthenticatedShare<FE>],
        bit_size: usize,
    ) -> Vec<AuthenticatedShare<FE>> {
        let correction_scale = -power_two::<FE>(bit_size);
        arithmetic_sums
            .iter()
            .zip(carry_field_shares.iter())
            .map(|(sum, carry)| {
                let local_correction = self
                    .fcom_fe
                    .local()
                    .get_refmut()
                    .affine_mult_cst(correction_scale, carry.local);
                let remote_correction = self
                    .fcom_fe
                    .remote()
                    .get_refmut()
                    .affine_mult_cst(correction_scale, carry.remote);
                AuthenticatedShare::new(
                    self.fcom_fe
                        .local()
                        .get_refmut()
                        .add(sum.local, local_correction),
                    self.fcom_fe
                        .remote()
                        .get_refmut()
                        .add(sum.remote, remote_correction),
                )
            })
            .collect()
    }

    fn assemble_global_edabits(
        &mut self,
        bit_shares: &[Vec<AuthenticatedShare<F40b>>],
        value_shares: &[AuthenticatedShare<FE>],
    ) -> Vec<GlobalEdabit<FE>> {
        bit_shares
            .iter()
            .zip(value_shares.iter())
            .map(|(bits, value)| SharedEdabit {
                bits: bits.clone(),
                value: *value,
            })
            .collect()
    }

    /// Combine the authenticated-share `private_edabits` into final
    /// authenticated-share `global_edabits`.
    pub fn combine_private_into_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &PrivateEdabitState<FE>,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        if state.private_edabits.is_empty() {
            return Ok(Vec::new());
        }

        let bit_size = state.private_edabits[0].shared.bit_len();
        let num = state.private_edabits.len();
        let shared_triples =
            self.generate_checked_shared_bit_triples(channel, rng, num * bit_size)?;
        let shared_dabits = self.generate_checked_shared_dabits(channel, rng, num)?;
        let own_private: Vec<_> = state
            .private_edabits
            .iter()
            .map(|private| private.shared.clone())
            .collect();
        let peer_private = state.peer_private_edabits.clone();
        let (first_party_private, second_party_private) = if self.role.is_first() {
            (own_private, peer_private)
        } else {
            (peer_private, own_private)
        };
        let (global_bits, overflow_carries) = self.add_private_bit_contributions(
            channel,
            &first_party_private,
            &second_party_private,
            &shared_triples,
        )?;
        let carry_field_shares =
            self.convert_shared_bits_to_field(channel, &overflow_carries, &shared_dabits)?;
        let arithmetic_sums = self.sum_private_arithmetic_shares(state);
        let corrected_values =
            self.apply_overflow_correction(&arithmetic_sums, &carry_field_shares, bit_size);
        Ok(self.assemble_global_edabits(&global_bits, &corrected_values))
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
    /// - QuickSilver-checked shared bit triples for the ripple-carry AND gates
    /// - checked shared dabits for overflow-bit conversion
    ///
    /// This is a coarse estimate for the new MPC-specific combine path.
    pub fn estimate_voles(num: usize, bit_size: u32) -> (usize, usize) {
        let (proof_f2_local, proof_fe_local) = ProverConv::<FE>::estimate_voles(num, bit_size);
        let (proof_f2_remote, proof_fe_remote) = VerifierConv::<FE>::estimate_voles(num, bit_size);
        let share_private_f2 = 4 * num * bit_size as usize;
        let share_private_fe = 4 * num;
        let triple_f2 = 6 * num * bit_size as usize + Degree::<F40b>::USIZE;
        let dabit_f2 = 2 * num;
        let dabit_fe = 2 * num + Degree::<FE>::USIZE;
        (
            proof_f2_local + proof_f2_remote + share_private_f2 + triple_f2 + dabit_f2,
            proof_fe_local + proof_fe_remote + share_private_fe + dabit_fe,
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
