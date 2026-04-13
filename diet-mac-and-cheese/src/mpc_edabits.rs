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

use crate::edabits::{ProverConv, VerifierConv};
use crate::mpc_conv::{
    AuthenticatedShare, GlobalEdabit, PrivateEdabit, PrivateEdabitState, SharedEdabit,
};
use crate::mpc_edabits_common::{
    estimate_combine_voles, flatten_bits, split_bits, MpcEdabitsCommon,
};
use crate::mpc_homcom::{PeerFieldMacs, PeerRole};
use eyre::Result;
use ocelot::svole::wykw::LpnParams;
use rand::{CryptoRng, Rng};
use scuttlebutt::{
    field::{F40b, FiniteField, F2},
    ring::FiniteRing,
    AbstractChannel,
};

struct LocalPrivateEdabitBatch<FE: FiniteField> {
    private_edabits: Vec<PrivateEdabit<FE>>,
    proof_edabits: Vec<crate::conv::EdabitsProver<FE>>,
}

struct RemotePrivateEdabitBatch<FE: FiniteField> {
    peer_private_edabits: Vec<SharedEdabit<FE>>,
    peer_private_proof_edabits: Vec<crate::conv::EdabitsVerifier<FE>>,
}

pub fn select_cut_and_choose_parameters(num_edabits: usize) -> (usize, usize) {
    crate::mpc_edabits_common::select_cut_and_choose_parameters(num_edabits)
}

/// MPC-facing peer that owns both directions of the A2B flow.
pub struct MpcEdabitsPeer<FE: FiniteField> {
    role: PeerRole,
    pub fcom_f2: PeerFieldMacs<F40b>,
    pub fcom_fe: PeerFieldMacs<FE>,
    local_conv: ProverConv<FE>,
    remote_conv: VerifierConv<FE>,
}

impl<FE: FiniteField<PrimeField = FE>> MpcEdabitsCommon<FE> for MpcEdabitsPeer<FE> {
    fn role(&self) -> PeerRole {
        self.role
    }

    fn fcom_f2(&self) -> &PeerFieldMacs<F40b> {
        &self.fcom_f2
    }

    fn fcom_f2_mut(&mut self) -> &mut PeerFieldMacs<F40b> {
        &mut self.fcom_f2
    }

    fn fcom_fe(&self) -> &PeerFieldMacs<FE> {
        &self.fcom_fe
    }

    fn fcom_fe_mut(&mut self) -> &mut PeerFieldMacs<FE> {
        &mut self.fcom_fe
    }

    fn local_conv_mut(&mut self) -> &mut ProverConv<FE> {
        &mut self.local_conv
    }

    fn remote_conv_mut(&mut self) -> &mut VerifierConv<FE> {
        &mut self.remote_conv
    }
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

    /// Combine the authenticated-share `private_edabits` into final
    /// authenticated-share `global_edabits`.
    pub fn combine_private_into_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &PrivateEdabitState<FE>,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        MpcEdabitsCommon::combine_private_into_global_edabits(
            self,
            channel,
            rng,
            &state.private_edabits,
            &state.peer_private_edabits,
        )
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
        MpcEdabitsCommon::open_global_edabits(self, channel, global_edabits)
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
        estimate_combine_voles::<FE>(num, bit_size)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mpc_edabits_common::convert_bits_to_field;
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
