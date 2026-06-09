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
use std::time::Duration;

struct LocalPrivateEdabitBatch<FE: FiniteField> {
    private_edabits: Vec<PrivateEdabit<FE>>,
    proof_edabits: Vec<crate::conv::EdabitsProver<FE>>,
}

struct RemotePrivateEdabitBatch<FE: FiniteField> {
    peer_private_edabits: Vec<SharedEdabit<FE>>,
    peer_private_proof_edabits: Vec<crate::conv::EdabitsVerifier<FE>>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct MpcEdabitsCheckBreakdown {
    pub aux: Duration,
    pub core: Duration,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PrivateInputSharingPolicy {
    RandomAdditive,
    OwnerZero,
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

    fn share_private_clear_edabits_with_policy<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        clear_bits: &[Vec<F2>],
        clear_values: &[FE],
        policy: PrivateInputSharingPolicy,
    ) -> Result<Vec<PrivateEdabit<FE>>> {
        let num = clear_bits.len();
        let bit_size = clear_bits.first().map_or(0, Vec::len);
        debug_assert_eq!(num, clear_values.len());
        let mut local_bit_shares = Vec::with_capacity(num);
        let mut remote_bit_shares = Vec::with_capacity(num);
        let mut local_value_shares = Vec::with_capacity(num);
        let mut remote_value_shares = Vec::with_capacity(num);

        for (proof_bits, proof_value) in clear_bits.iter().zip(clear_values.iter().copied()) {
            let (local_bits, remote_bits) = match policy {
                PrivateInputSharingPolicy::RandomAdditive => {
                    let mut local_bits = Vec::with_capacity(bit_size);
                    let mut remote_bits = Vec::with_capacity(bit_size);
                    for bit in proof_bits {
                        let local_bit = F2::random(rng);
                        local_bits.push(local_bit);
                        remote_bits.push(*bit + local_bit);
                    }
                    (local_bits, remote_bits)
                }
                PrivateInputSharingPolicy::OwnerZero => {
                    (proof_bits.clone(), vec![F2::ZERO; bit_size])
                }
            };

            let (local_value, remote_value) = match policy {
                PrivateInputSharingPolicy::RandomAdditive => {
                    let local_value = FE::random(rng);
                    (local_value, proof_value - local_value)
                }
                PrivateInputSharingPolicy::OwnerZero => (proof_value, FE::ZERO),
            };

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

        let (remote_bit_auth, remote_value_auth) = match policy {
            PrivateInputSharingPolicy::RandomAdditive => {
                channel.write_serializable_seq::<F2>(&flatten_bits(&remote_bit_shares))?;
                channel.write_serializable_seq::<FE>(&remote_value_shares)?;
                channel.flush()?;

                let remote_bit_auth = self.fcom_f2.remote().get_refmut().input(
                    channel,
                    rng,
                    flat_local_bits.len(),
                )?;
                let remote_value_auth = self
                    .fcom_fe
                    .remote()
                    .get_refmut()
                    .input(channel, rng, num)?;
                (remote_bit_auth, remote_value_auth)
            }
            PrivateInputSharingPolicy::OwnerZero => {
                channel.flush()?;
                (
                    vec![self.zero_bit_share().remote; flat_local_bits.len()],
                    vec![self.zero_field_share().remote; num],
                )
            }
        };

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

        Ok(private_edabits)
    }

    fn sample_private_edabits_with_policy<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
        policy: PrivateInputSharingPolicy,
    ) -> Result<LocalPrivateEdabitBatch<FE>> {
        let proof_edabits = self
            .local_conv
            .random_edabits(channel, rng, bit_size, num)?;
        let clear_bits: Vec<_> = proof_edabits
            .iter()
            .map(|proof| proof.bits.iter().map(|bit| bit.value()).collect())
            .collect();
        let clear_values: Vec<_> = proof_edabits
            .iter()
            .map(|proof| proof.value.value())
            .collect();
        let private_edabits = self.share_private_clear_edabits_with_policy(
            channel,
            rng,
            &clear_bits,
            &clear_values,
            policy,
        )?;

        Ok(LocalPrivateEdabitBatch {
            private_edabits,
            proof_edabits,
        })
    }

    fn sample_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<LocalPrivateEdabitBatch<FE>> {
        self.sample_private_edabits_with_policy(
            channel,
            rng,
            bit_size,
            num,
            PrivateInputSharingPolicy::RandomAdditive,
        )
    }

    fn sample_private_edabits_owner_zero<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<LocalPrivateEdabitBatch<FE>> {
        self.sample_private_edabits_with_policy(
            channel,
            rng,
            bit_size,
            num,
            PrivateInputSharingPolicy::OwnerZero,
        )
    }

    fn receive_private_edabit_contributions_with_policy<
        C: AbstractChannel,
        RNG: CryptoRng + Rng,
    >(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
        policy: PrivateInputSharingPolicy,
    ) -> Result<Vec<SharedEdabit<FE>>> {
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

        let (remote_bit_shares, remote_value_shares, local_bit_macs, local_value_macs) =
            match policy {
                PrivateInputSharingPolicy::RandomAdditive => {
                    let remote_bit_shares = channel.read_serializable_seq::<F2>(num * bit_size)?;
                    let remote_value_shares = channel.read_serializable_seq::<FE>(num)?;

                    let local_bit_macs = self.fcom_f2.local().get_refmut().input(
                        channel,
                        rng,
                        &remote_bit_shares,
                    )?;
                    let local_value_macs = self.fcom_fe.local().get_refmut().input(
                        channel,
                        rng,
                        &remote_value_shares,
                    )?;
                    (
                        remote_bit_shares,
                        remote_value_shares,
                        local_bit_macs,
                        local_value_macs,
                    )
                }
                PrivateInputSharingPolicy::OwnerZero => (
                    vec![F2::ZERO; num * bit_size],
                    vec![FE::ZERO; num],
                    vec![F40b::ZERO; num * bit_size],
                    vec![FE::ZERO; num],
                ),
            };

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

        Ok(peer_private_edabits)
    }

    fn receive_peer_private_edabits_with_policy<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
        policy: PrivateInputSharingPolicy,
    ) -> Result<RemotePrivateEdabitBatch<FE>> {
        let peer_private_proof_edabits = self
            .remote_conv
            .random_edabits(channel, rng, bit_size, num)?;
        let peer_private_edabits = self.receive_private_edabit_contributions_with_policy(
            channel, rng, bit_size, num, policy,
        )?;

        Ok(RemotePrivateEdabitBatch {
            peer_private_edabits,
            peer_private_proof_edabits,
        })
    }

    fn receive_peer_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<RemotePrivateEdabitBatch<FE>> {
        self.receive_peer_private_edabits_with_policy(
            channel,
            rng,
            bit_size,
            num,
            PrivateInputSharingPolicy::RandomAdditive,
        )
    }

    fn receive_peer_private_edabits_owner_zero<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<RemotePrivateEdabitBatch<FE>> {
        self.receive_peer_private_edabits_with_policy(
            channel,
            rng,
            bit_size,
            num,
            PrivateInputSharingPolicy::OwnerZero,
        )
    }

    /// Sampling/input plus sharing/authentication stage for `private_edabits`.
    pub fn sample_and_share_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<PrivateEdabitState<FE>> {
        self.sample_and_share_private_edabits_with_policy(
            channel,
            rng,
            bit_size,
            num,
            PrivateInputSharingPolicy::RandomAdditive,
        )
    }

    /// Sampling/input stage for `private_edabits` using owner/0 sharing:
    /// the owner keeps the full authenticated share of each local contribution
    /// and the peer receives a literal authenticated zero share.
    pub fn sample_and_share_private_edabits_owner_zero<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<PrivateEdabitState<FE>> {
        self.sample_and_share_private_edabits_with_policy(
            channel,
            rng,
            bit_size,
            num,
            PrivateInputSharingPolicy::OwnerZero,
        )
    }

    /// Run the existing conversion-consistency check on previously sampled
    /// private edaBits.
    pub fn verify_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &PrivateEdabitState<FE>,
    ) -> Result<()> {
        let (num_bucket, num_cut) = select_cut_and_choose_parameters(state.len());
        self.cut_and_choose_private(channel, rng, num_bucket, num_cut, state)
    }

    pub fn last_check_breakdown(&self) -> MpcEdabitsCheckBreakdown {
        let local = self.local_conv.last_conv_timing();
        let remote = self.remote_conv.last_conv_timing();
        MpcEdabitsCheckBreakdown {
            aux: local.aux + remote.aux,
            core: local.core + remote.core,
        }
    }

    fn sample_and_share_private_edabits_with_policy<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
        policy: PrivateInputSharingPolicy,
    ) -> Result<PrivateEdabitState<FE>> {
        let (local, remote) = if self.role.is_first() {
            let local = match policy {
                PrivateInputSharingPolicy::RandomAdditive => {
                    self.sample_private_edabits(channel, rng, bit_size, num)?
                }
                PrivateInputSharingPolicy::OwnerZero => {
                    self.sample_private_edabits_owner_zero(channel, rng, bit_size, num)?
                }
            };
            let remote = match policy {
                PrivateInputSharingPolicy::RandomAdditive => {
                    self.receive_peer_private_edabits(channel, rng, bit_size, num)?
                }
                PrivateInputSharingPolicy::OwnerZero => {
                    self.receive_peer_private_edabits_owner_zero(channel, rng, bit_size, num)?
                }
            };
            (local, remote)
        } else {
            let remote = match policy {
                PrivateInputSharingPolicy::RandomAdditive => {
                    self.receive_peer_private_edabits(channel, rng, bit_size, num)?
                }
                PrivateInputSharingPolicy::OwnerZero => {
                    self.receive_peer_private_edabits_owner_zero(channel, rng, bit_size, num)?
                }
            };
            let local = match policy {
                PrivateInputSharingPolicy::RandomAdditive => {
                    self.sample_private_edabits(channel, rng, bit_size, num)?
                }
                PrivateInputSharingPolicy::OwnerZero => {
                    self.sample_private_edabits_owner_zero(channel, rng, bit_size, num)?
                }
            };
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
        self.generate_global_edabits_with_policy(
            channel,
            rng,
            bit_size,
            num,
            PrivateInputSharingPolicy::RandomAdditive,
        )
    }

    /// Full MPC flow using owner/0 input sharing for the private contribution
    /// layer before the existing global-combine step.
    pub fn generate_global_edabits_owner_zero<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        self.generate_global_edabits_with_policy(
            channel,
            rng,
            bit_size,
            num,
            PrivateInputSharingPolicy::OwnerZero,
        )
    }

    fn generate_global_edabits_with_policy<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
        policy: PrivateInputSharingPolicy,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        let (num_bucket, num_cut) = select_cut_and_choose_parameters(num);
        let state =
            self.sample_and_share_private_edabits_with_policy(channel, rng, bit_size, num, policy)?;
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

    /// Backwards-compatible alias for the owner/0 private-input-sharing
    /// variant.
    pub fn generate_edabits_owner_zero<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        self.generate_global_edabits_owner_zero(channel, rng, bit_size, num)
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
    use scuttlebutt::{
        field::{F40b, F61p},
        AesRng, Channel,
    };
    use std::{
        io::{BufReader, BufWriter},
        os::unix::net::UnixStream,
    };

    fn run_opened_global_edabits_with_policy(
        policy: PrivateInputSharingPolicy,
        bit_size: usize,
        num: usize,
        full_generate: bool,
    ) -> Vec<(Vec<F2>, F61p)> {
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
            let global_edabits = if full_generate {
                match policy {
                    PrivateInputSharingPolicy::RandomAdditive => peer
                        .generate_global_edabits(&mut channel, &mut rng, bit_size, num)
                        .unwrap(),
                    PrivateInputSharingPolicy::OwnerZero => peer
                        .generate_global_edabits_owner_zero(&mut channel, &mut rng, bit_size, num)
                        .unwrap(),
                }
            } else {
                let state = match policy {
                    PrivateInputSharingPolicy::RandomAdditive => peer
                        .sample_and_share_private_edabits(&mut channel, &mut rng, bit_size, num)
                        .unwrap(),
                    PrivateInputSharingPolicy::OwnerZero => peer
                        .sample_and_share_private_edabits_owner_zero(
                            &mut channel,
                            &mut rng,
                            bit_size,
                            num,
                        )
                        .unwrap(),
                };
                peer.combine_private_into_global_edabits(&mut channel, &mut rng, &state)
                    .unwrap()
            };

            peer.open_global_edabits(&mut channel, &global_edabits)
                .unwrap()
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
        let global_edabits = if full_generate {
            match policy {
                PrivateInputSharingPolicy::RandomAdditive => peer
                    .generate_global_edabits(&mut channel, &mut rng, bit_size, num)
                    .unwrap(),
                PrivateInputSharingPolicy::OwnerZero => peer
                    .generate_global_edabits_owner_zero(&mut channel, &mut rng, bit_size, num)
                    .unwrap(),
            }
        } else {
            let state = match policy {
                PrivateInputSharingPolicy::RandomAdditive => peer
                    .sample_and_share_private_edabits(&mut channel, &mut rng, bit_size, num)
                    .unwrap(),
                PrivateInputSharingPolicy::OwnerZero => peer
                    .sample_and_share_private_edabits_owner_zero(
                        &mut channel,
                        &mut rng,
                        bit_size,
                        num,
                    )
                    .unwrap(),
            };
            peer.combine_private_into_global_edabits(&mut channel, &mut rng, &state)
                .unwrap()
        };

        let opened = peer
            .open_global_edabits(&mut channel, &global_edabits)
            .unwrap();
        let peer_opened = handle.join().unwrap();
        assert_eq!(opened, peer_opened);
        opened
    }

    fn fixed_clear_edabits(
        role_offset: usize,
        bit_size: usize,
        num: usize,
    ) -> (Vec<Vec<F2>>, Vec<F61p>) {
        let mut clear_bits = Vec::with_capacity(num);
        let mut clear_values = Vec::with_capacity(num);
        for i in 0..num {
            let bits: Vec<_> = (0..bit_size)
                .map(|j| {
                    if ((i * 13 + j * 7 + role_offset) % 2) == 0 {
                        F2::ZERO
                    } else {
                        F2::ONE
                    }
                })
                .collect();
            clear_values.push(convert_bits_to_field::<F61p>(&bits));
            clear_bits.push(bits);
        }
        (clear_bits, clear_values)
    }

    fn run_opened_combined_edabits_for_fixed_inputs(
        policy: PrivateInputSharingPolicy,
        bit_size: usize,
        num: usize,
    ) -> Vec<(Vec<F2>, F61p)> {
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
            let (clear_bits, clear_values) = fixed_clear_edabits(0, bit_size, num);
            let private_edabits = peer
                .share_private_clear_edabits_with_policy(
                    &mut channel,
                    &mut rng,
                    &clear_bits,
                    &clear_values,
                    policy,
                )
                .unwrap();
            let peer_private_edabits = peer
                .receive_private_edabit_contributions_with_policy(
                    &mut channel,
                    &mut rng,
                    bit_size,
                    num,
                    policy,
                )
                .unwrap();
            let state = PrivateEdabitState {
                private_edabits,
                peer_private_edabits,
                private_proof_edabits: Vec::new(),
                peer_private_proof_edabits: Vec::new(),
            };
            let global_edabits = peer
                .combine_private_into_global_edabits(&mut channel, &mut rng, &state)
                .unwrap();
            peer.open_global_edabits(&mut channel, &global_edabits)
                .unwrap()
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
        let (clear_bits, clear_values) = fixed_clear_edabits(1, bit_size, num);
        let peer_private_edabits = peer
            .receive_private_edabit_contributions_with_policy(
                &mut channel,
                &mut rng,
                bit_size,
                num,
                policy,
            )
            .unwrap();
        let private_edabits = peer
            .share_private_clear_edabits_with_policy(
                &mut channel,
                &mut rng,
                &clear_bits,
                &clear_values,
                policy,
            )
            .unwrap();
        let state = PrivateEdabitState {
            private_edabits,
            peer_private_edabits,
            private_proof_edabits: Vec::new(),
            peer_private_proof_edabits: Vec::new(),
        };
        let global_edabits = peer
            .combine_private_into_global_edabits(&mut channel, &mut rng, &state)
            .unwrap();
        let opened = peer
            .open_global_edabits(&mut channel, &global_edabits)
            .unwrap();
        let peer_opened = handle.join().unwrap();
        assert_eq!(opened, peer_opened);
        opened
    }

    // Checks the owner/0 sharing invariant before the combine step:
    // the owner side keeps the full clear contribution and the peer side is
    // represented with literal authenticated zero shares.
    fn assert_owner_zero_state(state: &PrivateEdabitState<F61p>) {
        for private in &state.private_edabits {
            for (clear_bit, shared_bit) in private.clear_bits.iter().zip(private.shared.bits.iter())
            {
                assert_eq!(shared_bit.local.value(), *clear_bit);
                assert_eq!(shared_bit.remote.mac(), F40b::ZERO);
            }
            assert_eq!(private.shared.value.local.value(), private.clear_value);
            assert_eq!(private.shared.value.remote.mac(), F61p::ZERO);
        }

        for peer_private in &state.peer_private_edabits {
            for shared_bit in &peer_private.bits {
                assert_eq!(shared_bit.local.value(), F2::ZERO);
                assert_eq!(shared_bit.local.mac(), F40b::ZERO);
            }
            assert_eq!(peer_private.value.local.value(), F61p::ZERO);
            assert_eq!(peer_private.value.local.mac(), F61p::ZERO);
        }
    }

    // Baseline regression test for the original random-additive private-input
    // sharing path. It generates full global edaBits, opens them, and checks
    // that the opened bits reconstruct to the opened field value.
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

    // End-to-end roundtrip for the new owner/0 input-sharing policy. This
    // shows that keeping the owner's full contribution and giving the peer
    // literal authenticated zeros still produces valid global edaBits.
    #[test]
    fn test_mpc_global_edabits_owner_zero_roundtrip() {
        let opened = run_opened_global_edabits_with_policy(
            PrivateInputSharingPolicy::OwnerZero,
            8,
            1024,
            true,
        );
        assert_eq!(opened.len(), 1024);
        for (bits, value) in opened {
            assert_eq!(bits.len(), 8);
            assert_eq!(convert_bits_to_field::<F61p>(&bits), value);
        }
    }

    // Semantic equivalence test for the combine layer. Both sharing policies
    // are fed the same fixed clear private contributions, and the resulting
    // opened global edaBits must match exactly.
    #[test]
    fn test_mpc_owner_zero_matches_random_share_combine() {
        let random_opened = run_opened_combined_edabits_for_fixed_inputs(
            PrivateInputSharingPolicy::RandomAdditive,
            8,
            64,
        );
        let owner_zero_opened = run_opened_combined_edabits_for_fixed_inputs(
            PrivateInputSharingPolicy::OwnerZero,
            8,
            64,
        );
        assert_eq!(random_opened, owner_zero_opened);
    }

    // Stress test for repeated zero-side contributions. It verifies that the
    // owner/0 private state is populated with literal zero authenticated shares
    // on the peer side, and that reusing those zeros across many wires still
    // combines into valid global edaBits.
    #[test]
    fn test_mpc_owner_zero_private_state_uses_literal_zero_shares() {
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
            let state = peer
                .sample_and_share_private_edabits_owner_zero(&mut channel, &mut rng, 8, 128)
                .unwrap();
            assert_owner_zero_state(&state);
            let global_edabits = peer
                .combine_private_into_global_edabits(&mut channel, &mut rng, &state)
                .unwrap();
            peer.open_global_edabits(&mut channel, &global_edabits)
                .unwrap()
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
        let state = peer
            .sample_and_share_private_edabits_owner_zero(&mut channel, &mut rng, 8, 128)
            .unwrap();
        assert_owner_zero_state(&state);
        let global_edabits = peer
            .combine_private_into_global_edabits(&mut channel, &mut rng, &state)
            .unwrap();
        let opened = peer
            .open_global_edabits(&mut channel, &global_edabits)
            .unwrap();
        let peer_opened = handle.join().unwrap();
        assert_eq!(opened, peer_opened);
        for (bits, value) in opened {
            assert_eq!(convert_bits_to_field::<F61p>(&bits), value);
        }
    }
}
