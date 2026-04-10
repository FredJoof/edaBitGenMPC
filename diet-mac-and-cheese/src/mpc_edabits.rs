#![allow(clippy::too_many_arguments)]

//! Peer-oriented edaBits / A2B flow built on top of the repository's existing
//! VOLE/tag machinery.
//!
//! Correspondence with the ZK-oriented code:
//! - [`crate::mpc_homcom`] mirrors [`crate::homcom`] with bidirectional,
//!   peer-facing initialization.
//! - [`crate::mpc_conv`] mirrors [`crate::conv`] with neutral local/remote
//!   naming.
//! - This module mirrors [`crate::edabits`] at the orchestration level, but a
//!   single peer now owns both directions and runs the local-owner and
//!   remote-owner phases in a deterministic schedule.
//!
//! The implementation intentionally keeps the underlying VOLE/tag mechanics and
//! QuickSilver-backed checks from the existing codebase. The MPC-facing change
//! is the protocol boundary: each peer samples and distributes its own random
//! edaBits, and each peer also authenticates the edaBits sampled by the peer on
//! the other side.

use crate::conv::{ConvProverT, ConvVerifierT};
use crate::edabits::{ProverConv, VerifierConv};
use crate::mpc_conv::{LocalEdabit, PeerEdabitBatch, RemoteEdabit};
use crate::mpc_homcom::{PeerFieldMacs, PeerRole};
use eyre::Result;
use ocelot::svole::wykw::LpnParams;
use rand::{CryptoRng, Rng};
use scuttlebutt::{
    field::{F40b, FiniteField},
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

    /// Sample locally owned candidate edaBits and distribute their
    /// authenticated shares to the peer on the other side.
    pub fn sample_local_candidates<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Vec<LocalEdabit<FE>>> {
        self.local_conv.random_edabits(channel, rng, bit_size, num)
    }

    /// Receive the authenticated view of candidate edaBits sampled by the peer
    /// on the other side of the channel.
    pub fn receive_remote_candidates<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Vec<RemoteEdabit<FE>>> {
        self.remote_conv.random_edabits(channel, rng, bit_size, num)
    }

    /// Sampling/input plus sharing/authentication stage.
    ///
    /// The ordering is role-dependent so that both peers can call the same
    /// function without deadlocking on the shared duplex channel.
    pub fn sample_and_share_candidates<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<PeerEdabitBatch<FE>> {
        let (local, remote) = if self.role.is_first() {
            (
                self.sample_local_candidates(channel, rng, bit_size, num)?,
                self.receive_remote_candidates(channel, rng, bit_size, num)?,
            )
        } else {
            let remote = self.receive_remote_candidates(channel, rng, bit_size, num)?;
            let local = self.sample_local_candidates(channel, rng, bit_size, num)?;
            (local, remote)
        };

        Ok(PeerEdabitBatch::new(local, remote))
    }

    /// Local-owner cut-and-choose, including the bucket consistency checks
    /// carried by the existing QuickSilver-backed A2B flow.
    pub fn cut_and_choose_local<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num_bucket: usize,
        num_cut: usize,
        edabits: &[LocalEdabit<FE>],
    ) -> Result<()> {
        self.local_conv
            .conv(channel, rng, num_bucket, num_cut, edabits, None)
    }

    /// Remote-owner cut-and-choose, including the bucket consistency checks
    /// carried by the existing QuickSilver-backed A2B flow.
    pub fn cut_and_choose_remote<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num_bucket: usize,
        num_cut: usize,
        edabits: &[RemoteEdabit<FE>],
    ) -> Result<()> {
        self.remote_conv
            .conv(channel, rng, num_bucket, num_cut, edabits, None)
    }

    /// Cut-and-choose plus bucket consistency stage.
    ///
    /// The local-owner and remote-owner checks are run in opposite orders on
    /// the two peers so both directions can share the same network channel.
    pub fn run_cut_and_choose<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num_bucket: usize,
        num_cut: usize,
        batch: &PeerEdabitBatch<FE>,
    ) -> Result<()> {
        if self.role.is_first() {
            self.cut_and_choose_local(channel, rng, num_bucket, num_cut, &batch.local)?;
            self.cut_and_choose_remote(channel, rng, num_bucket, num_cut, &batch.remote)?;
        } else {
            self.cut_and_choose_remote(channel, rng, num_bucket, num_cut, &batch.remote)?;
            self.cut_and_choose_local(channel, rng, num_bucket, num_cut, &batch.local)?;
        }
        Ok(())
    }

    /// Final MPC edaBits flow:
    /// 1. sampling/input
    /// 2. sharing/authentication
    /// 3. cut-and-choose
    /// 4. QuickSilver-backed bucket consistency
    /// 5. return the final local/remote edaBit batches
    pub fn generate_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<PeerEdabitBatch<FE>> {
        let (num_bucket, num_cut) = select_cut_and_choose_parameters(num);
        let batch = self.sample_and_share_candidates(channel, rng, bit_size, num)?;
        self.run_cut_and_choose(channel, rng, num_bucket, num_cut, &batch)?;
        Ok(batch)
    }

    /// Aggregate VOLE estimate for the full peer-facing flow.
    ///
    /// A peer executes both the locally owned and the remotely owned direction,
    /// so the estimate is the sum of the two directional A2B estimates.
    pub fn estimate_voles(num: usize, bit_size: u32) -> (usize, usize) {
        let (n2_local, np_local) = ProverConv::<FE>::estimate_voles(num, bit_size);
        let (n2_remote, np_remote) = VerifierConv::<FE>::estimate_voles(num, bit_size);
        (n2_local + n2_remote, np_local + np_remote)
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
    fn test_mpc_edabits_peer_roundtrip() {
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
            let batch = peer
                .generate_edabits(&mut channel, &mut rng, 8, 1024)
                .unwrap();
            assert_eq!(batch.len_local(), 1024);
            assert_eq!(batch.len_remote(), 1024);
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
        let batch = peer
            .generate_edabits(&mut channel, &mut rng, 8, 1024)
            .unwrap();
        assert_eq!(batch.len_local(), 1024);
        assert_eq!(batch.len_remote(), 1024);
        handle.join().unwrap();
    }
}
