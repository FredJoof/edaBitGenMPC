//! SPDZ-facing edaBit types built around authenticated additive secret shares.
//!
//! Correspondence with the VOLE-backed MPC code:
//! - [`crate::mpc_conv`] stores one local share and one remote-auth object.
//! - This module stores the SPDZ-style local value share together with the
//!   current peer's MAC share under a shared global MAC key.

use scuttlebutt::field::{F40b, FiniteField, F2};

/// A current-peer view of a SPDZ-style authenticated additive share.
#[derive(Clone, Copy, Debug)]
pub struct SpdzAuthenticatedShare<MF: FiniteField> {
    pub share: MF::PrimeField,
    pub mac: MF,
}

impl<MF: FiniteField> SpdzAuthenticatedShare<MF> {
    pub fn new(share: MF::PrimeField, mac: MF) -> Self {
        Self { share, mac }
    }
}

pub type SpdzBitShare = SpdzAuthenticatedShare<F40b>;
pub type SpdzFieldShare<FE> = SpdzAuthenticatedShare<FE>;

/// An edaBit represented as SPDZ-style authenticated additive shares.
#[derive(Clone, Debug)]
pub struct SpdzSharedEdabit<FE: FiniteField> {
    pub bits: Vec<SpdzBitShare>,
    pub value: SpdzFieldShare<FE>,
}

impl<FE: FiniteField> SpdzSharedEdabit<FE> {
    pub fn bit_len(&self) -> usize {
        self.bits.len()
    }
}

/// A private edaBit contribution sampled by the current peer.
#[derive(Clone, Debug)]
pub struct SpdzPrivateEdabit<FE: FiniteField> {
    pub clear_bits: Vec<F2>,
    pub clear_value: FE::PrimeField,
    pub shared: SpdzSharedEdabit<FE>,
}

/// Final combined authenticated secret-shared edaBit in the SPDZ path.
pub type SpdzGlobalEdabit<FE> = SpdzSharedEdabit<FE>;
