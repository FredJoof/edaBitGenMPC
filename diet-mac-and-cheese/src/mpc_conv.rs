//! MPC-facing edaBit types built around authenticated secret shares.
//!
//! Correspondence with the ZK-oriented code:
//! - [`crate::conv::EdabitsProver`] and [`crate::conv::EdabitsVerifier`] are
//!   still used internally for the owner/checker consistency proof.
//! - This module adds the MPC-facing state on top: `private_edabits` are
//!   per-party contributions that also exist as authenticated secret shares,
//!   while `global_edabits` are the final combined authenticated secret shares.

use crate::conv::{EdabitsProver, EdabitsVerifier};
use crate::mpc_homcom::{LocalAuth, RemoteAuth};
use scuttlebutt::field::{F40b, FiniteField, F2};

/// A current-peer view of a single authenticated secret share.
///
/// `local` is the additive share owned by the current peer and authenticated
/// towards the peer on the other side of the channel. `remote` is the
/// authentication state held for the peer's additive share.
#[derive(Clone, Copy, Debug)]
pub struct AuthenticatedShare<FE: FiniteField> {
    pub local: LocalAuth<FE>,
    pub remote: RemoteAuth<FE>,
}

impl<FE: FiniteField> AuthenticatedShare<FE> {
    pub fn new(local: LocalAuth<FE>, remote: RemoteAuth<FE>) -> Self {
        Self { local, remote }
    }
}

/// An edaBit represented as authenticated secret shares.
#[derive(Clone, Debug)]
pub struct SharedEdabit<FE: FiniteField> {
    pub bits: Vec<AuthenticatedShare<F40b>>,
    pub value: AuthenticatedShare<FE>,
}

impl<FE: FiniteField> SharedEdabit<FE> {
    pub fn bit_len(&self) -> usize {
        self.bits.len()
    }
}

/// A private edaBit contribution sampled by the current peer.
///
/// The sampler keeps the clear value for the local proof/check path, but the
/// same contribution also exists as authenticated secret shares in `shared`.
#[derive(Clone, Debug)]
pub struct PrivateEdabit<FE: FiniteField> {
    pub clear_bits: Vec<F2>,
    pub clear_value: FE::PrimeField,
    pub shared: SharedEdabit<FE>,
}

/// Internal MPC state for the private-contribution phase.
#[derive(Clone, Debug)]
pub struct PrivateEdabitState<FE: FiniteField> {
    pub private_edabits: Vec<PrivateEdabit<FE>>,
    pub peer_private_edabits: Vec<SharedEdabit<FE>>,
    pub private_proof_edabits: Vec<EdabitsProver<FE>>,
    pub peer_private_proof_edabits: Vec<EdabitsVerifier<FE>>,
}

impl<FE: FiniteField> PrivateEdabitState<FE> {
    pub fn len(&self) -> usize {
        self.private_edabits.len()
    }

    pub fn is_empty(&self) -> bool {
        self.private_edabits.is_empty()
    }
}

/// Final combined authenticated secret-shared edaBit.
pub type GlobalEdabit<FE> = SharedEdabit<FE>;
