//! MPC-facing conversion types that mirror the layout of [`crate::conv`]
//! without exposing prover/verifier terminology at the API boundary.
//!
//! Correspondence with the ZK-oriented code:
//! - [`crate::conv::EdabitsProver`] becomes a locally owned MPC batch item.
//! - [`crate::conv::EdabitsVerifier`] becomes the local authentication view of
//!   a batch item owned by the remote peer.

use crate::conv::{EdabitsProver, EdabitsVerifier};
use crate::mpc_homcom::{LocalAuth, RemoteAuth};
use scuttlebutt::field::{F40b, FiniteField};

/// Locally owned daBit view.
pub type LocalDabit<FE> = (LocalAuth<F40b>, LocalAuth<FE>);

/// Authentication view of a daBit owned by the remote peer.
pub type RemoteDabit<FE> = (RemoteAuth<F40b>, RemoteAuth<FE>);

/// Locally owned edaBit view.
pub type LocalEdabit<FE> = EdabitsProver<FE>;

/// Authentication view of an edaBit owned by the remote peer.
pub type RemoteEdabit<FE> = EdabitsVerifier<FE>;

/// The per-peer output of the MPC-oriented edaBits flow.
///
/// `local` contains the final edaBits sampled and owned by the current peer.
/// `remote` contains the authenticated view of the final edaBits sampled and
/// owned by the peer on the other side of the channel.
#[derive(Clone, Debug)]
pub struct PeerEdabitBatch<FE: FiniteField> {
    pub local: Vec<LocalEdabit<FE>>,
    pub remote: Vec<RemoteEdabit<FE>>,
}

impl<FE: FiniteField> PeerEdabitBatch<FE> {
    pub fn new(local: Vec<LocalEdabit<FE>>, remote: Vec<RemoteEdabit<FE>>) -> Self {
        Self { local, remote }
    }

    pub fn len_local(&self) -> usize {
        self.local.len()
    }

    pub fn len_remote(&self) -> usize {
        self.remote.len()
    }

    pub fn is_empty(&self) -> bool {
        self.local.is_empty() && self.remote.is_empty()
    }
}
