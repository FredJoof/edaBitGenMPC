//! MPC-oriented wrappers around the directional VOLE/tag functionality in
//! [`crate::homcom`].
//!
//! Correspondence with the ZK-oriented code:
//! - [`crate::homcom`] exposes one direction for values owned by the sender
//!   (`FComProver`) and one direction for values checked by the receiver
//!   (`FComVerifier`).
//! - This module packages both directions into a peer-facing field backend so a
//!   single MPC peer can both distribute its own shares and authenticate the
//!   peer's shares on the same channel.

use crate::edabits::RcRefCell;
use crate::homcom::{FComProver, FComVerifier, MacProver, MacVerifier};
use eyre::Result;
use ocelot::svole::wykw::LpnParams;
use rand::{CryptoRng, Rng};
use scuttlebutt::{field::FiniteField, AbstractChannel};

/// Local authenticated value owned by the current peer.
pub type LocalAuth<FE> = MacProver<FE>;

/// Authentication state held by the current peer for a value owned by the peer
/// on the other side of the channel.
pub type RemoteAuth<FE> = MacVerifier<FE>;

/// Fixed ordering used to turn the directional homcom setup into a peer-facing
/// API without exposing prover/verifier terminology to callers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PeerRole {
    /// This peer initializes its outbound VOLE/auth direction first.
    First,
    /// This peer initializes its inbound VOLE/auth direction first.
    Second,
}

impl PeerRole {
    pub fn is_first(self) -> bool {
        matches!(self, Self::First)
    }
}

/// Bidirectional VOLE/auth state for a single field.
///
/// `local` is the direction used when this peer distributes a share it owns.
/// `remote` is the direction used when the peer on the other side distributes a
/// share it owns.
pub struct PeerFieldMacs<FE: FiniteField> {
    local: RcRefCell<FComProver<FE>>,
    remote: RcRefCell<FComVerifier<FE>>,
}

impl<FE: FiniteField> PeerFieldMacs<FE> {
    /// Initialize the two directional homcom instances in a role-dependent
    /// order so both peers can call the same API symmetrically.
    pub fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        role: PeerRole,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
    ) -> Result<Self> {
        let (local, remote) = if role.is_first() {
            (
                FComProver::init(channel, rng, lpn_setup, lpn_extend)?,
                FComVerifier::init(channel, rng, lpn_setup, lpn_extend)?,
            )
        } else {
            let remote = FComVerifier::init(channel, rng, lpn_setup, lpn_extend)?;
            let local = FComProver::init(channel, rng, lpn_setup, lpn_extend)?;
            (local, remote)
        };

        Ok(Self {
            local: RcRefCell::new(local),
            remote: RcRefCell::new(remote),
        })
    }

    /// Outbound direction used for this peer's locally owned shares.
    pub fn local(&self) -> &RcRefCell<FComProver<FE>> {
        &self.local
    }

    /// Inbound direction used for shares owned by the remote peer.
    pub fn remote(&self) -> &RcRefCell<FComVerifier<FE>> {
        &self.remote
    }
}
