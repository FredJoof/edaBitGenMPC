#![allow(clippy::too_many_arguments)]

//! Peer-oriented 2PC implementation of the original edaBits paper flow.
//!
//! Correspondence with the repository:
//! - [`crate::mpc_homcom`] provides the peer-facing VOLE/tag backend.
//! - [`crate::mpc_conv`] provides the authenticated-share `private_edabits` and
//!   `global_edabits` types.
//! - This module mirrors the original paper's private-edaBit cut-and-choose:
//!   private edaBits and private triples are sampled and shared, a random cut
//!   set is opened, and the remaining buckets are checked with faulty triples.
//!
//! The final combine still follows the paper's Figure 3 structure:
//! - add the private bit contributions with a ripple-carry adder over
//!   authenticated secret-shared bits
//! - convert the overflow carry bits into authenticated field shares
//! - subtract `2^m` times the carry contribution from the summed arithmetic
//!   shares

use crate::edabits::{DabitProver, DabitVerifier, ProverConv, VerifierConv};
use crate::homcom::{MacProver, MacVerifier};
use crate::mpc_conv::{AuthenticatedShare, GlobalEdabit, PrivateEdabit, SharedEdabit};
use crate::mpc_homcom::{PeerFieldMacs, PeerRole};
use eyre::{eyre, Result};
use ocelot::svole::wykw::LpnParams;
use rand::{CryptoRng, Rng, SeedableRng};
use scuttlebutt::{
    field::{F40b, FiniteField, F2},
    ring::FiniteRing,
    AbstractChannel, AesRng, Block,
};

pub fn select_cut_and_choose_parameters(num_edabits: usize) -> (usize, usize) {
    crate::mpc_edabits::select_cut_and_choose_parameters(num_edabits)
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

fn split_bits(flat: &[F2], chunk_size: usize) -> Vec<Vec<F2>> {
    flat.chunks(chunk_size)
        .map(|chunk| chunk.to_vec())
        .collect()
}

fn generate_permutation<T, RNG: CryptoRng + Rng>(rng: &mut RNG, v: &mut [T]) {
    if v.is_empty() {
        return;
    }

    let mut i = v.len() - 1;
    while i > 0 {
        let idx = rng.gen_range(0..i);
        v.swap(idx, i);
        i -= 1;
    }
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

#[derive(Clone, Copy, Debug)]
struct SharedBitTriple {
    a: AuthenticatedShare<F40b>,
    b: AuthenticatedShare<F40b>,
    c: AuthenticatedShare<F40b>,
}

#[derive(Clone, Copy, Debug)]
struct PrivateBitTriple {
    clear_a: F2,
    clear_b: F2,
    clear_c: F2,
    shared: SharedBitTriple,
}

#[derive(Clone, Copy, Debug)]
struct SharedDabit<FE: FiniteField> {
    bit: AuthenticatedShare<F40b>,
    value: AuthenticatedShare<FE>,
}

struct LocalPrivateEdabitBatch<FE: FiniteField> {
    private_edabits: Vec<PrivateEdabit<FE>>,
}

struct RemotePrivateEdabitBatch<FE: FiniteField> {
    peer_private_edabits: Vec<SharedEdabit<FE>>,
}

struct LocalPrivateTripleBatch {
    private_triples: Vec<PrivateBitTriple>,
}

struct RemotePrivateTripleBatch {
    peer_private_triples: Vec<SharedBitTriple>,
}

struct RawPrivateEdabitState<FE: FiniteField> {
    private_edabits: Vec<PrivateEdabit<FE>>,
    peer_private_edabits: Vec<SharedEdabit<FE>>,
    private_triples: Vec<PrivateBitTriple>,
    peer_private_triples: Vec<SharedBitTriple>,
}

struct VerifiedPrivateEdabitState<FE: FiniteField> {
    private_edabits: Vec<PrivateEdabit<FE>>,
    peer_private_edabits: Vec<SharedEdabit<FE>>,
}

pub struct MpcOriginalEdabitsPeer<FE: FiniteField> {
    role: PeerRole,
    pub fcom_f2: PeerFieldMacs<F40b>,
    pub fcom_fe: PeerFieldMacs<FE>,
    local_conv: ProverConv<FE>,
    remote_conv: VerifierConv<FE>,
}

impl<FE: FiniteField<PrimeField = FE>> MpcOriginalEdabitsPeer<FE> {
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

    fn open_shared_field_batch<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        shares: &[AuthenticatedShare<FE>],
    ) -> Result<Vec<FE::PrimeField>> {
        if shares.is_empty() {
            return Ok(Vec::new());
        }

        let local_batch: Vec<_> = shares.iter().map(|share| share.local).collect();
        let remote_batch: Vec<_> = shares.iter().map(|share| share.remote).collect();
        let mut remote_values = Vec::with_capacity(shares.len());
        if self.role.is_first() {
            self.fcom_fe
                .local()
                .get_refmut()
                .open(channel, &local_batch)?;
            self.fcom_fe
                .remote()
                .get_refmut()
                .open(channel, &remote_batch, &mut remote_values)?;
        } else {
            self.fcom_fe
                .remote()
                .get_refmut()
                .open(channel, &remote_batch, &mut remote_values)?;
            self.fcom_fe
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
        let mut clear_bits = Vec::with_capacity(num);
        let mut clear_values = Vec::with_capacity(num);
        for _ in 0..num {
            let mut bits = Vec::with_capacity(bit_size);
            for _ in 0..bit_size {
                bits.push(F2::random(rng));
            }
            clear_values.push(convert_bits_to_field::<FE>(&bits));
            clear_bits.push(bits);
        }

        let flat_bits = flatten_bits(&clear_bits);
        let shared_bits = self.share_owned_f2_values(channel, rng, &flat_bits)?;
        let shared_values = self.share_owned_fe_values(channel, rng, &clear_values)?;
        let shared_bit_rows = split_bits(&flat_bits, bit_size);

        let mut private_edabits = Vec::with_capacity(num);
        let mut bit_offset = 0;
        for i in 0..num {
            let mut bits = Vec::with_capacity(bit_size);
            for _ in 0..bit_size {
                bits.push(shared_bits[bit_offset]);
                bit_offset += 1;
            }
            debug_assert_eq!(shared_bit_rows[i], clear_bits[i]);
            private_edabits.push(PrivateEdabit {
                clear_bits: clear_bits[i].clone(),
                clear_value: clear_values[i],
                shared: SharedEdabit {
                    bits,
                    value: shared_values[i],
                },
            });
        }

        Ok(LocalPrivateEdabitBatch { private_edabits })
    }

    fn receive_peer_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<RemotePrivateEdabitBatch<FE>> {
        let flat_bits = self.receive_shared_f2_values(channel, rng, num * bit_size)?;
        let shared_values = self.receive_shared_fe_values(channel, rng, num)?;

        let mut peer_private_edabits = Vec::with_capacity(num);
        let mut bit_offset = 0;
        for i in 0..num {
            let mut bits = Vec::with_capacity(bit_size);
            for _ in 0..bit_size {
                bits.push(flat_bits[bit_offset]);
                bit_offset += 1;
            }
            peer_private_edabits.push(SharedEdabit {
                bits,
                value: shared_values[i],
            });
        }

        Ok(RemotePrivateEdabitBatch {
            peer_private_edabits,
        })
    }

    fn sample_private_triples<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num: usize,
    ) -> Result<LocalPrivateTripleBatch> {
        let mut a_values = Vec::with_capacity(num);
        let mut b_values = Vec::with_capacity(num);
        let mut c_values = Vec::with_capacity(num);
        for _ in 0..num {
            let a = F2::random(rng);
            let b = F2::random(rng);
            let c = a * b;
            a_values.push(a);
            b_values.push(b);
            c_values.push(c);
        }

        let shared_a = self.share_owned_f2_values(channel, rng, &a_values)?;
        let shared_b = self.share_owned_f2_values(channel, rng, &b_values)?;
        let shared_c = self.share_owned_f2_values(channel, rng, &c_values)?;

        let mut private_triples = Vec::with_capacity(num);
        for i in 0..num {
            private_triples.push(PrivateBitTriple {
                clear_a: a_values[i],
                clear_b: b_values[i],
                clear_c: c_values[i],
                shared: SharedBitTriple {
                    a: shared_a[i],
                    b: shared_b[i],
                    c: shared_c[i],
                },
            });
        }

        Ok(LocalPrivateTripleBatch { private_triples })
    }

    fn receive_peer_private_triples<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num: usize,
    ) -> Result<RemotePrivateTripleBatch> {
        let shared_a = self.receive_shared_f2_values(channel, rng, num)?;
        let shared_b = self.receive_shared_f2_values(channel, rng, num)?;
        let shared_c = self.receive_shared_f2_values(channel, rng, num)?;

        let mut peer_private_triples = Vec::with_capacity(num);
        for i in 0..num {
            peer_private_triples.push(SharedBitTriple {
                a: shared_a[i],
                b: shared_b[i],
                c: shared_c[i],
            });
        }

        Ok(RemotePrivateTripleBatch {
            peer_private_triples,
        })
    }

    fn sample_and_share_private_material<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num_edabits: usize,
        num_triples: usize,
    ) -> Result<RawPrivateEdabitState<FE>> {
        let (local_edabits, remote_edabits, local_triples, remote_triples) = if self.role.is_first()
        {
            (
                self.sample_private_edabits(channel, rng, bit_size, num_edabits)?,
                self.receive_peer_private_edabits(channel, rng, bit_size, num_edabits)?,
                self.sample_private_triples(channel, rng, num_triples)?,
                self.receive_peer_private_triples(channel, rng, num_triples)?,
            )
        } else {
            let remote_edabits =
                self.receive_peer_private_edabits(channel, rng, bit_size, num_edabits)?;
            let local_edabits = self.sample_private_edabits(channel, rng, bit_size, num_edabits)?;
            let remote_triples = self.receive_peer_private_triples(channel, rng, num_triples)?;
            let local_triples = self.sample_private_triples(channel, rng, num_triples)?;
            (local_edabits, remote_edabits, local_triples, remote_triples)
        };

        Ok(RawPrivateEdabitState {
            private_edabits: local_edabits.private_edabits,
            peer_private_edabits: remote_edabits.peer_private_edabits,
            private_triples: local_triples.private_triples,
            peer_private_triples: remote_triples.peer_private_triples,
        })
    }

    fn sample_joint_block<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) -> Result<Block> {
        let local = rng.gen::<Block>();
        let remote = if self.role.is_first() {
            channel.write_block(&local)?;
            channel.flush()?;
            channel.read_block()?
        } else {
            let remote = channel.read_block()?;
            channel.write_block(&local)?;
            channel.flush()?;
            remote
        };
        Ok(local ^ remote)
    }

    fn open_and_check_edabits<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        edabits: &[SharedEdabit<FE>],
    ) -> Result<()> {
        if edabits.is_empty() {
            return Ok(());
        }

        let bit_size = edabits[0].bit_len();
        let flat_bits: Vec<_> = edabits
            .iter()
            .flat_map(|edabit| edabit.bits.iter().copied())
            .collect();
        let values: Vec<_> = edabits.iter().map(|edabit| edabit.value).collect();
        let opened_bits = self.open_shared_bit_batch(channel, &flat_bits)?;
        let opened_values = self.open_shared_field_batch(channel, &values)?;
        for (bits, value) in split_bits(&opened_bits, bit_size)
            .into_iter()
            .zip(opened_values)
        {
            if convert_bits_to_field::<FE>(&bits) != value {
                return Err(eyre!("opened private edabit is inconsistent"));
            }
        }
        Ok(())
    }

    fn open_and_check_triples<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        triples: &[SharedBitTriple],
    ) -> Result<()> {
        if triples.is_empty() {
            return Ok(());
        }

        let a_batch: Vec<_> = triples.iter().map(|triple| triple.a).collect();
        let b_batch: Vec<_> = triples.iter().map(|triple| triple.b).collect();
        let c_batch: Vec<_> = triples.iter().map(|triple| triple.c).collect();
        let opened_a = self.open_shared_bit_batch(channel, &a_batch)?;
        let opened_b = self.open_shared_bit_batch(channel, &b_batch)?;
        let opened_c = self.open_shared_bit_batch(channel, &c_batch)?;
        for ((a, b), c) in opened_a
            .into_iter()
            .zip(opened_b.into_iter())
            .zip(opened_c.into_iter())
        {
            if a * b != c {
                return Err(eyre!("opened private triple is inconsistent"));
            }
        }
        Ok(())
    }

    fn multiply_shared_bits_with_triples<C: AbstractChannel>(
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

    fn add_bit_contributions_with_triples<C: AbstractChannel>(
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

            let and_results = self.multiply_shared_bits_with_triples(
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

    fn open_and_check_bucket_pairs<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        edabit_buckets: &[Vec<SharedEdabit<FE>>],
        triple_buckets: &[Vec<SharedBitTriple>],
    ) -> Result<()> {
        if edabit_buckets.is_empty() {
            return Ok(());
        }

        let num_buckets = edabit_buckets.len();
        let bucket_size = edabit_buckets[0].len();
        let bit_size = edabit_buckets[0][0].bit_len();
        let num_pairs = num_buckets * (bucket_size - 1);

        let mut lhs = Vec::with_capacity(num_pairs);
        let mut rhs = Vec::with_capacity(num_pairs);
        let mut triples = Vec::with_capacity(num_pairs * bit_size);
        let mut arithmetic_sums = Vec::with_capacity(num_pairs);
        for bucket_idx in 0..num_buckets {
            let anchor = edabit_buckets[bucket_idx][0].clone();
            for pair_idx in 1..bucket_size {
                let other = edabit_buckets[bucket_idx][pair_idx].clone();
                lhs.push(anchor.clone());
                rhs.push(other.clone());
                arithmetic_sums.push(AuthenticatedShare::new(
                    self.fcom_fe
                        .local()
                        .get_refmut()
                        .add(anchor.value.local, other.value.local),
                    self.fcom_fe
                        .remote()
                        .get_refmut()
                        .add(anchor.value.remote, other.value.remote),
                ));
            }
            triples.extend_from_slice(&triple_buckets[bucket_idx]);
        }

        let (sum_bits, carry_bits) =
            self.add_bit_contributions_with_triples(channel, &lhs, &rhs, &triples)?;
        let carry_dabits = self.generate_checked_shared_dabits(channel, rng, num_pairs)?;
        let carry_field_shares =
            self.convert_shared_bits_to_field(channel, &carry_bits, &carry_dabits)?;
        let correction_scale = -power_two::<FE>(bit_size);
        let corrected_values: Vec<_> = arithmetic_sums
            .into_iter()
            .zip(carry_field_shares.into_iter())
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
            .collect();

        let flat_bits: Vec<_> = sum_bits
            .iter()
            .flat_map(|bits| bits.iter().copied())
            .collect();
        let opened_bits = self.open_shared_bit_batch(channel, &flat_bits)?;
        let opened_values = self.open_shared_field_batch(channel, &corrected_values)?;
        for (bits, value) in split_bits(&opened_bits, bit_size)
            .into_iter()
            .zip(opened_values)
        {
            if convert_bits_to_field::<FE>(&bits) != value {
                return Err(eyre!("bucket consistency check failed"));
            }
        }

        Ok(())
    }

    fn cut_and_choose_local<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num_bucket: usize,
        num_cut: usize,
        private_edabits: &[PrivateEdabit<FE>],
        private_triples: &[PrivateBitTriple],
    ) -> Result<Vec<PrivateEdabit<FE>>> {
        let mut shuffled_private_edabits = private_edabits.to_vec();
        let mut shuffled_shared_edabits: Vec<_> = shuffled_private_edabits
            .iter()
            .map(|private| private.shared.clone())
            .collect();
        let mut shuffled_private_triples = private_triples.to_vec();
        let mut shuffled_shared_triples: Vec<_> = shuffled_private_triples
            .iter()
            .map(|triple| triple.shared)
            .collect();

        let edabit_seed = self.sample_joint_block(channel, rng)?;
        let triple_seed = self.sample_joint_block(channel, rng)?;
        let mut edabit_rng_private = AesRng::from_seed(edabit_seed);
        let mut edabit_rng_shared = AesRng::from_seed(edabit_seed);
        let mut triple_rng_private = AesRng::from_seed(triple_seed);
        let mut triple_rng_shared = AesRng::from_seed(triple_seed);
        generate_permutation(&mut edabit_rng_private, &mut shuffled_private_edabits);
        generate_permutation(&mut edabit_rng_shared, &mut shuffled_shared_edabits);
        generate_permutation(&mut triple_rng_private, &mut shuffled_private_triples);
        generate_permutation(&mut triple_rng_shared, &mut shuffled_shared_triples);

        self.open_and_check_edabits(channel, &shuffled_shared_edabits[..num_cut])?;
        self.open_and_check_triples(channel, &shuffled_shared_triples[..num_cut * bit_size])?;

        for triple in &shuffled_private_triples[..num_cut * bit_size] {
            if triple.clear_a * triple.clear_b != triple.clear_c {
                return Err(eyre!("opened private triple is not correct"));
            }
        }

        let output_num = (shuffled_private_edabits.len() - num_cut) / num_bucket;
        let mut edabit_buckets = Vec::with_capacity(output_num);
        for chunk in shuffled_shared_edabits[num_cut..].chunks(num_bucket) {
            edabit_buckets.push(chunk.to_vec());
        }
        let mut triple_buckets = Vec::with_capacity(output_num);
        for chunk in
            shuffled_shared_triples[num_cut * bit_size..].chunks((num_bucket - 1) * bit_size)
        {
            triple_buckets.push(chunk.to_vec());
        }
        self.open_and_check_bucket_pairs(channel, rng, &edabit_buckets, &triple_buckets)?;

        Ok(shuffled_private_edabits[num_cut..]
            .chunks(num_bucket)
            .map(|bucket| bucket[0].clone())
            .collect())
    }

    fn cut_and_choose_remote<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num_bucket: usize,
        num_cut: usize,
        peer_private_edabits: &[SharedEdabit<FE>],
        peer_private_triples: &[SharedBitTriple],
    ) -> Result<Vec<SharedEdabit<FE>>> {
        let mut shuffled_peer_edabits = peer_private_edabits.to_vec();
        let mut shuffled_peer_triples = peer_private_triples.to_vec();

        let mut edabit_rng = AesRng::from_seed(self.sample_joint_block(channel, rng)?);
        let mut triple_rng = AesRng::from_seed(self.sample_joint_block(channel, rng)?);
        generate_permutation(&mut edabit_rng, &mut shuffled_peer_edabits);
        generate_permutation(&mut triple_rng, &mut shuffled_peer_triples);

        self.open_and_check_edabits(channel, &shuffled_peer_edabits[..num_cut])?;
        self.open_and_check_triples(channel, &shuffled_peer_triples[..num_cut * bit_size])?;

        let output_num = (shuffled_peer_edabits.len() - num_cut) / num_bucket;
        let mut edabit_buckets = Vec::with_capacity(output_num);
        for chunk in shuffled_peer_edabits[num_cut..].chunks(num_bucket) {
            edabit_buckets.push(chunk.to_vec());
        }
        let mut triple_buckets = Vec::with_capacity(output_num);
        for chunk in shuffled_peer_triples[num_cut * bit_size..].chunks((num_bucket - 1) * bit_size)
        {
            triple_buckets.push(chunk.to_vec());
        }
        self.open_and_check_bucket_pairs(channel, rng, &edabit_buckets, &triple_buckets)?;

        Ok(shuffled_peer_edabits[num_cut..]
            .chunks(num_bucket)
            .map(|bucket| bucket[0].clone())
            .collect())
    }

    fn run_cut_and_choose<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num_bucket: usize,
        num_cut: usize,
        raw: RawPrivateEdabitState<FE>,
    ) -> Result<VerifiedPrivateEdabitState<FE>> {
        let (private_edabits, peer_private_edabits) = if self.role.is_first() {
            (
                self.cut_and_choose_local(
                    channel,
                    rng,
                    bit_size,
                    num_bucket,
                    num_cut,
                    &raw.private_edabits,
                    &raw.private_triples,
                )?,
                self.cut_and_choose_remote(
                    channel,
                    rng,
                    bit_size,
                    num_bucket,
                    num_cut,
                    &raw.peer_private_edabits,
                    &raw.peer_private_triples,
                )?,
            )
        } else {
            let peer_private_edabits = self.cut_and_choose_remote(
                channel,
                rng,
                bit_size,
                num_bucket,
                num_cut,
                &raw.peer_private_edabits,
                &raw.peer_private_triples,
            )?;
            let private_edabits = self.cut_and_choose_local(
                channel,
                rng,
                bit_size,
                num_bucket,
                num_cut,
                &raw.private_edabits,
                &raw.private_triples,
            )?;
            (private_edabits, peer_private_edabits)
        };

        Ok(VerifiedPrivateEdabitState {
            private_edabits,
            peer_private_edabits,
        })
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

    fn sum_private_arithmetic_shares(
        &mut self,
        state: &VerifiedPrivateEdabitState<FE>,
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

    fn combine_private_into_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &VerifiedPrivateEdabitState<FE>,
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
        let (global_bits, overflow_carries) = self.add_bit_contributions_with_triples(
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

    fn generate_global_edabits_with_parameters<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
        num_bucket: usize,
        num_cut: usize,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        let num_random_edabits = num * num_bucket + num_cut;
        let num_random_triples = num * (num_bucket - 1) * bit_size + num_cut * bit_size;
        let raw = self.sample_and_share_private_material(
            channel,
            rng,
            bit_size,
            num_random_edabits,
            num_random_triples,
        )?;
        let verified = self.run_cut_and_choose(channel, rng, bit_size, num_bucket, num_cut, raw)?;
        self.combine_private_into_global_edabits(channel, rng, &verified)
    }

    pub fn generate_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        let (num_bucket, num_cut) = select_cut_and_choose_parameters(num);
        self.generate_global_edabits_with_parameters(
            channel, rng, bit_size, num, num_bucket, num_cut,
        )
    }

    pub fn generate_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        self.generate_global_edabits(channel, rng, bit_size, num)
    }

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
    fn test_mpc_original_global_edabits_roundtrip() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = MpcOriginalEdabitsPeer::<F61p>::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            let global_edabits = peer
                .generate_global_edabits_with_parameters(&mut channel, &mut rng, 8, 16, 4, 4)
                .unwrap();
            assert_eq!(global_edabits.len(), 16);

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
        let mut peer = MpcOriginalEdabitsPeer::<F61p>::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        let global_edabits = peer
            .generate_global_edabits_with_parameters(&mut channel, &mut rng, 8, 16, 4, 4)
            .unwrap();
        assert_eq!(global_edabits.len(), 16);

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
