use crate::conv::{ConvProverT, ConvVerifierT};
use crate::edabits::{DabitProver, DabitVerifier, ProverConv, VerifierConv};
use crate::homcom::{MacProver, MacVerifier};
use crate::mpc_conv::{AuthenticatedShare, GlobalEdabit, PrivateEdabit, SharedEdabit};
use crate::mpc_homcom::{PeerFieldMacs, PeerRole};
use eyre::Result;
use generic_array::typenum::Unsigned;
use rand::{CryptoRng, Rng};
use scuttlebutt::{
    field::{Degree, F40b, FiniteField, F2},
    ring::FiniteRing,
    AbstractChannel,
};

pub(crate) fn select_cut_and_choose_parameters(num_edabits: usize) -> (usize, usize) {
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

pub(crate) fn f2_to_fe<FE: FiniteField>(bit: F2) -> FE::PrimeField {
    if bit == F2::ZERO {
        FE::PrimeField::ZERO
    } else {
        FE::PrimeField::ONE
    }
}

pub(crate) fn convert_bits_to_field<FE: FiniteField>(bits: &[F2]) -> FE::PrimeField {
    let mut out = FE::PrimeField::ZERO;
    for bit in bits.iter().rev() {
        out += out;
        out += f2_to_fe::<FE>(*bit);
    }
    out
}

pub(crate) fn power_two<FE: FiniteField>(power: usize) -> FE::PrimeField {
    let mut out = FE::PrimeField::ONE;
    for _ in 0..power {
        out += out;
    }
    out
}

pub(crate) fn flatten_bits(bit_vectors: &[Vec<F2>]) -> Vec<F2> {
    let total: usize = bit_vectors.iter().map(Vec::len).sum();
    let mut out = Vec::with_capacity(total);
    for bits in bit_vectors {
        out.extend_from_slice(bits);
    }
    out
}

pub(crate) fn split_bits(flat: &[F2], chunk_size: usize) -> Vec<Vec<F2>> {
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

#[derive(Clone, Copy, Debug)]
pub(crate) struct SharedBitTriple {
    pub(crate) a: AuthenticatedShare<F40b>,
    pub(crate) b: AuthenticatedShare<F40b>,
    pub(crate) c: AuthenticatedShare<F40b>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct SharedDabit<FE: FiniteField> {
    pub(crate) bit: AuthenticatedShare<F40b>,
    pub(crate) value: AuthenticatedShare<FE>,
}

pub(crate) fn estimate_combine_voles<FE: FiniteField<PrimeField = FE>>(
    num: usize,
    bit_size: u32,
) -> (usize, usize) {
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

pub(crate) trait MpcEdabitsCommon<FE: FiniteField<PrimeField = FE>> {
    fn role(&self) -> PeerRole;
    fn fcom_f2(&self) -> &PeerFieldMacs<F40b>;
    fn fcom_f2_mut(&mut self) -> &mut PeerFieldMacs<F40b>;
    fn fcom_fe(&self) -> &PeerFieldMacs<FE>;
    fn fcom_fe_mut(&mut self) -> &mut PeerFieldMacs<FE>;
    fn local_conv_mut(&mut self) -> &mut ProverConv<FE>;
    fn remote_conv_mut(&mut self) -> &mut VerifierConv<FE>;

    fn zero_bit_share(&self) -> AuthenticatedShare<F40b> {
        AuthenticatedShare::new(
            MacProver::new(F2::ZERO, F40b::ZERO),
            MacVerifier::new(F40b::ZERO),
        )
    }

    fn zero_field_share(&self) -> AuthenticatedShare<FE> {
        AuthenticatedShare::new(
            MacProver::new(FE::PrimeField::ZERO, FE::ZERO),
            MacVerifier::new(FE::ZERO),
        )
    }

    fn add_bit_shares(
        &mut self,
        lhs: AuthenticatedShare<F40b>,
        rhs: AuthenticatedShare<F40b>,
    ) -> AuthenticatedShare<F40b> {
        let local = self
            .fcom_f2_mut()
            .local()
            .get_refmut()
            .add(lhs.local, rhs.local);
        let remote = self
            .fcom_f2_mut()
            .remote()
            .get_refmut()
            .add(lhs.remote, rhs.remote);
        AuthenticatedShare::new(local, remote)
    }

    fn add_bit_const(
        &mut self,
        share: AuthenticatedShare<F40b>,
        cst: F2,
    ) -> AuthenticatedShare<F40b> {
        if cst == F2::ZERO {
            share
        } else if self.role().is_first() {
            let local = self
                .fcom_f2_mut()
                .local()
                .get_refmut()
                .affine_add_cst(cst, share.local);
            AuthenticatedShare::new(local, share.remote)
        } else {
            let remote = self
                .fcom_f2_mut()
                .remote()
                .get_refmut()
                .affine_add_cst(cst, share.remote);
            AuthenticatedShare::new(share.local, remote)
        }
    }

    fn negate_field_share(&mut self, share: AuthenticatedShare<FE>) -> AuthenticatedShare<FE> {
        let local = self.fcom_fe_mut().local().get_refmut().neg(share.local);
        let remote = self.fcom_fe_mut().remote().get_refmut().neg(share.remote);
        AuthenticatedShare::new(local, remote)
    }

    fn add_field_const(
        &mut self,
        share: AuthenticatedShare<FE>,
        cst: FE::PrimeField,
    ) -> AuthenticatedShare<FE> {
        if cst == FE::PrimeField::ZERO {
            share
        } else if self.role().is_first() {
            let local = self
                .fcom_fe_mut()
                .local()
                .get_refmut()
                .affine_add_cst(cst, share.local);
            AuthenticatedShare::new(local, share.remote)
        } else {
            let remote = self
                .fcom_fe_mut()
                .remote()
                .get_refmut()
                .affine_add_cst(cst, share.remote);
            AuthenticatedShare::new(share.local, remote)
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
        if self.role().is_first() {
            self.fcom_f2_mut()
                .local()
                .get_refmut()
                .open(channel, &local_batch)?;
            self.fcom_f2_mut().remote().get_refmut().open(
                channel,
                &remote_batch,
                &mut remote_values,
            )?;
        } else {
            self.fcom_f2_mut().remote().get_refmut().open(
                channel,
                &remote_batch,
                &mut remote_values,
            )?;
            self.fcom_f2_mut()
                .local()
                .get_refmut()
                .open(channel, &local_batch)?;
        }

        Ok(local_batch
            .iter()
            .zip(remote_values)
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
        if self.role().is_first() {
            self.fcom_fe_mut()
                .local()
                .get_refmut()
                .open(channel, &local_batch)?;
            self.fcom_fe_mut().remote().get_refmut().open(
                channel,
                &remote_batch,
                &mut remote_values,
            )?;
        } else {
            self.fcom_fe_mut().remote().get_refmut().open(
                channel,
                &remote_batch,
                &mut remote_values,
            )?;
            self.fcom_fe_mut()
                .local()
                .get_refmut()
                .open(channel, &local_batch)?;
        }

        Ok(local_batch
            .iter()
            .zip(remote_values)
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

        let local_macs =
            self.fcom_f2_mut()
                .local()
                .get_refmut()
                .input(channel, rng, &local_shares)?;
        channel.write_serializable_seq::<F2>(&remote_shares)?;
        channel.flush()?;
        let remote_auth =
            self.fcom_f2_mut()
                .remote()
                .get_refmut()
                .input(channel, rng, values.len())?;

        Ok(local_shares
            .into_iter()
            .zip(local_macs)
            .zip(remote_auth)
            .map(|((share, mac), auth)| AuthenticatedShare::new(MacProver::new(share, mac), auth))
            .collect())
    }

    fn share_private_clear_edabits_owner_zero<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        clear_bits: &[Vec<F2>],
        clear_values: &[FE],
    ) -> Result<Vec<PrivateEdabit<FE>>> {
        let num = clear_bits.len();
        let bit_size = clear_bits.first().map_or(0, Vec::len);
        debug_assert_eq!(num, clear_values.len());

        let flat_local_bits = flatten_bits(clear_bits);
        let local_bit_macs =
            self.fcom_f2_mut()
                .local()
                .get_refmut()
                .input(channel, rng, &flat_local_bits)?;
        let local_value_macs =
            self.fcom_fe_mut()
                .local()
                .get_refmut()
                .input(channel, rng, clear_values)?;
        channel.flush()?;

        let remote_bit_auth = vec![self.zero_bit_share().remote; flat_local_bits.len()];
        let remote_value_auth = vec![self.zero_field_share().remote; num];

        let mut private_edabits = Vec::with_capacity(num);
        let mut bit_mac_offset = 0;
        for i in 0..num {
            let mut shared_bits = Vec::with_capacity(bit_size);
            for j in 0..bit_size {
                let local_idx = bit_mac_offset + j;
                shared_bits.push(AuthenticatedShare::new(
                    MacProver::new(clear_bits[i][j], local_bit_macs[local_idx]),
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
                        MacProver::new(clear_values[i], local_value_macs[i]),
                        remote_value_auth[i],
                    ),
                },
            });
        }

        Ok(private_edabits)
    }

    fn receive_shared_f2_values<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num: usize,
    ) -> Result<Vec<AuthenticatedShare<F40b>>> {
        let remote_auth = self
            .fcom_f2_mut()
            .remote()
            .get_refmut()
            .input(channel, rng, num)?;
        let local_shares = channel.read_serializable_seq::<F2>(num)?;
        let local_macs =
            self.fcom_f2_mut()
                .local()
                .get_refmut()
                .input(channel, rng, &local_shares)?;
        channel.flush()?;

        Ok(local_shares
            .into_iter()
            .zip(local_macs)
            .zip(remote_auth)
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

        let local_macs =
            self.fcom_fe_mut()
                .local()
                .get_refmut()
                .input(channel, rng, &local_shares)?;
        channel.write_serializable_seq::<FE>(&remote_shares)?;
        channel.flush()?;
        let remote_auth =
            self.fcom_fe_mut()
                .remote()
                .get_refmut()
                .input(channel, rng, values.len())?;

        Ok(local_shares
            .into_iter()
            .zip(local_macs)
            .zip(remote_auth)
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
            .fcom_fe_mut()
            .remote()
            .get_refmut()
            .input(channel, rng, num)?;
        let local_shares = channel.read_serializable_seq::<FE>(num)?;
        let local_macs =
            self.fcom_fe_mut()
                .local()
                .get_refmut()
                .input(channel, rng, &local_shares)?;
        channel.flush()?;

        Ok(local_shares
            .into_iter()
            .zip(local_macs)
            .zip(remote_auth)
            .map(|((share, mac), auth)| AuthenticatedShare::new(MacProver::new(share, mac), auth))
            .collect())
    }

    fn receive_private_edabit_contributions_owner_zero<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Vec<SharedEdabit<FE>>> {
        let remote_bit_auth =
            self.fcom_f2_mut()
                .remote()
                .get_refmut()
                .input(channel, rng, num * bit_size)?;
        let remote_value_auth = self
            .fcom_fe_mut()
            .remote()
            .get_refmut()
            .input(channel, rng, num)?;

        let remote_bit_shares = vec![F2::ZERO; num * bit_size];
        let remote_value_shares = vec![FE::ZERO; num];
        let local_bit_macs = vec![F40b::ZERO; num * bit_size];
        let local_value_macs = vec![FE::ZERO; num];

        let remote_bit_chunks = split_bits(&remote_bit_shares, bit_size);
        let mut peer_private_edabits = Vec::with_capacity(num);
        let mut bit_mac_offset = 0;
        for i in 0..num {
            let mut shared_bits = Vec::with_capacity(bit_size);
            for j in 0..bit_size {
                let local_idx = bit_mac_offset + j;
                shared_bits.push(AuthenticatedShare::new(
                    MacProver::new(remote_bit_chunks[i][j], local_bit_macs[local_idx]),
                    remote_bit_auth[local_idx],
                ));
            }
            bit_mac_offset += bit_size;

            peer_private_edabits.push(SharedEdabit {
                bits: shared_bits,
                value: AuthenticatedShare::new(
                    MacProver::new(remote_value_shares[i], local_value_macs[i]),
                    remote_value_auth[i],
                ),
            });
        }

        Ok(peer_private_edabits)
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

        if self.role().is_first() {
            let mut triples = Vec::with_capacity(num);
            self.local_conv_mut()
                .random_triples(channel, rng, num, &mut triples)?;
            self.fcom_f2_mut()
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
                .zip(b_shared)
                .zip(c_shared)
                .map(|((a, b), c)| SharedBitTriple { a, b, c })
                .collect())
        } else {
            let mut triples = Vec::with_capacity(num);
            self.remote_conv_mut()
                .random_triples(channel, rng, num, &mut triples)?;
            self.fcom_f2_mut()
                .remote()
                .get_refmut()
                .quicksilver_check_multiply(channel, rng, &triples)?;

            let a_shared = self.receive_shared_f2_values(channel, rng, num)?;
            let b_shared = self.receive_shared_f2_values(channel, rng, num)?;
            let c_shared = self.receive_shared_f2_values(channel, rng, num)?;

            Ok(a_shared
                .into_iter()
                .zip(b_shared)
                .zip(c_shared)
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

        if self.role().is_first() {
            let dabits: Vec<DabitProver<FE>> =
                self.local_conv_mut().random_dabits(channel, rng, num)?;
            self.local_conv_mut().fdabit(channel, rng, &dabits)?;

            let bit_values: Vec<_> = dabits.iter().map(|dabit| dabit.bit.value()).collect();
            let field_values: Vec<_> = dabits.iter().map(|dabit| dabit.value.value()).collect();
            let shared_bits = self.share_owned_f2_values(channel, rng, &bit_values)?;
            let shared_values = self.share_owned_fe_values(channel, rng, &field_values)?;

            Ok(shared_bits
                .into_iter()
                .zip(shared_values)
                .map(|(bit, value)| SharedDabit { bit, value })
                .collect())
        } else {
            let dabits: Vec<DabitVerifier<FE>> =
                self.remote_conv_mut().random_dabits(channel, rng, num)?;
            self.remote_conv_mut().fdabit(channel, rng, &dabits)?;

            let shared_bits = self.receive_shared_f2_values(channel, rng, num)?;
            let shared_values = self.receive_shared_fe_values(channel, rng, num)?;

            Ok(shared_bits
                .into_iter()
                .zip(shared_values)
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
            .zip(d_values.into_iter().zip(e_values))
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
            for (carry_slot, and_result) in carry.iter_mut().zip(and_results) {
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
            .zip(opened_masks)
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
        private_edabits: &[PrivateEdabit<FE>],
        peer_private_edabits: &[SharedEdabit<FE>],
    ) -> Vec<AuthenticatedShare<FE>> {
        private_edabits
            .iter()
            .zip(peer_private_edabits.iter())
            .map(|(local, remote)| {
                let local_sum = self
                    .fcom_fe_mut()
                    .local()
                    .get_refmut()
                    .add(local.shared.value.local, remote.value.local);
                let remote_sum = self
                    .fcom_fe_mut()
                    .remote()
                    .get_refmut()
                    .add(local.shared.value.remote, remote.value.remote);
                AuthenticatedShare::new(local_sum, remote_sum)
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
                    .fcom_fe_mut()
                    .local()
                    .get_refmut()
                    .affine_mult_cst(correction_scale, carry.local);
                let remote_correction = self
                    .fcom_fe_mut()
                    .remote()
                    .get_refmut()
                    .affine_mult_cst(correction_scale, carry.remote);
                let local = self
                    .fcom_fe_mut()
                    .local()
                    .get_refmut()
                    .add(sum.local, local_correction);
                let remote = self
                    .fcom_fe_mut()
                    .remote()
                    .get_refmut()
                    .add(sum.remote, remote_correction);
                AuthenticatedShare::new(local, remote)
            })
            .collect()
    }

    fn assemble_global_edabits(
        &self,
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
        private_edabits: &[PrivateEdabit<FE>],
        peer_private_edabits: &[SharedEdabit<FE>],
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        if private_edabits.is_empty() {
            return Ok(Vec::new());
        }

        let bit_size = private_edabits[0].shared.bit_len();
        let num = private_edabits.len();
        let shared_triples =
            self.generate_checked_shared_bit_triples(channel, rng, num * bit_size)?;
        let shared_dabits = self.generate_checked_shared_dabits(channel, rng, num)?;
        let own_private: Vec<_> = private_edabits
            .iter()
            .map(|private| private.shared.clone())
            .collect();
        let peer_private = peer_private_edabits.to_vec();
        let (first_party_private, second_party_private) = if self.role().is_first() {
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
        let arithmetic_sums =
            self.sum_private_arithmetic_shares(private_edabits, peer_private_edabits);
        let corrected_values =
            self.apply_overflow_correction(&arithmetic_sums, &carry_field_shares, bit_size);
        Ok(self.assemble_global_edabits(&global_bits, &corrected_values))
    }

    fn open_global_edabits<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        global_edabits: &[GlobalEdabit<FE>],
    ) -> Result<Vec<(Vec<F2>, FE)>> {
        let mut opened = Vec::with_capacity(global_edabits.len());
        for edabit in global_edabits {
            let mut bits = Vec::with_capacity(edabit.bits.len());
            for bit in &edabit.bits {
                bits.push(open_authenticated_share(
                    self.role(),
                    self.fcom_f2(),
                    channel,
                    bit,
                )?);
            }
            let value =
                open_authenticated_share(self.role(), self.fcom_fe(), channel, &edabit.value)?;
            opened.push((bits, value));
        }
        Ok(opened)
    }
}
