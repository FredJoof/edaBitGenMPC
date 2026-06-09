#![allow(clippy::too_many_arguments)]

//! Peer-oriented 2PC implementation of the original edaBits paper flow using
//! a SPDZ-style authenticated-share backend instead of VOLE/FCom.
//!
//! Correspondence with the repository:
//! - [`crate::mpc_original_edabits`] keeps the same protocol shape with the
//!   VOLE/tag backend.
//! - [`crate::mpc_spdz_common`] provides the SPDZ-style authenticated-share
//!   machinery used here.
//! - Bucket consistency still uses the original paper's faulty triples.

use crate::mpc_edabits_common::{convert_bits_to_field, split_bits};
use crate::mpc_homcom::PeerRole;
use crate::mpc_original_edabits::select_cut_and_choose_parameters;
use crate::mpc_spdz_common::{MpcSpdzCommon, SpdzFieldBackend, SpdzOtExt, SpdzSharedBitTriple};
use crate::mpc_spdz_conv::{SpdzGlobalEdabit, SpdzPrivateEdabit, SpdzSharedEdabit};
use eyre::{eyre, Result};
use ocelot::svole::wykw::LpnParams;
use rand::{CryptoRng, Rng, SeedableRng};
use scuttlebutt::{
    field::{F40b, FiniteField, F2},
    ring::FiniteRing,
    AbstractChannel, AesRng, Block,
};

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

#[derive(Clone, Copy, Debug)]
struct PrivateBitTriple {
    clear_a: F2,
    clear_b: F2,
    clear_c: F2,
    shared: SpdzSharedBitTriple,
}

struct LocalPrivateEdabitBatch<FE: FiniteField> {
    private_edabits: Vec<SpdzPrivateEdabit<FE>>,
}

struct RemotePrivateEdabitBatch<FE: FiniteField> {
    peer_private_edabits: Vec<SpdzSharedEdabit<FE>>,
}

struct LocalPrivateTripleBatch {
    private_triples: Vec<PrivateBitTriple>,
}

struct RemotePrivateTripleBatch {
    peer_private_triples: Vec<SpdzSharedBitTriple>,
}

struct RawPrivateEdabitState<FE: FiniteField> {
    private_edabits: Vec<SpdzPrivateEdabit<FE>>,
    peer_private_edabits: Vec<SpdzSharedEdabit<FE>>,
    private_triples: Vec<PrivateBitTriple>,
    peer_private_triples: Vec<SpdzSharedBitTriple>,
}

struct VerifiedPrivateEdabitState<FE: FiniteField> {
    private_edabits: Vec<SpdzPrivateEdabit<FE>>,
    peer_private_edabits: Vec<SpdzSharedEdabit<FE>>,
}

pub struct MpcOriginalEdabitsSpdzPeer<FE: FiniteField> {
    role: PeerRole,
    f2_backend: SpdzFieldBackend<F40b>,
    fe_backend: SpdzFieldBackend<FE>,
    ot: SpdzOtExt,
}

impl<FE: FiniteField<PrimeField = FE>> MpcSpdzCommon<FE> for MpcOriginalEdabitsSpdzPeer<FE> {
    fn role(&self) -> PeerRole {
        self.role
    }

    fn spdz_f2(&self) -> &SpdzFieldBackend<F40b> {
        &self.f2_backend
    }

    fn spdz_f2_mut(&mut self) -> &mut SpdzFieldBackend<F40b> {
        &mut self.f2_backend
    }

    fn spdz_fe(&self) -> &SpdzFieldBackend<FE> {
        &self.fe_backend
    }

    fn spdz_fe_mut(&mut self) -> &mut SpdzFieldBackend<FE> {
        &mut self.fe_backend
    }

    fn ot_mut(&mut self) -> &mut SpdzOtExt {
        &mut self.ot
    }
}

impl<FE: FiniteField<PrimeField = FE>> MpcOriginalEdabitsSpdzPeer<FE> {
    pub fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        role: PeerRole,
        _lpn_setup: LpnParams,
        _lpn_extend: LpnParams,
    ) -> Result<Self> {
        let f2_backend = SpdzFieldBackend::init(channel, rng, role)?;
        let fe_backend = SpdzFieldBackend::init(channel, rng, role)?;
        let ot = SpdzOtExt::init(channel, rng, role)?;
        Ok(Self {
            role,
            f2_backend,
            fe_backend,
            ot,
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

        let flat_bits: Vec<_> = clear_bits
            .iter()
            .flat_map(|bits| bits.iter().copied())
            .collect();
        let shared_bits = self.share_owned_f2_values(channel, rng, &flat_bits)?;
        let shared_values = self.share_owned_fe_values(channel, rng, &clear_values)?;

        let mut private_edabits = Vec::with_capacity(num);
        let mut bit_offset = 0;
        for i in 0..num {
            let mut bits = Vec::with_capacity(bit_size);
            for _ in 0..bit_size {
                bits.push(shared_bits[bit_offset]);
                bit_offset += 1;
            }
            private_edabits.push(SpdzPrivateEdabit {
                clear_bits: clear_bits[i].clone(),
                clear_value: clear_values[i],
                shared: SpdzSharedEdabit {
                    bits,
                    value: shared_values[i],
                },
            });
        }

        Ok(LocalPrivateEdabitBatch { private_edabits })
    }

    fn receive_peer_private_edabits<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        bit_size: usize,
        num: usize,
    ) -> Result<RemotePrivateEdabitBatch<FE>> {
        let flat_bits = self.receive_shared_f2_values(channel, num * bit_size)?;
        let shared_values = self.receive_shared_fe_values(channel, num)?;

        let mut peer_private_edabits = Vec::with_capacity(num);
        let mut bit_offset = 0;
        for i in 0..num {
            let mut bits = Vec::with_capacity(bit_size);
            for _ in 0..bit_size {
                bits.push(flat_bits[bit_offset]);
                bit_offset += 1;
            }
            peer_private_edabits.push(SpdzSharedEdabit {
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
                shared: SpdzSharedBitTriple {
                    a: shared_a[i],
                    b: shared_b[i],
                    c: shared_c[i],
                },
            });
        }

        Ok(LocalPrivateTripleBatch { private_triples })
    }

    fn receive_peer_private_triples<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        num: usize,
    ) -> Result<RemotePrivateTripleBatch> {
        let shared_a = self.receive_shared_f2_values(channel, num)?;
        let shared_b = self.receive_shared_f2_values(channel, num)?;
        let shared_c = self.receive_shared_f2_values(channel, num)?;

        let mut peer_private_triples = Vec::with_capacity(num);
        for i in 0..num {
            peer_private_triples.push(SpdzSharedBitTriple {
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
                self.receive_peer_private_edabits(channel, bit_size, num_edabits)?,
                self.sample_private_triples(channel, rng, num_triples)?,
                self.receive_peer_private_triples(channel, num_triples)?,
            )
        } else {
            let remote_edabits =
                self.receive_peer_private_edabits(channel, bit_size, num_edabits)?;
            let local_edabits = self.sample_private_edabits(channel, rng, bit_size, num_edabits)?;
            let remote_triples = self.receive_peer_private_triples(channel, num_triples)?;
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

    fn open_and_check_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        edabits: &[SpdzSharedEdabit<FE>],
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
        let opened_bits = self.open_shared_bit_batch(channel, rng, &flat_bits)?;
        let opened_values = self.open_shared_field_batch(channel, rng, &values)?;
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

    fn open_and_check_triples<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        triples: &[SpdzSharedBitTriple],
    ) -> Result<()> {
        if triples.is_empty() {
            return Ok(());
        }

        let a_batch: Vec<_> = triples.iter().map(|triple| triple.a).collect();
        let b_batch: Vec<_> = triples.iter().map(|triple| triple.b).collect();
        let c_batch: Vec<_> = triples.iter().map(|triple| triple.c).collect();
        let opened_a = self.open_shared_bit_batch(channel, rng, &a_batch)?;
        let opened_b = self.open_shared_bit_batch(channel, rng, &b_batch)?;
        let opened_c = self.open_shared_bit_batch(channel, rng, &c_batch)?;
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

    fn open_and_check_bucket_pairs<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        edabit_buckets: &[Vec<SpdzSharedEdabit<FE>>],
        triple_buckets: &[Vec<SpdzSharedBitTriple>],
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
                arithmetic_sums.push(self.add_field_shares(anchor.value, other.value));
            }
            triples.extend_from_slice(&triple_buckets[bucket_idx]);
        }

        let (sum_bits, carry_bits) =
            self.add_private_bit_contributions_with_triples(channel, rng, &lhs, &rhs, &triples)?;
        let carry_field_shares = self.convert_shared_bits_to_field(channel, rng, &carry_bits)?;
        let corrected_values =
            self.apply_overflow_correction(&arithmetic_sums, &carry_field_shares, bit_size);

        let flat_bits: Vec<_> = sum_bits
            .iter()
            .flat_map(|bits| bits.iter().copied())
            .collect();
        let opened_bits = self.open_shared_bit_batch(channel, rng, &flat_bits)?;
        let opened_values = self.open_shared_field_batch(channel, rng, &corrected_values)?;
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
        private_edabits: &[SpdzPrivateEdabit<FE>],
        private_triples: &[PrivateBitTriple],
    ) -> Result<Vec<SpdzPrivateEdabit<FE>>> {
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

        self.open_and_check_edabits(channel, rng, &shuffled_shared_edabits[..num_cut])?;
        self.open_and_check_triples(channel, rng, &shuffled_shared_triples[..num_cut * bit_size])?;

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
        peer_private_edabits: &[SpdzSharedEdabit<FE>],
        peer_private_triples: &[SpdzSharedBitTriple],
    ) -> Result<Vec<SpdzSharedEdabit<FE>>> {
        let mut shuffled_peer_edabits = peer_private_edabits.to_vec();
        let mut shuffled_peer_triples = peer_private_triples.to_vec();

        let mut edabit_rng = AesRng::from_seed(self.sample_joint_block(channel, rng)?);
        let mut triple_rng = AesRng::from_seed(self.sample_joint_block(channel, rng)?);
        generate_permutation(&mut edabit_rng, &mut shuffled_peer_edabits);
        generate_permutation(&mut triple_rng, &mut shuffled_peer_triples);

        self.open_and_check_edabits(channel, rng, &shuffled_peer_edabits[..num_cut])?;
        self.open_and_check_triples(channel, rng, &shuffled_peer_triples[..num_cut * bit_size])?;

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

    fn combine_private_into_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &VerifiedPrivateEdabitState<FE>,
    ) -> Result<Vec<SpdzGlobalEdabit<FE>>> {
        MpcSpdzCommon::combine_private_into_global_edabits(
            self,
            channel,
            rng,
            &state.private_edabits,
            &state.peer_private_edabits,
        )
    }

    fn generate_global_edabits_with_parameters<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
        num_bucket: usize,
        num_cut: usize,
    ) -> Result<Vec<SpdzGlobalEdabit<FE>>> {
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
    ) -> Result<Vec<SpdzGlobalEdabit<FE>>> {
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
    ) -> Result<Vec<SpdzGlobalEdabit<FE>>> {
        self.generate_global_edabits(channel, rng, bit_size, num)
    }

    pub fn open_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        global_edabits: &[SpdzGlobalEdabit<FE>],
    ) -> Result<Vec<(Vec<F2>, FE)>> {
        MpcSpdzCommon::open_global_edabits(self, channel, rng, global_edabits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ocelot::svole::wykw::{LPN_EXTEND_SMALL, LPN_SETUP_SMALL};
    use scuttlebutt::{field::F61p, Channel};
    use std::{
        io::{BufReader, BufWriter},
        os::unix::net::UnixStream,
    };

    #[test]
    fn test_mpc_spdz_field_share_roundtrip() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = MpcOriginalEdabitsSpdzPeer::<F61p>::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            let values = [F61p::ONE, F61p::try_from(7u128).unwrap()];
            let shares = peer
                .share_owned_fe_values(&mut channel, &mut rng, &values)
                .unwrap();
            let opened = peer
                .open_shared_field_batch(&mut channel, &mut rng, &shares)
                .unwrap();
            assert_eq!(opened, values);
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(right.try_clone().unwrap());
        let writer = BufWriter::new(right);
        let mut channel = Channel::new(reader, writer);
        let mut peer = MpcOriginalEdabitsSpdzPeer::<F61p>::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        let shares = peer.receive_shared_fe_values(&mut channel, 2).unwrap();
        let opened = peer
            .open_shared_field_batch(&mut channel, &mut rng, &shares)
            .unwrap();
        assert_eq!(opened, [F61p::ONE, F61p::try_from(7u128).unwrap()]);

        handle.join().unwrap();
    }

    #[test]
    fn test_mpc_spdz_bit_to_field_roundtrip() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = MpcOriginalEdabitsSpdzPeer::<F61p>::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            let bits = [F2::ZERO, F2::ONE, F2::ONE, F2::ZERO];
            let shared_bits = peer
                .share_owned_f2_values(&mut channel, &mut rng, &bits)
                .unwrap();
            let field_bits = peer
                .convert_shared_bits_to_field(&mut channel, &mut rng, &shared_bits)
                .unwrap();
            let opened_bits = peer
                .open_shared_bit_batch(&mut channel, &mut rng, &shared_bits)
                .unwrap();
            let opened_fields = peer
                .open_shared_field_batch(&mut channel, &mut rng, &field_bits)
                .unwrap();
            for (bit, field) in opened_bits.into_iter().zip(opened_fields) {
                assert_eq!(
                    if bit == F2::ONE {
                        F61p::ONE
                    } else {
                        F61p::ZERO
                    },
                    field
                );
            }
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(right.try_clone().unwrap());
        let writer = BufWriter::new(right);
        let mut channel = Channel::new(reader, writer);
        let mut peer = MpcOriginalEdabitsSpdzPeer::<F61p>::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        let shared_bits = peer.receive_shared_f2_values(&mut channel, 4).unwrap();
        let field_bits = peer
            .convert_shared_bits_to_field(&mut channel, &mut rng, &shared_bits)
            .unwrap();
        let opened_bits = peer
            .open_shared_bit_batch(&mut channel, &mut rng, &shared_bits)
            .unwrap();
        let opened_fields = peer
            .open_shared_field_batch(&mut channel, &mut rng, &field_bits)
            .unwrap();
        for (bit, field) in opened_bits.into_iter().zip(opened_fields) {
            assert_eq!(
                if bit == F2::ONE {
                    F61p::ONE
                } else {
                    F61p::ZERO
                },
                field
            );
        }

        handle.join().unwrap();
    }

    #[test]
    fn test_mpc_original_spdz_global_edabits_roundtrip() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = MpcOriginalEdabitsSpdzPeer::<F61p>::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            let global_edabits = peer
                .generate_global_edabits_with_parameters(&mut channel, &mut rng, 8, 64, 4, 4)
                .unwrap();
            assert_eq!(global_edabits.len(), 64);

            let opened = peer
                .open_global_edabits(&mut channel, &mut rng, &global_edabits)
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
        let mut peer = MpcOriginalEdabitsSpdzPeer::<F61p>::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        let global_edabits = peer
            .generate_global_edabits_with_parameters(&mut channel, &mut rng, 8, 64, 4, 4)
            .unwrap();
        assert_eq!(global_edabits.len(), 64);

        let opened = peer
            .open_global_edabits(&mut channel, &mut rng, &global_edabits)
            .unwrap();
        for (bits, value) in opened {
            assert_eq!(bits.len(), 8);
            assert_eq!(convert_bits_to_field::<F61p>(&bits), value);
        }

        handle.join().unwrap();
    }
}
