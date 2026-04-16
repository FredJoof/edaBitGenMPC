use crate::mpc_edabits_common::{f2_to_fe, power_two};
use crate::mpc_homcom::PeerRole;
use crate::mpc_spdz_conv::{
    SpdzAuthenticatedShare, SpdzBitShare, SpdzFieldShare, SpdzGlobalEdabit, SpdzPrivateEdabit,
    SpdzSharedEdabit,
};
use eyre::{eyre, Result};
use generic_array::{typenum::Unsigned, GenericArray};
use ocelot::{
    ot::{
        KosReceiver, KosSender, Receiver as OcelotReceiver, Sender as OcelotSender,
    },
};
use rand::{CryptoRng, Rng};
use scuttlebutt::{
    field::{Degree, F40b, FiniteField, F2},
    ring::FiniteRing,
    serialization::CanonicalSerialize,
    AbstractChannel, Aes128, Block,
};
use subtle::{Choice, ConditionallySelectable};

fn generate_powers<FE: FiniteField>() -> Vec<FE> {
    let mut acc = FE::ONE;
    let mut out = Vec::with_capacity(Degree::<FE>::USIZE);
    for _ in 0..Degree::<FE>::USIZE {
        out.push(acc);
        acc *= FE::GENERATOR;
    }
    out
}

fn lift_prime_to_field<MF: FiniteField>(value: MF::PrimeField) -> MF {
    let bits = value.bit_decomposition();
    let mut out = MF::ZERO;
    for bit in bits.iter().rev() {
        out += out;
        if *bit {
            out += MF::ONE;
        }
    }
    out
}

fn copee_prf<FE: FiniteField>(aes: &Aes128, pt: Block) -> FE::PrimeField {
    let seed = aes.encrypt(pt);
    FE::PrimeField::from_uniform_bytes(&<[u8; 16]>::from(seed))
}

struct SpdzCopeeSender<FE: FiniteField> {
    aes_objs: Vec<(Aes128, Aes128)>,
    powers: Vec<FE>,
    twos: Vec<FE>,
    nbits: usize,
    counter: u64,
}

struct SpdzCopeeReceiver<FE: FiniteField> {
    choices: GenericArray<bool, FE::NumberOfBitsInBitDecomposition>,
    aes_objs: Vec<Aes128>,
    powers: Vec<FE>,
    twos: Vec<FE>,
    nbits: usize,
    counter: u64,
}

impl<FE: FiniteField> SpdzCopeeSender<FE> {
    fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
    ) -> Result<Self> {
        let nbits = <FE::PrimeField as FiniteField>::NumberOfBitsInBitDecomposition::USIZE;
        let mut ot = KosSender::init(channel, rng)?;
        let keys = ocelot::ot::RandomSender::send_random(&mut ot, channel, nbits * Degree::<FE>::USIZE, rng)?;
        let aes_objs = keys
            .iter()
            .map(|(k0, k1)| (Aes128::new(*k0), Aes128::new(*k1)))
            .collect();
        let mut acc = FE::ONE;
        let two = FE::ONE + FE::ONE;
        let mut twos = vec![FE::ZERO; nbits];
        for item in &mut twos {
            *item = acc;
            acc *= two;
        }
        Ok(Self {
            aes_objs,
            powers: generate_powers::<FE>(),
            twos,
            nbits,
            counter: 0,
        })
    }

    fn send<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        input: &FE::PrimeField,
    ) -> Result<FE> {
        let pt = Block::from(self.counter as u128);
        let mut w = FE::ZERO;
        for (i, pow) in self.powers.iter().enumerate() {
            let mut sum = FE::ZERO;
            for (j, two) in self.twos.iter().enumerate() {
                let (prf0, prf1) = &self.aes_objs[i * self.nbits + j];
                let w0 = copee_prf::<FE>(prf0, pt);
                let w1 = copee_prf::<FE>(prf1, pt);
                sum += w0 * *two;
                channel.write_serializable(&(w0 - w1 - *input))?;
            }
            w += sum * *pow;
        }
        self.counter += 1;
        Ok(w)
    }
}

impl<FE: FiniteField> SpdzCopeeReceiver<FE> {
    fn init_with_delta<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        delta: FE,
    ) -> Result<Self> {
        let nbits = <FE::PrimeField as FiniteField>::NumberOfBitsInBitDecomposition::USIZE;
        let mut ot = KosReceiver::init(channel, rng)?;
        let choices = delta.bit_decomposition();
        let keys = ocelot::ot::RandomReceiver::receive_random(&mut ot, channel, &choices, rng)?;
        let aes_objs = keys.into_iter().map(Aes128::new).collect();
        let mut acc = FE::ONE;
        let two = FE::ONE + FE::ONE;
        let mut twos = vec![FE::ZERO; nbits];
        for item in &mut twos {
            *item = acc;
            acc *= two;
        }
        Ok(Self {
            choices,
            aes_objs,
            powers: generate_powers::<FE>(),
            twos,
            nbits,
            counter: 0,
        })
    }

    fn receive<C: AbstractChannel>(&mut self, channel: &mut C) -> Result<FE> {
        let pt = Block::from(self.counter as u128);
        let mut out = FE::ZERO;
        for (i, pow) in self.powers.iter().enumerate() {
            let mut sum = FE::ZERO;
            for (j, two) in self.twos.iter().enumerate() {
                let w = copee_prf::<FE>(&self.aes_objs[i * self.nbits + j], pt);
                let mut tau = channel.read_serializable::<FE::PrimeField>()?;
                tau += w;
                let choice = Choice::from(self.choices[i * self.nbits + j] as u8);
                let v = FE::PrimeField::conditional_select(&w, &tau, choice);
                sum += v * *two;
            }
            out += sum * *pow;
        }
        self.counter += 1;
        Ok(out)
    }
}

pub(crate) struct SpdzFieldBackend<MF: FiniteField> {
    alpha_share: MF,
    outbound: SpdzCopeeSender<MF>,
    inbound: SpdzCopeeReceiver<MF>,
}

impl<MF: FiniteField> SpdzFieldBackend<MF> {
    pub(crate) fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        role: PeerRole,
    ) -> Result<Self> {
        let alpha_share = MF::random(rng);
        let (outbound, inbound) = if role.is_first() {
            (
                SpdzCopeeSender::init(channel, rng)?,
                SpdzCopeeReceiver::init_with_delta(channel, rng, alpha_share)?,
            )
        } else {
            let inbound = SpdzCopeeReceiver::init_with_delta(channel, rng, alpha_share)?;
            let outbound = SpdzCopeeSender::init(channel, rng)?;
            (outbound, inbound)
        };
        Ok(Self {
            alpha_share,
            outbound,
            inbound,
        })
    }

    pub(crate) fn alpha_share(&self) -> MF {
        self.alpha_share
    }

    fn input_owned_values<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        values: &[MF::PrimeField],
    ) -> Result<Vec<SpdzAuthenticatedShare<MF>>> {
        let mut remote_shares = Vec::with_capacity(values.len());
        let mut local_shares = Vec::with_capacity(values.len());
        let mut peer_terms = Vec::with_capacity(values.len());
        for value in values {
            let remote = MF::PrimeField::random(rng);
            remote_shares.push(remote);
            local_shares.push(*value - remote);
            peer_terms.push(self.outbound.send(channel, value)?);
        }
        channel.write_serializable_seq(&remote_shares)?;
        channel.flush()?;

        Ok(local_shares
            .into_iter()
            .zip(values.iter().copied())
            .zip(peer_terms)
            .map(|((share, value), peer_term)| {
                let mac = self.alpha_share * lift_prime_to_field::<MF>(value) + peer_term;
                SpdzAuthenticatedShare::new(share, mac)
            })
            .collect())
    }

    fn receive_shared_values<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        num: usize,
    ) -> Result<Vec<SpdzAuthenticatedShare<MF>>> {
        let mut peer_terms = Vec::with_capacity(num);
        for _ in 0..num {
            peer_terms.push(self.inbound.receive(channel)?);
        }
        let local_shares = channel.read_serializable_seq::<MF::PrimeField>(num)?;
        Ok(local_shares
            .into_iter()
            .zip(peer_terms)
            .map(|(share, peer_term)| SpdzAuthenticatedShare::new(share, -peer_term))
            .collect())
    }
}

pub(crate) struct SpdzOtExt {
    sender: KosSender,
    receiver: KosReceiver,
}

impl SpdzOtExt {
    pub(crate) fn init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        role: PeerRole,
    ) -> Result<Self> {
        let (sender, receiver) = if role.is_first() {
            (KosSender::init(channel, rng)?, KosReceiver::init(channel, rng)?)
        } else {
            let receiver = KosReceiver::init(channel, rng)?;
            let sender = KosSender::init(channel, rng)?;
            (sender, receiver)
        };
        Ok(Self { sender, receiver })
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct SpdzSharedBitTriple {
    pub(crate) a: SpdzBitShare,
    pub(crate) b: SpdzBitShare,
    pub(crate) c: SpdzBitShare,
}

fn field_to_block<F: CanonicalSerialize>(value: F) -> Block {
    assert!(F::ByteReprLen::USIZE <= 16);
    let mut bytes = [0u8; 16];
    let repr = value.to_bytes();
    bytes[..F::ByteReprLen::USIZE].copy_from_slice(repr.as_slice());
    Block::from(bytes)
}

fn block_to_field<F: CanonicalSerialize>(block: Block) -> Result<F> {
    assert!(F::ByteReprLen::USIZE <= 16);
    let bytes: [u8; 16] = block.into();
    let mut repr = GenericArray::<u8, F::ByteReprLen>::default();
    repr.copy_from_slice(&bytes[..F::ByteReprLen::USIZE]);
    F::from_bytes(&repr).map_err(|err| eyre!(err))
}

fn exchange_sequence<T: CanonicalSerialize, C: AbstractChannel>(
    channel: &mut C,
    role: PeerRole,
    values: &[T],
) -> Result<Vec<T>> {
    if role.is_first() {
        channel.write_serializable_seq(values)?;
        channel.flush()?;
        channel.read_serializable_seq(values.len()).map_err(Into::into)
    } else {
        let remote = channel.read_serializable_seq(values.len())?;
        channel.write_serializable_seq(values)?;
        channel.flush()?;
        Ok(remote)
    }
}

fn sample_joint_field<F: FiniteField, C: AbstractChannel, RNG: CryptoRng + Rng>(
    channel: &mut C,
    rng: &mut RNG,
    role: PeerRole,
) -> Result<F> {
    let local = F::random(rng);
    let remote = if role.is_first() {
        channel.write_serializable(&local)?;
        channel.flush()?;
        channel.read_serializable::<F>()?
    } else {
        let remote = channel.read_serializable::<F>()?;
        channel.write_serializable(&local)?;
        channel.flush()?;
        remote
    };
    Ok(local + remote)
}

pub(crate) trait MpcSpdzCommon<FE: FiniteField<PrimeField = FE>> {
    fn role(&self) -> PeerRole;
    fn spdz_f2(&self) -> &SpdzFieldBackend<F40b>;
    fn spdz_f2_mut(&mut self) -> &mut SpdzFieldBackend<F40b>;
    fn spdz_fe(&self) -> &SpdzFieldBackend<FE>;
    fn spdz_fe_mut(&mut self) -> &mut SpdzFieldBackend<FE>;
    fn ot_mut(&mut self) -> &mut SpdzOtExt;

    fn zero_bit_share(&self) -> SpdzBitShare {
        SpdzAuthenticatedShare::new(F2::ZERO, F40b::ZERO)
    }

    fn add_bit_shares(&self, lhs: SpdzBitShare, rhs: SpdzBitShare) -> SpdzBitShare {
        SpdzAuthenticatedShare::new(lhs.share + rhs.share, lhs.mac + rhs.mac)
    }

    fn add_field_shares(
        &self,
        lhs: SpdzFieldShare<FE>,
        rhs: SpdzFieldShare<FE>,
    ) -> SpdzFieldShare<FE> {
        SpdzAuthenticatedShare::new(lhs.share + rhs.share, lhs.mac + rhs.mac)
    }

    fn scale_field_share(
        &self,
        value: SpdzFieldShare<FE>,
        scalar: FE::PrimeField,
    ) -> SpdzFieldShare<FE> {
        SpdzAuthenticatedShare::new(value.share * scalar, value.mac * scalar)
    }

    fn add_bit_const(&self, share: SpdzBitShare, cst: F2) -> SpdzBitShare {
        let share_value = if self.role().is_first() {
            share.share + cst
        } else {
            share.share
        };
        let mac = share.mac + self.spdz_f2().alpha_share() * lift_prime_to_field::<F40b>(cst);
        SpdzAuthenticatedShare::new(share_value, mac)
    }

    fn share_owned_f2_values<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        values: &[F2],
    ) -> Result<Vec<SpdzBitShare>> {
        self.spdz_f2_mut().input_owned_values(channel, rng, values)
    }

    fn receive_shared_f2_values<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        num: usize,
    ) -> Result<Vec<SpdzBitShare>> {
        self.spdz_f2_mut().receive_shared_values(channel, num)
    }

    fn share_owned_fe_values<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        values: &[FE::PrimeField],
    ) -> Result<Vec<SpdzFieldShare<FE>>> {
        self.spdz_fe_mut().input_owned_values(channel, rng, values)
    }

    fn receive_shared_fe_values<C: AbstractChannel>(
        &mut self,
        channel: &mut C,
        num: usize,
    ) -> Result<Vec<SpdzFieldShare<FE>>> {
        self.spdz_fe_mut().receive_shared_values(channel, num)
    }

    fn open_shared_bit_batch<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        shares: &[SpdzBitShare],
    ) -> Result<Vec<F2>> {
        if shares.is_empty() {
            return Ok(Vec::new());
        }

        let local_values: Vec<_> = shares.iter().map(|share| share.share).collect();
        let remote_values = exchange_sequence(channel, self.role(), &local_values)?;
        let opened: Vec<_> = local_values
            .into_iter()
            .zip(remote_values)
            .map(|(local, remote)| local + remote)
            .collect();

        let chi = sample_joint_field::<F40b, _, _>(channel, rng, self.role())?;
        let mut coeff = F40b::ONE;
        let mut local_check = F40b::ZERO;
        for (share, value) in shares.iter().zip(opened.iter().copied()) {
            local_check +=
                coeff * (share.mac - self.spdz_f2().alpha_share() * lift_prime_to_field::<F40b>(f2_to_fe::<F40b>(value)));
            coeff *= chi;
        }
        let remote_check = exchange_sequence(channel, self.role(), &[local_check])?;
        if local_check + remote_check[0] != F40b::ZERO {
            return Err(eyre!("SPDZ bit MAC check failed"));
        }
        Ok(opened)
    }

    fn open_shared_field_batch<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        shares: &[SpdzFieldShare<FE>],
    ) -> Result<Vec<FE::PrimeField>> {
        if shares.is_empty() {
            return Ok(Vec::new());
        }

        let local_values: Vec<_> = shares.iter().map(|share| share.share).collect();
        let remote_values = exchange_sequence(channel, self.role(), &local_values)?;
        let opened: Vec<_> = local_values
            .into_iter()
            .zip(remote_values)
            .map(|(local, remote)| local + remote)
            .collect();

        let chi = sample_joint_field::<FE, _, _>(channel, rng, self.role())?;
        let mut coeff = FE::ONE;
        let mut local_check = FE::ZERO;
        for (share, value) in shares.iter().zip(opened.iter().copied()) {
            local_check += coeff * (share.mac - self.spdz_fe().alpha_share() * value);
            coeff *= chi;
        }
        let remote_check = exchange_sequence(channel, self.role(), &[local_check])?;
        if local_check + remote_check[0] != FE::ZERO {
            return Err(eyre!("SPDZ field MAC check failed"));
        }
        Ok(opened)
    }

    fn multiply_shared_bits_with_triples<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        lhs: &[SpdzBitShare],
        rhs: &[SpdzBitShare],
        triples: &[SpdzSharedBitTriple],
    ) -> Result<Vec<SpdzBitShare>> {
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
        let d_values = self.open_shared_bit_batch(channel, rng, &d_masks)?;
        let e_values = self.open_shared_bit_batch(channel, rng, &e_masks)?;

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

    fn authenticated_cross_term_bit<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        sender_bits: &[F2],
        receiver_bits: &[F2],
        current_is_sender: bool,
    ) -> Result<Vec<SpdzBitShare>> {
        let n = if current_is_sender {
            sender_bits.len()
        } else {
            receiver_bits.len()
        };
        if n == 0 {
            return Ok(Vec::new());
        }

        if current_is_sender {
            let mut value_msgs = Vec::with_capacity(n);
            let mut mac_msgs = Vec::with_capacity(n);
            let mut value_shares = Vec::with_capacity(n);
            let mut mac_shares = Vec::with_capacity(n);
            for &bit in sender_bits {
                let r = F2::random(rng);
                value_shares.push(r);
                value_msgs.push((field_to_block(r), field_to_block(r + bit)));

                let rho = F40b::random(rng);
                mac_shares.push(-rho);
                let delta = if bit == F2::ONE {
                    self.spdz_f2().alpha_share()
                } else {
                    F40b::ZERO
                };
                mac_msgs.push((field_to_block(rho), field_to_block(rho + delta)));
            }
            self.ot_mut().sender.send(channel, &value_msgs, rng)?;
            self.ot_mut().sender.send(channel, &mac_msgs, rng)?;

            let choices: Vec<_> = sender_bits.iter().map(|bit| *bit == F2::ONE).collect();
            let reverse_mac = self.ot_mut().receiver.receive(channel, &choices, rng)?;
            Ok(value_shares
                .into_iter()
                .zip(mac_shares)
                .zip(reverse_mac)
                .map(|((share, mac), reverse)| {
                    SpdzAuthenticatedShare::new(share, mac + block_to_field::<F40b>(reverse).unwrap())
                })
                .collect())
        } else {
            let choices: Vec<_> = receiver_bits.iter().map(|bit| *bit == F2::ONE).collect();
            let received_values = self.ot_mut().receiver.receive(channel, &choices, rng)?;
            let received_mac = self.ot_mut().receiver.receive(channel, &choices, rng)?;

            let mut reverse_mac_msgs = Vec::with_capacity(n);
            let mut reverse_mac_shares = Vec::with_capacity(n);
            for &bit in receiver_bits {
                let rho = F40b::random(rng);
                reverse_mac_shares.push(-rho);
                let delta = if bit == F2::ONE {
                    self.spdz_f2().alpha_share()
                } else {
                    F40b::ZERO
                };
                reverse_mac_msgs.push((field_to_block(rho), field_to_block(rho + delta)));
            }
            self.ot_mut().sender.send(channel, &reverse_mac_msgs, rng)?;

            Ok(received_values
                .into_iter()
                .zip(received_mac)
                .zip(reverse_mac_shares)
                .map(|((value, mac), reverse_mac)| {
                    SpdzAuthenticatedShare::new(
                        block_to_field::<F2>(value).unwrap(),
                        block_to_field::<F40b>(mac).unwrap() + reverse_mac,
                    )
                })
                .collect())
        }
    }

    fn authenticated_cross_term_field<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        sender_bits: &[F2],
        receiver_bits: &[F2],
        current_is_sender: bool,
    ) -> Result<Vec<SpdzFieldShare<FE>>> {
        let n = if current_is_sender {
            sender_bits.len()
        } else {
            receiver_bits.len()
        };
        if n == 0 {
            return Ok(Vec::new());
        }

        if current_is_sender {
            let mut value_msgs = Vec::with_capacity(n);
            let mut mac_msgs = Vec::with_capacity(n);
            let mut value_shares = Vec::with_capacity(n);
            let mut mac_shares = Vec::with_capacity(n);
            for &bit in sender_bits {
                let r = FE::random(rng);
                value_shares.push(-r);
                let delta_value = if bit == F2::ONE {
                    FE::ONE
                } else {
                    FE::ZERO
                };
                value_msgs.push((field_to_block(r), field_to_block(r + delta_value)));

                let rho = FE::random(rng);
                mac_shares.push(-rho);
                let delta_mac = if bit == F2::ONE {
                    self.spdz_fe().alpha_share()
                } else {
                    FE::ZERO
                };
                mac_msgs.push((field_to_block(rho), field_to_block(rho + delta_mac)));
            }
            self.ot_mut().sender.send(channel, &value_msgs, rng)?;
            self.ot_mut().sender.send(channel, &mac_msgs, rng)?;

            let choices: Vec<_> = sender_bits.iter().map(|bit| *bit == F2::ONE).collect();
            let reverse_mac = self.ot_mut().receiver.receive(channel, &choices, rng)?;
            Ok(value_shares
                .into_iter()
                .zip(mac_shares)
                .zip(reverse_mac)
                .map(|((share, mac), reverse)| {
                    SpdzAuthenticatedShare::new(share, mac + block_to_field::<FE>(reverse).unwrap())
                })
                .collect())
        } else {
            let choices: Vec<_> = receiver_bits.iter().map(|bit| *bit == F2::ONE).collect();
            let received_values = self.ot_mut().receiver.receive(channel, &choices, rng)?;
            let received_mac = self.ot_mut().receiver.receive(channel, &choices, rng)?;

            let mut reverse_mac_msgs = Vec::with_capacity(n);
            let mut reverse_mac_shares = Vec::with_capacity(n);
            for &bit in receiver_bits {
                let rho = FE::random(rng);
                reverse_mac_shares.push(-rho);
                let delta_mac = if bit == F2::ONE {
                    self.spdz_fe().alpha_share()
                } else {
                    FE::ZERO
                };
                reverse_mac_msgs.push((field_to_block(rho), field_to_block(rho + delta_mac)));
            }
            self.ot_mut().sender.send(channel, &reverse_mac_msgs, rng)?;

            Ok(received_values
                .into_iter()
                .zip(received_mac)
                .zip(reverse_mac_shares)
                .map(|((value, mac), reverse_mac)| {
                    SpdzAuthenticatedShare::new(
                        block_to_field::<FE>(value).unwrap(),
                        block_to_field::<FE>(mac).unwrap() + reverse_mac,
                    )
                })
                .collect())
        }
    }

    fn multiply_shared_bits_direct<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        lhs: &[SpdzBitShare],
        rhs: &[SpdzBitShare],
    ) -> Result<Vec<SpdzBitShare>> {
        if lhs.is_empty() {
            return Ok(Vec::new());
        }

        let local_terms: Vec<_> = lhs
            .iter()
            .zip(rhs.iter())
            .map(|(x, y)| x.share * y.share)
            .collect();
        let (owned_local_terms, peer_local_terms) = if self.role().is_first() {
            (
                self.share_owned_f2_values(channel, rng, &local_terms)?,
                self.receive_shared_f2_values(channel, local_terms.len())?,
            )
        } else {
            let peer_local_terms = self.receive_shared_f2_values(channel, local_terms.len())?;
            let owned_local_terms = self.share_owned_f2_values(channel, rng, &local_terms)?;
            (owned_local_terms, peer_local_terms)
        };

        let lhs_values: Vec<_> = lhs.iter().map(|share| share.share).collect();
        let rhs_values: Vec<_> = rhs.iter().map(|share| share.share).collect();
        let first_second = self.authenticated_cross_term_bit(
            channel,
            rng,
            &lhs_values,
            &rhs_values,
            self.role().is_first(),
        )?;
        let second_first = self.authenticated_cross_term_bit(
            channel,
            rng,
            &lhs_values,
            &rhs_values,
            !self.role().is_first(),
        )?;

        Ok(owned_local_terms
            .into_iter()
            .zip(peer_local_terms)
            .zip(first_second)
            .zip(second_first)
            .map(|(((local_term, peer_term), first_second), second_first)| {
                self.add_bit_shares(
                    self.add_bit_shares(local_term, peer_term),
                    self.add_bit_shares(first_second, second_first),
                )
            })
            .collect())
    }

    fn add_private_bit_contributions_with_triples<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        lhs: &[SpdzSharedEdabit<FE>],
        rhs: &[SpdzSharedEdabit<FE>],
        triples: &[SpdzSharedBitTriple],
    ) -> Result<(Vec<Vec<SpdzBitShare>>, Vec<SpdzBitShare>)> {
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
                rng,
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

    fn add_private_bit_contributions_direct<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        lhs: &[SpdzSharedEdabit<FE>],
        rhs: &[SpdzSharedEdabit<FE>],
    ) -> Result<(Vec<Vec<SpdzBitShare>>, Vec<SpdzBitShare>)> {
        if lhs.is_empty() {
            return Ok((Vec::new(), Vec::new()));
        }

        let num = lhs.len();
        let bit_size = lhs[0].bit_len();
        let mut carry = vec![self.zero_bit_share(); num];
        let mut sums = vec![Vec::with_capacity(bit_size); num];
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

            let and_results =
                self.multiply_shared_bits_direct(channel, rng, &and1_batch, &and2_batch)?;
            for (carry_slot, and_result) in carry.iter_mut().zip(and_results) {
                *carry_slot = self.add_bit_shares(*carry_slot, and_result);
            }
        }
        Ok((sums, carry))
    }

    fn convert_shared_bits_to_field<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bits: &[SpdzBitShare],
    ) -> Result<Vec<SpdzFieldShare<FE>>> {
        if bits.is_empty() {
            return Ok(Vec::new());
        }

        let local_field_bits: Vec<_> = bits
            .iter()
            .map(|bit| if bit.share == F2::ONE { FE::ONE } else { FE::ZERO })
            .collect();
        let (local_contribs, peer_contribs) = if self.role().is_first() {
            (
                self.share_owned_fe_values(channel, rng, &local_field_bits)?,
                self.receive_shared_fe_values(channel, local_field_bits.len())?,
            )
        } else {
            let peer_contribs = self.receive_shared_fe_values(channel, local_field_bits.len())?;
            let local_contribs = self.share_owned_fe_values(channel, rng, &local_field_bits)?;
            (local_contribs, peer_contribs)
        };

        let bit_values: Vec<_> = bits.iter().map(|bit| bit.share).collect();
        let cross_terms = self.authenticated_cross_term_field(
            channel,
            rng,
            &bit_values,
            &bit_values,
            self.role().is_first(),
        )?;
        Ok(local_contribs
            .into_iter()
            .zip(peer_contribs)
            .zip(cross_terms)
            .map(|((local, peer), cross)| {
                self.add_field_shares(
                    self.add_field_shares(local, peer),
                    self.scale_field_share(cross, -(FE::ONE + FE::ONE)),
                )
            })
            .collect())
    }

    fn sum_private_arithmetic_shares(
        &self,
        private_edabits: &[SpdzPrivateEdabit<FE>],
        peer_private_edabits: &[SpdzSharedEdabit<FE>],
    ) -> Vec<SpdzFieldShare<FE>> {
        private_edabits
            .iter()
            .zip(peer_private_edabits.iter())
            .map(|(local, remote)| self.add_field_shares(local.shared.value, remote.value))
            .collect()
    }

    fn apply_overflow_correction(
        &self,
        arithmetic_sums: &[SpdzFieldShare<FE>],
        carry_field_shares: &[SpdzFieldShare<FE>],
        bit_size: usize,
    ) -> Vec<SpdzFieldShare<FE>> {
        let correction_scale = -power_two::<FE>(bit_size);
        arithmetic_sums
            .iter()
            .zip(carry_field_shares.iter())
            .map(|(sum, carry)| self.add_field_shares(*sum, self.scale_field_share(*carry, correction_scale)))
            .collect()
    }

    fn assemble_global_edabits(
        &self,
        bit_shares: &[Vec<SpdzBitShare>],
        value_shares: &[SpdzFieldShare<FE>],
    ) -> Vec<SpdzGlobalEdabit<FE>> {
        bit_shares
            .iter()
            .zip(value_shares.iter())
            .map(|(bits, value)| SpdzSharedEdabit {
                bits: bits.clone(),
                value: *value,
            })
            .collect()
    }

    fn open_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        global_edabits: &[SpdzGlobalEdabit<FE>],
    ) -> Result<Vec<(Vec<F2>, FE)>> {
        let mut out = Vec::with_capacity(global_edabits.len());
        for edabit in global_edabits {
            let bits = self.open_shared_bit_batch(channel, rng, &edabit.bits)?;
            let value = self.open_shared_field_batch(channel, rng, &[edabit.value])?[0];
            out.push((bits, value));
        }
        Ok(out)
    }

    fn combine_private_into_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        private_edabits: &[SpdzPrivateEdabit<FE>],
        peer_private_edabits: &[SpdzSharedEdabit<FE>],
    ) -> Result<Vec<SpdzGlobalEdabit<FE>>> {
        if private_edabits.is_empty() {
            return Ok(Vec::new());
        }

        let bit_size = private_edabits[0].shared.bit_len();
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
        let (global_bits, overflow_carries) = self.add_private_bit_contributions_direct(
            channel,
            rng,
            &first_party_private,
            &second_party_private,
        )?;
        let carry_field_shares = self.convert_shared_bits_to_field(channel, rng, &overflow_carries)?;
        let arithmetic_sums =
            self.sum_private_arithmetic_shares(private_edabits, peer_private_edabits);
        let corrected_values =
            self.apply_overflow_correction(&arithmetic_sums, &carry_field_shares, bit_size);
        Ok(self.assemble_global_edabits(&global_bits, &corrected_values))
    }
}
