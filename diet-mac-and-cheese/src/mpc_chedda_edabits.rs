#![allow(clippy::too_many_arguments)]

//! Peer-oriented MPC edaBits built from the Chedda seed-daBit plus PRG
//! pipeline, followed by owner/0 embedding and the existing global combine.

use crate::cheddabits::{
    ChedDabitGeneratorProverV1, ChedDabitGeneratorProverV2, ChedDabitGeneratorVerifierV1,
    ChedDabitGeneratorVerifierV2, DabitGeneratorProverT, DabitGeneratorVerifierT,
};
use crate::cheddaprg::{LocalPrg, PredicateT, PrgDimensions, TSPAPredicate, Xor4Maj7Predicate};
use crate::conv::{EdabitsProver, EdabitsVerifier, ProverFromHomComsT, VerifierFromHomComsT};
use crate::edabits::{ProverConv, RcRefCell, VerifierConv};
use crate::hd_quicksilver::{HDMacProver, HDMacVerifier, QSStateProver, QSStateVerifier};
use crate::homcom::{FComProver, FComVerifier, MacProver, MacVerifier};
use crate::mpc_conv::{GlobalEdabit, PrivateEdabit, PrivateEdabitState, SharedEdabit};
use crate::mpc_edabits_common::{convert_bits_to_field, estimate_combine_voles, MpcEdabitsCommon};
use crate::mpc_homcom::{PeerFieldMacs, PeerRole};
use eyre::{eyre, Result};
use num_traits::One;
use ocelot::svole::wykw::LpnParams;
use rand::{CryptoRng, Rng};
use scuttlebutt::{
    field::{F40b, FiniteField, F2},
    ring::FiniteRing,
    utils::{pack_bits, unpack_bits},
    AbstractChannel,
};

#[derive(Clone, Debug)]
struct ExpandedProverDabit<FE: FiniteField<PrimeField = FE>, const D2: usize, const DP: usize> {
    bit: HDMacProver<F40b, D2>,
    value: HDMacProver<FE, DP>,
}

impl<FE: FiniteField<PrimeField = FE>, const D2: usize, const DP: usize>
    ExpandedProverDabit<FE, D2, DP>
{
    fn clear_bit(&self) -> F2 {
        if self.bit.value() == F40b::ZERO {
            debug_assert_eq!(self.value.value(), FE::ZERO);
            F2::ZERO
        } else {
            debug_assert_eq!(self.bit.value(), F40b::ONE);
            debug_assert_eq!(self.value.value(), FE::ONE);
            F2::ONE
        }
    }
}

#[derive(Clone, Debug)]
struct ExpandedVerifierDabit<FE: FiniteField<PrimeField = FE>> {
    bit: HDMacVerifier<F40b>,
    value: HDMacVerifier<FE>,
}

struct LocalPrivateEdabitBatch<FE: FiniteField<PrimeField = FE>, const D2: usize, const DP: usize> {
    private_edabits: Vec<PrivateEdabit<FE>>,
    proof_edabits: Vec<EdabitsProver<FE>>,
    dabits: Vec<ExpandedProverDabit<FE, D2, DP>>,
}

struct RemotePrivateEdabitBatch<FE: FiniteField<PrimeField = FE>> {
    peer_private_edabits: Vec<SharedEdabit<FE>>,
    peer_private_proof_edabits: Vec<EdabitsVerifier<FE>>,
    dabits: Vec<ExpandedVerifierDabit<FE>>,
}

/// Opaque checkpoint for benchmarking the MPC Chedda pipeline in phases.
pub struct UncheckedPrivateEdabitState<
    FE: FiniteField<PrimeField = FE>,
    const D2: usize,
    const DP: usize,
> {
    state: PrivateEdabitState<FE>,
    local_dabits: Vec<ExpandedProverDabit<FE, D2, DP>>,
    remote_dabits: Vec<ExpandedVerifierDabit<FE>>,
}

fn gen_powers_of_two<FE: FiniteField>(k: usize) -> Vec<FE> {
    let two = FE::ONE + FE::ONE;
    let mut power = two;
    let mut powers_of_two = Vec::with_capacity(k);
    powers_of_two.push(FE::ONE);
    if k == 0 {
        return powers_of_two;
    }
    for i in 1..k {
        if i == 1 {
            powers_of_two.push(two);
        } else {
            power *= two;
            powers_of_two.push(power);
        }
    }
    powers_of_two
}

fn extract_prover_edabits<FE: FiniteField<PrimeField = FE>>(
    private_edabits: &[PrivateEdabit<FE>],
) -> Vec<EdabitsProver<FE>> {
    private_edabits
        .iter()
        .map(|private| EdabitsProver {
            bits: private
                .shared
                .bits
                .iter()
                .map(|bit_share| bit_share.local)
                .collect(),
            value: private.shared.value.local,
        })
        .collect()
}

fn extract_verifier_edabits<FE: FiniteField<PrimeField = FE>>(
    peer_private_edabits: &[SharedEdabit<FE>],
) -> Vec<EdabitsVerifier<FE>> {
    peer_private_edabits
        .iter()
        .map(|shared| EdabitsVerifier {
            bits: shared
                .bits
                .iter()
                .map(|bit_share| bit_share.remote)
                .collect(),
            value: shared.value.remote,
        })
        .collect()
}

fn prover_dabits_to_clear_edabits_generic<
    FE: FiniteField<PrimeField = FE>,
    const D2: usize,
    const DP: usize,
>(
    dabits: &[ExpandedProverDabit<FE, D2, DP>],
    bit_size: usize,
) -> (Vec<Vec<F2>>, Vec<FE>) {
    let mut clear_bits = Vec::with_capacity(dabits.len() / bit_size);
    let mut clear_values = Vec::with_capacity(dabits.len() / bit_size);
    for chunk in dabits.chunks_exact(bit_size) {
        let bits: Vec<_> = chunk.iter().map(ExpandedProverDabit::clear_bit).collect();
        clear_values.push(convert_bits_to_field::<FE>(&bits));
        clear_bits.push(bits);
    }
    (clear_bits, clear_values)
}

struct CheddaDaBitSourceProver<
    FE: FiniteField<PrimeField = FE>,
    DGP: DabitGeneratorProverT<FE>,
    PRED: PredicateT<FE, LOC, D2, DP> + PrgDimensions,
    const LOC: usize,
    const D2: usize,
    const DP: usize,
> {
    prg: LocalPrg<PRED, FE, LOC, D2, DP>,
    fcom_f2: RcRefCell<FComProver<F40b>>,
    fcom_fe: RcRefCell<FComProver<FE>>,
    dabit_gen: DGP,
    seed_2: Vec<MacProver<F40b>>,
    seed_p: Vec<MacProver<FE>>,
}

impl<
        FE: FiniteField<PrimeField = FE>,
        DGP: DabitGeneratorProverT<FE>,
        PRED: PredicateT<FE, LOC, D2, DP> + PrgDimensions,
        const LOC: usize,
        const D2: usize,
        const DP: usize,
    > CheddaDaBitSourceProver<FE, DGP, PRED, LOC, D2, DP>
where
    DGP: ProverFromHomComsT<FE>,
{
    fn new(
        prg: LocalPrg<PRED, FE, LOC, D2, DP>,
        fcom_f2: &RcRefCell<FComProver<F40b>>,
        fcom_fe: &RcRefCell<FComProver<FE>>,
    ) -> Result<Self> {
        Ok(Self {
            prg,
            fcom_f2: fcom_f2.clone(),
            fcom_fe: fcom_fe.clone(),
            dabit_gen: DGP::from_homcoms(fcom_f2, fcom_fe)?,
            seed_2: Vec::new(),
            seed_p: Vec::new(),
        })
    }
}

impl<
        FE: FiniteField<PrimeField = FE>,
        DGP: DabitGeneratorProverT<FE>,
        PRED: PredicateT<FE, LOC, D2, DP> + PrgDimensions,
        const LOC: usize,
        const D2: usize,
        const DP: usize,
    > CheddaDaBitSourceProver<FE, DGP, PRED, LOC, D2, DP>
{
    fn gen_seed<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) -> Result<()> {
        let prg_seed_size = self.prg.get_seed_length();
        if self.seed_2.is_empty() || self.prg.get_remaining() < prg_seed_size {
            (self.seed_2, self.seed_p) = self.dabit_gen.gen_dabits(channel, rng, prg_seed_size)?;
        } else {
            let mut new_seed_2_values = Vec::with_capacity(prg_seed_size);
            let mut new_seed_p_values = Vec::with_capacity(prg_seed_size);
            let mut dabits = Vec::with_capacity(prg_seed_size);
            for _ in 0..prg_seed_size {
                let dabit = self
                    .prg
                    .next_prover(&self.seed_2, &self.seed_p)
                    .expect("enough output capacity left");
                if dabit.0.value() == F40b::ZERO {
                    debug_assert_eq!(dabit.1.value(), FE::ZERO);
                    new_seed_2_values.push(F2::ZERO);
                    new_seed_p_values.push(FE::ZERO);
                } else if dabit.0.value() == F40b::ONE {
                    debug_assert_eq!(dabit.1.value(), FE::ONE);
                    new_seed_2_values.push(F2::ONE);
                    new_seed_p_values.push(FE::ONE);
                } else {
                    unreachable!();
                }
                dabits.push(dabit);
            }

            let new_seed_2_macs =
                self.fcom_f2
                    .get_refmut()
                    .input(channel, rng, &new_seed_2_values)?;
            let new_seed_p_macs =
                self.fcom_fe
                    .get_refmut()
                    .input(channel, rng, &new_seed_p_values)?;
            channel.flush()?;

            let new_seed_2: Vec<_> = new_seed_2_values
                .iter()
                .copied()
                .zip(new_seed_2_macs.into_iter())
                .map(|(value, mac)| MacProver::new(value, mac))
                .collect();
            let new_seed_p: Vec<_> = new_seed_p_values
                .iter()
                .copied()
                .zip(new_seed_p_macs.into_iter())
                .map(|(value, mac)| MacProver::new(value, mac))
                .collect();

            let chi_2 = channel.read_serializable()?;
            let chi_p = channel.read_serializable()?;
            let mut qs_state_2 = QSStateProver::<F40b, D2>::init_with_chi(chi_2);
            let mut qs_state_p = QSStateProver::<FE, DP>::init_with_chi(chi_p);
            for i in 0..prg_seed_size {
                dabits[i].0.sub_assign(&HDMacProver::from(new_seed_2[i]));
                dabits[i].1.sub_assign(&HDMacProver::from(new_seed_p[i]));
                qs_state_2.check_zero(&dabits[i].0);
                qs_state_p.check_zero(&dabits[i].1);
            }
            qs_state_2.finalize(channel, rng, &mut self.fcom_f2.get_refmut())?;
            qs_state_p.finalize(channel, rng, &mut self.fcom_fe.get_refmut())?;
            self.prg.reset();
            self.seed_2 = new_seed_2;
            self.seed_p = new_seed_p;
        }
        Ok(())
    }

    fn gen_dabit<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) -> Result<ExpandedProverDabit<FE, D2, DP>> {
        if self.seed_2.is_empty() || self.prg.get_remaining() <= self.prg.get_seed_length() {
            self.gen_seed(channel, rng)?;
        }
        assert!(self.prg.get_remaining() > self.prg.get_seed_length());
        let (bit, value) = self
            .prg
            .next_prover(&self.seed_2, &self.seed_p)
            .ok_or(eyre!("dabit generation failed"))?;
        Ok(ExpandedProverDabit { bit, value })
    }

    fn gen_dabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num: usize,
    ) -> Result<Vec<ExpandedProverDabit<FE, D2, DP>>> {
        let mut out = Vec::with_capacity(num);
        for _ in 0..num {
            out.push(self.gen_dabit(channel, rng)?);
        }
        Ok(out)
    }

    fn verify_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        conversion_tuples: &[EdabitsProver<FE>],
        dabits: &[ExpandedProverDabit<FE, D2, DP>],
    ) -> Result<()> {
        if conversion_tuples.is_empty() {
            return Ok(());
        }
        let num_cts = conversion_tuples.len();
        let bit_size = conversion_tuples[0].bits.len();
        let num_bits = num_cts * bit_size;
        debug_assert_eq!(dabits.len(), num_bits);

        let corrections = {
            let mut corrections = Vec::<bool>::with_capacity(num_bits);
            let mut dabit_j = 0;
            for ct in conversion_tuples {
                debug_assert_eq!(ct.bits.len(), bit_size);
                for bit in &ct.bits {
                    corrections
                        .push((F40b::from(bit.value()) + dabits[dabit_j].bit.poly[D2]).is_one());
                    dabit_j += 1;
                }
            }
            channel.write_bytes(&pack_bits(&corrections))?;
            channel.flush()?;
            corrections
        };

        let chi_2: F40b = channel.read_serializable()?;
        let chi_p: FE = channel.read_serializable()?;
        let mut qs_state_2 = QSStateProver::<F40b, D2>::init_with_chi(chi_2);
        let mut qs_state_p = QSStateProver::<FE, DP>::init_with_chi(chi_p);
        let powers_of_two = gen_powers_of_two(bit_size);

        let mut dabit_j = 0;
        for ct in conversion_tuples {
            let mut acc = HDMacProver::from(ct.value);
            for (i, bit) in ct.bits.iter().enumerate() {
                let c = corrections[dabit_j];
                let mut bit_check = dabits[dabit_j].bit.clone();
                bit_check.add_assign(&HDMacProver::from(*bit));
                bit_check.add_assign_constant(if c { F40b::ONE } else { F40b::ZERO });
                qs_state_2.check_zero(&bit_check);

                let mut value_check = dabits[dabit_j].value.clone();
                if c {
                    value_check.sub_assign_constant(FE::ONE);
                    value_check.mul_assign_constant(-FE::ONE);
                }
                value_check.mul_assign_constant(powers_of_two[i]);
                acc.sub_assign(&value_check);
                dabit_j += 1;
            }
            qs_state_p.check_zero(&acc);
        }

        qs_state_2.finalize(channel, rng, &mut self.fcom_f2.get_refmut())?;
        qs_state_p.finalize(channel, rng, &mut self.fcom_fe.get_refmut())?;
        Ok(())
    }
}

struct CheddaDaBitSourceVerifier<
    FE: FiniteField<PrimeField = FE>,
    DGV: DabitGeneratorVerifierT<FE>,
    PRED: PredicateT<FE, LOC, D2, DP> + PrgDimensions,
    const LOC: usize,
    const D2: usize,
    const DP: usize,
> {
    prg: LocalPrg<PRED, FE, LOC, D2, DP>,
    fcom_f2: RcRefCell<FComVerifier<F40b>>,
    fcom_fe: RcRefCell<FComVerifier<FE>>,
    dabit_gen: DGV,
    seed_2: Vec<MacVerifier<F40b>>,
    seed_p: Vec<MacVerifier<FE>>,
}

impl<
        FE: FiniteField<PrimeField = FE>,
        DGV: DabitGeneratorVerifierT<FE>,
        PRED: PredicateT<FE, LOC, D2, DP> + PrgDimensions,
        const LOC: usize,
        const D2: usize,
        const DP: usize,
    > CheddaDaBitSourceVerifier<FE, DGV, PRED, LOC, D2, DP>
where
    DGV: VerifierFromHomComsT<FE>,
{
    fn new(
        prg: LocalPrg<PRED, FE, LOC, D2, DP>,
        fcom_f2: &RcRefCell<FComVerifier<F40b>>,
        fcom_fe: &RcRefCell<FComVerifier<FE>>,
    ) -> Result<Self> {
        Ok(Self {
            prg,
            fcom_f2: fcom_f2.clone(),
            fcom_fe: fcom_fe.clone(),
            dabit_gen: DGV::from_homcoms(fcom_f2, fcom_fe)?,
            seed_2: Vec::new(),
            seed_p: Vec::new(),
        })
    }
}

impl<
        FE: FiniteField<PrimeField = FE>,
        DGV: DabitGeneratorVerifierT<FE>,
        PRED: PredicateT<FE, LOC, D2, DP> + PrgDimensions,
        const LOC: usize,
        const D2: usize,
        const DP: usize,
    > CheddaDaBitSourceVerifier<FE, DGV, PRED, LOC, D2, DP>
{
    fn gen_seed<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) -> Result<()> {
        let prg_seed_size = self.prg.get_seed_length();
        if self.seed_2.is_empty() || self.prg.get_remaining() < prg_seed_size {
            (self.seed_2, self.seed_p) = self.dabit_gen.gen_dabits(channel, rng, prg_seed_size)?;
        } else {
            let delta_2 = self.fcom_f2.get_refmut().get_delta();
            let delta_p = self.fcom_fe.get_refmut().get_delta();
            let mut dabits = Vec::with_capacity(prg_seed_size);
            for _ in 0..prg_seed_size {
                dabits.push(
                    self.prg
                        .next_verifier(delta_2, delta_p, &self.seed_2, &self.seed_p)
                        .expect("enough output capacity left"),
                );
            }

            let new_seed_2 = self
                .fcom_f2
                .get_refmut()
                .input(channel, rng, prg_seed_size)?;
            let new_seed_p = self
                .fcom_fe
                .get_refmut()
                .input(channel, rng, prg_seed_size)?;
            let chi_2 = F40b::random(rng);
            let chi_p = FE::random(rng);
            channel.write_serializable(&chi_2)?;
            channel.write_serializable(&chi_p)?;
            channel.flush()?;

            let mut qs_state_2 = QSStateVerifier::<F40b>::init_with_delta_and_chi(delta_2, chi_2);
            let mut qs_state_p = QSStateVerifier::<FE>::init_with_delta_and_chi(delta_p, chi_p);
            for i in 0..prg_seed_size {
                dabits[i]
                    .0
                    .sub_assign(delta_2, &HDMacVerifier::from(new_seed_2[i]));
                dabits[i]
                    .1
                    .sub_assign(delta_p, &HDMacVerifier::from(new_seed_p[i]));
                qs_state_2.check_zero(&dabits[i].0);
                qs_state_p.check_zero(&dabits[i].1);
            }
            if !qs_state_2.finalize_and_verify::<C, RNG, D2>(
                channel,
                rng,
                &mut self.fcom_f2.get_refmut(),
            )? {
                return Err(eyre!("QS over F2 verification failed"));
            }
            if !qs_state_p.finalize_and_verify::<C, RNG, DP>(
                channel,
                rng,
                &mut self.fcom_fe.get_refmut(),
            )? {
                return Err(eyre!("QS over Fp verification failed"));
            }

            self.prg.reset();
            self.seed_2 = new_seed_2;
            self.seed_p = new_seed_p;
        }
        Ok(())
    }

    fn gen_dabit<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) -> Result<ExpandedVerifierDabit<FE>> {
        if self.seed_2.is_empty() || self.prg.get_remaining() <= self.prg.get_seed_length() {
            self.gen_seed(channel, rng)?;
        }
        assert!(self.prg.get_remaining() > self.prg.get_seed_length());
        let delta_2 = self.fcom_f2.get_refmut().get_delta();
        let delta_p = self.fcom_fe.get_refmut().get_delta();
        let (bit, value) = self
            .prg
            .next_verifier(delta_2, delta_p, &self.seed_2, &self.seed_p)
            .ok_or(eyre!("dabit generation failed"))?;
        Ok(ExpandedVerifierDabit { bit, value })
    }

    fn gen_dabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        num: usize,
    ) -> Result<Vec<ExpandedVerifierDabit<FE>>> {
        let mut out = Vec::with_capacity(num);
        for _ in 0..num {
            out.push(self.gen_dabit(channel, rng)?);
        }
        Ok(out)
    }

    fn verify_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        conversion_tuples: &[EdabitsVerifier<FE>],
        dabits: &[ExpandedVerifierDabit<FE>],
    ) -> Result<()> {
        if conversion_tuples.is_empty() {
            return Ok(());
        }
        let num_cts = conversion_tuples.len();
        let bit_size = conversion_tuples[0].bits.len();
        let num_bits = num_cts * bit_size;
        debug_assert_eq!(dabits.len(), num_bits);

        let mut correction_bytes = vec![0u8; (num_bits + 7) / 8];
        channel.read_bytes(&mut correction_bytes)?;
        let corrections = unpack_bits(&correction_bytes, num_bits);

        let delta_2 = self.fcom_f2.get_refmut().get_delta();
        let delta_p = self.fcom_fe.get_refmut().get_delta();
        let chi_2 = F40b::random(rng);
        let chi_p = FE::random(rng);
        channel.write_serializable(&chi_2)?;
        channel.write_serializable(&chi_p)?;
        channel.flush()?;

        let mut qs_state_2 = QSStateVerifier::<F40b>::init_with_delta_and_chi(delta_2, chi_2);
        let mut qs_state_p = QSStateVerifier::<FE>::init_with_delta_and_chi(delta_p, chi_p);
        let powers_of_two = gen_powers_of_two(bit_size);

        let mut dabit_j = 0;
        for ct in conversion_tuples {
            let mut acc = HDMacVerifier::from(ct.value);
            for (i, bit) in ct.bits.iter().enumerate() {
                let c = corrections[dabit_j];
                let mut bit_check = dabits[dabit_j].bit.clone();
                bit_check.add_assign(delta_2, &HDMacVerifier::from(*bit));
                bit_check.add_assign_constant(delta_2, if c { F40b::ONE } else { F40b::ZERO });
                qs_state_2.check_zero(&bit_check);

                let mut value_check = dabits[dabit_j].value.clone();
                if c {
                    value_check.sub_assign_constant(delta_p, FE::ONE);
                    value_check.mul_assign_constant(-FE::ONE);
                }
                value_check.mul_assign_constant(powers_of_two[i]);
                acc.sub_assign(delta_p, &value_check);
                dabit_j += 1;
            }
            qs_state_p.check_zero(&acc);
        }

        if !qs_state_2.finalize_and_verify::<C, RNG, D2>(
            channel,
            rng,
            &mut self.fcom_f2.get_refmut(),
        )? {
            return Err(eyre!("QS over F2 verification failed"));
        }
        if !qs_state_p.finalize_and_verify::<C, RNG, DP>(
            channel,
            rng,
            &mut self.fcom_fe.get_refmut(),
        )? {
            return Err(eyre!("QS over Fp verification failed"));
        }
        Ok(())
    }
}

pub struct MpcCheddaEdabitsPeer<
    FE: FiniteField<PrimeField = FE>,
    DGP: DabitGeneratorProverT<FE>,
    DGV: DabitGeneratorVerifierT<FE>,
    PRED: PredicateT<FE, LOC, D2, DP> + PrgDimensions,
    const LOC: usize,
    const D2: usize,
    const DP: usize,
> {
    role: PeerRole,
    pub fcom_f2: PeerFieldMacs<F40b>,
    pub fcom_fe: PeerFieldMacs<FE>,
    local_conv: ProverConv<FE>,
    remote_conv: VerifierConv<FE>,
    local_chedda: CheddaDaBitSourceProver<FE, DGP, PRED, LOC, D2, DP>,
    remote_chedda: CheddaDaBitSourceVerifier<FE, DGV, PRED, LOC, D2, DP>,
}

impl<
        FE: FiniteField<PrimeField = FE>,
        DGP: DabitGeneratorProverT<FE>,
        DGV: DabitGeneratorVerifierT<FE>,
        PRED: PredicateT<FE, LOC, D2, DP> + PrgDimensions,
        const LOC: usize,
        const D2: usize,
        const DP: usize,
    > MpcEdabitsCommon<FE> for MpcCheddaEdabitsPeer<FE, DGP, DGV, PRED, LOC, D2, DP>
{
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

impl<
        FE: FiniteField<PrimeField = FE>,
        DGP: DabitGeneratorProverT<FE> + ProverFromHomComsT<FE>,
        DGV: DabitGeneratorVerifierT<FE> + VerifierFromHomComsT<FE>,
        PRED: PredicateT<FE, LOC, D2, DP> + PrgDimensions,
        const LOC: usize,
        const D2: usize,
        const DP: usize,
    > MpcCheddaEdabitsPeer<FE, DGP, DGV, PRED, LOC, D2, DP>
{
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
        let prg_seed = Default::default();
        let local_chedda = CheddaDaBitSourceProver::new(
            LocalPrg::<PRED, FE, LOC, D2, DP>::setup(
                prg_seed,
                PRED::SEED_LENGTH,
                PRED::OUTPUT_LENGTH,
            ),
            fcom_f2.local(),
            fcom_fe.local(),
        )?;
        let remote_chedda = CheddaDaBitSourceVerifier::new(
            LocalPrg::<PRED, FE, LOC, D2, DP>::setup(
                prg_seed,
                PRED::SEED_LENGTH,
                PRED::OUTPUT_LENGTH,
            ),
            fcom_f2.remote(),
            fcom_fe.remote(),
        )?;
        Ok(Self {
            role,
            fcom_f2,
            fcom_fe,
            local_conv,
            remote_conv,
            local_chedda,
            remote_chedda,
        })
    }

    fn sample_local_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<LocalPrivateEdabitBatch<FE, D2, DP>> {
        let dabits = self.local_chedda.gen_dabits(channel, rng, bit_size * num)?;
        let (clear_bits, clear_values) = prover_dabits_to_clear_edabits_generic(&dabits, bit_size);
        let private_edabits =
            self.share_private_clear_edabits_owner_zero(channel, rng, &clear_bits, &clear_values)?;
        let proof_edabits = extract_prover_edabits(&private_edabits);
        Ok(LocalPrivateEdabitBatch {
            private_edabits,
            proof_edabits,
            dabits,
        })
    }

    fn receive_peer_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<RemotePrivateEdabitBatch<FE>> {
        let dabits = self
            .remote_chedda
            .gen_dabits(channel, rng, bit_size * num)?;
        let peer_private_edabits =
            self.receive_private_edabit_contributions_owner_zero(channel, rng, bit_size, num)?;
        let peer_private_proof_edabits = extract_verifier_edabits(&peer_private_edabits);
        Ok(RemotePrivateEdabitBatch {
            peer_private_edabits,
            peer_private_proof_edabits,
            dabits,
        })
    }

    fn sample_and_share_private_edabits_unchecked_inner<
        C: AbstractChannel,
        RNG: CryptoRng + Rng,
    >(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<UncheckedPrivateEdabitState<FE, D2, DP>> {
        let (local, remote) = if self.role.is_first() {
            let local = self.sample_local_private_edabits(channel, rng, bit_size, num)?;
            let remote = self.receive_peer_private_edabits(channel, rng, bit_size, num)?;
            (local, remote)
        } else {
            let remote = self.receive_peer_private_edabits(channel, rng, bit_size, num)?;
            let local = self.sample_local_private_edabits(channel, rng, bit_size, num)?;
            (local, remote)
        };

        Ok(UncheckedPrivateEdabitState {
            state: PrivateEdabitState {
                private_edabits: local.private_edabits,
                peer_private_edabits: remote.peer_private_edabits,
                private_proof_edabits: local.proof_edabits,
                peer_private_proof_edabits: remote.peer_private_proof_edabits,
            },
            local_dabits: local.dabits,
            remote_dabits: remote.dabits,
        })
    }

    /// Sampling/input plus owner/0-sharing stage, without the protocol-specific
    /// Chedda verification yet.
    pub fn sample_and_share_private_edabits_unchecked<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<UncheckedPrivateEdabitState<FE, D2, DP>> {
        self.sample_and_share_private_edabits_unchecked_inner(channel, rng, bit_size, num)
    }

    /// Run the Chedda consistency check on previously sampled private edaBits.
    pub fn verify_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &UncheckedPrivateEdabitState<FE, D2, DP>,
    ) -> Result<()> {
        if self.role.is_first() {
            self.local_chedda.verify_edabits(
                channel,
                rng,
                &state.state.private_proof_edabits,
                &state.local_dabits,
            )?;
            self.remote_chedda.verify_edabits(
                channel,
                rng,
                &state.state.peer_private_proof_edabits,
                &state.remote_dabits,
            )?;
        } else {
            self.remote_chedda.verify_edabits(
                channel,
                rng,
                &state.state.peer_private_proof_edabits,
                &state.remote_dabits,
            )?;
            self.local_chedda.verify_edabits(
                channel,
                rng,
                &state.state.private_proof_edabits,
                &state.local_dabits,
            )?;
        }
        Ok(())
    }

    /// Combine a previously sampled-and-verified private state into the final
    /// authenticated global edaBits.
    pub fn combine_sampled_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &UncheckedPrivateEdabitState<FE, D2, DP>,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        self.combine_private_into_global_edabits(channel, rng, &state.state)
    }

    pub fn sample_and_share_private_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<PrivateEdabitState<FE>> {
        let state =
            self.sample_and_share_private_edabits_unchecked_inner(channel, rng, bit_size, num)?;
        self.verify_private_edabits(channel, rng, &state)?;
        Ok(state.state)
    }

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

    pub fn generate_global_edabits<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Vec<GlobalEdabit<FE>>> {
        let state = self.sample_and_share_private_edabits(channel, rng, bit_size, num)?;
        self.combine_private_into_global_edabits(channel, rng, &state)
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
        MpcEdabitsCommon::open_global_edabits(self, channel, global_edabits)
    }

    pub fn estimate_combine_voles(num: usize, bit_size: u32) -> (usize, usize) {
        estimate_combine_voles::<FE>(num, bit_size)
    }
}

pub type MpcCheddaEdabitsV1TSPAPeer<FE> = MpcCheddaEdabitsPeer<
    FE,
    ChedDabitGeneratorProverV1<FE>,
    ChedDabitGeneratorVerifierV1<FE>,
    TSPAPredicate,
    { TSPAPredicate::LOC },
    { TSPAPredicate::D2 },
    { TSPAPredicate::DP },
>;

pub type TSPAUncheckedPrivateEdabitState<FE> =
    UncheckedPrivateEdabitState<FE, { TSPAPredicate::D2 }, { TSPAPredicate::DP }>;

pub type MpcCheddaEdabitsV2TSPAPeer<FE> = MpcCheddaEdabitsPeer<
    FE,
    ChedDabitGeneratorProverV2<FE>,
    ChedDabitGeneratorVerifierV2<FE>,
    TSPAPredicate,
    { TSPAPredicate::LOC },
    { TSPAPredicate::D2 },
    { TSPAPredicate::DP },
>;

pub type MpcCheddaEdabitsV1Xor4Maj7Peer<FE> = MpcCheddaEdabitsPeer<
    FE,
    ChedDabitGeneratorProverV1<FE>,
    ChedDabitGeneratorVerifierV1<FE>,
    Xor4Maj7Predicate,
    { Xor4Maj7Predicate::LOC },
    { Xor4Maj7Predicate::D2 },
    { Xor4Maj7Predicate::DP },
>;

pub type Xor4Maj7UncheckedPrivateEdabitState<FE> =
    UncheckedPrivateEdabitState<FE, { Xor4Maj7Predicate::D2 }, { Xor4Maj7Predicate::DP }>;

pub type MpcCheddaEdabitsV2Xor4Maj7Peer<FE> = MpcCheddaEdabitsPeer<
    FE,
    ChedDabitGeneratorProverV2<FE>,
    ChedDabitGeneratorVerifierV2<FE>,
    Xor4Maj7Predicate,
    { Xor4Maj7Predicate::LOC },
    { Xor4Maj7Predicate::D2 },
    { Xor4Maj7Predicate::DP },
>;

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

    type TestPeer = MpcCheddaEdabitsV1TSPAPeer<F61p>;

    fn fixed_clear_edabits(owner: usize, bit_size: usize, num: usize) -> (Vec<Vec<F2>>, Vec<F61p>) {
        let mut clear_bits = Vec::with_capacity(num);
        let mut clear_values = Vec::with_capacity(num);
        for row in 0..num {
            let mut bits = Vec::with_capacity(bit_size);
            for bit in 0..bit_size {
                let parity = ((owner + 1) * (row + 3) + bit) % 2;
                bits.push(if parity == 0 { F2::ZERO } else { F2::ONE });
            }
            clear_values.push(convert_bits_to_field::<F61p>(&bits));
            clear_bits.push(bits);
        }
        (clear_bits, clear_values)
    }

    fn assert_owner_zero_state(state: &PrivateEdabitState<F61p>) {
        for private in &state.private_edabits {
            for bit in &private.shared.bits {
                assert_eq!(bit.remote.mac(), F40b::ZERO);
            }
            assert_eq!(private.shared.value.remote.mac(), F61p::ZERO);
        }
        for peer_private in &state.peer_private_edabits {
            for bit in &peer_private.bits {
                assert_eq!(bit.local.value(), F2::ZERO);
                assert_eq!(bit.local.mac(), F40b::ZERO);
            }
            assert_eq!(peer_private.value.local.value(), F61p::ZERO);
            assert_eq!(peer_private.value.local.mac(), F61p::ZERO);
        }
    }

    #[test]
    fn test_chedda_seed_dabit_generation() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = TestPeer::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            peer.local_chedda.gen_seed(&mut channel, &mut rng).unwrap();
            peer.local_chedda
                .seed_2
                .iter()
                .zip(peer.local_chedda.seed_p.iter())
                .map(|(bit, value)| (bit.value(), value.value(), bit.mac(), value.mac()))
                .collect::<Vec<_>>()
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(right.try_clone().unwrap());
        let writer = BufWriter::new(right);
        let mut channel = Channel::new(reader, writer);
        let mut peer = TestPeer::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        peer.remote_chedda.gen_seed(&mut channel, &mut rng).unwrap();
        let remote_seed = peer.remote_chedda.seed_2.clone();
        let remote_seed_p = peer.remote_chedda.seed_p.clone();
        let delta_2 = peer.fcom_f2.remote().get_refmut().get_delta();
        let delta_p = peer.fcom_fe.remote().get_refmut().get_delta();

        let local_seed = handle.join().unwrap();
        assert_eq!(local_seed.len(), TSPAPredicate::SEED_LENGTH);
        assert_eq!(remote_seed.len(), TSPAPredicate::SEED_LENGTH);
        for i in 0..remote_seed.len() {
            let (bit, value, bit_mac, value_mac) = local_seed[i];
            assert_eq!(u8::from(bit) as u128, u128::from(value));
            assert_eq!(bit_mac, delta_2 * F40b::from(bit) + remote_seed[i].mac());
            assert_eq!(value_mac, delta_p * value + remote_seed_p[i].mac());
        }
    }

    #[test]
    fn test_chedda_prg_private_dabits_format() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = TestPeer::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            peer.local_chedda
                .gen_dabits(&mut channel, &mut rng, 32)
                .unwrap()
                .into_iter()
                .map(|dabit| (dabit.clear_bit(), dabit.value.value()))
                .collect::<Vec<_>>()
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(right.try_clone().unwrap());
        let writer = BufWriter::new(right);
        let mut channel = Channel::new(reader, writer);
        let mut peer = TestPeer::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        let verifier_dabits = peer
            .remote_chedda
            .gen_dabits(&mut channel, &mut rng, 32)
            .unwrap();
        let prover_dabits = handle.join().unwrap();
        assert_eq!(prover_dabits.len(), verifier_dabits.len());
        for (i, (bit, field_bit)) in prover_dabits.into_iter().enumerate() {
            assert!(bit == F2::ZERO || bit == F2::ONE);
            assert_eq!(
                field_bit,
                if bit == F2::ONE {
                    F61p::ONE
                } else {
                    F61p::ZERO
                }
            );
            assert!(verifier_dabits[i].bit.qs_degree >= 1);
            assert!(verifier_dabits[i].value.qs_degree >= 1);
        }
    }

    #[test]
    fn test_private_dabit_to_private_edabit_conversion() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = TestPeer::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            let dabits = peer
                .local_chedda
                .gen_dabits(&mut channel, &mut rng, 24)
                .unwrap();
            prover_dabits_to_clear_edabits_generic(&dabits, 8)
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(right.try_clone().unwrap());
        let writer = BufWriter::new(right);
        let mut channel = Channel::new(reader, writer);
        let mut peer = TestPeer::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        peer.remote_chedda
            .gen_dabits(&mut channel, &mut rng, 24)
            .unwrap();
        let (clear_bits, clear_values) = handle.join().unwrap();
        assert_eq!(clear_bits.len(), 3);
        assert_eq!(clear_values.len(), 3);
        for (bits, value) in clear_bits.iter().zip(clear_values.iter()) {
            assert_eq!(*value, convert_bits_to_field::<F61p>(bits));
        }
    }

    #[test]
    fn test_owner_zero_embedding_correctness() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = TestPeer::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            let (clear_bits, clear_values) = fixed_clear_edabits(0, 8, 4);
            let private_edabits = peer
                .share_private_clear_edabits_owner_zero(
                    &mut channel,
                    &mut rng,
                    &clear_bits,
                    &clear_values,
                )
                .unwrap();
            let peer_private_edabits = peer
                .receive_private_edabit_contributions_owner_zero(&mut channel, &mut rng, 8, 4)
                .unwrap();
            PrivateEdabitState {
                private_edabits,
                peer_private_edabits,
                private_proof_edabits: Vec::new(),
                peer_private_proof_edabits: Vec::new(),
            }
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(right.try_clone().unwrap());
        let writer = BufWriter::new(right);
        let mut channel = Channel::new(reader, writer);
        let mut peer = TestPeer::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        let peer_private_edabits = peer
            .receive_private_edabit_contributions_owner_zero(&mut channel, &mut rng, 8, 4)
            .unwrap();
        let (clear_bits, clear_values) = fixed_clear_edabits(1, 8, 4);
        let private_edabits = peer
            .share_private_clear_edabits_owner_zero(
                &mut channel,
                &mut rng,
                &clear_bits,
                &clear_values,
            )
            .unwrap();
        let local_state = PrivateEdabitState {
            private_edabits,
            peer_private_edabits,
            private_proof_edabits: Vec::new(),
            peer_private_proof_edabits: Vec::new(),
        };
        assert_owner_zero_state(&local_state);
        let remote_state = handle.join().unwrap();
        assert_owner_zero_state(&remote_state);
    }

    #[test]
    fn test_repeated_literal_zero_share_reuse() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = TestPeer::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            for _ in 0..3 {
                let (clear_bits, clear_values) = fixed_clear_edabits(0, 8, 8);
                let state = PrivateEdabitState {
                    private_edabits: peer
                        .share_private_clear_edabits_owner_zero(
                            &mut channel,
                            &mut rng,
                            &clear_bits,
                            &clear_values,
                        )
                        .unwrap(),
                    peer_private_edabits: peer
                        .receive_private_edabit_contributions_owner_zero(
                            &mut channel,
                            &mut rng,
                            8,
                            8,
                        )
                        .unwrap(),
                    private_proof_edabits: Vec::new(),
                    peer_private_proof_edabits: Vec::new(),
                };
                assert_owner_zero_state(&state);
            }
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(right.try_clone().unwrap());
        let writer = BufWriter::new(right);
        let mut channel = Channel::new(reader, writer);
        let mut peer = TestPeer::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        for _ in 0..3 {
            let (clear_bits, clear_values) = fixed_clear_edabits(1, 8, 8);
            let state = PrivateEdabitState {
                peer_private_edabits: peer
                    .receive_private_edabit_contributions_owner_zero(&mut channel, &mut rng, 8, 8)
                    .unwrap(),
                private_edabits: peer
                    .share_private_clear_edabits_owner_zero(
                        &mut channel,
                        &mut rng,
                        &clear_bits,
                        &clear_values,
                    )
                    .unwrap(),
                private_proof_edabits: Vec::new(),
                peer_private_proof_edabits: Vec::new(),
            };
            assert_owner_zero_state(&state);
        }
        handle.join().unwrap();
    }

    fn run_opened_global_edabits(bit_size: usize, num: usize) -> Vec<(Vec<F2>, F61p)> {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = TestPeer::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            let global_edabits = peer
                .generate_global_edabits(&mut channel, &mut rng, bit_size, num)
                .unwrap();
            peer.open_global_edabits(&mut channel, &global_edabits)
                .unwrap()
        });

        let mut rng = AesRng::from_seed(Default::default());
        let reader = BufReader::new(right.try_clone().unwrap());
        let writer = BufWriter::new(right);
        let mut channel = Channel::new(reader, writer);
        let mut peer = TestPeer::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        let global_edabits = peer
            .generate_global_edabits(&mut channel, &mut rng, bit_size, num)
            .unwrap();
        let opened = peer
            .open_global_edabits(&mut channel, &global_edabits)
            .unwrap();
        let opened_first = handle.join().unwrap();
        assert_eq!(opened, opened_first);
        opened
    }

    #[test]
    fn test_mpc_chedda_global_edabits_roundtrip() {
        let opened = run_opened_global_edabits(8, 6000);
        assert_eq!(opened.len(), 6000);
        for (bits, value) in opened {
            assert_eq!(value, convert_bits_to_field::<F61p>(&bits));
        }
    }

    #[test]
    fn test_mpc_chedda_matches_private_to_global_combine_semantics() {
        let (left, right) = UnixStream::pair().unwrap();
        let handle = std::thread::spawn(move || {
            let mut rng = AesRng::from_seed(Default::default());
            let reader = BufReader::new(left.try_clone().unwrap());
            let writer = BufWriter::new(left);
            let mut channel = Channel::new(reader, writer);
            let mut peer = TestPeer::init(
                &mut channel,
                &mut rng,
                PeerRole::First,
                LPN_SETUP_SMALL,
                LPN_EXTEND_SMALL,
            )
            .unwrap();
            let (clear_bits, clear_values) = fixed_clear_edabits(0, 8, 16);
            let private_edabits = peer
                .share_private_clear_edabits_owner_zero(
                    &mut channel,
                    &mut rng,
                    &clear_bits,
                    &clear_values,
                )
                .unwrap();
            let peer_private_edabits = peer
                .receive_private_edabit_contributions_owner_zero(&mut channel, &mut rng, 8, 16)
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
        let mut peer = TestPeer::init(
            &mut channel,
            &mut rng,
            PeerRole::Second,
            LPN_SETUP_SMALL,
            LPN_EXTEND_SMALL,
        )
        .unwrap();
        let (clear_bits, clear_values) = fixed_clear_edabits(1, 8, 16);
        let peer_private_edabits = peer
            .receive_private_edabit_contributions_owner_zero(&mut channel, &mut rng, 8, 16)
            .unwrap();
        let private_edabits = peer
            .share_private_clear_edabits_owner_zero(
                &mut channel,
                &mut rng,
                &clear_bits,
                &clear_values,
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
        let opened_first = handle.join().unwrap();
        assert_eq!(opened, opened_first);

        let (_left_bits, left_values) = fixed_clear_edabits(0, 8, 16);
        for (i, (bits, value)) in opened.into_iter().enumerate() {
            let lhs = u128::from(left_values[i]);
            let rhs = u128::from(clear_values[i]);
            let expected = (lhs + rhs) & ((1u128 << 8) - 1);
            let expected_bits: Vec<_> = (0..8)
                .map(|bit| {
                    if ((expected >> bit) & 1) == 1 {
                        F2::ONE
                    } else {
                        F2::ZERO
                    }
                })
                .collect();
            let expected_value = F61p::try_from(expected).unwrap();
            assert_eq!(bits, expected_bits);
            assert_eq!(value, expected_value);
        }
    }
}
