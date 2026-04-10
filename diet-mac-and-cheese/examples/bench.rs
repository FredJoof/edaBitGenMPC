use clap::{error::ErrorKind, Args, CommandFactory, Parser, Subcommand};
use diet_mac_and_cheese::{
    benchmark_tools::{setup_network, BenchmarkMetaData, FieldParameter, NetworkOptions, Party},
    cheddaconv::{
        CheddaConvProverV1TSPA, CheddaConvProverV1Xor4Maj7, CheddaConvProverV2TSPA,
        CheddaConvProverV2Xor4Maj7, CheddaConvVerifierV1TSPA, CheddaConvVerifierV1Xor4Maj7,
        CheddaConvVerifierV2TSPA, CheddaConvVerifierV2Xor4Maj7,
    },
    conv::{ConvProverFromHomComsT, ConvProverT, ConvVerifierFromHomComsT, ConvVerifierT},
    edabits::{
        random_edabits_prover, random_edabits_verifier, ProverConv as EdabitsConvProver, RcRefCell,
        VerifierConv as EdabitsConvVerifier,
    },
    homcom::{FComProver, FComStats, FComVerifier, MacProver},
    trunc::{
        random_fpm_triples_prover, random_fpm_triples_verifier, FPMProverFromHomComsT,
        FPMVerifierFromHomComsT,
    },
};
use generic_array::typenum::Unsigned;
use itertools::izip;
use ocelot::svole::wykw::choose_lpn_parameters;
use rand::SeedableRng;
use scuttlebutt::{
    channel::{track_unix_channel_pair, TrackChannel},
    field::{Degree, F40b, F61p, FiniteField},
    AbstractChannel, AesRng,
};
use serde::Serialize;
use serde_json;
use std::{
    string::ToString,
    sync::{Arc, Barrier},
    thread,
    time::{Duration, Instant},
};

#[derive(Debug, clap::Parser)]
#[clap(
    name = "Benchmarks",
    author = "Lennart Braun",
    version = "0.1",
    disable_help_flag = true
)]
struct Cli {
    /// Select a benchmark to run
    #[command(subcommand)]
    command: BenchmarkCommand,
}

/// The supported conversion protocols
#[derive(Clone, Copy, Debug, PartialEq, clap::ValueEnum, Serialize)]
enum ConversionProtocol {
    /// A naive version
    Naive,
    /// The protocol from BBMRS21 (CCS'21)
    #[clap(name = "edabits")]
    Edabits,
    /// The new protocol from ABBS25 (EC'25) (with TSPA predicate and version 1 seed setup)
    #[clap(name = "cheddabits-v1-tspa")]
    CheddabitsV1TSPA,
    /// The new protocol from ABBS25 (EC'25) (with TSPA predicate and version 2 seed setup)
    #[clap(name = "cheddabits-v2-tspa")]
    CheddabitsV2TSPA,
    /// The new protocol from ABBS25 (EC'25) (with Xor4Maj7 predicate and version 1 seed setup)
    #[clap(name = "cheddabits-v1-xor4maj7")]
    CheddabitsV1Xor4Maj7,
    /// The new protocol from ABBS25 (EC'25) (with Xor4Maj7 predicate and version 2 seed setup)
    #[clap(name = "cheddabits-v2-xor4maj7")]
    CheddabitsV2Xor4Maj7,
}

#[derive(Debug, Subcommand)]
enum BenchmarkCommand {
    #[clap(name = "mult")]
    Multiplication {
        #[clap(flatten)]
        common_opts: CommonOptions,
        #[clap(flatten)]
        mult_opts: MultiplicationOptions,
    },
    #[clap(name = "conv")]
    Conversion {
        #[clap(flatten)]
        common_opts: CommonOptions,
        #[clap(flatten)]
        conv_opts: ConversionOptions,
    },
    #[clap(name = "fpm")]
    FixedPointMult {
        #[clap(flatten)]
        common_opts: CommonOptions,
        #[clap(flatten)]
        fpm_opts: FixedPointMultOptions,
    },
    #[clap(name = "edabits-2pc")]
    SymmetricEdabits {
        #[clap(flatten)]
        common_opts: CommonOptions,
        #[clap(flatten)]
        sym_opts: SymmetricEdabitsOptions,
    },
}

impl BenchmarkCommand {
    pub fn check(&self) {
        fn check_num_positive(num: usize) {
            if num == 0 {
                Cli::command()
                    .error(
                        ErrorKind::InvalidValue,
                        "Need to check a positive number of things",
                    )
                    .exit();
            }
        }

        fn check_edabits_num_conversions(num: usize) {
            if num < 1024 {
                Cli::command()
                    .error(
                        ErrorKind::InvalidValue,
                        "Need to check at least 1024 conversions to use the Edabits protocol",
                    )
                    .exit();
            }
        }

        fn check_edabits_num_fpm(num: usize) {
            if num < 1024 {
                Cli::command()
                    .error(
                        ErrorKind::InvalidValue,
                        "Need to check at least 1024 fixed-point multiplications to use the Edabits protocol",
                    )
                    .exit();
            }
        }

        fn check_no_binary_field(field: FieldParameter) {
            if field == FieldParameter::F40b {
                Cli::command()
                    .error(
                        ErrorKind::InvalidValue,
                        "Binary fields such as {field} are not supported here",
                    )
                    .exit();
            }
        }

        fn check_bitsize(field: FieldParameter, bit_size: usize) {
            let ok = match field {
                FieldParameter::F61p => bit_size < 61,
                _ => false,
            };
            if !ok {
                Cli::command()
                    .error(
                        ErrorKind::InvalidValue,
                        format!("Bit-size of {bit_size} is not compatible with field {field}"),
                    )
                    .exit();
            }
        }

        match self {
            &BenchmarkCommand::Multiplication {
                mult_opts: MultiplicationOptions { num, .. },
                ..
            } => check_num_positive(num),
            &BenchmarkCommand::Conversion {
                conv_opts:
                    ConversionOptions {
                        protocol,
                        num,
                        field,
                        bit_size,
                    },
                ..
            } => {
                check_num_positive(num);
                check_no_binary_field(field);
                check_bitsize(field, bit_size);
                if protocol == ConversionProtocol::Edabits {
                    check_edabits_num_conversions(num);
                }
            }
            &BenchmarkCommand::FixedPointMult {
                fpm_opts:
                    FixedPointMultOptions {
                        protocol,
                        num,
                        field,
                        integer_size,
                        fraction_size,
                    },
                ..
            } => {
                check_num_positive(num);
                check_no_binary_field(field);
                check_bitsize(field, integer_size + 2 * fraction_size);
                if protocol == ConversionProtocol::Edabits {
                    check_edabits_num_fpm(num);
                }
            }
            BenchmarkCommand::SymmetricEdabits {
                common_opts,
                sym_opts,
            } => {
                check_num_positive(sym_opts.num);
                check_no_binary_field(sym_opts.field);
                check_bitsize(sym_opts.field, sym_opts.bit_size);
                if !matches!(common_opts.party, Party::Both) {
                    Cli::command()
                        .error(
                            ErrorKind::InvalidValue,
                            "The symmetric 2PC edabits benchmark requires --party both",
                        )
                        .exit();
                }
                check_edabits_num_conversions(sym_opts.num);
            }
        };
    }

    pub fn get_common_options(&self) -> &CommonOptions {
        match self {
            BenchmarkCommand::Multiplication { common_opts, .. } => common_opts,
            BenchmarkCommand::Conversion { common_opts, .. } => common_opts,
            BenchmarkCommand::FixedPointMult { common_opts, .. } => common_opts,
            BenchmarkCommand::SymmetricEdabits { common_opts, .. } => common_opts,
        }
    }
}

/// Common options for all kinds of benchmarks
#[derive(Debug, Args)]
struct CommonOptions {
    /// Which party should be run
    #[clap(short = 'P', long, value_enum)]
    party: Party,

    /// Network options
    // #[clap(flatten, help_heading = "Network options")]
    #[clap(flatten)]
    network_options: NetworkOptions,

    /// Number of repetitions
    #[clap(short, long, default_value_t = 1)]
    repetitions: usize,

    /// Output recorded data in JSON
    #[clap(short, long)]
    json: bool,

    /// Output additional information
    #[clap(short, long)]
    verbose: bool,
}

/// Options for multiplication benchmarks
#[derive(Debug, Args)]
struct MultiplicationOptions {
    /// Which field to use
    #[clap(short = 'f', long, value_enum, default_value_t = FieldParameter::F61p)]
    field: FieldParameter,

    /// Number of multiplications to verify
    #[clap(short, long)]
    num: usize,
}

/// Options for conversion benchmarks
#[derive(Debug, Args)]
struct ConversionOptions {
    /// Which conversion protocol to use
    #[clap(long, value_enum)]
    protocol: ConversionProtocol,

    /// Which field to use for the arithmetic domain
    #[clap(short = 'f', long, value_enum, default_value_t = FieldParameter::F61p)]
    field: FieldParameter,

    /// Number of conversions to verify
    #[clap(short, long)]
    num: usize,

    /// Bit-size of elements to convert
    #[clap(short, long)]
    bit_size: usize,
}

/// Options for fixed-point multiplication benchmarks
#[derive(Debug, Args)]
struct FixedPointMultOptions {
    /// Which conversion protocol to use
    #[clap(long, value_enum)]
    protocol: ConversionProtocol,

    /// Which field to use for the arithmetic domain
    #[clap(short = 'f', long, value_enum, default_value_t = FieldParameter::F61p)]
    field: FieldParameter,

    /// Number of conversions to verify
    #[clap(short, long)]
    num: usize,

    /// Bit-size of the integer part of a fixed-point number
    #[clap(short = 'b', long)]
    integer_size: usize,

    /// Bit-size of the fraction part of a fixed-point number
    #[clap(short = 's', long)]
    fraction_size: usize,
}

/// Options for the symmetric 2PC edabits benchmark
#[derive(Debug, Args)]
struct SymmetricEdabitsOptions {
    /// Which field to use for the arithmetic domain
    #[clap(short = 'f', long, value_enum, default_value_t = FieldParameter::F61p)]
    field: FieldParameter,

    /// Number of global edabits to generate
    #[clap(short, long)]
    num: usize,

    /// Bit-size of the generated edabits
    #[clap(short, long)]
    bit_size: usize,
}

#[derive(Clone, Debug, Serialize)]
enum ProtocolStats {
    Multiplication(MultiplicationStats),
    Conversion(ConversionStats),
    FixedPointMult(FixedPointMultStats),
    SymmetricEdabits(SymmetricEdabitsStats),
}

#[derive(Clone, Debug, Default, Serialize)]
struct TimeStats {
    init_time: Duration,
    voles_time: Duration,
    commit_time: Duration,
    check_time: Duration,
}

#[derive(Clone, Debug, Default, PartialEq, Serialize)]
struct CommStats {
    init_kb_sent: f64,
    init_kb_received: f64,
    voles_kb_sent: f64,
    voles_kb_received: f64,
    voles_f2_stats: FComStats,
    voles_fp_stats: FComStats,
    commit_kb_sent: f64,
    commit_kb_received: f64,
    commit_f2_stats: FComStats,
    commit_fp_stats: FComStats,
    check_kb_sent: f64,
    check_kb_received: f64,
    check_f2_stats: FComStats,
    check_fp_stats: FComStats,
}

#[derive(Clone, Debug, Default, Serialize)]
struct MultiplicationStats {
    num: usize,
    time_stats: Vec<TimeStats>,
    comm_stats: CommStats,
}

#[derive(Clone, Debug, Serialize)]
struct ConversionStats {
    protocol: ConversionProtocol,
    num: usize,
    bit_size: usize,
    time_stats: Vec<TimeStats>,
    comm_stats: CommStats,
}

#[derive(Clone, Debug, Serialize)]
struct FixedPointMultStats {
    protocol: ConversionProtocol,
    num: usize,
    integer_size: usize,
    fraction_size: usize,
    time_stats: Vec<TimeStats>,
    comm_stats: CommStats,
}

#[derive(Clone, Copy, Debug, PartialEq, Serialize)]
enum SymmetricEdabitsAggregation {
    AveragePerPeer,
}

#[derive(Clone, Debug, Serialize)]
struct SymmetricEdabitsStats {
    num: usize,
    bit_size: usize,
    peer_count: usize,
    aggregation: SymmetricEdabitsAggregation,
    time_stats: Vec<TimeStats>,
    comm_stats: CommStats,
}

#[derive(Clone, Debug, Serialize)]
struct BenchmarkResult {
    pub repetitions: usize,
    pub party: String,
    pub network_options: NetworkOptions,
    //     pub lpn_parameters: LpnParameters,
    pub meta_data: BenchmarkMetaData,
    pub protocol_stats: Vec<ProtocolStats>,
}

impl BenchmarkResult {
    pub fn aggregate(&mut self) {
        assert!(!self.protocol_stats.is_empty());
        let mut result = self.protocol_stats[0].clone();
        match &mut result {
            ProtocolStats::Multiplication(MultiplicationStats {
                num,
                time_stats,
                comm_stats,
            }) => {
                for prot_stats in self.protocol_stats.drain(..).skip(1) {
                    if let ProtocolStats::Multiplication(mut mult_stats) = prot_stats {
                        assert_eq!(mult_stats.num, *num);
                        assert_eq!(mult_stats.comm_stats, *comm_stats);
                        assert_eq!(mult_stats.time_stats.len(), 1);
                        time_stats.push(mult_stats.time_stats.pop().unwrap());
                    } else {
                        assert!(false, "mixed ProtocolStats");
                    }
                }
            }
            ProtocolStats::Conversion(ConversionStats {
                protocol,
                num,
                bit_size,
                time_stats,
                comm_stats,
            }) => {
                for prot_stats in self.protocol_stats.drain(..).skip(1) {
                    if let ProtocolStats::Conversion(mut conv_stats) = prot_stats {
                        assert_eq!(conv_stats.protocol, *protocol);
                        assert_eq!(conv_stats.num, *num);
                        assert_eq!(conv_stats.bit_size, *bit_size);
                        assert_eq!(conv_stats.comm_stats, *comm_stats);
                        assert_eq!(conv_stats.time_stats.len(), 1);
                        time_stats.push(conv_stats.time_stats.pop().unwrap());
                    } else {
                        assert!(false, "mixed ProtocolStats");
                    }
                }
            }
            ProtocolStats::FixedPointMult(FixedPointMultStats {
                protocol,
                num,
                integer_size,
                fraction_size,
                time_stats,
                comm_stats,
            }) => {
                for prot_stats in self.protocol_stats.drain(..).skip(1) {
                    if let ProtocolStats::FixedPointMult(mut fpm_stats) = prot_stats {
                        assert_eq!(fpm_stats.protocol, *protocol);
                        assert_eq!(fpm_stats.num, *num);
                        assert_eq!(fpm_stats.integer_size, *integer_size);
                        assert_eq!(fpm_stats.fraction_size, *fraction_size);
                        assert_eq!(fpm_stats.comm_stats, *comm_stats);
                        assert_eq!(fpm_stats.time_stats.len(), 1);
                        time_stats.push(fpm_stats.time_stats.pop().unwrap());
                    } else {
                        assert!(false, "mixed ProtocolStats");
                    }
                }
            }
            ProtocolStats::SymmetricEdabits(SymmetricEdabitsStats {
                num,
                bit_size,
                peer_count,
                aggregation,
                time_stats,
                comm_stats,
            }) => {
                for prot_stats in self.protocol_stats.drain(..).skip(1) {
                    if let ProtocolStats::SymmetricEdabits(mut sym_stats) = prot_stats {
                        assert_eq!(sym_stats.num, *num);
                        assert_eq!(sym_stats.bit_size, *bit_size);
                        assert_eq!(sym_stats.peer_count, *peer_count);
                        assert_eq!(sym_stats.aggregation, *aggregation);
                        assert_eq!(sym_stats.comm_stats, *comm_stats);
                        assert_eq!(sym_stats.time_stats.len(), 1);
                        time_stats.push(sym_stats.time_stats.pop().unwrap());
                    } else {
                        assert!(false, "mixed ProtocolStats");
                    }
                }
            }
        };
        self.protocol_stats = vec![result];
    }
}

impl BenchmarkResult {
    pub fn new(cmd: &BenchmarkCommand) -> Self {
        Self {
            repetitions: cmd.get_common_options().repetitions,
            party: cmd.get_common_options().party.to_string(),
            // field: options.field.to_string(),
            network_options: cmd.get_common_options().network_options.clone(),
            // lpn_parameters: options.lpn_parameters,
            meta_data: BenchmarkMetaData::collect(),
            protocol_stats: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Default)]
struct SymmetricPeerBenchmarkStats {
    time_stats: TimeStats,
    comm_stats: CommStats,
}

fn sum_fcom_stats(lhs: FComStats, rhs: FComStats) -> FComStats {
    FComStats {
        num_voles_used: lhs.num_voles_used + rhs.num_voles_used,
        num_vole_extensions_performed: lhs.num_vole_extensions_performed
            + rhs.num_vole_extensions_performed,
    }
}

fn average_fcom_stats(lhs: FComStats, rhs: FComStats) -> FComStats {
    assert_eq!(
        lhs, rhs,
        "symmetric peers should consume identical VOLE stats"
    );
    lhs
}

fn sum_time_stats(lhs: &TimeStats, rhs: &TimeStats) -> TimeStats {
    TimeStats {
        init_time: lhs.init_time + rhs.init_time,
        voles_time: lhs.voles_time + rhs.voles_time,
        commit_time: lhs.commit_time + rhs.commit_time,
        check_time: lhs.check_time + rhs.check_time,
    }
}

fn average_time_stats(lhs: &TimeStats, rhs: &TimeStats) -> TimeStats {
    TimeStats {
        init_time: (lhs.init_time + rhs.init_time) / 2,
        voles_time: (lhs.voles_time + rhs.voles_time) / 2,
        commit_time: (lhs.commit_time + rhs.commit_time) / 2,
        check_time: (lhs.check_time + rhs.check_time) / 2,
    }
}

fn sum_comm_stats(lhs: &CommStats, rhs: &CommStats) -> CommStats {
    CommStats {
        init_kb_sent: lhs.init_kb_sent + rhs.init_kb_sent,
        init_kb_received: lhs.init_kb_received + rhs.init_kb_received,
        voles_kb_sent: lhs.voles_kb_sent + rhs.voles_kb_sent,
        voles_kb_received: lhs.voles_kb_received + rhs.voles_kb_received,
        voles_f2_stats: sum_fcom_stats(lhs.voles_f2_stats, rhs.voles_f2_stats),
        voles_fp_stats: sum_fcom_stats(lhs.voles_fp_stats, rhs.voles_fp_stats),
        commit_kb_sent: lhs.commit_kb_sent + rhs.commit_kb_sent,
        commit_kb_received: lhs.commit_kb_received + rhs.commit_kb_received,
        commit_f2_stats: sum_fcom_stats(lhs.commit_f2_stats, rhs.commit_f2_stats),
        commit_fp_stats: sum_fcom_stats(lhs.commit_fp_stats, rhs.commit_fp_stats),
        check_kb_sent: lhs.check_kb_sent + rhs.check_kb_sent,
        check_kb_received: lhs.check_kb_received + rhs.check_kb_received,
        check_f2_stats: sum_fcom_stats(lhs.check_f2_stats, rhs.check_f2_stats),
        check_fp_stats: sum_fcom_stats(lhs.check_fp_stats, rhs.check_fp_stats),
    }
}

fn average_comm_stats(lhs: &CommStats, rhs: &CommStats) -> CommStats {
    CommStats {
        init_kb_sent: (lhs.init_kb_sent + rhs.init_kb_sent) / 2.0,
        init_kb_received: (lhs.init_kb_received + rhs.init_kb_received) / 2.0,
        voles_kb_sent: (lhs.voles_kb_sent + rhs.voles_kb_sent) / 2.0,
        voles_kb_received: (lhs.voles_kb_received + rhs.voles_kb_received) / 2.0,
        voles_f2_stats: average_fcom_stats(lhs.voles_f2_stats, rhs.voles_f2_stats),
        voles_fp_stats: average_fcom_stats(lhs.voles_fp_stats, rhs.voles_fp_stats),
        commit_kb_sent: (lhs.commit_kb_sent + rhs.commit_kb_sent) / 2.0,
        commit_kb_received: (lhs.commit_kb_received + rhs.commit_kb_received) / 2.0,
        commit_f2_stats: average_fcom_stats(lhs.commit_f2_stats, rhs.commit_f2_stats),
        commit_fp_stats: average_fcom_stats(lhs.commit_fp_stats, rhs.commit_fp_stats),
        check_kb_sent: (lhs.check_kb_sent + rhs.check_kb_sent) / 2.0,
        check_kb_received: (lhs.check_kb_received + rhs.check_kb_received) / 2.0,
        check_f2_stats: average_fcom_stats(lhs.check_f2_stats, rhs.check_f2_stats),
        check_fp_stats: average_fcom_stats(lhs.check_fp_stats, rhs.check_fp_stats),
    }
}

fn estimate_edabits_benchmark_voles_prover<FE: FiniteField<PrimeField = FE>>(
    num: usize,
    bit_size: usize,
) -> (usize, usize) {
    let (mut num_voles_2, mut num_voles_p) =
        EdabitsConvProver::<FE>::estimate_voles(num, bit_size as u32);
    num_voles_2 += num * bit_size;
    num_voles_p += num;
    (num_voles_2, num_voles_p)
}

fn estimate_edabits_benchmark_voles_verifier<FE: FiniteField<PrimeField = FE>>(
    num: usize,
    bit_size: usize,
) -> (usize, usize) {
    let (mut num_voles_2, mut num_voles_p) =
        EdabitsConvVerifier::<FE>::estimate_voles(num, bit_size as u32);
    num_voles_2 += num * bit_size;
    num_voles_p += num;
    (num_voles_2, num_voles_p)
}

trait SymmetricEdabitsSession<FE: FiniteField<PrimeField = FE>>: Sized {
    fn init<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        channel: &mut C,
        rng: &mut RNG,
        sym_opts: &SymmetricEdabitsOptions,
    ) -> Self;

    fn reserve_voles<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    );

    fn commit<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        sym_opts: &SymmetricEdabitsOptions,
    );

    fn check<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    );

    fn take_fcom_stats(&mut self) -> (FComStats, FComStats);

    fn expected_voles(&self) -> (usize, usize);
}

struct SymmetricEdabitsProverSession<FE: FiniteField> {
    f2_prover: RcRefCell<FComProver<F40b>>,
    fp_prover: RcRefCell<FComProver<FE>>,
    conv_prover: EdabitsConvProver<FE>,
    conversion_tuples: Option<Vec<diet_mac_and_cheese::conv::EdabitsProver<FE>>>,
    num_voles_2: usize,
    num_voles_p: usize,
}

impl<FE: FiniteField<PrimeField = FE>> SymmetricEdabitsSession<FE>
    for SymmetricEdabitsProverSession<FE>
{
    fn init<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        channel: &mut C,
        rng: &mut RNG,
        sym_opts: &SymmetricEdabitsOptions,
    ) -> Self {
        let (num_voles_2, num_voles_p) =
            estimate_edabits_benchmark_voles_prover::<FE>(sym_opts.num, sym_opts.bit_size);
        let (lpn_setup_params_2, lpn_extend_params_2) = choose_lpn_parameters::<F40b>(num_voles_p);
        let (lpn_setup_params_p, lpn_extend_params_p) = choose_lpn_parameters::<FE>(num_voles_p);

        let f2_prover = RcRefCell::new(
            FComProver::<F40b>::init(channel, rng, lpn_setup_params_2, lpn_extend_params_2)
                .expect("FComProver::init failed"),
        );
        let fp_prover = RcRefCell::new(
            FComProver::<FE>::init(channel, rng, lpn_setup_params_p, lpn_extend_params_p)
                .expect("FComProver::init failed"),
        );
        let conv_prover = EdabitsConvProver::<FE>::from_homcoms(&f2_prover, &fp_prover)
            .expect("from_homcoms failed");

        Self {
            f2_prover,
            fp_prover,
            conv_prover,
            conversion_tuples: None,
            num_voles_2,
            num_voles_p,
        }
    }

    fn reserve_voles<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) {
        self.f2_prover
            .get_refmut()
            .voles_reserve(channel, rng, self.num_voles_2)
            .expect("voles_reserve failed");
        self.fp_prover
            .get_refmut()
            .voles_reserve(channel, rng, self.num_voles_p)
            .expect("voles_reserve failed");
        channel.flush().expect("flush failed");
    }

    fn commit<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        sym_opts: &SymmetricEdabitsOptions,
    ) {
        self.conversion_tuples = Some(
            random_edabits_prover(
                &mut self.f2_prover.get_refmut(),
                &mut self.fp_prover.get_refmut(),
                channel,
                rng,
                sym_opts.bit_size,
                sym_opts.num,
            )
            .expect("random_edabits_prover failed"),
        );
        channel.flush().expect("flush failed");
    }

    fn check<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) {
        self.conv_prover
            .verify_conversions(
                channel,
                rng,
                self.conversion_tuples
                    .as_ref()
                    .expect("conversion tuples should be committed before checking"),
            )
            .expect("verify_conversions failed");
    }

    fn take_fcom_stats(&mut self) -> (FComStats, FComStats) {
        let fp_stats = self.fp_prover.get_refmut().get_stats();
        self.fp_prover.get_refmut().clear_stats();
        let f2_stats = self.f2_prover.get_refmut().get_stats();
        self.f2_prover.get_refmut().clear_stats();
        (f2_stats, fp_stats)
    }

    fn expected_voles(&self) -> (usize, usize) {
        (self.num_voles_2, self.num_voles_p)
    }
}

struct SymmetricEdabitsVerifierSession<FE: FiniteField> {
    f2_verifier: RcRefCell<FComVerifier<F40b>>,
    fp_verifier: RcRefCell<FComVerifier<FE>>,
    conv_verifier: EdabitsConvVerifier<FE>,
    conversion_tuples: Option<Vec<diet_mac_and_cheese::conv::EdabitsVerifier<FE>>>,
    num_voles_2: usize,
    num_voles_p: usize,
}

impl<FE: FiniteField<PrimeField = FE>> SymmetricEdabitsSession<FE>
    for SymmetricEdabitsVerifierSession<FE>
{
    fn init<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        channel: &mut C,
        rng: &mut RNG,
        sym_opts: &SymmetricEdabitsOptions,
    ) -> Self {
        let (num_voles_2, num_voles_p) =
            estimate_edabits_benchmark_voles_verifier::<FE>(sym_opts.num, sym_opts.bit_size);
        let (lpn_setup_params_2, lpn_extend_params_2) = choose_lpn_parameters::<F40b>(num_voles_p);
        let (lpn_setup_params_p, lpn_extend_params_p) = choose_lpn_parameters::<FE>(num_voles_p);

        let f2_verifier = RcRefCell::new(
            FComVerifier::<F40b>::init(channel, rng, lpn_setup_params_2, lpn_extend_params_2)
                .expect("FComVerifier::init failed"),
        );
        let fp_verifier = RcRefCell::new(
            FComVerifier::<FE>::init(channel, rng, lpn_setup_params_p, lpn_extend_params_p)
                .expect("FComVerifier::init failed"),
        );
        let conv_verifier = EdabitsConvVerifier::<FE>::from_homcoms(&f2_verifier, &fp_verifier)
            .expect("from_homcoms failed");

        Self {
            f2_verifier,
            fp_verifier,
            conv_verifier,
            conversion_tuples: None,
            num_voles_2,
            num_voles_p,
        }
    }

    fn reserve_voles<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) {
        self.f2_verifier
            .get_refmut()
            .voles_reserve(channel, rng, self.num_voles_2)
            .expect("voles_reserve failed");
        self.fp_verifier
            .get_refmut()
            .voles_reserve(channel, rng, self.num_voles_p)
            .expect("voles_reserve failed");
        channel.flush().expect("flush failed");
    }

    fn commit<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        sym_opts: &SymmetricEdabitsOptions,
    ) {
        self.conversion_tuples = Some(
            random_edabits_verifier(
                &mut self.f2_verifier.get_refmut(),
                &mut self.fp_verifier.get_refmut(),
                channel,
                rng,
                sym_opts.bit_size,
                sym_opts.num,
            )
            .expect("random_edabits_verifier failed"),
        );
        channel.flush().expect("flush failed");
    }

    fn check<C: AbstractChannel, RNG: rand::CryptoRng + rand::Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
    ) {
        self.conv_verifier
            .verify_conversions(
                channel,
                rng,
                self.conversion_tuples
                    .as_ref()
                    .expect("conversion tuples should be committed before checking"),
            )
            .expect("verify_conversions failed");
    }

    fn take_fcom_stats(&mut self) -> (FComStats, FComStats) {
        let fp_stats = self.fp_verifier.get_refmut().get_stats();
        self.fp_verifier.get_refmut().clear_stats();
        let f2_stats = self.f2_verifier.get_refmut().get_stats();
        self.f2_verifier.get_refmut().clear_stats();
        (f2_stats, fp_stats)
    }

    fn expected_voles(&self) -> (usize, usize) {
        (self.num_voles_2, self.num_voles_p)
    }
}

fn symmetric_phase_comm_stats<C1: AbstractChannel, C2: AbstractChannel>(
    primary_channel: &TrackChannel<C1>,
    secondary_channel: &TrackChannel<C2>,
) -> (f64, f64) {
    (
        primary_channel.kilobytes_written() + secondary_channel.kilobytes_written(),
        primary_channel.kilobytes_read() + secondary_channel.kilobytes_read(),
    )
}

fn finalize_symmetric_phase<C1: AbstractChannel, C2: AbstractChannel>(
    primary_channel: &mut TrackChannel<C1>,
    secondary_channel: &mut TrackChannel<C2>,
    barrier: &Barrier,
) {
    primary_channel.clear();
    secondary_channel.clear();
    barrier.wait();
}

fn run_symmetric_edabits_peer<
    FE: FiniteField<PrimeField = FE>,
    PrimarySession: SymmetricEdabitsSession<FE>,
    SecondarySession: SymmetricEdabitsSession<FE>,
    C1: AbstractChannel,
    C2: AbstractChannel,
>(
    primary_channel: &mut TrackChannel<C1>,
    secondary_channel: &mut TrackChannel<C2>,
    sym_opts: &SymmetricEdabitsOptions,
    barrier: &Barrier,
) -> SymmetricPeerBenchmarkStats {
    let mut stats = SymmetricPeerBenchmarkStats::default();
    let mut rng = AesRng::from_seed(Default::default());
    primary_channel.clear();
    secondary_channel.clear();

    let t_start = Instant::now();
    let mut primary = PrimarySession::init(primary_channel, &mut rng, sym_opts);
    let mut secondary = SecondarySession::init(secondary_channel, &mut rng, sym_opts);
    stats.time_stats.init_time = t_start.elapsed();
    let (init_kb_sent, init_kb_received) =
        symmetric_phase_comm_stats(primary_channel, secondary_channel);
    stats.comm_stats.init_kb_sent = init_kb_sent;
    stats.comm_stats.init_kb_received = init_kb_received;
    finalize_symmetric_phase(primary_channel, secondary_channel, barrier);

    let expected_voles_primary = primary.expected_voles();
    let expected_voles_secondary = secondary.expected_voles();

    let t_start = Instant::now();
    primary.reserve_voles(primary_channel, &mut rng);
    secondary.reserve_voles(secondary_channel, &mut rng);
    stats.time_stats.voles_time = t_start.elapsed();
    let (voles_kb_sent, voles_kb_received) =
        symmetric_phase_comm_stats(primary_channel, secondary_channel);
    stats.comm_stats.voles_kb_sent = voles_kb_sent;
    stats.comm_stats.voles_kb_received = voles_kb_received;
    let (primary_f2_stats, primary_fp_stats) = primary.take_fcom_stats();
    let (secondary_f2_stats, secondary_fp_stats) = secondary.take_fcom_stats();
    stats.comm_stats.voles_f2_stats = sum_fcom_stats(primary_f2_stats, secondary_f2_stats);
    stats.comm_stats.voles_fp_stats = sum_fcom_stats(primary_fp_stats, secondary_fp_stats);
    finalize_symmetric_phase(primary_channel, secondary_channel, barrier);

    let t_start = Instant::now();
    primary.commit(primary_channel, &mut rng, sym_opts);
    secondary.commit(secondary_channel, &mut rng, sym_opts);
    stats.time_stats.commit_time = t_start.elapsed();
    let (commit_kb_sent, commit_kb_received) =
        symmetric_phase_comm_stats(primary_channel, secondary_channel);
    stats.comm_stats.commit_kb_sent = commit_kb_sent;
    stats.comm_stats.commit_kb_received = commit_kb_received;
    let (primary_f2_stats, primary_fp_stats) = primary.take_fcom_stats();
    let (secondary_f2_stats, secondary_fp_stats) = secondary.take_fcom_stats();
    stats.comm_stats.commit_f2_stats = sum_fcom_stats(primary_f2_stats, secondary_f2_stats);
    stats.comm_stats.commit_fp_stats = sum_fcom_stats(primary_fp_stats, secondary_fp_stats);
    assert_eq!(
        stats
            .comm_stats
            .commit_fp_stats
            .num_vole_extensions_performed,
        0
    );
    assert_eq!(
        stats
            .comm_stats
            .commit_f2_stats
            .num_vole_extensions_performed,
        0
    );
    finalize_symmetric_phase(primary_channel, secondary_channel, barrier);

    let t_start = Instant::now();
    primary.check(primary_channel, &mut rng);
    secondary.check(secondary_channel, &mut rng);
    stats.time_stats.check_time = t_start.elapsed();
    let (check_kb_sent, check_kb_received) =
        symmetric_phase_comm_stats(primary_channel, secondary_channel);
    stats.comm_stats.check_kb_sent = check_kb_sent;
    stats.comm_stats.check_kb_received = check_kb_received;
    let (primary_f2_stats, primary_fp_stats) = primary.take_fcom_stats();
    let (secondary_f2_stats, secondary_fp_stats) = secondary.take_fcom_stats();
    stats.comm_stats.check_f2_stats = sum_fcom_stats(primary_f2_stats, secondary_f2_stats);
    stats.comm_stats.check_fp_stats = sum_fcom_stats(primary_fp_stats, secondary_fp_stats);
    assert_eq!(
        stats
            .comm_stats
            .check_fp_stats
            .num_vole_extensions_performed,
        0
    );
    assert_eq!(
        stats
            .comm_stats
            .check_f2_stats
            .num_vole_extensions_performed,
        0
    );
    finalize_symmetric_phase(primary_channel, secondary_channel, barrier);

    assert_eq!(
        stats.comm_stats.commit_fp_stats.num_voles_used
            + stats.comm_stats.check_fp_stats.num_voles_used,
        expected_voles_primary.1 + expected_voles_secondary.1,
    );
    assert_eq!(
        stats.comm_stats.commit_f2_stats.num_voles_used
            + stats.comm_stats.check_f2_stats.num_voles_used,
        expected_voles_primary.0 + expected_voles_secondary.0,
    );

    stats
}

fn aggregate_symmetric_edabits_peers(
    sym_opts: &SymmetricEdabitsOptions,
    lhs: &SymmetricPeerBenchmarkStats,
    rhs: &SymmetricPeerBenchmarkStats,
) -> SymmetricEdabitsStats {
    let combined_lhs = SymmetricPeerBenchmarkStats {
        time_stats: sum_time_stats(&lhs.time_stats, &TimeStats::default()),
        comm_stats: sum_comm_stats(&lhs.comm_stats, &CommStats::default()),
    };
    let combined_rhs = SymmetricPeerBenchmarkStats {
        time_stats: sum_time_stats(&rhs.time_stats, &TimeStats::default()),
        comm_stats: sum_comm_stats(&rhs.comm_stats, &CommStats::default()),
    };

    SymmetricEdabitsStats {
        num: sym_opts.num,
        bit_size: sym_opts.bit_size,
        peer_count: 2,
        aggregation: SymmetricEdabitsAggregation::AveragePerPeer,
        time_stats: vec![average_time_stats(
            &combined_lhs.time_stats,
            &combined_rhs.time_stats,
        )],
        comm_stats: average_comm_stats(&combined_lhs.comm_stats, &combined_rhs.comm_stats),
    }
}

fn run_symmetric_edabits_benchmark<FE: FiniteField<PrimeField = FE>>(
    common_opts: &CommonOptions,
    sym_opts: &SymmetricEdabitsOptions,
) -> Vec<ProtocolStats> {
    let (mut primary_peer0, mut primary_peer1) = track_unix_channel_pair();
    let (mut secondary_peer0, mut secondary_peer1) = track_unix_channel_pair();
    let barrier = Arc::new(Barrier::new(2));
    let repetitions = common_opts.repetitions;
    let peer0_barrier = barrier.clone();
    let peer0_opts = SymmetricEdabitsOptions {
        field: sym_opts.field,
        num: sym_opts.num,
        bit_size: sym_opts.bit_size,
    };
    let peer0 = thread::spawn(move || {
        let mut stats = Vec::with_capacity(repetitions);
        for _ in 0..repetitions {
            stats.push(run_symmetric_edabits_peer::<
                FE,
                SymmetricEdabitsProverSession<FE>,
                SymmetricEdabitsVerifierSession<FE>,
                _,
                _,
            >(
                &mut primary_peer0,
                &mut secondary_peer0,
                &peer0_opts,
                peer0_barrier.as_ref(),
            ));
        }
        stats
    });

    let peer1_barrier = barrier.clone();
    let peer1_opts = SymmetricEdabitsOptions {
        field: sym_opts.field,
        num: sym_opts.num,
        bit_size: sym_opts.bit_size,
    };
    let peer1 = thread::spawn(move || {
        let mut stats = Vec::with_capacity(repetitions);
        for _ in 0..repetitions {
            stats.push(run_symmetric_edabits_peer::<
                FE,
                SymmetricEdabitsVerifierSession<FE>,
                SymmetricEdabitsProverSession<FE>,
                _,
                _,
            >(
                &mut primary_peer1,
                &mut secondary_peer1,
                &peer1_opts,
                peer1_barrier.as_ref(),
            ));
        }
        stats
    });

    let peer0_stats = peer0.join().unwrap();
    let peer1_stats = peer1.join().unwrap();
    peer0_stats
        .iter()
        .zip(peer1_stats.iter())
        .map(|(lhs, rhs)| {
            ProtocolStats::SymmetricEdabits(aggregate_symmetric_edabits_peers(sym_opts, lhs, rhs))
        })
        .collect()
}

fn run_mult_prover<FE: FiniteField, C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    _: &CommonOptions,
    mult_opts: &MultiplicationOptions,
) -> MultiplicationStats {
    let mut stats = MultiplicationStats {
        num: mult_opts.num,
        time_stats: vec![Default::default()],
        comm_stats: Default::default(),
    };

    let mut rng = AesRng::from_seed(Default::default());
    channel.clear();

    // estimate voles required and choose LPN parameters
    let num_voles = 3 * mult_opts.num + Degree::<FE>::USIZE;
    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<FE>(num_voles);

    // Init
    let t_start = Instant::now();
    let mut fp_prover =
        FComProver::<FE>::init(channel, &mut rng, lpn_setup_params, lpn_extend_params)
            .expect("FComProver::init failed");
    stats.time_stats[0].init_time = t_start.elapsed();
    stats.comm_stats.init_kb_received = channel.kilobytes_read();
    stats.comm_stats.init_kb_sent = channel.kilobytes_written();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // Preprocess VOLEs
    let t_start = Instant::now();
    let num_voles = 3 * mult_opts.num + Degree::<FE>::USIZE;
    fp_prover
        .voles_reserve(channel, &mut rng, num_voles)
        .expect("voles_reserve failed");
    channel.flush().expect("flush failed");
    stats.time_stats[0].voles_time = t_start.elapsed();
    stats.comm_stats.voles_kb_received = channel.kilobytes_read();
    stats.comm_stats.voles_kb_sent = channel.kilobytes_written();
    stats.comm_stats.voles_fp_stats = fp_prover.get_stats();
    fp_prover.clear_stats();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // Commit
    let t_start = Instant::now();
    let triples: Vec<_> = {
        let mut as_ = Vec::with_capacity(mult_opts.num);
        let mut bs = Vec::with_capacity(mult_opts.num);
        let mut c_values = Vec::with_capacity(mult_opts.num);
        for _ in 0..mult_opts.num {
            let a = fp_prover.random(channel, &mut rng).expect("random failed");
            let b = fp_prover.random(channel, &mut rng).expect("random failed");
            let c_val = a.value() * b.value();
            as_.push(a);
            bs.push(b);
            c_values.push(c_val);
        }
        let c_macs = fp_prover
            .input(channel, &mut rng, &c_values)
            .expect("input failed");
        izip!(
            as_.into_iter(),
            bs.into_iter(),
            c_values.into_iter(),
            c_macs.into_iter()
        )
        .map(|(a, b, c_val, c_mac)| (a, b, MacProver::new(c_val, c_mac)))
        .collect()
    };
    channel.flush().expect("flush failed");
    stats.time_stats[0].commit_time = t_start.elapsed();
    stats.comm_stats.commit_kb_received = channel.kilobytes_read();
    stats.comm_stats.commit_kb_sent = channel.kilobytes_written();
    stats.comm_stats.commit_fp_stats = fp_prover.get_stats();
    assert_eq!(
        stats
            .comm_stats
            .commit_fp_stats
            .num_vole_extensions_performed,
        0
    );
    fp_prover.clear_stats();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // Check
    let t_start = Instant::now();
    fp_prover
        .quicksilver_check_multiply(channel, &mut rng, &triples)
        .expect("quicksilver_check_multiply failed");
    stats.time_stats[0].check_time = t_start.elapsed();
    stats.comm_stats.check_kb_received = channel.kilobytes_read();
    stats.comm_stats.check_kb_sent = channel.kilobytes_written();
    stats.comm_stats.check_fp_stats = fp_prover.get_stats();
    assert_eq!(
        stats
            .comm_stats
            .check_fp_stats
            .num_vole_extensions_performed,
        0
    );
    fp_prover.clear_stats();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    assert_eq!(
        stats.comm_stats.commit_fp_stats.num_voles_used
            + stats.comm_stats.check_fp_stats.num_voles_used,
        num_voles,
    );

    stats
}

fn run_mult_verifier<FE: FiniteField, C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    _: &CommonOptions,
    mult_opts: &MultiplicationOptions,
) -> MultiplicationStats {
    let mut stats = MultiplicationStats {
        num: mult_opts.num,
        time_stats: vec![Default::default()],
        comm_stats: Default::default(),
    };

    let mut rng = AesRng::from_seed(Default::default());
    channel.clear();

    // estimate voles required and choose LPN parameters
    let num_voles = 3 * mult_opts.num + Degree::<FE>::USIZE;
    let (lpn_setup_params, lpn_extend_params) = choose_lpn_parameters::<FE>(num_voles);

    // Init
    let t_start = Instant::now();
    let mut fp_verifier =
        FComVerifier::<FE>::init(channel, &mut rng, lpn_setup_params, lpn_extend_params)
            .expect("FComVerifier::init failed");
    stats.time_stats[0].init_time = t_start.elapsed();
    stats.comm_stats.init_kb_received = channel.kilobytes_read();
    stats.comm_stats.init_kb_sent = channel.kilobytes_written();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    // Preprocess VOLEs
    let t_start = Instant::now();
    let num_voles = 3 * mult_opts.num + Degree::<FE>::USIZE;
    fp_verifier
        .voles_reserve(channel, &mut rng, num_voles)
        .expect("voles_reserve failed");
    channel.flush().expect("flush failed");
    stats.time_stats[0].voles_time = t_start.elapsed();
    stats.comm_stats.voles_kb_received = channel.kilobytes_read();
    stats.comm_stats.voles_kb_sent = channel.kilobytes_written();
    stats.comm_stats.voles_fp_stats = fp_verifier.get_stats();
    fp_verifier.clear_stats();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    // Commit
    let t_start = Instant::now();
    let triples: Vec<_> = {
        let mut as_ = Vec::with_capacity(mult_opts.num);
        let mut bs = Vec::with_capacity(mult_opts.num);
        for _ in 0..mult_opts.num {
            let a = fp_verifier
                .random(channel, &mut rng)
                .expect("random failed");
            let b = fp_verifier
                .random(channel, &mut rng)
                .expect("random failed");
            as_.push(a);
            bs.push(b);
        }
        let cs = fp_verifier
            .input(channel, &mut rng, mult_opts.num)
            .expect("input failed");
        izip!(as_.into_iter(), bs.into_iter(), cs.into_iter()).collect()
    };
    channel.flush().expect("flush failed");
    stats.time_stats[0].commit_time = t_start.elapsed();
    stats.comm_stats.commit_kb_received = channel.kilobytes_read();
    stats.comm_stats.commit_kb_sent = channel.kilobytes_written();
    stats.comm_stats.commit_fp_stats = fp_verifier.get_stats();
    assert_eq!(
        stats
            .comm_stats
            .commit_fp_stats
            .num_vole_extensions_performed,
        0
    );
    fp_verifier.clear_stats();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    // Check
    let t_start = Instant::now();
    fp_verifier
        .quicksilver_check_multiply(channel, &mut rng, &triples)
        .expect("quicksilver_check_multiply failed");
    stats.time_stats[0].check_time = t_start.elapsed();
    stats.comm_stats.check_kb_received = channel.kilobytes_read();
    stats.comm_stats.check_kb_sent = channel.kilobytes_written();
    stats.comm_stats.check_fp_stats = fp_verifier.get_stats();
    assert_eq!(
        stats
            .comm_stats
            .check_fp_stats
            .num_vole_extensions_performed,
        0
    );
    fp_verifier.clear_stats();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    assert_eq!(
        stats.comm_stats.commit_fp_stats.num_voles_used
            + stats.comm_stats.check_fp_stats.num_voles_used,
        num_voles,
    );

    stats
}

fn run_conv_prover<FE: FiniteField, C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    common_opts: &CommonOptions,
    conv_opts: &ConversionOptions,
) -> ConversionStats {
    match conv_opts.protocol {
        ConversionProtocol::Edabits => run_conv_prover_impl::<F61p, EdabitsConvProver<F61p>, _>(
            channel,
            common_opts,
            conv_opts,
        ),
        ConversionProtocol::CheddabitsV1TSPA => run_conv_prover_impl::<
            F61p,
            CheddaConvProverV1TSPA<F61p>,
            _,
        >(channel, common_opts, conv_opts),
        ConversionProtocol::CheddabitsV2TSPA => run_conv_prover_impl::<
            F61p,
            CheddaConvProverV2TSPA<F61p>,
            _,
        >(channel, common_opts, conv_opts),
        ConversionProtocol::CheddabitsV1Xor4Maj7 => run_conv_prover_impl::<
            F61p,
            CheddaConvProverV1Xor4Maj7<F61p>,
            _,
        >(channel, common_opts, conv_opts),
        ConversionProtocol::CheddabitsV2Xor4Maj7 => run_conv_prover_impl::<
            F61p,
            CheddaConvProverV2Xor4Maj7<F61p>,
            _,
        >(channel, common_opts, conv_opts),
        _ => panic!("not implemented"),
    }
}

fn run_conv_prover_impl<FE: FiniteField, CP: ConvProverFromHomComsT<FE>, C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    _: &CommonOptions,
    conv_opts: &ConversionOptions,
) -> ConversionStats {
    let mut stats = ConversionStats {
        num: conv_opts.num,
        bit_size: conv_opts.bit_size,
        protocol: conv_opts.protocol,
        time_stats: vec![Default::default()],
        comm_stats: Default::default(),
    };

    let mut rng = AesRng::from_seed(Default::default());
    channel.clear();

    // estimate voles required and choose LPN parameters
    let (num_voles_2, num_voles_p) = {
        let (mut n2, mut np) = CP::estimate_voles(conv_opts.num, conv_opts.bit_size as u32);
        n2 += conv_opts.num * conv_opts.bit_size;
        np += conv_opts.num;
        (n2, np)
    };
    let (lpn_setup_params_2, lpn_extend_params_2) = choose_lpn_parameters::<F40b>(num_voles_p);
    let (lpn_setup_params_p, lpn_extend_params_p) = choose_lpn_parameters::<FE>(num_voles_p);

    // Init
    let t_start = Instant::now();
    let f2_prover = RcRefCell::new(
        FComProver::<F40b>::init(channel, &mut rng, lpn_setup_params_2, lpn_extend_params_2)
            .expect("FComProver::init failed"),
    );
    let fp_prover = RcRefCell::new(
        FComProver::<FE>::init(channel, &mut rng, lpn_setup_params_p, lpn_extend_params_p)
            .expect("FComProver::init failed"),
    );
    let mut conv_prover = CP::from_homcoms(&f2_prover, &fp_prover).expect("from_homcoms failed");
    stats.time_stats[0].init_time = t_start.elapsed();
    stats.comm_stats.init_kb_received = channel.kilobytes_read();
    stats.comm_stats.init_kb_sent = channel.kilobytes_written();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // Preprocess VOLEs
    let t_start = Instant::now();
    f2_prover
        .get_refmut()
        .voles_reserve(channel, &mut rng, num_voles_2)
        .expect("voles_reserve failed");
    fp_prover
        .get_refmut()
        .voles_reserve(channel, &mut rng, num_voles_p)
        .expect("voles_reserve failed");
    channel.flush().expect("flush failed");
    stats.time_stats[0].voles_time = t_start.elapsed();
    stats.comm_stats.voles_kb_received = channel.kilobytes_read();
    stats.comm_stats.voles_kb_sent = channel.kilobytes_written();
    stats.comm_stats.voles_fp_stats = fp_prover.get_refmut().get_stats();
    stats.comm_stats.voles_f2_stats = f2_prover.get_refmut().get_stats();
    fp_prover.get_refmut().clear_stats();
    f2_prover.get_refmut().clear_stats();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // Commit
    let t_start = Instant::now();
    let conversion_tuples = random_edabits_prover(
        &mut f2_prover.get_refmut(),
        &mut fp_prover.get_refmut(),
        channel,
        &mut rng,
        conv_opts.bit_size,
        conv_opts.num,
    )
    .expect("random_edabits_prover failed");
    channel.flush().expect("flush failed");
    stats.time_stats[0].commit_time = t_start.elapsed();
    stats.comm_stats.commit_kb_received = channel.kilobytes_read();
    stats.comm_stats.commit_kb_sent = channel.kilobytes_written();
    stats.comm_stats.commit_fp_stats = fp_prover.get_refmut().get_stats();
    stats.comm_stats.commit_f2_stats = f2_prover.get_refmut().get_stats();
    assert_eq!(
        stats
            .comm_stats
            .commit_fp_stats
            .num_vole_extensions_performed,
        0
    );
    assert_eq!(
        stats
            .comm_stats
            .commit_f2_stats
            .num_vole_extensions_performed,
        0
    );
    fp_prover.get_refmut().clear_stats();
    f2_prover.get_refmut().clear_stats();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // Check
    let t_start = Instant::now();
    conv_prover
        .verify_conversions(channel, &mut rng, &conversion_tuples)
        .expect("verify_conversions failed");
    stats.time_stats[0].check_time = t_start.elapsed();
    stats.comm_stats.check_kb_received = channel.kilobytes_read();
    stats.comm_stats.check_kb_sent = channel.kilobytes_written();
    stats.comm_stats.check_fp_stats = fp_prover.get_refmut().get_stats();
    stats.comm_stats.check_f2_stats = f2_prover.get_refmut().get_stats();
    assert_eq!(
        stats
            .comm_stats
            .check_fp_stats
            .num_vole_extensions_performed,
        0
    );
    assert_eq!(
        stats
            .comm_stats
            .check_f2_stats
            .num_vole_extensions_performed,
        0
    );
    fp_prover.get_refmut().clear_stats();
    f2_prover.get_refmut().clear_stats();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // eprintln!(
    //     "VOLES (p): {} + {} = {} =? {}",
    //     stats.comm_stats.commit_fp_stats.num_voles_used,
    //     stats.comm_stats.check_fp_stats.num_voles_used,
    //     stats.comm_stats.commit_fp_stats.num_voles_used
    //         + stats.comm_stats.check_fp_stats.num_voles_used,
    //     num_voles_p,
    // );
    // eprintln!(
    //     "VOLES (2): {} + {} = {} =? {}",
    //     stats.comm_stats.commit_f2_stats.num_voles_used,
    //     stats.comm_stats.check_f2_stats.num_voles_used,
    //     stats.comm_stats.commit_f2_stats.num_voles_used
    //         + stats.comm_stats.check_f2_stats.num_voles_used,
    //     num_voles_2,
    // );
    assert_eq!(
        stats.comm_stats.commit_fp_stats.num_voles_used
            + stats.comm_stats.check_fp_stats.num_voles_used,
        num_voles_p,
    );
    assert_eq!(
        stats.comm_stats.commit_f2_stats.num_voles_used
            + stats.comm_stats.check_f2_stats.num_voles_used,
        num_voles_2,
    );

    stats
}

fn run_conv_verifier<FE: FiniteField, C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    common_opts: &CommonOptions,
    conv_opts: &ConversionOptions,
) -> ConversionStats {
    match conv_opts.protocol {
        ConversionProtocol::Edabits => {
            run_conv_verifier_impl::<F61p, EdabitsConvVerifier<F61p>, _>(
                channel,
                common_opts,
                conv_opts,
            )
        }
        ConversionProtocol::CheddabitsV1TSPA => run_conv_verifier_impl::<
            F61p,
            CheddaConvVerifierV1TSPA<F61p>,
            _,
        >(channel, common_opts, conv_opts),
        ConversionProtocol::CheddabitsV2TSPA => run_conv_verifier_impl::<
            F61p,
            CheddaConvVerifierV2TSPA<F61p>,
            _,
        >(channel, common_opts, conv_opts),
        ConversionProtocol::CheddabitsV1Xor4Maj7 => run_conv_verifier_impl::<
            F61p,
            CheddaConvVerifierV1Xor4Maj7<F61p>,
            _,
        >(channel, common_opts, conv_opts),
        ConversionProtocol::CheddabitsV2Xor4Maj7 => run_conv_verifier_impl::<
            F61p,
            CheddaConvVerifierV2Xor4Maj7<F61p>,
            _,
        >(channel, common_opts, conv_opts),
        _ => panic!("not implemented"),
    }
}

fn run_conv_verifier_impl<FE: FiniteField, CV: ConvVerifierFromHomComsT<FE>, C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    _: &CommonOptions,
    conv_opts: &ConversionOptions,
) -> ConversionStats {
    let mut stats = ConversionStats {
        num: conv_opts.num,
        bit_size: conv_opts.bit_size,
        protocol: conv_opts.protocol,
        time_stats: vec![Default::default()],
        comm_stats: Default::default(),
    };

    let mut rng = AesRng::from_seed(Default::default());
    channel.clear();

    // estimate voles required and choose LPN parameters
    let (num_voles_2, num_voles_p) = {
        let (mut n2, mut np) = CV::estimate_voles(conv_opts.num, conv_opts.bit_size as u32);
        n2 += conv_opts.num * conv_opts.bit_size;
        np += conv_opts.num;
        (n2, np)
    };
    let (lpn_setup_params_2, lpn_extend_params_2) = choose_lpn_parameters::<F40b>(num_voles_p);
    let (lpn_setup_params_p, lpn_extend_params_p) = choose_lpn_parameters::<FE>(num_voles_p);

    // Init
    let t_start = Instant::now();
    let f2_verifier = RcRefCell::new(
        FComVerifier::<F40b>::init(channel, &mut rng, lpn_setup_params_2, lpn_extend_params_2)
            .expect("FComProver::init failed"),
    );
    let fp_verifier = RcRefCell::new(
        FComVerifier::<FE>::init(channel, &mut rng, lpn_setup_params_p, lpn_extend_params_p)
            .expect("FComProver::init failed"),
    );
    let mut conv_verifier =
        CV::from_homcoms(&f2_verifier, &fp_verifier).expect("from_homcoms failed");
    stats.time_stats[0].init_time = t_start.elapsed();
    stats.comm_stats.init_kb_received = channel.kilobytes_read();
    stats.comm_stats.init_kb_sent = channel.kilobytes_written();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    // Preprocess VOLEs
    let t_start = Instant::now();
    f2_verifier
        .get_refmut()
        .voles_reserve(channel, &mut rng, num_voles_2)
        .expect("voles_reserve failed");
    fp_verifier
        .get_refmut()
        .voles_reserve(channel, &mut rng, num_voles_p)
        .expect("voles_reserve failed");
    channel.flush().expect("flush failed");
    stats.time_stats[0].voles_time = t_start.elapsed();
    stats.comm_stats.voles_kb_received = channel.kilobytes_read();
    stats.comm_stats.voles_kb_sent = channel.kilobytes_written();
    stats.comm_stats.voles_fp_stats = fp_verifier.get_refmut().get_stats();
    stats.comm_stats.voles_f2_stats = f2_verifier.get_refmut().get_stats();
    fp_verifier.get_refmut().clear_stats();
    f2_verifier.get_refmut().clear_stats();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    // Commit
    let t_start = Instant::now();
    let conversion_tuples = random_edabits_verifier(
        &mut f2_verifier.get_refmut(),
        &mut fp_verifier.get_refmut(),
        channel,
        &mut rng,
        conv_opts.bit_size,
        conv_opts.num,
    )
    .expect("random_edabits_verifier failed");
    channel.flush().expect("flush failed");
    stats.time_stats[0].commit_time = t_start.elapsed();
    stats.comm_stats.commit_kb_received = channel.kilobytes_read();
    stats.comm_stats.commit_kb_sent = channel.kilobytes_written();
    stats.comm_stats.commit_fp_stats = fp_verifier.get_refmut().get_stats();
    stats.comm_stats.commit_f2_stats = f2_verifier.get_refmut().get_stats();
    assert_eq!(
        stats
            .comm_stats
            .commit_fp_stats
            .num_vole_extensions_performed,
        0
    );
    assert_eq!(
        stats
            .comm_stats
            .commit_f2_stats
            .num_vole_extensions_performed,
        0
    );
    fp_verifier.get_refmut().clear_stats();
    f2_verifier.get_refmut().clear_stats();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    // Check
    let t_start = Instant::now();
    conv_verifier
        .verify_conversions(channel, &mut rng, &conversion_tuples)
        .expect("verify_conversions failed");
    stats.time_stats[0].check_time = t_start.elapsed();
    stats.comm_stats.check_kb_received = channel.kilobytes_read();
    stats.comm_stats.check_kb_sent = channel.kilobytes_written();
    stats.comm_stats.check_fp_stats = fp_verifier.get_refmut().get_stats();
    stats.comm_stats.check_f2_stats = f2_verifier.get_refmut().get_stats();
    assert_eq!(
        stats
            .comm_stats
            .check_fp_stats
            .num_vole_extensions_performed,
        0
    );
    assert_eq!(
        stats
            .comm_stats
            .check_f2_stats
            .num_vole_extensions_performed,
        0
    );
    fp_verifier.get_refmut().clear_stats();
    f2_verifier.get_refmut().clear_stats();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    assert_eq!(
        stats.comm_stats.commit_fp_stats.num_voles_used
            + stats.comm_stats.check_fp_stats.num_voles_used,
        num_voles_p,
    );
    assert_eq!(
        stats.comm_stats.commit_f2_stats.num_voles_used
            + stats.comm_stats.check_f2_stats.num_voles_used,
        num_voles_2,
    );

    stats
}

fn run_fpm_prover<FE: FiniteField, C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    common_opts: &CommonOptions,
    fpm_opts: &FixedPointMultOptions,
) -> FixedPointMultStats {
    match fpm_opts.protocol {
        ConversionProtocol::Edabits => {
            run_fpm_prover_impl::<F61p, EdabitsConvProver<F61p>, _>(channel, common_opts, fpm_opts)
        }
        ConversionProtocol::CheddabitsV1TSPA => run_fpm_prover_impl::<
            F61p,
            CheddaConvProverV1TSPA<F61p>,
            _,
        >(channel, common_opts, fpm_opts),
        ConversionProtocol::CheddabitsV2TSPA => run_fpm_prover_impl::<
            F61p,
            CheddaConvProverV2TSPA<F61p>,
            _,
        >(channel, common_opts, fpm_opts),
        ConversionProtocol::CheddabitsV1Xor4Maj7 => run_fpm_prover_impl::<
            F61p,
            CheddaConvProverV1Xor4Maj7<F61p>,
            _,
        >(channel, common_opts, fpm_opts),
        ConversionProtocol::CheddabitsV2Xor4Maj7 => run_fpm_prover_impl::<
            F61p,
            CheddaConvProverV2Xor4Maj7<F61p>,
            _,
        >(channel, common_opts, fpm_opts),
        _ => panic!("not implemented"),
    }
}

fn run_fpm_prover_impl<FE: FiniteField, FPMP: FPMProverFromHomComsT<FE>, C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    _: &CommonOptions,
    fpm_opts: &FixedPointMultOptions,
) -> FixedPointMultStats
where
    <<FE as FiniteField>::PrimeField as TryFrom<u128>>::Error: std::fmt::Debug,
{
    let mut stats = FixedPointMultStats {
        num: fpm_opts.num,
        integer_size: fpm_opts.integer_size,
        fraction_size: fpm_opts.fraction_size,
        protocol: fpm_opts.protocol,
        time_stats: vec![Default::default()],
        comm_stats: Default::default(),
    };

    let mut rng = AesRng::from_seed(Default::default());
    channel.clear();

    // estimate voles required and choose LPN parameters
    let (num_voles_2, num_voles_p) = {
        let (n2, mut np) = FPMP::estimate_voles(
            fpm_opts.num,
            fpm_opts.integer_size as u32,
            fpm_opts.fraction_size as u32,
        );
        np += 3 * fpm_opts.num;
        (n2, np)
    };
    let (lpn_setup_params_2, lpn_extend_params_2) = choose_lpn_parameters::<F40b>(num_voles_p);
    let (lpn_setup_params_p, lpn_extend_params_p) = choose_lpn_parameters::<FE>(num_voles_p);

    // Init
    let t_start = Instant::now();
    let f2_prover = RcRefCell::new(
        FComProver::<F40b>::init(channel, &mut rng, lpn_setup_params_2, lpn_extend_params_2)
            .expect("FComProver::init failed"),
    );
    let fp_prover = RcRefCell::new(
        FComProver::<FE>::init(channel, &mut rng, lpn_setup_params_p, lpn_extend_params_p)
            .expect("FComProver::init failed"),
    );
    let mut fpm_prover = FPMP::from_homcoms(&f2_prover, &fp_prover).expect("from_homcoms failed");
    stats.time_stats[0].init_time = t_start.elapsed();
    stats.comm_stats.init_kb_received = channel.kilobytes_read();
    stats.comm_stats.init_kb_sent = channel.kilobytes_written();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // Preprocess VOLEs
    let t_start = Instant::now();
    f2_prover
        .get_refmut()
        .voles_reserve(channel, &mut rng, num_voles_2)
        .expect("voles_reserve failed");
    fp_prover
        .get_refmut()
        .voles_reserve(channel, &mut rng, num_voles_p)
        .expect("voles_reserve failed");
    channel.flush().expect("flush failed");
    stats.time_stats[0].voles_time = t_start.elapsed();
    stats.comm_stats.voles_kb_received = channel.kilobytes_read();
    stats.comm_stats.voles_kb_sent = channel.kilobytes_written();
    stats.comm_stats.voles_fp_stats = fp_prover.get_refmut().get_stats();
    stats.comm_stats.voles_f2_stats = f2_prover.get_refmut().get_stats();
    fp_prover.get_refmut().clear_stats();
    f2_prover.get_refmut().clear_stats();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // Commit
    let t_start = Instant::now();
    let fpm_tuples = random_fpm_triples_prover(
        &mut fp_prover.get_refmut(),
        channel,
        &mut rng,
        fpm_opts.integer_size as u32,
        fpm_opts.fraction_size as u32,
        fpm_opts.num,
    )
    .expect("random_fpm_triples_prover failed");
    channel.flush().expect("flush failed");
    stats.time_stats[0].commit_time = t_start.elapsed();
    stats.comm_stats.commit_kb_received = channel.kilobytes_read();
    stats.comm_stats.commit_kb_sent = channel.kilobytes_written();
    stats.comm_stats.commit_fp_stats = fp_prover.get_refmut().get_stats();
    stats.comm_stats.commit_f2_stats = f2_prover.get_refmut().get_stats();
    assert_eq!(
        stats
            .comm_stats
            .commit_fp_stats
            .num_vole_extensions_performed,
        0
    );
    assert_eq!(
        stats
            .comm_stats
            .commit_f2_stats
            .num_vole_extensions_performed,
        0
    );
    fp_prover.get_refmut().clear_stats();
    f2_prover.get_refmut().clear_stats();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // Check
    let t_start = Instant::now();
    fpm_prover
        .verify_fp_mult(
            channel,
            &mut rng,
            &fpm_tuples,
            fpm_opts.integer_size as u32,
            fpm_opts.fraction_size as u32,
        )
        .expect("verify_conversions failed");
    stats.time_stats[0].check_time = t_start.elapsed();
    stats.comm_stats.check_kb_received = channel.kilobytes_read();
    stats.comm_stats.check_kb_sent = channel.kilobytes_written();
    stats.comm_stats.check_fp_stats = fp_prover.get_refmut().get_stats();
    stats.comm_stats.check_f2_stats = f2_prover.get_refmut().get_stats();
    assert_eq!(
        stats
            .comm_stats
            .check_fp_stats
            .num_vole_extensions_performed,
        0
    );
    assert_eq!(
        stats
            .comm_stats
            .check_f2_stats
            .num_vole_extensions_performed,
        0
    );
    fp_prover.get_refmut().clear_stats();
    f2_prover.get_refmut().clear_stats();

    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    channel.clear();

    // eprintln!(
    //     "VOLES (p): {} + {} = {} =? {}",
    //     stats.comm_stats.commit_fp_stats.num_voles_used,
    //     stats.comm_stats.check_fp_stats.num_voles_used,
    //     stats.comm_stats.commit_fp_stats.num_voles_used
    //         + stats.comm_stats.check_fp_stats.num_voles_used,
    //     num_voles_p,
    // );
    // eprintln!(
    //     "VOLES (2): {} + {} = {} =? {}",
    //     stats.comm_stats.commit_f2_stats.num_voles_used,
    //     stats.comm_stats.check_f2_stats.num_voles_used,
    //     stats.comm_stats.commit_f2_stats.num_voles_used
    //         + stats.comm_stats.check_f2_stats.num_voles_used,
    //     num_voles_2,
    // );
    assert_eq!(
        stats.comm_stats.commit_fp_stats.num_voles_used
            + stats.comm_stats.check_fp_stats.num_voles_used,
        num_voles_p,
    );
    assert_eq!(
        stats.comm_stats.commit_f2_stats.num_voles_used
            + stats.comm_stats.check_f2_stats.num_voles_used,
        num_voles_2,
    );

    stats
}

fn run_fpm_verifier<FE: FiniteField, C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    common_opts: &CommonOptions,
    fpm_opts: &FixedPointMultOptions,
) -> FixedPointMultStats {
    match fpm_opts.protocol {
        ConversionProtocol::Edabits => run_fpm_verifier_impl::<F61p, EdabitsConvVerifier<F61p>, _>(
            channel,
            common_opts,
            fpm_opts,
        ),
        ConversionProtocol::CheddabitsV1TSPA => run_fpm_verifier_impl::<
            F61p,
            CheddaConvVerifierV1TSPA<F61p>,
            _,
        >(channel, common_opts, fpm_opts),
        ConversionProtocol::CheddabitsV2TSPA => run_fpm_verifier_impl::<
            F61p,
            CheddaConvVerifierV2TSPA<F61p>,
            _,
        >(channel, common_opts, fpm_opts),
        ConversionProtocol::CheddabitsV1Xor4Maj7 => run_fpm_verifier_impl::<
            F61p,
            CheddaConvVerifierV1Xor4Maj7<F61p>,
            _,
        >(channel, common_opts, fpm_opts),
        ConversionProtocol::CheddabitsV2Xor4Maj7 => run_fpm_verifier_impl::<
            F61p,
            CheddaConvVerifierV2Xor4Maj7<F61p>,
            _,
        >(channel, common_opts, fpm_opts),
        _ => panic!("not implemented"),
    }
}

fn run_fpm_verifier_impl<FE: FiniteField, FPMV: FPMVerifierFromHomComsT<FE>, C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    _: &CommonOptions,
    fpm_opts: &FixedPointMultOptions,
) -> FixedPointMultStats {
    let mut stats = FixedPointMultStats {
        num: fpm_opts.num,
        integer_size: fpm_opts.integer_size,
        fraction_size: fpm_opts.fraction_size,
        protocol: fpm_opts.protocol,
        time_stats: vec![Default::default()],
        comm_stats: Default::default(),
    };

    let mut rng = AesRng::from_seed(Default::default());
    channel.clear();

    // estimate voles required and choose LPN parameters
    let (num_voles_2, num_voles_p) = {
        let (n2, mut np) = FPMV::estimate_voles(
            fpm_opts.num,
            fpm_opts.integer_size as u32,
            fpm_opts.fraction_size as u32,
        );
        np += 3 * fpm_opts.num;
        (n2, np)
    };
    let (lpn_setup_params_2, lpn_extend_params_2) = choose_lpn_parameters::<F40b>(num_voles_p);
    let (lpn_setup_params_p, lpn_extend_params_p) = choose_lpn_parameters::<FE>(num_voles_p);

    // Init
    let t_start = Instant::now();
    let f2_verifier = RcRefCell::new(
        FComVerifier::<F40b>::init(channel, &mut rng, lpn_setup_params_2, lpn_extend_params_2)
            .expect("FComProver::init failed"),
    );
    let fp_verifier = RcRefCell::new(
        FComVerifier::<FE>::init(channel, &mut rng, lpn_setup_params_p, lpn_extend_params_p)
            .expect("FComProver::init failed"),
    );
    let mut fpm_verifier =
        FPMV::from_homcoms(&f2_verifier, &fp_verifier).expect("from_homcoms failed");
    stats.time_stats[0].init_time = t_start.elapsed();
    stats.comm_stats.init_kb_received = channel.kilobytes_read();
    stats.comm_stats.init_kb_sent = channel.kilobytes_written();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    // Preprocess VOLEs
    let t_start = Instant::now();
    f2_verifier
        .get_refmut()
        .voles_reserve(channel, &mut rng, num_voles_2)
        .expect("voles_reserve failed");
    fp_verifier
        .get_refmut()
        .voles_reserve(channel, &mut rng, num_voles_p)
        .expect("voles_reserve failed");
    channel.flush().expect("flush failed");
    stats.time_stats[0].voles_time = t_start.elapsed();
    stats.comm_stats.voles_kb_received = channel.kilobytes_read();
    stats.comm_stats.voles_kb_sent = channel.kilobytes_written();
    stats.comm_stats.voles_fp_stats = fp_verifier.get_refmut().get_stats();
    stats.comm_stats.voles_f2_stats = f2_verifier.get_refmut().get_stats();
    fp_verifier.get_refmut().clear_stats();
    f2_verifier.get_refmut().clear_stats();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    // Commit
    let t_start = Instant::now();
    let fpm_tuples = random_fpm_triples_verifier(
        &mut fp_verifier.get_refmut(),
        channel,
        &mut rng,
        fpm_opts.num,
    )
    .expect("random_fpm_triples_verifier failed");
    channel.flush().expect("flush failed");
    stats.time_stats[0].commit_time = t_start.elapsed();
    stats.comm_stats.commit_kb_received = channel.kilobytes_read();
    stats.comm_stats.commit_kb_sent = channel.kilobytes_written();
    stats.comm_stats.commit_fp_stats = fp_verifier.get_refmut().get_stats();
    stats.comm_stats.commit_f2_stats = f2_verifier.get_refmut().get_stats();
    assert_eq!(
        stats
            .comm_stats
            .commit_fp_stats
            .num_vole_extensions_performed,
        0
    );
    assert_eq!(
        stats
            .comm_stats
            .commit_f2_stats
            .num_vole_extensions_performed,
        0
    );
    fp_verifier.get_refmut().clear_stats();
    f2_verifier.get_refmut().clear_stats();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    // Check
    let t_start = Instant::now();
    fpm_verifier
        .verify_fp_mult(
            channel,
            &mut rng,
            &fpm_tuples,
            fpm_opts.integer_size as u32,
            fpm_opts.fraction_size as u32,
        )
        .expect("verify_conversions failed");
    stats.time_stats[0].check_time = t_start.elapsed();
    stats.comm_stats.check_kb_received = channel.kilobytes_read();
    stats.comm_stats.check_kb_sent = channel.kilobytes_written();
    stats.comm_stats.check_fp_stats = fp_verifier.get_refmut().get_stats();
    stats.comm_stats.check_f2_stats = f2_verifier.get_refmut().get_stats();
    assert_eq!(
        stats
            .comm_stats
            .check_fp_stats
            .num_vole_extensions_performed,
        0
    );
    assert_eq!(
        stats
            .comm_stats
            .check_f2_stats
            .num_vole_extensions_performed,
        0
    );
    fp_verifier.get_refmut().clear_stats();
    f2_verifier.get_refmut().clear_stats();

    channel.write_bool(true).expect("write_bool failed");
    channel.flush().expect("flush failed");
    let _: bool = channel.read_bool().expect("read_bool failed");
    channel.clear();

    assert_eq!(
        stats.comm_stats.commit_fp_stats.num_voles_used
            + stats.comm_stats.check_fp_stats.num_voles_used,
        num_voles_p,
    );
    assert_eq!(
        stats.comm_stats.commit_f2_stats.num_voles_used
            + stats.comm_stats.check_f2_stats.num_voles_used,
        num_voles_2,
    );

    stats
}

fn run_prover<C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    cmd: &BenchmarkCommand,
) -> ProtocolStats {
    match cmd {
        BenchmarkCommand::Multiplication {
            common_opts,
            mult_opts,
        } => ProtocolStats::Multiplication(match mult_opts.field {
            FieldParameter::F40b => run_mult_prover::<F40b, _>(channel, common_opts, mult_opts),
            FieldParameter::F61p => run_mult_prover::<F61p, _>(channel, common_opts, mult_opts),
        }),
        BenchmarkCommand::Conversion {
            common_opts,
            conv_opts,
        } => ProtocolStats::Conversion(match conv_opts.field {
            FieldParameter::F61p => run_conv_prover::<F61p, _>(channel, common_opts, conv_opts),
            _ => unimplemented!("only implemented for field F61p"),
        }),
        BenchmarkCommand::FixedPointMult {
            common_opts,
            fpm_opts,
        } => ProtocolStats::FixedPointMult(match fpm_opts.field {
            FieldParameter::F61p => run_fpm_prover::<F61p, _>(channel, common_opts, fpm_opts),
            _ => unimplemented!("only implemented for field F61p"),
        }),
    }
}

fn run_verifier<C: AbstractChannel>(
    channel: &mut TrackChannel<C>,
    cmd: &BenchmarkCommand,
) -> ProtocolStats {
    match cmd {
        BenchmarkCommand::Multiplication {
            common_opts,
            mult_opts,
        } => ProtocolStats::Multiplication(match mult_opts.field {
            FieldParameter::F40b => run_mult_verifier::<F40b, _>(channel, common_opts, mult_opts),
            FieldParameter::F61p => run_mult_verifier::<F61p, _>(channel, common_opts, mult_opts),
        }),
        BenchmarkCommand::Conversion {
            common_opts,
            conv_opts,
        } => ProtocolStats::Conversion(match conv_opts.field {
            FieldParameter::F61p => run_conv_verifier::<F61p, _>(channel, common_opts, conv_opts),
            _ => unimplemented!("only implemented for field F61p"),
        }),
        BenchmarkCommand::FixedPointMult {
            common_opts,
            fpm_opts,
        } => ProtocolStats::FixedPointMult(match fpm_opts.field {
            FieldParameter::F61p => run_fpm_verifier::<F61p, _>(channel, common_opts, fpm_opts),
            _ => unimplemented!("only implemented for field F61p"),
        }),
    }
}

fn run_benchmark(cmd: BenchmarkCommand) {
    let cmd = Arc::new(cmd);
    let options = cmd.get_common_options();
    let t_start = Instant::now();
    if !options.json {
        println!("Startup time: {:?}", t_start.elapsed());
    }

    let mut results = BenchmarkResult::new(&cmd);

    match &options.party {
        Party::Both => {
            let mut results_p = results.clone();
            let mut results_v = results;
            let (mut channel_v, mut channel_p) = track_unix_channel_pair();
            let repetitions = options.repetitions.clone();
            //             let mut results_p = BenchmarkResult::new(&options);
            //             let mut results_v = results_p.clone();
            let cmd_p = cmd.clone();
            let prover_thread = thread::spawn(move || {
                let mut proto_stats = Vec::with_capacity(repetitions);
                for _ in 0..repetitions {
                    let stats = run_prover(&mut channel_p, &cmd_p);
                    proto_stats.push(stats)
                }
                proto_stats
            });
            let cmd_v = cmd.clone();
            let verifier_thread = thread::spawn(move || {
                let mut proto_stats = Vec::with_capacity(repetitions);
                for _ in 0..repetitions {
                    let stats = run_verifier(&mut channel_v, &cmd_v);
                    proto_stats.push(stats)
                }
                proto_stats
            });
            results_p.protocol_stats = prover_thread.join().unwrap();
            results_v.protocol_stats = verifier_thread.join().unwrap();
            results_p.aggregate();
            results_v.aggregate();

            if options.json {
                println!("{}", serde_json::to_string_pretty(&results_p).unwrap());
                println!("{}", serde_json::to_string_pretty(&results_v).unwrap());
            } else {
                println!("results prover: {:#?}", results_p);
                println!("results verifier: {:#?}", results_v);
            }
        }
        party => {
            let mut channel = {
                match setup_network(&options.network_options) {
                    Ok(channel) => channel,
                    Err(e) => {
                        eprintln!("Network connection failed: {}", e.to_string());
                        return;
                    }
                }
            };
            results.protocol_stats.reserve(options.repetitions);
            for _ in 0..options.repetitions {
                let stats = match party {
                    Party::Prover => run_prover(&mut channel, &cmd),
                    Party::Verifier => run_verifier(&mut channel, &cmd),
                    _ => panic!("can't happen"),
                };
                results.protocol_stats.push(stats)
            }
            results.aggregate();
            if options.json {
                println!("{}", serde_json::to_string_pretty(&results).unwrap());
            } else {
                println!("results: {:#?}", results);
            }
        }
    }
}

fn main() {
    let cli = Cli::parse();
    cli.command.check();
    // check_options(&cli);
    run_benchmark(cli.command);
}
