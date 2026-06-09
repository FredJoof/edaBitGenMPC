use diet_mac_and_cheese::{
    mpc_chedda_edabits::{
        MpcCheddaEdabitsV1TSPAPeer, MpcCheddaEdabitsV1Xor4Maj7Peer, MpcCheddaEdabitsV2TSPAPeer,
        MpcCheddaEdabitsV2Xor4Maj7Peer, TSPAUncheckedPrivateEdabitState,
        Xor4Maj7UncheckedPrivateEdabitState,
    },
    mpc_conv::PrivateEdabitState,
    mpc_edabits::{MpcEdabitsCheckBreakdown, MpcEdabitsPeer},
    mpc_homcom::PeerRole,
    mpc_original_edabits::{
        CheckedPrivateEdabitState, MpcOriginalEdabitsPeer, SampledPrivateEdabitState,
    },
};
use eyre::Result;
use ocelot::svole::wykw::{LpnParams, LPN_EXTEND_SMALL, LPN_SETUP_SMALL};
use rand::{CryptoRng, Rng};
use scuttlebutt::{
    field::F61p, track_unix_channel_pair, AbstractChannel, AesRng, TrackUnixChannel,
};
use std::io::Write;
use std::time::{Duration, Instant};

/// EdaBit bit lengths to sweep over.
const BIT_SIZES: &[usize] = &[32];

/// Number of edaBits to generate per run, swept independently of bit length.
/// The cut-and-choose parameter selection (shared by all protocols here)
/// asserts `num_edabits >= 1024`, so the sweep can't go below that.
const NUM_EDABITS: &[usize] = &[4096];

/// LPN parameters shared by all protocols. `SMALL` keeps the sweep fast;
/// switch to `LPN_SETUP_MEDIUM`/`LPN_EXTEND_MEDIUM` for more realistic
/// large-batch numbers (at the cost of much longer `init` phases).
const LPN_SETUP: LpnParams = LPN_SETUP_SMALL;
const LPN_EXTEND: LpnParams = LPN_EXTEND_SMALL;

/// Small hidden warm-up to reduce first-run noise without doubling the real
/// benchmark cost for large batches.
const WARMUP_BIT_SIZE: usize = 32;
const WARMUP_NUM_EDABITS: usize = 1024;
const WARMUP_ROUNDS: usize = 1;

/// Wall-clock time and total communication (both directions, in kilobits) for
/// a single protocol phase, combined across both parties.
#[derive(Clone, Copy, Debug, Default)]
struct PhaseMetrics {
    time: Duration,
    comm_kilobits: f64,
}

impl PhaseMetrics {
    fn plus(self, other: Self) -> Self {
        Self {
            time: self.time + other.time,
            comm_kilobits: self.comm_kilobits + other.comm_kilobits,
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct PartyMetrics {
    init: PhaseMetrics,
    share: PhaseMetrics,
    check: PhaseMetrics,
    check_breakdown: Option<CheckTimeBreakdown>,
    combine: PhaseMetrics,
    table2_like: PhaseMetrics,
    total: PhaseMetrics,
}

#[derive(Clone, Copy, Debug, Default)]
struct CheckTimeBreakdown {
    aux: Duration,
    core: Duration,
}

#[derive(Clone, Debug)]
struct BenchResult {
    implementation: &'static str,
    bit_size: usize,
    num_edabits: usize,
    init: PhaseMetrics,
    share: PhaseMetrics,
    check: PhaseMetrics,
    check_breakdown: Option<CheckTimeBreakdown>,
    combine: PhaseMetrics,
    table2_like: PhaseMetrics,
    total: PhaseMetrics,
}

trait BenchEdabitsPeer: Sized {
    type PreparedState;
    type CheckedState;

    fn bench_init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        role: PeerRole,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
    ) -> Result<Self>;

    fn bench_prepare<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Self::PreparedState>;

    fn bench_check<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: Self::PreparedState,
    ) -> Result<Self::CheckedState>;

    fn bench_combine<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &Self::CheckedState,
    ) -> Result<()>;

    fn bench_last_check_breakdown(&self) -> Option<CheckTimeBreakdown> {
        None
    }
}

impl BenchEdabitsPeer for MpcEdabitsPeer<F61p> {
    type PreparedState = PrivateEdabitState<F61p>;
    type CheckedState = PrivateEdabitState<F61p>;

    fn bench_init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        role: PeerRole,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
    ) -> Result<Self> {
        Self::init(channel, rng, role, lpn_setup, lpn_extend)
    }

    fn bench_prepare<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Self::PreparedState> {
        self.sample_and_share_private_edabits_owner_zero(channel, rng, bit_size, num)
    }

    fn bench_check<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: Self::PreparedState,
    ) -> Result<Self::CheckedState> {
        self.verify_private_edabits(channel, rng, &state)?;
        Ok(state)
    }

    fn bench_combine<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &Self::CheckedState,
    ) -> Result<()> {
        self.combine_private_into_global_edabits(channel, rng, state)?;
        Ok(())
    }

    fn bench_last_check_breakdown(&self) -> Option<CheckTimeBreakdown> {
        let MpcEdabitsCheckBreakdown { aux, core } = self.last_check_breakdown();
        Some(CheckTimeBreakdown { aux, core })
    }
}

impl BenchEdabitsPeer for MpcOriginalEdabitsPeer<F61p> {
    type PreparedState = SampledPrivateEdabitState<F61p>;
    type CheckedState = CheckedPrivateEdabitState<F61p>;

    fn bench_init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        role: PeerRole,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
    ) -> Result<Self> {
        Self::init(channel, rng, role, lpn_setup, lpn_extend)
    }

    fn bench_prepare<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<Self::PreparedState> {
        self.sample_and_share_private_edabits_unchecked(channel, rng, bit_size, num)
    }

    fn bench_check<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: Self::PreparedState,
    ) -> Result<Self::CheckedState> {
        self.verify_private_edabits(channel, rng, state)
    }

    fn bench_combine<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        state: &Self::CheckedState,
    ) -> Result<()> {
        self.combine_checked_private_edabits(channel, rng, state)?;
        Ok(())
    }
}

macro_rules! impl_bench_chedda_peer {
    ($peer:ty, $state:ty) => {
        impl BenchEdabitsPeer for $peer {
            type PreparedState = $state;
            type CheckedState = $state;

            fn bench_init<C: AbstractChannel, RNG: CryptoRng + Rng>(
                channel: &mut C,
                rng: &mut RNG,
                role: PeerRole,
                lpn_setup: LpnParams,
                lpn_extend: LpnParams,
            ) -> Result<Self> {
                Self::init(channel, rng, role, lpn_setup, lpn_extend)
            }

            fn bench_prepare<C: AbstractChannel, RNG: CryptoRng + Rng>(
                &mut self,
                channel: &mut C,
                rng: &mut RNG,
                bit_size: usize,
                num: usize,
            ) -> Result<Self::PreparedState> {
                self.sample_and_share_private_edabits_unchecked(channel, rng, bit_size, num)
            }

            fn bench_check<C: AbstractChannel, RNG: CryptoRng + Rng>(
                &mut self,
                channel: &mut C,
                rng: &mut RNG,
                state: Self::PreparedState,
            ) -> Result<Self::CheckedState> {
                self.verify_private_edabits(channel, rng, &state)?;
                Ok(state)
            }

            fn bench_combine<C: AbstractChannel, RNG: CryptoRng + Rng>(
                &mut self,
                channel: &mut C,
                rng: &mut RNG,
                state: &Self::CheckedState,
            ) -> Result<()> {
                self.combine_sampled_private_edabits(channel, rng, state)?;
                Ok(())
            }
        }
    };
}

impl_bench_chedda_peer!(
    MpcCheddaEdabitsV1TSPAPeer<F61p>,
    TSPAUncheckedPrivateEdabitState<F61p>
);
impl_bench_chedda_peer!(
    MpcCheddaEdabitsV2TSPAPeer<F61p>,
    TSPAUncheckedPrivateEdabitState<F61p>
);
impl_bench_chedda_peer!(
    MpcCheddaEdabitsV1Xor4Maj7Peer<F61p>,
    Xor4Maj7UncheckedPrivateEdabitState<F61p>
);
impl_bench_chedda_peer!(
    MpcCheddaEdabitsV2Xor4Maj7Peer<F61p>,
    Xor4Maj7UncheckedPrivateEdabitState<F61p>
);

fn capture_phase(channel: &TrackUnixChannel, start: Instant) -> PhaseMetrics {
    PhaseMetrics {
        time: start.elapsed(),
        comm_kilobits: channel.kilobits_written() + channel.kilobits_read(),
    }
}

fn run_party<P: BenchEdabitsPeer>(
    channel: &mut TrackUnixChannel,
    role: PeerRole,
    bit_size: usize,
    num_edabits: usize,
) -> PartyMetrics {
    let mut rng = AesRng::new();

    let init_start = Instant::now();
    let mut peer = P::bench_init(channel, &mut rng, role, LPN_SETUP, LPN_EXTEND)
        .expect("peer initialization failed");
    let init = capture_phase(channel, init_start);
    channel.clear();

    let total_start = Instant::now();

    let share_start = Instant::now();
    let prepared = peer
        .bench_prepare(channel, &mut rng, bit_size, num_edabits)
        .expect("edabits sampling/share failed");
    let share = capture_phase(channel, share_start);
    channel.clear();

    let check_start = Instant::now();
    let checked = peer
        .bench_check(channel, &mut rng, prepared)
        .expect("edabits check failed");
    let check_breakdown = peer.bench_last_check_breakdown();
    let check = capture_phase(channel, check_start);
    channel.clear();

    let combine_start = Instant::now();
    peer.bench_combine(channel, &mut rng, &checked)
        .expect("edabits combine failed");
    let combine = capture_phase(channel, combine_start);

    let table2_like = share.plus(check);
    let total = PhaseMetrics {
        time: total_start.elapsed(),
        comm_kilobits: share.comm_kilobits + check.comm_kilobits + combine.comm_kilobits,
    };

    PartyMetrics {
        init,
        share,
        check,
        check_breakdown,
        combine,
        table2_like,
        total,
    }
}

/// Runs a single (implementation, bit_size, num_edabits) combination end to
/// end and combines the two parties' metrics: time is the wall-clock max
/// (the phase isn't done until both parties finish) and communication is
/// summed (each party's view double-counts the same bits, once as sent and
/// once as received, so summing both parties' totals would double-count
/// again -- we instead take a single party's combined sent+received, which
/// already accounts for the full bidirectional exchange).
fn run_bench<P>(implementation: &'static str, bit_size: usize, num_edabits: usize) -> BenchResult
where
    P: BenchEdabitsPeer + 'static,
{
    let (mut first_channel, mut second_channel) = track_unix_channel_pair();

    let handle = std::thread::spawn(move || {
        run_party::<P>(&mut first_channel, PeerRole::First, bit_size, num_edabits)
    });

    let second = run_party::<P>(&mut second_channel, PeerRole::Second, bit_size, num_edabits);
    let first = handle.join().expect("party thread panicked");

    let combine_phase = |a: PhaseMetrics, b: PhaseMetrics| PhaseMetrics {
        time: a.time.max(b.time),
        comm_kilobits: (a.comm_kilobits + b.comm_kilobits) / 2.0,
    };
    let combine_check_breakdown =
        |a: Option<CheckTimeBreakdown>, b: Option<CheckTimeBreakdown>| match (a, b) {
            (Some(a), Some(b)) => Some(CheckTimeBreakdown {
                aux: a.aux.max(b.aux),
                core: a.core.max(b.core),
            }),
            _ => None,
        };

    BenchResult {
        implementation,
        bit_size,
        num_edabits,
        init: combine_phase(first.init, second.init),
        share: combine_phase(first.share, second.share),
        check: combine_phase(first.check, second.check),
        check_breakdown: combine_check_breakdown(first.check_breakdown, second.check_breakdown),
        combine: combine_phase(first.combine, second.combine),
        table2_like: combine_phase(first.table2_like, second.table2_like),
        total: combine_phase(first.total, second.total),
    }
}

struct BenchSpec {
    implementation: &'static str,
    run: fn(&'static str, usize, usize) -> BenchResult,
}

impl BenchSpec {
    fn new<P>(implementation: &'static str) -> Self
    where
        P: BenchEdabitsPeer + 'static,
    {
        Self {
            implementation,
            run: run_named_bench::<P>,
        }
    }
}

fn run_named_bench<P>(
    implementation: &'static str,
    bit_size: usize,
    num_edabits: usize,
) -> BenchResult
where
    P: BenchEdabitsPeer + 'static,
{
    run_bench::<P>(implementation, bit_size, num_edabits)
}

fn warm_up(benches: &[BenchSpec]) {
    println!(
        "Warming up each implementation with bits={} and n={} ({} round{})...\n",
        WARMUP_BIT_SIZE,
        WARMUP_NUM_EDABITS,
        WARMUP_ROUNDS,
        if WARMUP_ROUNDS == 1 { "" } else { "s" }
    );

    for bench in benches {
        for round in 0..WARMUP_ROUNDS {
            print!(
                "warm-up {:<28} | round {}/{} ... ",
                bench.implementation,
                round + 1,
                WARMUP_ROUNDS,
            );
            std::io::stdout().flush().expect("failed to flush stdout");
            let _ = (bench.run)(bench.implementation, WARMUP_BIT_SIZE, WARMUP_NUM_EDABITS);
            println!("done");
        }
    }

    println!();
}

fn main() {
    let benches: &[BenchSpec] = &[
        BenchSpec::new::<MpcEdabitsPeer<F61p>>("mpc_edabits"),
        BenchSpec::new::<MpcOriginalEdabitsPeer<F61p>>("mpc_original_edabits"),
        BenchSpec::new::<MpcCheddaEdabitsV1TSPAPeer<F61p>>("mpc_chedda (v1, tspa)"),
        BenchSpec::new::<MpcCheddaEdabitsV2TSPAPeer<F61p>>("mpc_chedda (v2, tspa)"),
        BenchSpec::new::<MpcCheddaEdabitsV1Xor4Maj7Peer<F61p>>("mpc_chedda (v1, xor4maj7)"),
        BenchSpec::new::<MpcCheddaEdabitsV2Xor4Maj7Peer<F61p>>("mpc_chedda (v2, xor4maj7)"),
    ];

    let total_runs = BIT_SIZES.len() * NUM_EDABITS.len() * benches.len();
    println!("EdaBits generation benchmark (field = F61p, simulated WAN topology, no bandwidth throttling)");
    println!("Phase split:");
    println!("  init        = one-time VOLE/FCom setup");
    println!("  share       = sample/share/authenticate the private tuples");
    println!("  check       = protocol-specific consistency check");
    println!("  check_aux   = only for mpc_edabits: auxiliary random edabits/dabits");
    println!("                plus fdabit/cut-and-choose setup inside the old conv");
    println!("  check_core  = only for mpc_edabits: the actual bucketed conversion checks");
    println!("  combine     = final 2PC global-edaBit combine");
    println!("  share+check = closest comparison here to Table 2's per-conversion total");
    println!("                (Table 2 does not include our final combine step, and our");
    println!("                 VOLE work is still paid lazily inside these phases)");
    warm_up(benches);
    println!("Running {total_runs} (implementation, bit_size, num_edabits) combinations...\n");

    let mut results = Vec::new();
    let mut run_index = 0usize;
    for &bit_size in BIT_SIZES {
        for &num_edabits in NUM_EDABITS {
            for bench in benches {
                run_index += 1;
                print!(
                    "[{run_index:>3}/{total_runs:<3}] {:<28} | bits={:<3} | n={:<8} | running... ",
                    bench.implementation, bit_size, num_edabits,
                );
                std::io::stdout().flush().expect("failed to flush stdout");

                let result = (bench.run)(bench.implementation, bit_size, num_edabits);
                if let Some(breakdown) = result.check_breakdown {
                    println!(
                        "share: {:>8.2?} / {:>9.2} kb | check: {:>8.2?} / {:>9.2} kb | aux: {:>8.2?} | core: {:>8.2?} | combine: {:>8.2?} / {:>9.2} kb | share+check: {:>8.2?}",
                        result.share.time,
                        result.share.comm_kilobits,
                        result.check.time,
                        result.check.comm_kilobits,
                        breakdown.aux,
                        breakdown.core,
                        result.combine.time,
                        result.combine.comm_kilobits,
                        result.table2_like.time,
                    );
                } else {
                    println!(
                        "share: {:>8.2?} / {:>9.2} kb | check: {:>8.2?} / {:>9.2} kb | combine: {:>8.2?} / {:>9.2} kb | share+check: {:>8.2?}",
                        result.share.time,
                        result.share.comm_kilobits,
                        result.check.time,
                        result.check.comm_kilobits,
                        result.combine.time,
                        result.combine.comm_kilobits,
                        result.table2_like.time,
                    );
                }
                results.push(result);
            }
        }
    }

    println!("\n=== Summary ({} results) ===", results.len());
    println!(
        "{:<28} | {:<8} | {:<8} | {:<17} | {:<17} | {:<17} | {:<17} | {:<17}",
        "implementation", "bit_size", "num", "init", "share", "check", "combine", "share+check"
    );
    println!("{}", "-".repeat(170));
    for result in &results {
        println!(
            "{:<28} | {:<8} | {:<8} | {:>8.2?}/{:>7.2} | {:>8.2?}/{:>7.2} | {:>8.2?}/{:>7.2} | {:>8.2?}/{:>7.2} | {:>8.2?}/{:>7.2}",
            result.implementation,
            result.bit_size,
            result.num_edabits,
            result.init.time,
            result.init.comm_kilobits,
            result.share.time,
            result.share.comm_kilobits,
            result.check.time,
            result.check.comm_kilobits,
            result.combine.time,
            result.combine.comm_kilobits,
            result.table2_like.time,
            result.table2_like.comm_kilobits,
        );
    }

    let detailed_results: Vec<_> = results
        .iter()
        .filter_map(|result| result.check_breakdown.map(|breakdown| (result, breakdown)))
        .collect();
    if !detailed_results.is_empty() {
        println!("\n=== Detailed Check Breakdown ===");
        println!(
            "{:<28} | {:<8} | {:<8} | {:<12} | {:<12}",
            "implementation", "bit_size", "num", "check_aux", "check_core"
        );
        println!("{}", "-".repeat(82));
        for (result, breakdown) in detailed_results {
            println!(
                "{:<28} | {:<8} | {:<8} | {:>8.2?} | {:>8.2?}",
                result.implementation,
                result.bit_size,
                result.num_edabits,
                breakdown.aux,
                breakdown.core,
            );
        }
    }

    println!("\n=== Totals (including combine) ===");
    println!(
        "{:<28} | {:<8} | {:<8} | {:<17}",
        "implementation", "bit_size", "num", "total"
    );
    println!("{}", "-".repeat(80));
    for result in &results {
        println!(
            "{:<28} | {:<8} | {:<8} | {:>8.2?}/{:>7.2}",
            result.implementation,
            result.bit_size,
            result.num_edabits,
            result.total.time,
            result.total.comm_kilobits,
        );
    }
}
