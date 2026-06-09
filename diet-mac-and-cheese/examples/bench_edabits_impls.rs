use diet_mac_and_cheese::{
    mpc_chedda_edabits::{
        MpcCheddaEdabitsV1TSPAPeer, MpcCheddaEdabitsV1Xor4Maj7Peer, MpcCheddaEdabitsV2TSPAPeer,
        MpcCheddaEdabitsV2Xor4Maj7Peer,
    },
    mpc_edabits::MpcEdabitsPeer,
    mpc_homcom::PeerRole,
    mpc_original_edabits::MpcOriginalEdabitsPeer,
};
use eyre::Result;
use ocelot::svole::wykw::{LpnParams, LPN_EXTEND_SMALL, LPN_SETUP_SMALL};
use rand::{CryptoRng, Rng};
use scuttlebutt::{field::F61p, track_unix_channel_pair, AbstractChannel, AesRng, TrackUnixChannel};
use std::io::Write;
use std::time::{Duration, Instant};

const NUM_IMPLEMENTATIONS: usize = 6;

/// EdaBit bit lengths to sweep over.
const BIT_SIZES: &[usize] = &[8, 16, 32];

/// Number of edaBits to generate per run, swept independently of bit length.
/// The cut-and-choose parameter selection (shared by all protocols here)
/// asserts `num_edabits >= 1024`, so the sweep can't go below that.
const NUM_EDABITS: &[usize] = &[1_024, 10_000];

/// LPN parameters shared by all protocols. `SMALL` keeps the sweep fast;
/// switch to `LPN_SETUP_MEDIUM`/`LPN_EXTEND_MEDIUM` for more realistic
/// large-batch numbers (at the cost of much longer `init` phases).
const LPN_SETUP: LpnParams = LPN_SETUP_SMALL;
const LPN_EXTEND: LpnParams = LPN_EXTEND_SMALL;

/// Wall-clock time and total communication (both directions, in kilobits) for
/// a single protocol phase, combined across both parties.
#[derive(Clone, Copy, Debug)]
struct PhaseMetrics {
    time: Duration,
    comm_kilobits: f64,
}

#[derive(Clone, Copy, Debug)]
struct PartyMetrics {
    init: PhaseMetrics,
    generate: PhaseMetrics,
}

#[derive(Clone, Debug)]
struct BenchResult {
    implementation: &'static str,
    bit_size: usize,
    num_edabits: usize,
    init: PhaseMetrics,
    generate: PhaseMetrics,
}

trait BenchEdabitsPeer: Sized {
    fn bench_init<C: AbstractChannel, RNG: CryptoRng + Rng>(
        channel: &mut C,
        rng: &mut RNG,
        role: PeerRole,
        lpn_setup: LpnParams,
        lpn_extend: LpnParams,
    ) -> Result<Self>;

    fn bench_generate<C: AbstractChannel, RNG: CryptoRng + Rng>(
        &mut self,
        channel: &mut C,
        rng: &mut RNG,
        bit_size: usize,
        num: usize,
    ) -> Result<()>;
}

macro_rules! impl_bench_edabits_peer {
    ($peer:ty) => {
        impl BenchEdabitsPeer for $peer {
            fn bench_init<C: AbstractChannel, RNG: CryptoRng + Rng>(
                channel: &mut C,
                rng: &mut RNG,
                role: PeerRole,
                lpn_setup: LpnParams,
                lpn_extend: LpnParams,
            ) -> Result<Self> {
                Self::init(channel, rng, role, lpn_setup, lpn_extend)
            }

            fn bench_generate<C: AbstractChannel, RNG: CryptoRng + Rng>(
                &mut self,
                channel: &mut C,
                rng: &mut RNG,
                bit_size: usize,
                num: usize,
            ) -> Result<()> {
                self.generate_edabits(channel, rng, bit_size, num)?;
                Ok(())
            }
        }
    };
}

impl_bench_edabits_peer!(MpcEdabitsPeer<F61p>);
impl_bench_edabits_peer!(MpcOriginalEdabitsPeer<F61p>);
impl_bench_edabits_peer!(MpcCheddaEdabitsV1TSPAPeer<F61p>);
impl_bench_edabits_peer!(MpcCheddaEdabitsV2TSPAPeer<F61p>);
impl_bench_edabits_peer!(MpcCheddaEdabitsV1Xor4Maj7Peer<F61p>);
impl_bench_edabits_peer!(MpcCheddaEdabitsV2Xor4Maj7Peer<F61p>);

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
    let init = PhaseMetrics {
        time: init_start.elapsed(),
        comm_kilobits: channel.kilobits_written() + channel.kilobits_read(),
    };
    channel.clear();

    let gen_start = Instant::now();
    peer.bench_generate(channel, &mut rng, bit_size, num_edabits)
        .expect("edabits generation failed");
    let generate = PhaseMetrics {
        time: gen_start.elapsed(),
        comm_kilobits: channel.kilobits_written() + channel.kilobits_read(),
    };

    PartyMetrics { init, generate }
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

    let combine = |a: PhaseMetrics, b: PhaseMetrics| PhaseMetrics {
        time: a.time.max(b.time),
        comm_kilobits: (a.comm_kilobits + b.comm_kilobits) / 2.0,
    };

    BenchResult {
        implementation,
        bit_size,
        num_edabits,
        init: combine(first.init, second.init),
        generate: combine(first.generate, second.generate),
    }
}

fn main() {
    let total_runs = BIT_SIZES.len() * NUM_EDABITS.len() * NUM_IMPLEMENTATIONS;
    println!("EdaBits generation benchmark (field = F61p, simulated WAN topology, no bandwidth throttling)");
    println!("Running {total_runs} (implementation, bit_size, num_edabits) combinations...\n");

    let mut results = Vec::new();
    let mut run_index = 0usize;
    for &bit_size in BIT_SIZES {
        for &num_edabits in NUM_EDABITS {
            macro_rules! bench {
                ($peer:ty, $name:expr) => {{
                    run_index += 1;
                    print!(
                        "[{run_index:>3}/{total_runs:<3}] {:<28} | bits={:<3} | n={:<6} | running... ",
                        $name, bit_size, num_edabits,
                    );
                    std::io::stdout().flush().expect("failed to flush stdout");

                    let result = run_bench::<$peer>($name, bit_size, num_edabits);
                    println!(
                        "init: {:>9.2?} / {:>8.2} kb | generate: {:>9.2?} / {:>8.2} kb",
                        result.init.time,
                        result.init.comm_kilobits,
                        result.generate.time,
                        result.generate.comm_kilobits,
                    );
                    results.push(result);
                }};
            }

            bench!(MpcEdabitsPeer<F61p>, "mpc_edabits");
            bench!(MpcOriginalEdabitsPeer<F61p>, "mpc_original_edabits");
            bench!(MpcCheddaEdabitsV1TSPAPeer<F61p>, "mpc_chedda (v1, tspa)");
            bench!(MpcCheddaEdabitsV2TSPAPeer<F61p>, "mpc_chedda (v2, tspa)");
            bench!(MpcCheddaEdabitsV1Xor4Maj7Peer<F61p>, "mpc_chedda (v1, xor4maj7)");
            bench!(MpcCheddaEdabitsV2Xor4Maj7Peer<F61p>, "mpc_chedda (v2, xor4maj7)");
        }
    }

    println!("\n=== Summary ({} results) ===", results.len());
    println!(
        "{:<28} | {:<8} | {:<8} | {:<24} | {:<24}",
        "implementation", "bit_size", "num", "init (time / comm)", "generate (time / comm)"
    );
    println!("{}", "-".repeat(120));
    for result in &results {
        println!(
            "{:<28} | {:<8} | {:<8} | {:>9.2?} / {:>8.2} kb   | {:>9.2?} / {:>8.2} kb",
            result.implementation,
            result.bit_size,
            result.num_edabits,
            result.init.time,
            result.init.comm_kilobits,
            result.generate.time,
            result.generate.comm_kilobits,
        );
    }
}
