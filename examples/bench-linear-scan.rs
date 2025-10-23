use ark_ff::UniformRand as _;
use clap::Parser;
use eyre::{Context, eyre};
use figment::{
    Figment,
    providers::{Env, Format as _, Serialized, Toml},
};
use mpc_core::protocols::{
    rep3::{self, Rep3PrimeFieldShare, Rep3State, conversion::A2BType},
    rep3_ring::{self, Rep3RingShare, ring::ring_impl::RingElement},
};
use mpc_net::{
    Network,
    tcp::{NetworkConfig, TcpNetwork},
};
use oblivious_linear_scan_map::{LinearScanObliviousMap, local::LinearScanMap};
use rand::{CryptoRng, Rng, SeedableRng};
use rand_chacha::ChaCha12Rng;
use serde::{Deserialize, Serialize};
use std::{
    path::PathBuf,
    process::ExitCode,
    time::{Duration, Instant},
};

const SLEEP: Duration = Duration::from_millis(200);

/// Cli arguments
#[derive(Debug, Serialize, Parser)]
pub struct Cli {
    /// The path to the config file
    #[arg(long)]
    pub config: Option<PathBuf>,

    /// The seed for the RNG
    #[arg(short, long, default_value_t = 0)]
    pub seed: u64,

    /// The number of test runs
    #[arg(short, long, default_value_t = 10)]
    pub runs: usize,

    /// The number of elements in the map
    #[arg(short, long, default_value_t = 100)]
    pub num_items: usize,
}

/// Config
#[derive(Debug, Deserialize)]
pub struct Config {
    /// The number of test runs
    pub runs: usize,
    /// The seed for the RNG
    pub seed: u64,
    /// The number of elements in the map
    pub num_items: usize,
    /// Network config
    pub network: NetworkConfig,
}

impl Config {
    /// Parse config from file, env, cli
    pub fn parse(cli: Cli) -> Result<Self, Box<figment::error::Error>> {
        if let Some(path) = &cli.config {
            Ok(Figment::new()
                .merge(Toml::file(path))
                .merge(Env::prefixed(CONFIG_ENV_PREFIX))
                .merge(Serialized::defaults(cli))
                .extract()?)
        } else {
            Ok(Figment::new()
                .merge(Env::prefixed(CONFIG_ENV_PREFIX))
                .merge(Serialized::defaults(cli))
                .extract()?)
        }
    }
}

/// Prefix for config env variables
pub const CONFIG_ENV_PREFIX: &str = "WORLD_";

fn get_random_map<R: Rng>(num_items: usize, rng: &mut R) -> LinearScanMap {
    let mut keys = Vec::with_capacity(num_items);

    for _ in 0..num_items {
        // Duplicate keys are possible with this sampling method, but this is fine for benchmarking
        keys.push(rand::random::<u32>());
    }
    // fill the map with random values - doesn't matter for benchmarking
    LinearScanMap::with_garbage_values(keys, rng)
}

fn print_runtimes(times: Vec<f64>, id: usize, s: &str) {
    let mut min = f64::INFINITY;
    let mut max = 0f64;
    let mut avg = 0f64;

    let len = times.len();
    for runtime in times {
        avg += runtime;
        min = min.min(runtime);
        max = max.max(runtime);
    }
    avg /= len as f64;

    tracing::info!("{}: Party {}, {} runs", s, id, len);
    tracing::info!("\tavg: {:.2}µs", avg);
    tracing::info!("\tmin: {:.2}µs", min);
    tracing::info!("\tmax: {:.2}µs", max);
}

fn print_data(send_receive: Vec<(usize, usize)>, my_id: usize, other_id: usize, s: &str) {
    let mut min_send = f64::INFINITY;
    let mut max_send = 0f64;
    let mut avg_send = 0f64;
    let mut min_rcv = f64::INFINITY;
    let mut max_rcv = 0f64;
    let mut avg_rcv = 0f64;

    let len = send_receive.len();
    for (send, rcv) in send_receive {
        avg_send += send as f64;
        min_send = min_send.min(send as f64);
        max_send = max_send.max(send as f64);

        avg_rcv += rcv as f64;
        min_rcv = min_rcv.min(rcv as f64);
        max_rcv = max_rcv.max(rcv as f64);
    }
    avg_send /= len as f64;
    avg_rcv /= len as f64;

    tracing::info!("{}: Party {}->{}, {} runs", s, my_id, other_id, len);
    tracing::info!("\tavg: {:.2} bytes", avg_send);
    tracing::info!("\tmin: {:.2} bytes", min_send);
    tracing::info!("\tmax: {:.2} bytes", max_send);
    tracing::info!("{}: Party {}<-{}, {} runs", s, my_id, other_id, len);
    tracing::info!("\tavg: {:.2} bytes", avg_rcv);
    tracing::info!("\tmin: {:.2} bytes", min_rcv);
    tracing::info!("\tmax: {:.2} bytes", max_rcv);
}
fn install_tracing() {
    use tracing_subscriber::prelude::*;
    use tracing_subscriber::{EnvFilter, fmt};

    let fmt_layer = fmt::layer().with_target(false).with_line_number(false);
    let filter_layer = EnvFilter::try_from_default_env()
        .or_else(|_| EnvFilter::try_new("bench=info"))
        .unwrap();

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();
}

fn main() -> eyre::Result<ExitCode> {
    rustls::crypto::aws_lc_rs::default_provider()
        .install_default()
        .map_err(|_| eyre!("Could not install default rustls crypto provider"))?;

    let cli = Cli::parse();
    let config = Config::parse(cli).context("while parsing config")?;

    // install tracing for party ID 0
    if config.network.my_id == 0 {
        install_tracing();
    }

    let mut seed = [0u8; 32];
    seed[0..8].copy_from_slice(&config.seed.to_le_bytes());
    let mut rng = ChaCha12Rng::from_seed(seed);
    benchmarks(&config, &mut rng)?;

    Ok(ExitCode::SUCCESS)
}

fn benchmarks<R: Rng + CryptoRng>(config: &Config, rng: &mut R) -> eyre::Result<ExitCode> {
    tracing::info!("Sampling random Map");
    let map = get_random_map(config.num_items, rng);
    let unused_key = map.unused_key(rng);
    let used_key = map.used_key(rng);
    let unused_key =
        rep3_ring::share_ring_element_binary(RingElement(unused_key), rng)[config.network.my_id];

    let used_key =
        rep3_ring::share_ring_element_binary(RingElement(used_key), rng)[config.network.my_id];
    let r_idx = rep3::share_field_element(ark_bn254::Fr::rand(rng), rng)[config.network.my_id];
    let r_value = rep3::share_field_element(ark_bn254::Fr::rand(rng), rng)[config.network.my_id];

    tracing::info!("Sharing Map");
    let [map0, map1, map2] = map.share(rng)?;
    let mut map = match config.network.my_id {
        0 => map0,
        1 => map1,
        2 => map2,
        _ => return Err(eyre!("my_id must be 0, 1 or 2")),
    };

    tracing::info!("Starting benchmarks");
    read(&map, used_key, r_idx, config)?;
    insert_seq(&mut map, unused_key, r_idx, r_value, config, rng)?;
    insert_threads(&mut map, unused_key, r_idx, r_value, config, rng)?;
    // update(map, config, rng)?;

    Ok(ExitCode::SUCCESS)
}

fn read(
    map: &LinearScanObliviousMap,
    key: Rep3RingShare<u32>,
    randomness: Rep3PrimeFieldShare<ark_bn254::Fr>,
    config: &Config,
) -> eyre::Result<ExitCode> {
    bench_op(
        config,
        format!("Read (d=E2E, n={})", config.num_items),
        |state, net0, net1| {
            map.oblivious_read(key, net0, net1, randomness, state)?;
            Ok(())
        },
    )
}
pub fn insert_seq<R: Rng + CryptoRng>(
    map: &mut LinearScanObliviousMap,
    key: Rep3RingShare<u32>,
    r_idx: Rep3PrimeFieldShare<ark_bn254::Fr>,
    r_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    config: &Config,
    rng: &mut R,
) -> eyre::Result<ExitCode> {
    // Generate fresh random field element and secret-share locally.
    let rand_fe = ark_bn254::Fr::rand(rng);
    let shared = rep3::share_field_element(rand_fe, rng)[config.network.my_id];

    // Capture everything needed inside the closure.
    bench_op(
        config,
        format!("Insert Seq (n={})", config.num_items),
        |state, net0, net1| {
            map.oblivious_insert_seq(key, shared, net0, net1, r_idx, r_value, state)?;
            Ok(())
        },
    )
}

pub fn insert_threads<R: Rng + CryptoRng>(
    map: &mut LinearScanObliviousMap,
    key: Rep3RingShare<u32>,
    r_idx: Rep3PrimeFieldShare<ark_bn254::Fr>,
    r_value: Rep3PrimeFieldShare<ark_bn254::Fr>,
    config: &Config,
    rng: &mut R,
) -> eyre::Result<ExitCode> {
    // Generate fresh random field element and secret-share locally.
    let rand_fe = ark_bn254::Fr::rand(rng);
    let shared = rep3::share_field_element(rand_fe, rng)[config.network.my_id];

    // Capture everything needed inside the closure.
    bench_op(
        config,
        format!("Insert Threads (n={})", config.num_items),
        |state, net0, net1| {
            map.oblivious_insert_threads(key, shared, net0, net1, r_idx, r_value, state)?;
            Ok(())
        },
    )
}
pub fn bench_op<F>(config: &Config, label: impl Into<String>, mut op: F) -> eyre::Result<ExitCode>
where
    F: FnMut(&mut Rep3State, &TcpNetwork, &TcpNetwork) -> eyre::Result<()>,
{
    let label = label.into();
    let mut times = Vec::with_capacity(config.runs);
    let mut send_receive_prev = Vec::with_capacity(config.runs);
    let mut send_receive_next = Vec::with_capacity(config.runs);

    // connect once
    let [net0, net1] = TcpNetwork::networks::<2>(config.network.to_owned())?;
    // init protocol state once
    let mut state = Rep3State::new(&net0, A2BType::default())?;

    for _ in 0..config.runs {
        let stats_before0 = net0.get_connection_stats();
        let stats_before1 = net1.get_connection_stats();

        let start = Instant::now();
        op(&mut state, &net0, &net1)?;
        let duration = start.elapsed().as_micros() as f64;
        times.push(duration);

        // gather per-run network deltas
        let stats_after0 = net0.get_connection_stats();
        let stats_after1 = net1.get_connection_stats();
        let mut stats0 = stats_after0.get_diff_to(&stats_before0);
        let stats1 = stats_after1.get_diff_to(&stats_before1);

        // merge stats1 into stats0
        for (party, (sent, recv)) in stats1 {
            stats0
                .entry(party)
                .and_modify(|(s, r)| {
                    *s += sent;
                    *r += recv;
                })
                .or_insert((sent, recv));
        }

        let prev_id = state.id.prev() as usize;
        let next_id = state.id.next() as usize;

        let prev_stats = stats0
            .get(&prev_id)
            .expect("invalid party id (prev) in stats");
        let next_stats = stats0
            .get(&next_id)
            .expect("invalid party id (next) in stats");

        send_receive_prev.push(*prev_stats);
        send_receive_next.push(*next_stats);
    }

    std::thread::sleep(SLEEP);
    print_runtimes(times, config.network.my_id, &label);
    print_data(
        send_receive_next,
        config.network.my_id,
        state.id.next() as usize,
        &label,
    );
    print_data(
        send_receive_prev,
        config.network.my_id,
        state.id.prev() as usize,
        &label,
    );

    Ok(ExitCode::SUCCESS)
}
