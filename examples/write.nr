use std::{
    fs::File,
    path::{Path, PathBuf},
    process::ExitCode,
};

use ark_ff::UniformRand;
use ark_serialize::{CanonicalDeserialize as _, CanonicalSerialize as _, Validate};
use circom_types::groth16::{ConstraintMatricesWrapper, JsonPublicInput};
use clap::Parser;
use co_circom::ProvingKey;
use co_noir::Bn254;
use co_noir_to_r1cs::{noir::ultrahonk, r1cs::noir_proof_schema::NoirProofScheme};
use eyre::Context as _;
use figment::{
    Figment,
    providers::{Env, Format as _, Serialized, Toml},
};
use mpc_core::protocols::{
    rep3::{self, Rep3State, conversion::A2BType},
    rep3_ring::{self, ring::ring_impl::RingElement},
};
use mpc_net::tcp::{NetworkConfig, TcpNetwork};
use oblivious_linear_scan_map::{
    Groth16Material, LinearScanObliviousMap, ObliviousInsertRequest, ObliviousWriteResult,
};
use rand::{Rng, SeedableRng as _};
use rand_chacha::ChaCha12Rng;
use serde::{Deserialize, Serialize};

/// Prefix for config env variables
pub const CONFIG_ENV_PREFIX: &str = "TACEO_";

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

    /// Where to write the resulting proof
    #[arg(short, long)]
    pub proof_path: PathBuf,

    /// Where to write the resulting public inputs
    #[arg(short, long)]
    pub public_inputs_path: PathBuf,

    /// Path of the read proof schema
    #[arg(short, long)]
    pub read_groth16_compiled_program: PathBuf,

    /// Path of the read pk
    #[arg(short, long)]
    pub read_groth16_pk: PathBuf,

    /// Path of the read matrices
    #[arg(short, long)]
    pub read_groth16_matrices: PathBuf,

    /// Path of the write program
    #[arg(short, long)]
    pub write_groth16_compiled_program: PathBuf,

    /// Path of the write pk
    #[arg(short, long)]
    pub write_groth16_pk: PathBuf,

    /// Path of the write matrices
    #[arg(short, long)]
    pub write_groth16_matrices: PathBuf,

    /// Define deserialization mode
    #[clap(short, long)]
    pub uncompressed: bool,
}

/// Config
#[derive(Debug, Deserialize)]
pub struct Config {
    /// The number of test runs
    pub runs: usize,
    /// The seed for the RNG
    pub seed: u64,
    /// The number of elements in the map
    pub num_runs: usize,
    /// Network config
    pub network: NetworkConfig,
    /// Where to write the resulting proof
    pub proof_path: PathBuf,
    /// Where to write the resulting public inputs
    pub public_inputs_path: PathBuf,
    /// Path of the read program
    pub read_groth16_compiled_program: PathBuf,
    /// Path of the read pk
    pub read_groth16_pk: PathBuf,
    /// Path of the read matrices
    pub read_groth16_matrices: PathBuf,
    /// Path of the write program
    pub write_groth16_compiled_program: PathBuf,
    /// Path of the write pk
    pub write_groth16_pk: PathBuf,
    /// Path of the write matrices
    pub write_groth16_matrices: PathBuf,
    /// Define deserialization mode
    pub uncompressed: bool,
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

fn install_tracing() {
    use tracing_subscriber::prelude::*;
    use tracing_subscriber::{EnvFilter, fmt};

    let fmt_layer = fmt::layer().with_target(true).with_line_number(false);
    let filter_layer = EnvFilter::try_from_default_env()
        .or_else(|_| EnvFilter::try_new("bench_linear_scan=info,oblivious_linear_scan_map=debug"))
        .unwrap();

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();
}

fn load_groth16_material(
    compiled_program: impl AsRef<Path>,
    pk_path: impl AsRef<Path>,
    matrices_path: impl AsRef<Path>,
    mode: ark_serialize::Compress,
) -> eyre::Result<Groth16Material> {
    // load key material
    let pk = ProvingKey::<Bn254>::deserialize_with_mode(File::open(pk_path)?, mode, Validate::Yes)?;
    let matrices = ConstraintMatricesWrapper::<ark_bn254::Fr>::deserialize_with_mode(
        File::open(matrices_path)?,
        mode,
        Validate::Yes,
    )?
    .0;

    let compiled_program = ultrahonk::get_program_artifact(compiled_program)?;
    let proof_schema = NoirProofScheme::<ark_bn254::Fr>::from_program(compiled_program)?;
    Ok(Groth16Material::new(proof_schema, matrices, pk))
}
fn main() -> eyre::Result<ExitCode> {
    rustls::crypto::aws_lc_rs::default_provider()
        .install_default()
        .map_err(|_| eyre::eyre!("Could not install default rustls crypto provider"))?;

    let cli = Cli::parse();
    let config = Config::parse(cli).context("while parsing config")?;

    // install tracing for party ID 0
    if config.network.my_id == 0 {
        install_tracing();
    }

    let mut seed = [0u8; 32];
    seed[0..8].copy_from_slice(&config.seed.to_le_bytes());
    let mut rng = ChaCha12Rng::from_seed(seed);
    // start three nodes
    let mode = if config.uncompressed {
        ark_serialize::Compress::No
    } else {
        ark_serialize::Compress::Yes
    };

    // load key material
    let read_material = load_groth16_material(
        config.read_groth16_compiled_program,
        config.read_groth16_pk,
        config.read_groth16_matrices,
        mode,
    )?;
    let write_material = load_groth16_material(
        config.write_groth16_compiled_program,
        config.write_groth16_pk,
        config.write_groth16_matrices,
        mode,
    )?;

    // create the insert requests
    let mut requests0 = Vec::with_capacity(config.num_runs);
    let mut requests1 = Vec::with_capacity(config.num_runs);
    let mut requests2 = Vec::with_capacity(config.num_runs);
    for _ in 0..config.num_runs {
        let key = rng.r#gen::<u32>();
        let value = ark_bn254::Fr::rand(&mut rng);
        let r_key = ark_bn254::Fr::rand(&mut rng);
        let r_value = ark_bn254::Fr::rand(&mut rng);

        let key_shares = rep3_ring::share_ring_element_binary(RingElement(key), &mut rng);
        let value_shares = rep3::share_field_element(value, &mut rng);
        let r_key_shares = rep3::share_field_element(r_key, &mut rng);
        let r_value_shares = rep3::share_field_element(r_value, &mut rng);

        let insert0 = ObliviousInsertRequest {
            key: key_shares[0],
            insert_value: value_shares[0],
            randomness_index: r_key_shares[0],
            randomness_commitment: r_value_shares[0],
        };
        let insert1 = ObliviousInsertRequest {
            key: key_shares[1],
            insert_value: value_shares[1],
            randomness_index: r_key_shares[1],
            randomness_commitment: r_value_shares[1],
        };
        let insert2 = ObliviousInsertRequest {
            key: key_shares[2],
            insert_value: value_shares[2],
            randomness_index: r_key_shares[2],
            randomness_commitment: r_value_shares[2],
        };
        requests0.push(insert0);
        requests1.push(insert1);
        requests2.push(insert2);
    }

    Ok(ExitCode::SUCCESS)
}

fn run_mpc_party(
    config: Config,
    mode: ark_serialize::Compress,
    read_material: Groth16Material,
    write_material: Groth16Material,
    insert_requests: Vec<ObliviousInsertRequest>,
) -> eyre::Result<()> {
    // establish network
    let [net0, net1] = TcpNetwork::networks::<2>(config.network.to_owned())?;
    // init protocol state once
    let mut state = Rep3State::new(&net0, A2BType::default())?;
    let mut map = LinearScanObliviousMap::new(read_material, write_material);
    let mut results = Vec::with_capacity(insert_requests.len());
    for req in insert_requests {
        results.push(map.oblivious_insert(req, &net0, &net1, &mut state)?);
    }
    // Party0 writes only the last proof
    let result = results.pop().expect("is there");
    if config.network.my_id == 0 {
        let public_inputs = JsonPublicInput {
            values: result.inputs_to_vec(),
        };
        result
            .proof
            .serialize_with_mode(File::create(&config.proof_path)?, mode)?;
        tracing::info!("serialized pk to {}", config.proof_path.display());
        serde_js
    }
    Ok(())
}
