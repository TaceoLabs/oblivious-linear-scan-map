cargo build --release --bin bench

ARGS="--seed 0 --runs 5 --num-items 1000000"

cargo run --release --bin bench_linear_scan -- --config ./configs/party1.toml $ARGS &
cargo run --release --bin bench_linear_scan -- --config ./configs/party2.toml $ARGS &
cargo run --release --bin bench_linear_scan -- --config ./configs/party3.toml $ARGS
