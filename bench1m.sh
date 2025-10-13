cargo build --release --example bench-linear-scan

ARGS="--seed 0 --runs 5 --num-items 1000000"

cargo run --release --example bench-linear-scan -- --config ./examples/configs/party1.toml $ARGS &
cargo run --release --example bench-linear-scan -- --config ./examples/configs/party2.toml $ARGS &
cargo run --release --example bench-linear-scan -- --config ./examples/configs/party3.toml $ARGS
