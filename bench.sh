ARGS="--seed 0 --runs 5 --num-items 100000"

cargo run --release --features="local" --example bench-linear-scan -- --config ./examples/configs/party2.toml $ARGS &
cargo run --release --features="local" --example bench-linear-scan -- --config ./examples/configs/party3.toml $ARGS & 
cargo run --release --features="local" --example bench-linear-scan -- --config ./examples/configs/party1.toml $ARGS