[private]
default:
    @just --justfile {{justfile()}} --list --list-heading $'Project commands:\n'

[group: 'ci']
lint:
    cargo fmt --all -- --check
    cargo clippy --workspace --tests --examples --benches --bins -q -- -D warnings
    RUSTDOCFLAGS='-D warnings' cargo doc --workspace -q --no-deps --document-private-items

[group: 'ci']
unit-tests:
    cargo test --release --all-features --lib

[group: 'ci']
check-pr: lint unit-tests
    

[group: 'noir']
[working-directory: 'noir/oblivious_map_read']
recompile-read-circuit:
    nargo compile --expression-width=1000 --bounded-codegen
    mv target/oblivious_map_read.json ../compiled_circuits/oblivious_map_read.json

[group: 'noir']
[working-directory: 'noir/oblivious_map_write']
recompile-write-circuit:
    nargo compile --expression-width=1000 --bounded-codegen
    mv target/oblivious_map_write.json ../compiled_circuits/oblivious_map_write.json

[group: 'noir']
recompile-noir-circuits: recompile-write-circuit recompile-read-circuit
