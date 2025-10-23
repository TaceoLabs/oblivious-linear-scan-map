use ark_ff::PrimeField;
use criterion::{Criterion, criterion_group, criterion_main};
use itertools::Itertools as _;
use mpc_core::protocols::{
    rep3::rngs::Rep3Rand,
    rep3_ring::{Rep3RingShare, ring::bit::Bit},
};
use oblivious_linear_scan_map::Rep3BigIntShare;

pub fn dot<F: PrimeField>(
    ohv: &[Rep3RingShare<Bit>],
    other: &[Rep3BigIntShare<F>],
    default: F::BigInt,
    rand: &mut Rep3Rand,
) -> F::BigInt {
    let mut offset = true;
    let (mut dot, dot_b) = rand.random_biguint(F::MODULUS_BIT_SIZE as usize);
    dot ^= dot_b;
    let mut dot = F::BigInt::try_from(dot).expect("Works");
    for (ohv_, other_) in ohv.iter().zip(other.iter()) {
        if ohv_.a.0.convert() {
            offset ^= true;
            dot ^= other_.a ^ other_.b;
        }
        if ohv_.b.0.convert() {
            dot ^= &other_.a;
        }
    }
    if offset {
        dot ^= default;
    }
    dot
}

fn criterion_benchmark(c: &mut Criterion) {
    let elements = [1024, 4096, 16384, 65536, 1048576];

    let seed1 = rand::random();
    let seed2 = rand::random();

    for count in elements {
        let mut rand = Rep3Rand::new(seed1, seed2);
        let lhs = (0..count)
            .map(|_| {
                let (a, b) = rand.random_elements();
                Rep3RingShare::<Bit>::new(a, b)
            })
            .collect_vec();
        let rhs = (0..count)
            .map(|_| {
                let (a, b) = rand.random_elements();
                Rep3BigIntShare::<ark_bn254::Fr>::new(a, b)
            })
            .collect_vec();

        let mut group = c.benchmark_group(format!("ele={count}"));
        if count == 1048576 {
            group.sample_size(10);
        }
        // refresh randomness
        let mut rand = Rep3Rand::new(seed1, seed2);

        let default = ark_bn254::Fr::default().into_bigint();
        group.bench_function("dot_seq", |b| {
            b.iter(|| std::hint::black_box(dot(&lhs, &rhs, default, &mut rand)))
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
