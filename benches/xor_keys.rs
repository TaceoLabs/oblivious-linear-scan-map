use ark_ff::One as _;
use criterion::{Criterion, criterion_group, criterion_main};
use itertools::Itertools;
use mpc_core::protocols::rep3_ring::{Rep3RingShare, ring::ring_impl::RingElement};
use rayon::prelude::*;

fn xor_seq(
    key: Rep3RingShare<u32>,
    total_count: usize,
    layers: &[Vec<Rep3RingShare<u32>>],
) -> Vec<Rep3RingShare<u32>> {
    let mut to_compare = Vec::with_capacity(layers[0].len() + total_count);

    // To find the element
    for layer_key in layers[0].iter() {
        to_compare.push(layer_key ^ &key);
    }
    // To find the path
    let one = RingElement::one();
    let mut key_clone = key;
    for layer in layers.iter() {
        let neighbor_key = key_clone ^ one;
        for key_ in layer.iter() {
            to_compare.push(key_ ^ &neighbor_key);
        }
        key_clone.a >>= 1;
        key_clone.b >>= 1;
    }
    to_compare
}

fn xor_rayon_join_no_par_iter(
    key: Rep3RingShare<u32>,
    total_count: usize,
    layers: &[Vec<Rep3RingShare<u32>>],
) -> Vec<Rep3RingShare<u32>> {
    // To find the element
    let (mut x, mut y) = rayon::join(
        || {
            layers[0]
                .iter()
                .map(|layer_key| layer_key ^ &key)
                .collect_vec()
        },
        || {
            // To find the path
            let mut to_compare = Vec::with_capacity(total_count);
            let one = RingElement::one();
            let mut key_clone = key;
            for layer in layers.iter() {
                let neighbor_key = key_clone ^ one;
                for key_ in layer.iter() {
                    to_compare.push(key_ ^ &neighbor_key);
                }
                key_clone.a >>= 1;
                key_clone.b >>= 1;
            }
            to_compare
        },
    );
    x.append(&mut y);
    x
}

fn xor_rayon_no_join_par_iter(
    key: Rep3RingShare<u32>,
    layers: &[Vec<Rep3RingShare<u32>>],
) -> Vec<Rep3RingShare<u32>> {
    // To find the element
    let mut a = layers[0]
        .par_iter()
        .map(|layer_key| layer_key ^ &key)
        .collect::<Vec<_>>();

    let shifted_keys = (0..layers.len())
        .map(|shift| {
            let mut key = key;
            key.a >>= shift;
            key.b >>= shift;
            key
        })
        .collect_vec();

    let one = RingElement::one();
    let mut b = (layers, shifted_keys)
        .into_par_iter()
        .flat_map(|(layer, shifted_key)| {
            let neighbor_key = shifted_key ^ one;
            layer
                .into_par_iter()
                .map(|k| k ^ &neighbor_key)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    a.append(&mut b);
    a
}

fn xor_full_rayon(
    key: Rep3RingShare<u32>,
    layers: &[Vec<Rep3RingShare<u32>>],
) -> Vec<Rep3RingShare<u32>> {
    let (mut a, mut b) = rayon::join(
        || {
            layers[0]
                .par_iter()
                .map(|layer_key| layer_key ^ &key)
                .collect::<Vec<_>>()
        },
        || {
            let shifted_keys = (0..layers.len())
                .map(|shift| {
                    let mut key = key;
                    key.a >>= shift;
                    key.b >>= shift;
                    key
                })
                .collect_vec();

            let one = RingElement::one();
            (layers, shifted_keys)
                .into_par_iter()
                .flat_map(|(layer, shifted_key)| {
                    let neighbor_key = shifted_key ^ one;
                    layer
                        .into_par_iter()
                        .map(|k| k ^ &neighbor_key)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        },
    );

    a.append(&mut b);
    a
}

fn xor_full_rayon_inner_seq(
    key: Rep3RingShare<u32>,
    layers: &[Vec<Rep3RingShare<u32>>],
) -> Vec<Rep3RingShare<u32>> {
    let (mut a, mut b) = rayon::join(
        || {
            layers[0]
                .par_iter()
                .map(|layer_key| layer_key ^ &key)
                .collect::<Vec<_>>()
        },
        || {
            let shifted_keys = (0..layers.len())
                .map(|shift| {
                    let mut key = key;
                    key.a >>= shift;
                    key.b >>= shift;
                    key
                })
                .collect_vec();

            let one = RingElement::one();
            (layers, shifted_keys)
                .into_par_iter()
                .flat_map(|(layer, shifted_key)| {
                    let neighbor_key = shifted_key ^ one;
                    layer.iter().map(|k| k ^ &neighbor_key).collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        },
    );

    a.append(&mut b);
    a
}

fn random_ring_share() -> Rep3RingShare<u32> {
    let a = RingElement::from(rand::random::<u32>());
    let b = RingElement::from(rand::random::<u32>());
    Rep3RingShare::<u32>::new_ring(a, b)
}

fn criterion_benchmark(c: &mut Criterion) {
    let elements = [1024, 4096, 16384, 65536, 1048576];

    let mut layers = Vec::with_capacity(32);

    let mut total_count = 0;
    for leaves in elements {
        let mut count = leaves;
        for _ in 0..32 {
            total_count += count;
            layers.push((0..count).map(|_| random_ring_share()).collect::<Vec<_>>());
            count >>= 1;
            if count == 0 {
                count = 1;
            }
        }
        let key = random_ring_share();
        let seq = xor_seq(key, total_count, &layers);
        let join = xor_rayon_join_no_par_iter(key, total_count, &layers);
        let par_iter = xor_rayon_no_join_par_iter(key, &layers);
        let full_rayon = xor_full_rayon(key, &layers);
        let full_rayon_inner_seq = xor_full_rayon_inner_seq(key, &layers);

        assert_eq!(seq, join);
        assert_eq!(join, par_iter);
        assert_eq!(par_iter, full_rayon);
        assert_eq!(full_rayon, full_rayon_inner_seq);
        let mut group = c.benchmark_group(format!("ele={leaves}"));
        group.bench_function("seq", |b| {
            b.iter(|| std::hint::black_box(xor_seq(key, total_count, &layers)))
        });

        group.bench_function("rayon_join", |b| {
            b.iter(|| std::hint::black_box(xor_rayon_join_no_par_iter(key, total_count, &layers)))
        });

        group.bench_function("rayon_par", |b| {
            b.iter(|| std::hint::black_box(xor_rayon_no_join_par_iter(key, &layers)))
        });

        group.bench_function("rayon_full", |b| {
            b.iter(|| std::hint::black_box(xor_full_rayon(key, &layers)))
        });

        group.bench_function("rayon_full_inner_seq", |b| {
            b.iter(|| std::hint::black_box(xor_full_rayon_inner_seq(key, &layers)))
        });
        layers.clear();
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
