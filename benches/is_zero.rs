use ark_ff::{One as _, Zero as _};
use criterion::{Criterion, criterion_group, criterion_main};
use itertools::{Itertools, izip};
use mpc_core::protocols::{
    rep3::rngs::Rep3Rand,
    rep3_ring::{
        Rep3RingShare,
        ring::{bit::Bit, ring_impl::RingElement},
    },
};
use rayon::prelude::*;

const BITLEN: usize = 32;

macro_rules! and_fold {
    ($ele: expr, $rand: expr, $typ: ty, $bitlen: expr) => {{
        let (mut mask_a, mask_b) = $rand.random_elements::<RingElement<$typ>>();
        mask_a ^= mask_b;
        let y_a = $ele.a >> $bitlen;
        let y_b = $ele.b >> $bitlen;
        mask_a ^= RingElement::<$typ>::from(($ele.a & y_a).convert() as $typ);
        mask_a ^= RingElement::<$typ>::from(($ele.b & y_a).convert() as $typ);
        mask_a ^= RingElement::<$typ>::from(($ele.a & y_b).convert() as $typ);
        mask_a
    }};
}

macro_rules! fold_stage {
    ($x:expr, $state:expr,  $t:ty, $bits:expr) => {{
        let a = $x
            .into_iter()
            .map(|v| and_fold!(v, $state, $t, $bits))
            .collect_vec();
        let b = a.clone();
        izip!(a, b).map(|(a, b)| Rep3RingShare::<$t>::new_ring(a, b))
    }};
}

pub(crate) fn is_zero_many_folded(
    mut x: Vec<Rep3RingShare<u32>>,
    state: &mut Rep3Rand,
) -> Vec<Rep3RingShare<Bit>> {
    let one = RingElement::one();
    let mask_neg = (one << 32) - one;
    x.iter_mut().for_each(|x| *x ^= mask_neg);

    let x = fold_stage!(x, state, u16, 16);
    let x = fold_stage!(x, state, u8, 8);
    let x = fold_stage!(x, state, u8, 4);
    let x = fold_stage!(x, state, u8, 2);
    let x = fold_stage!(x, state, u8, 1);

    x.into_iter().map(|x| x.get_bit(0)).collect()
}

fn is_zero_seq(mut x: Vec<Rep3RingShare<u32>>, rand: &mut Rep3Rand) -> Vec<Rep3RingShare<Bit>> {
    let one = RingElement::one();
    let mask = (one << BITLEN) - one;

    for x_ in x.iter_mut() {
        *x_ ^= &mask; // Negate bits
    }

    let mut local_a = vec![RingElement::zero(); x.len()];

    let mut len = BITLEN;
    while len > 1 {
        if len % 2 == 1 {
            for x in x.iter_mut() {
                x.a.0 |= 1 << len;
                x.b.0 |= 1 << len;
            }
            len += 1;
        }
        len /= 2;

        // Optimized and_vec_inplace
        for (x, a) in x.iter_mut().zip(local_a.iter_mut()) {
            let (mut mask_a, mask_b) = rand.random_elements::<RingElement<u32>>();
            mask_a ^= mask_b;
            let y_a = x.a >> len;
            let y_b = x.b >> len;
            mask_a ^= x.a & y_a;
            mask_a ^= x.b & y_a;
            mask_a ^= x.a & y_b;
            *a = mask_a;
            x.a = mask_a;
        }
        let local_b = local_a.clone();
        izip!(x.iter_mut(), local_b).for_each(|(a, b)| a.b = b);
    }
    // extract LSB
    x.into_iter().map(|x| x.get_bit(0)).collect_vec()
}

fn is_zero_par_iter_all(
    mut x: Vec<Rep3RingShare<u32>>,
    rand: &mut Rep3Rand,
) -> Vec<Rep3RingShare<Bit>> {
    let one = RingElement::one();
    let mask = (one << BITLEN) - one;

    x.par_iter_mut().for_each(|x| {
        *x ^= mask;
    });

    let mut local_a = vec![RingElement::zero(); x.len()];

    let mut len = BITLEN;
    while len > 1 {
        if len % 2 == 1 {
            x.par_iter_mut().for_each(|x| {
                x.a.0 |= 1 << len;
                x.b.0 |= 1 << len;
            });
            len += 1;
        }
        len /= 2;

        let masks = (0..x.len())
            .map(|_| rand.random_elements::<RingElement<u32>>())
            .collect_vec();
        (
            x.par_iter_mut(),
            local_a.par_iter_mut(),
            masks.into_par_iter(),
        )
            .into_par_iter()
            .for_each(|(x, a, (mut mask_a, mask_b))| {
                mask_a ^= mask_b;
                let y_a = x.a >> len;
                let y_b = x.b >> len;
                mask_a ^= x.a & y_a;
                mask_a ^= x.b & y_a;
                mask_a ^= x.a & y_b;
                *a = mask_a;
                x.a = mask_a;
            });

        let local_b = local_a.clone();
        (x.par_iter_mut(), local_b)
            .into_par_iter()
            .for_each(|(a, b)| a.b = b);
    }
    // extract LSB
    x.into_par_iter().map(|x| x.get_bit(0)).collect()
}

fn is_zero_par_iter_min_len(
    mut x: Vec<Rep3RingShare<u32>>,
    rand: &mut Rep3Rand,
) -> Vec<Rep3RingShare<Bit>> {
    let one = RingElement::one();
    let mask = (one << BITLEN) - one;

    x.par_iter_mut().with_min_len(512).for_each(|x| {
        *x ^= mask;
    });

    let mut local_a = vec![RingElement::zero(); x.len()];

    let mut len = BITLEN;
    while len > 1 {
        if len % 2 == 1 {
            x.par_iter_mut().with_min_len(512).for_each(|x| {
                x.a.0 |= 1 << len;
                x.b.0 |= 1 << len;
            });
            len += 1;
        }
        len /= 2;

        let masks = (0..x.len())
            .map(|_| rand.random_elements::<RingElement<u32>>())
            .collect_vec();
        (
            x.par_iter_mut(),
            local_a.par_iter_mut(),
            masks.into_par_iter(),
        )
            .into_par_iter()
            .with_min_len(512)
            .for_each(|(x, a, (mut mask_a, mask_b))| {
                mask_a ^= mask_b;
                let y_a = x.a >> len;
                let y_b = x.b >> len;
                mask_a ^= x.a & y_a;
                mask_a ^= x.b & y_a;
                mask_a ^= x.a & y_b;
                *a = mask_a;
                x.a = mask_a;
            });

        let local_b = local_a.clone();
        (x.par_iter_mut(), local_b)
            .into_par_iter()
            .with_min_len(512)
            .for_each(|(a, b)| a.b = b);
    }
    // extract LSB
    x.into_par_iter()
        .with_min_len(512)
        .map(|x| x.get_bit(0))
        .collect()
}

fn criterion_benchmark(c: &mut Criterion) {
    let elements = [1024, 4096, 16384, 65536, 1048576];

    let seed1 = rand::random();
    let seed2 = rand::random();

    for count in elements {
        let mut rand = Rep3Rand::new(seed1, seed2);
        let x = (0..count)
            .map(|_| {
                let (a, b) = rand.random_elements();
                Rep3RingShare::new(a, b)
            })
            .collect_vec();

        let mut group = c.benchmark_group(format!("ele={count}"));
        if count == 1048576 {
            group.sample_size(10);
        }
        // refresh randomness
        let mut rand = Rep3Rand::new(seed1, seed2);
        let seq = is_zero_seq(x.clone(), &mut rand);
        let mut rand = Rep3Rand::new(seed1, seed2);
        let par_iter_current = is_zero_par_iter_all(x.clone(), &mut rand);
        let mut rand = Rep3Rand::new(seed1, seed2);
        let par_iter_min_len = is_zero_par_iter_min_len(x.clone(), &mut rand);
        let mut rand = Rep3Rand::new(seed1, seed2);
        let set_for_u32 = is_zero_many_folded(x.clone(), &mut rand);

        assert_eq!(seq, par_iter_current);
        assert_eq!(par_iter_current, par_iter_min_len);
        assert_eq!(par_iter_min_len, set_for_u32);

        group.bench_function("seq", |b| {
            b.iter_batched(
                || x.clone(),
                |x| std::hint::black_box(is_zero_seq(x, &mut rand)),
                criterion::BatchSize::LargeInput,
            )
        });

        group.bench_function("par_iter all", |b| {
            b.iter_batched(
                || x.clone(),
                |x| std::hint::black_box(is_zero_par_iter_all(x, &mut rand)),
                criterion::BatchSize::LargeInput,
            )
        });

        group.bench_function("par_iter all min len", |b| {
            b.iter_batched(
                || x.clone(),
                |x| std::hint::black_box(is_zero_par_iter_min_len(x, &mut rand)),
                criterion::BatchSize::LargeInput,
            )
        });

        group.bench_function("set_for_u32", |b| {
            b.iter_batched(
                || x.clone(),
                |x| std::hint::black_box(is_zero_many_folded(x, &mut rand)),
                criterion::BatchSize::LargeInput,
            )
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
