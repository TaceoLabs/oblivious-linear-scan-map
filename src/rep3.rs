use std::marker::PhantomData;

use ark_ff::{One as _, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use itertools::{Itertools as _, izip};
use mpc_core::protocols::{
    rep3::{
        Rep3BigUintShare, Rep3PrimeFieldShare, Rep3State, id::PartyID, network::Rep3NetworkExt,
    },
    rep3_ring::{
        Rep3RingShare,
        ring::{bit::Bit, ring_impl::RingElement},
    },
};
use mpc_net::Network;

// TODO check out https://github.com/recmo/uint for share over F::BigInt
#[derive(Default, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Rep3BigIntShare<F: PrimeField> {
    /// Share of this party
    pub a: F::BigInt,
    /// Share of the prev party
    pub b: F::BigInt,
    pub(crate) phantom: PhantomData<F>,
}

impl<F: PrimeField> TryFrom<Rep3BigUintShare<F>> for Rep3BigIntShare<F> {
    type Error = ();

    fn try_from(value: Rep3BigUintShare<F>) -> Result<Self, Self::Error> {
        Ok(Self {
            a: value.a.try_into()?,
            b: value.b.try_into()?,
            phantom: PhantomData,
        })
    }
}

impl<F: PrimeField> Rep3BigIntShare<F> {
    pub fn zero() -> Self {
        Self {
            a: F::BigInt::default(),
            b: F::BigInt::default(),
            phantom: PhantomData,
        }
    }

    pub fn new(a: F::BigInt, b: F::BigInt) -> Self {
        Self {
            a,
            b,
            phantom: PhantomData,
        }
    }
}
impl<F: PrimeField> std::ops::BitXor<&Rep3BigIntShare<F>> for &Rep3BigIntShare<F> {
    type Output = Rep3BigIntShare<F>;

    fn bitxor(self, rhs: &Rep3BigIntShare<F>) -> Self::Output {
        Self::Output {
            a: self.a ^ rhs.a,
            b: self.b ^ rhs.b,
            phantom: PhantomData,
        }
    }
}

impl<F: PrimeField> std::ops::BitXor<&Rep3BigIntShare<F>> for Rep3BigIntShare<F> {
    type Output = Rep3BigIntShare<F>;

    fn bitxor(self, rhs: &Rep3BigIntShare<F>) -> Self::Output {
        Self::Output {
            a: self.a ^ rhs.a,
            b: self.b ^ rhs.b,
            phantom: PhantomData,
        }
    }
}

impl<F: PrimeField> std::ops::BitXorAssign<Rep3BigIntShare<F>> for Rep3BigIntShare<F> {
    fn bitxor_assign(&mut self, rhs: Rep3BigIntShare<F>) {
        self.a ^= rhs.a;
        self.b ^= rhs.b;
    }
}

macro_rules! and_fold {
    ($ele: expr, $rand: expr, $typ: ty, $bitlen: expr) => {{
        let (mut mask_a, mask_b) = $rand.rngs.rand.random_elements::<RingElement<$typ>>();
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
    ($x:expr, $state:expr, $net:expr, $t:ty, $bits:expr) => {{
        let a = $x
            .into_iter()
            .map(|v| and_fold!(v, $state, $t, $bits))
            .collect_vec();
        let b = $net.reshare_many(&a)?;
        izip!(a, b).map(|(a, b)| Rep3RingShare::<$t>::new_ring(a, b))
    }};
}

pub(crate) fn is_zero_many<N: Network>(
    mut x: Vec<Rep3RingShare<u32>>,
    net: &N,
    state: &mut Rep3State,
) -> eyre::Result<Vec<Rep3RingShare<Bit>>> {
    let one = RingElement::one();
    let mask_neg = (one << 32) - one;
    x.iter_mut().for_each(|x| *x ^= mask_neg);

    let x = fold_stage!(x, state, net, u16, 16);
    let x = fold_stage!(x, state, net, u8, 8);
    let x = fold_stage!(x, state, net, u8, 4);
    let x = fold_stage!(x, state, net, u8, 2);
    let x = fold_stage!(x, state, net, u8, 1);

    Ok(x.into_iter().map(|x| x.get_bit(0)).collect())
}

pub(crate) fn bit_inject_from_bits_to_field_many<F: PrimeField, N: Network>(
    x: &[Rep3RingShare<Bit>],
    net: &N,
    state: &mut Rep3State,
) -> eyre::Result<Vec<Rep3PrimeFieldShare<F>>> {
    let mut res_a = Vec::with_capacity(x.len());

    // Approach: Split the value into x and y and compute an arithmetic xor.
    // The multiplication in the arithmetic xor is done in a special way according to https://eprint.iacr.org/2025/919.pdf

    let res_b = match state.id {
        PartyID::ID0 => {
            for el in x.iter() {
                let x0: F = state.rngs.rand.masking_field_element();
                let y = if el.b.0.convert() {
                    F::one()
                } else {
                    F::zero()
                };

                let z0 = y * x0;
                let r0 = x0 + y - z0 - z0;
                res_a.push(r0);
            }
            // Send to P1
            net.send_next_many(&res_a)?;

            // Receive from P2
            let res_b: Vec<F> = net.recv_prev_many()?;
            if res_b.len() != x.len() {
                eyre::bail!("Received wrong number of elements");
            }
            res_b
        }
        PartyID::ID1 => {
            for el in x.iter() {
                let x1: F = state.rngs.rand.masking_field_element();
                res_a.push(if el.a.0.convert() ^ el.b.0.convert() {
                    x1 + F::one()
                } else {
                    x1
                });
            }
            // Send to P2
            net.send_next_many(&res_a)?;

            // Receive from P0
            let res_b: Vec<F> = net.recv_prev_many()?;
            if res_b.len() != x.len() {
                eyre::bail!("Received wrong number of elements");
            }
            res_b
        }
        PartyID::ID2 => {
            // Receive from P1
            let res_b: Vec<F> = net.recv_prev_many()?;
            if res_b.len() != x.len() {
                eyre::bail!("Received wrong number of elements");
            }

            for (el, x1) in izip!(x.iter(), res_b.iter()) {
                let x2: F = state.rngs.rand.masking_field_element();
                let y = if el.a.0.convert() {
                    F::one()
                } else {
                    F::zero()
                };
                let z2 = y * (*x1 + x2);
                let r2 = x2 - z2 - z2;
                res_a.push(r2);
            }

            // Send to P0
            net.send_next_many(&res_a)?;
            res_b
        }
    };

    Ok(res_a
        .into_iter()
        .zip(res_b)
        .map(|(a, b)| Rep3PrimeFieldShare::<F>::new(a, b))
        .collect())
}

#[cfg(test)]
mod tests {
    use ark_ff::{One, Zero};
    use itertools::{Itertools, izip};
    use mpc_core::protocols::{
        rep3::{Rep3State, conversion::A2BType},
        rep3_ring::{
            self,
            ring::{bit::Bit, ring_impl::RingElement},
        },
    };
    use mpc_net::local::LocalNetwork;
    use rand::Rng;

    use crate::rep3::is_zero_many;

    #[test]
    fn test_is_zero_all_zeros() {
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let elements = vec![RingElement::<u32>::zero(); 2];
        let [share0, share1, share2] =
            rep3_ring::share_ring_elements_binary(&elements, &mut rand::thread_rng());
        let [res0, res1, res2] = std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
                is_zero_many(share0, &n0, &mut state)
            });

            let res1 = s.spawn(|| {
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                is_zero_many(share1, &n1, &mut state)
            });

            let res2 = s.spawn(|| {
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                is_zero_many(share2, &n2, &mut state)
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        let result = izip!(res0, res1, res2)
            .map(|(res0, res1, res2)| rep3_ring::combine_ring_element_binary(res0, res1, res2))
            .all(|res| res == RingElement::<Bit>::one());
        assert!(result);
    }

    #[test]
    fn test_is_zero_all_non_zero() {
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let mut rng = rand::thread_rng();
        let elements = (0..1024)
            .map(|_| {
                let x = rng.r#gen::<RingElement<u32>>();
                if x.0 == 0 {
                    RingElement::<u32>::one()
                } else {
                    x
                }
            })
            .collect_vec();
        let [share0, share1, share2] =
            rep3_ring::share_ring_elements_binary(&elements, &mut rand::thread_rng());
        let [res0, res1, res2] = std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
                is_zero_many(share0, &n0, &mut state)
            });

            let res1 = s.spawn(|| {
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                is_zero_many(share1, &n1, &mut state)
            });

            let res2 = s.spawn(|| {
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                is_zero_many(share2, &n2, &mut state)
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        let result = izip!(res0, res1, res2)
            .map(|(res0, res1, res2)| rep3_ring::combine_ring_element_binary(res0, res1, res2))
            .all(|res| res == RingElement::<Bit>::zero());
        assert!(result);
    }

    #[test]
    fn test_is_zero_one_zero() {
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let mut rng = rand::thread_rng();
        let mut elements = (0..1024)
            .map(|_| {
                let x = rng.r#gen::<RingElement<u32>>();
                if x.0 == 0 {
                    RingElement::<u32>::one()
                } else {
                    x
                }
            })
            .collect_vec();
        elements[42] = RingElement::<u32>::zero();
        let [share0, share1, share2] =
            rep3_ring::share_ring_elements_binary(&elements, &mut rand::thread_rng());
        let [res0, res1, res2] = std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
                is_zero_many(share0, &n0, &mut state)
            });

            let res1 = s.spawn(|| {
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                is_zero_many(share1, &n1, &mut state)
            });

            let res2 = s.spawn(|| {
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                is_zero_many(share2, &n2, &mut state)
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        // the ring element on 42 should be one
        let mut should_result = vec![RingElement::<Bit>::zero(); 1024];
        should_result[42] = RingElement::<Bit>::one();
        let is_result = izip!(res0, res1, res2)
            .map(|(res0, res1, res2)| rep3_ring::combine_ring_element_binary(res0, res1, res2))
            .collect_vec();
        assert_eq!(is_result, should_result);
    }
}
