use eyre::Context;
use itertools::izip;
use mpc_core::protocols::rep3::network::Rep3NetworkExt;

use crate::{LINEAR_SCAN_TREE_DEPTH, ObliviousLayer, base::MapBase};

struct OpenedBitStream {
    a: Vec<u64>,
    b: Vec<u64>,
    other: Vec<u64>,
    counter: usize,
}

impl Iterator for OpenedBitStream {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        // which index
        let idx = self.counter / 64;
        let shift = self.counter % 64;
        let a = (self.a[idx] >> shift) & 1;
        let b = (self.b[idx] >> shift) & 1;
        let c = (self.other[idx] >> shift) & 1;
        self.counter += 1;
        Some(a ^ b ^ c == 1)
    }
}

impl OpenedBitStream {
    fn new(a: Vec<u64>, b: Vec<u64>, other: Vec<u64>) -> eyre::Result<Self> {
        if a.len() != other.len() {
            eyre::bail!("did not receive correct length from peer")
        }
        Ok(Self {
            a,
            b,
            other,
            counter: 0,
        })
    }
}

impl MapBase {
    pub(super) fn prune<N: Rep3NetworkExt>(&mut self, net: &N) -> eyre::Result<()> {
        // 1) Open all bits that mark a value as used or not and batch them in u64
        let shift = LINEAR_SCAN_TREE_DEPTH - 1;
        // u128 doesn't implement canonical deserialize
        let mut batch_a = 0_u64;
        let mut batch_b = 0_u64;
        let mut current_shift = 0;
        let mut duplicate_a = Vec::with_capacity(self.total_count.div_ceil(64));
        let mut duplicate_b = Vec::with_capacity(self.total_count.div_ceil(64));
        for layer in self.layers.iter().skip(1) {
            for key in layer.keys.iter() {
                let used_bit_a = u64::from(key.a.convert()) >> shift;
                let used_bit_b = u64::from(key.b.convert()) >> shift;
                batch_a |= used_bit_a << current_shift;
                batch_b |= used_bit_b << current_shift;
                current_shift += 1;
                if current_shift == 64 {
                    duplicate_a.push(batch_a);
                    duplicate_b.push(batch_b);
                    batch_a = 0;
                    batch_b = 0;
                    current_shift = 0;
                }
            }
        }
        if current_shift != 0 {
            duplicate_a.push(batch_a);
            duplicate_b.push(batch_b);
        }

        // 2) Reshare to open bits
        let other_bits = net
            .reshare_many(&duplicate_b)
            .context("while opening duplicate bits")?;

        // 3) Read the bits back from the batch
        let mut opened_bit_stream = OpenedBitStream::new(duplicate_a, duplicate_b, other_bits)?;

        // 4) Create new layers
        let mut pruned = std::array::from_fn(|_| ObliviousLayer::default());
        // leaf layer is never duplicate
        std::mem::swap(&mut pruned[0].keys, &mut self.layers[0].keys);
        std::mem::swap(&mut pruned[0].values, &mut self.layers[0].values);
        let mut total_count = 0;
        for (idx, old_layer) in self.layers.iter().enumerate().skip(1) {
            for (key, value) in izip!(old_layer.keys.iter(), old_layer.values.iter()) {
                // 5) if the opened bit is 0, we add the current value back in the tree
                if !opened_bit_stream.next().expect("must be some") {
                    total_count += 1;
                    pruned[idx].keys.push(*key);
                    pruned[idx].values.push(*value);
                }
            }
        }
        // 6) Set the new values and new total count. The amount of leaf values stay the same.
        self.layers = pruned;
        self.total_count = total_count;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use co_noir_to_r1cs::noir::r1cs;
    use itertools::izip;
    use mpc_core::protocols::{
        rep3::{self, Rep3State, conversion::A2BType},
        rep3_ring::{self, ring::ring_impl::RingElement},
    };
    use mpc_net::local::LocalNetwork;

    use crate::{
        LinearScanObliviousMap, ObliviousInsertRequest, ObliviousReadRequest,
        tests::groth16_material,
    };
    #[test]
    fn prune_empty_map() -> eyre::Result<()> {
        // need two networks
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());

        let material0 = groth16_material()?;
        let material1 = material0.clone();
        let material2 = material0.clone();

        std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let (read_groth16, write_groth16) = material0;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                map.prune(&n0)?;
                assert_eq!(map.total_count(), 0);
                assert_eq!(map.leaf_count(), 0);
                for l in map.inner.layers {
                    assert!(l.keys.is_empty());
                    assert!(l.values.is_empty());
                }
                eyre::Ok(())
            });

            let res1 = s.spawn(|| {
                let (read_groth16, write_groth16) = material1;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                map.prune(&n1)?;
                assert_eq!(map.total_count(), 0);
                assert_eq!(map.leaf_count(), 0);
                for l in map.inner.layers {
                    assert!(l.keys.is_empty());
                    assert!(l.values.is_empty());
                }
                eyre::Ok(())
            });

            let res2 = s.spawn(|| {
                let (read_groth16, write_groth16) = material2;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                map.prune(&n2)?;
                assert_eq!(map.total_count(), 0);
                assert_eq!(map.leaf_count(), 0);
                for l in map.inner.layers {
                    assert!(l.keys.is_empty());
                    assert!(l.values.is_empty());
                }
                eyre::Ok(())
            });
            res0.join().expect("can join").expect("did work");
            res1.join().expect("can join").expect("did work");
            res2.join().expect("can join").expect("did work");
        });

        Ok(())
    }

    #[test]
    fn prune_after_inserts() -> eyre::Result<()> {
        const INSERTS: usize = 5;

        let mut rng = rand::thread_rng();
        // need two networks
        let [n0, n1, n2] = LocalNetwork::new_3_parties();
        let [n3, n4, n5] = LocalNetwork::new_3_parties();
        let random_default_value = ark_bn254::Fr::from(rand::random::<u128>());

        // generate a random key/values
        let mut keys = Vec::with_capacity(INSERTS);
        let mut values = Vec::with_capacity(INSERTS);
        let mut rands = Vec::with_capacity(INSERTS);
        // keys so that we have top most three layers and some random value
        for key in [1073741823, 2147483647, 3221225471, 4294967295, 0x42] {
            keys.push(RingElement(key));
            values.push(ark_bn254::Fr::from(rand::random::<u128>()));
            rands.push(ark_bn254::Fr::from(rand::random::<u128>()));
        }

        let [key_share0, key_share1, key_share2] =
            rep3_ring::share_ring_elements_binary(&keys, &mut rng);
        let [value_share0, value_share1, value_share2] =
            rep3::share_field_elements(&values, &mut rng);
        let [rand_share0, rand_share1, rand_share2] = rep3::share_field_elements(&rands, &mut rng);

        let material0 = groth16_material()?;
        let material1 = material0.clone();
        let material2 = material0.clone();
        let read_vk = material0.0.pk.vk.clone();

        let [reads0, reads1, reads2] = std::thread::scope(|s| {
            let res0 = s.spawn(|| {
                let (read_groth16, write_groth16) = material0;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n0, A2BType::Direct).expect("works");
                for (key, insert_value, r) in
                    izip!(key_share0.clone(), value_share0, rand_share0.clone())
                {
                    let insert_req = ObliviousInsertRequest {
                        key,
                        insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    map.oblivious_insert(insert_req, &n0, &n3, &mut state)?;
                }
                // prune the tree
                map.prune(&n0)?;

                // check the values and layers - then read
                // assert_eq!(map.total_count(), 12);
                assert_eq!(map.leaf_count(), 5);
                assert_eq!(map.inner.layers[31].keys.len(), 2);
                assert_eq!(map.inner.layers[31].values.len(), 2);
                assert_eq!(map.inner.layers[30].keys.len(), 4);
                assert_eq!(map.inner.layers[30].values.len(), 4);
                for layer in map.inner.layers.iter().rev().skip(2) {
                    assert_eq!(layer.keys.len(), 5);
                    assert_eq!(layer.values.len(), 5);
                }

                let mut reads = Vec::with_capacity(INSERTS);
                // read all values
                for (key, r) in izip!(key_share0, rand_share0) {
                    let read_req = ObliviousReadRequest {
                        key,
                        randomness_commitment: r,
                    };
                    reads.push(map.oblivious_read(read_req, &n0, &n3, &mut state)?);
                }

                eyre::Ok(reads)
            });

            let res1 = s.spawn(|| {
                let (read_groth16, write_groth16) = material1;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n1, A2BType::Direct).expect("works");
                for (key, insert_value, r) in
                    izip!(key_share1.clone(), value_share1, rand_share1.clone())
                {
                    let insert_req = ObliviousInsertRequest {
                        key,
                        insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    map.oblivious_insert(insert_req, &n1, &n4, &mut state)?;
                }
                // prune the tree
                map.prune(&n1)?;

                // check the values and layers - then read
                // assert_eq!(map.total_count(), 12);
                assert_eq!(map.leaf_count(), 5);
                assert_eq!(map.inner.layers[31].keys.len(), 2);
                assert_eq!(map.inner.layers[31].values.len(), 2);
                assert_eq!(map.inner.layers[30].keys.len(), 4);
                assert_eq!(map.inner.layers[30].values.len(), 4);
                for layer in map.inner.layers.iter().rev().skip(2) {
                    assert_eq!(layer.keys.len(), 5);
                    assert_eq!(layer.values.len(), 5);
                }

                let mut reads = Vec::with_capacity(INSERTS);
                // read all values
                for (key, r) in izip!(key_share1, rand_share1) {
                    let read_req = ObliviousReadRequest {
                        key,
                        randomness_commitment: r,
                    };
                    reads.push(map.oblivious_read(read_req, &n1, &n4, &mut state)?);
                }

                eyre::Ok(reads)
            });

            let res2 = s.spawn(|| {
                let (read_groth16, write_groth16) = material2;
                let mut map = LinearScanObliviousMap::with_default_value(
                    random_default_value,
                    read_groth16,
                    write_groth16,
                );
                let mut state = Rep3State::new(&n2, A2BType::Direct).expect("works");
                for (key, insert_value, r) in
                    izip!(key_share2.clone(), value_share2, rand_share2.clone())
                {
                    let insert_req = ObliviousInsertRequest {
                        key,
                        insert_value,
                        randomness_index: r,
                        randomness_commitment: r,
                    };
                    map.oblivious_insert(insert_req, &n2, &n5, &mut state)?;
                }

                // prune the tree
                map.prune(&n2)?;

                // check the values and layers - then read
                // assert_eq!(map.total_count(), 12);
                assert_eq!(map.leaf_count(), 5);
                assert_eq!(map.inner.layers[31].keys.len(), 2);
                assert_eq!(map.inner.layers[31].values.len(), 2);
                assert_eq!(map.inner.layers[30].keys.len(), 4);
                assert_eq!(map.inner.layers[30].values.len(), 4);
                for layer in map.inner.layers.iter().rev().skip(2) {
                    assert_eq!(layer.keys.len(), 5);
                    assert_eq!(layer.values.len(), 5);
                }

                let mut reads = Vec::with_capacity(INSERTS);
                // read all values
                for (key, r) in izip!(key_share2, rand_share2) {
                    let read_req = ObliviousReadRequest {
                        key,
                        randomness_commitment: r,
                    };
                    reads.push(map.oblivious_read(read_req, &n2, &n5, &mut state)?);
                }

                eyre::Ok(reads)
            });
            let res0 = res0.join().expect("can join").expect("did work");
            let res1 = res1.join().expect("can join").expect("did work");
            let res2 = res2.join().expect("can join").expect("did work");
            [res0, res1, res2]
        });

        for (r0, r1, r2, should_read) in izip!(reads0, reads1, reads2, values) {
            let is_read = r0.read.a + r1.read.a + r2.read.a;
            assert_eq!(is_read, should_read);

            assert!(r1cs::verify(
                &read_vk,
                &r0.proof,
                &[r0.root, r0.commitment]
            )?);
            assert!(r1cs::verify(
                &read_vk,
                &r1.proof,
                &[r1.root, r1.commitment]
            )?);
            assert!(r1cs::verify(
                &read_vk,
                &r2.proof,
                &[r2.root, r2.commitment]
            )?);
        }

        Ok(())
    }
}
