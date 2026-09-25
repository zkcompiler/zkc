//! Actual upstream PCS, independent verification, original custody and Lean fixtures.
mod common;
use ark_ff::Field;
use ark_std::rand::{SeedableRng, rngs::StdRng};
use common::{bounds, keys, scalars};
use zkc_arkworks::{Bounds, Error, Keys, RandomSource, Scalar, Table, VerifierKey, parse_decimal};

#[test]
fn two_originals_shared_keys_delayed_open_and_table_free_verifier() {
    for n in 1..=7 {
        let keys = keys(n, 91);
        let vk_bytes = keys.verifier_key().to_bytes(&bounds()).unwrap();
        let pin = keys.verifier_key().metadata().key_id();
        let point: Vec<_> = (0..n).map(|i| Scalar::from(19 + i as u64 * 7)).collect();
        let originals: Vec<_> = (0..2)
            .map(|factor| {
                let values: Vec<_> = (0..1usize << n)
                    .map(|i| Scalar::from((i * i + 3 * i + 5 + factor * 17) as u64))
                    .collect();
                let table = Table::from_logical_vec(values, &bounds()).unwrap();
                keys.prover_key().commit(&table).unwrap()
            })
            .collect();
        let mut a = originals[0].original().clone();
        let mut b = originals[1].original().clone();
        let mut claim = a.product_boolean_sum(&b).unwrap();
        for r in &point {
            let q = a.round_product(&b).unwrap();
            assert_eq!(q[0] + q[0] + q[1] + q[2], claim);
            a = a.restrict_first(*r).unwrap();
            b = b.restrict_first(*r).unwrap();
            claim = q[0] + *r * (q[1] + *r * q[2]);
        }
        let mut packets = Vec::new();
        for original in &originals {
            let before = original.original().to_logical_bytes(&bounds()).unwrap();
            assert!(original.open(&point[..n - 1]).is_err());
            let clone = original.clone();
            let (value, proof) = clone.open(&point).unwrap();
            let repeat = original.open(&point).unwrap();
            assert_eq!(
                proof.to_bytes(&bounds()).unwrap(),
                repeat.1.to_bytes(&bounds()).unwrap()
            );
            assert_eq!(
                before,
                original.original().to_logical_bytes(&bounds()).unwrap()
            );
            packets.push((
                original.commitment().to_bytes(&bounds()).unwrap(),
                value,
                proof.to_bytes(&bounds()).unwrap(),
            ));
        }
        assert_eq!(claim, packets[0].1 * packets[1].1);
        drop(originals);
        drop(keys);
        drop(a);
        drop(b);
        // This role function can only receive public bytes, point, values and pin.
        fn verify(
            vk_bytes: &[u8],
            pin: [u8; 32],
            p: &[Scalar],
            packets: &[(Vec<u8>, Scalar, Vec<u8>)],
        ) {
            let vk = VerifierKey::from_bytes(vk_bytes, pin, &bounds()).unwrap();
            for (c, v, proof) in packets {
                let c = vk.decode_commitment(c, &bounds()).unwrap();
                let proof = vk.decode_proof(proof, &bounds()).unwrap();
                assert!(vk.check(&c, p, *v, &proof).unwrap());
                assert!(!vk.check(&c, p, *v + Scalar::ONE, &proof).unwrap());
            }
        }
        verify(&vk_bytes, pin, &point, &packets);
    }
}

#[test]
fn wrong_key_shape_point_commitment_and_opening_are_nonacceptance() {
    let k = keys(2, 3);
    let foreign = keys(2, 4);
    let other_arity = keys(1, 3);
    let t = Table::from_logical(&scalars(&[2, 3, 5, 7]), &bounds()).unwrap();
    let u = Table::from_logical(&scalars(&[11, 13, 17, 19]), &bounds()).unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    let d = k.prover_key().commit(&u).unwrap();
    let p = scalars(&[29, 31]);
    let (v, proof) = c.open(&p).unwrap();
    let vk = k.verifier_key();
    assert!(!vk.check(d.commitment(), &p, v, &proof).unwrap());
    assert!(
        !vk.check(c.commitment(), &scalars(&[31, 29]), v, &proof)
            .unwrap()
    );
    assert!(
        !vk.check(c.commitment(), &p, v, &d.open(&p).unwrap().1)
            .unwrap()
    );
    assert_eq!(
        foreign.verifier_key().check(c.commitment(), &p, v, &proof),
        Err(Error::KeyMismatch)
    );
    for point in [vec![], scalars(&[29]), scalars(&[29, 31, 0])] {
        assert!(vk.check(c.commitment(), &point, v, &proof).is_err());
        assert!(c.open(&point).is_err());
    }
    assert!(other_arity.prover_key().commit(&t).is_err());
    let constant = Table::from_logical(&scalars(&[2]), &bounds()).unwrap();
    assert!(k.prover_key().commit(&constant).is_err());
    assert_ne!(
        k.verifier_key().metadata().setup_id(),
        foreign.verifier_key().metadata().setup_id()
    );
    assert_ne!(
        k.verifier_key().metadata().key_id(),
        foreign.verifier_key().metadata().key_id()
    );
    assert_eq!(keys(2, 3).verifier_key().metadata(), vk.metadata());
}

#[test]
fn setup_bounds_fail_before_rng_consumption() {
    let mut rng = StdRng::from_seed([8; 32]);
    let snapshot = rng.clone();
    for (n, policy, error) in [
        (0, bounds(), Error::PositiveArityRequired),
        (2, Bounds::new(1, 4, 10000, 100), Error::ArityLimit),
        (2, Bounds::new(2, 3, 10000, 100), Error::ElementLimit),
        (2, Bounds::new(2, 4, 10000, 7), Error::SetupLimit),
        (2, Bounds::new(2, 4, 1, 100), Error::ByteLimit),
        (
            usize::BITS as usize,
            Bounds::new(usize::MAX, usize::MAX, usize::MAX, usize::MAX),
            Error::CapacityOverflow,
        ),
    ] {
        assert_eq!(
            Keys::setup_with_rng(n, &mut rng, &policy).unwrap_err(),
            error
        );
        assert_eq!(rng, snapshot);
    }
}

#[test]
fn canonical_infinity_is_valid_for_zero_polynomials_and_quotients() {
    let k = keys(2, 61);
    let p = scalars(&[8, 9]);
    for values in [scalars(&[0, 0, 0, 0]), scalars(&[7, 7, 7, 7])] {
        let t = Table::from_logical(&values, &bounds()).unwrap();
        let c = k.prover_key().commit(&t).unwrap();
        let (v, proof) = c.open(&p).unwrap();
        let vk = k.verifier_key();
        let c = vk
            .decode_commitment(&c.commitment().to_bytes(&bounds()).unwrap(), &bounds())
            .unwrap();
        let proof = vk
            .decode_proof(&proof.to_bytes(&bounds()).unwrap(), &bounds())
            .unwrap();
        assert!(vk.check(&c, &p, v, &proof).unwrap());
    }
}

#[test]
fn os_entropy_setup_and_challenges_execute_real_upstream() {
    let k = Keys::setup_for_development(2, &bounds()).unwrap();
    let mut source = RandomSource::from_os().unwrap();
    let p = source.point(2, &bounds()).unwrap();
    let t = Table::from_logical(&scalars(&[1, 2, 3, 5]), &bounds()).unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    let (v, proof) = c.open(&p).unwrap();
    assert!(
        k.verifier_key()
            .check(c.commitment(), &p, v, &proof)
            .unwrap()
    );
    assert_eq!(source.point(0, &bounds()).unwrap().len(), 0);
    assert_eq!(source.point(11, &bounds()).unwrap_err(), Error::ArityLimit);
    assert_eq!(
        source.point(2, &Bounds::new(2, 4, 63, 10)).unwrap_err(),
        Error::ByteLimit
    );
}

#[cfg(feature = "test-utils")]
#[test]
fn deterministic_randomness_is_explicit_and_failed_admission_does_not_draw() {
    let mut a = RandomSource::for_testing([47; 32]);
    let mut b = RandomSource::for_testing([47; 32]);
    assert!(a.point(11, &bounds()).is_err());
    assert!(a.point(2, &Bounds::new(2, 4, 63, 10)).is_err());
    for _ in 0..32 {
        assert_eq!(a.scalar(), b.scalar());
    }
}

#[test]
fn aliases_remain_live_across_threads_and_owner_drops() {
    fn send_sync<T: Send + Sync>() {}
    send_sync::<zkc_arkworks::CommittedTable>();
    let k = keys(3, 9);
    let t = Table::from_logical(&scalars(&[1, 2, 3, 5, 8, 13, 21, 34]), &bounds()).unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    let vk = k.verifier_key().clone();
    let bytes = c.commitment().to_bytes(&bounds()).unwrap();
    let alias = c.clone();
    drop(t);
    drop(k);
    let thread = std::thread::spawn(move || {
        let scratch = alias.original().restrict_first(Scalar::from(8u64)).unwrap();
        assert_eq!(scratch.arity(), 2);
        alias.open(&scalars(&[2, 3, 5])).unwrap()
    });
    assert!(c.open(&[]).is_err());
    drop(c);
    let (v, p) = thread.join().unwrap();
    let commitment = vk.decode_commitment(&bytes, &bounds()).unwrap();
    assert!(vk.check(&commitment, &scalars(&[2, 3, 5]), v, &p).unwrap());
}

#[test]
fn recorded_lean_coordinate_oracle_all_rounds_and_openings() {
    fn row(lines: &mut std::str::Lines<'_>, label: &str) -> Vec<Scalar> {
        let mut words = lines.next().unwrap().split_whitespace();
        assert_eq!(words.next(), Some(label));
        words.map(|v| parse_decimal(v).unwrap()).collect()
    }
    let fixture = include_str!("fixtures/coordinate-layout.txt");
    let mut lines = fixture.lines();
    let (mut cases, mut rounds, mut controls) = (0, 0, 0);
    while let Some(header) = lines.next() {
        let words: Vec<_> = header.split_whitespace().collect();
        assert_eq!(words[0], "CASE");
        let n: usize = words[1].parse().unwrap();
        let a = row(&mut lines, "A");
        let b = row(&mut lines, "B");
        let p = row(&mut lines, "R");
        let sum = row(&mut lines, "S");
        let k = keys(n, 81);
        let original_a = Table::from_logical(&a, &bounds()).unwrap();
        let original_b = Table::from_logical(&b, &bounds()).unwrap();
        let committed_a = k.prover_key().commit(&original_a).unwrap();
        let committed_b = k.prover_key().commit(&original_b).unwrap();
        let mut ta = original_a.clone();
        let mut tb = original_b.clone();
        assert_eq!(ta.product_boolean_sum(&tb).unwrap(), sum[0]);
        for (round, r) in p.iter().enumerate() {
            let q = row(&mut lines, "Q");
            assert_eq!(ta.round_product(&tb).unwrap().as_slice(), q);
            if round == 0 && n >= 2 {
                // Feed an inverse-permuted logical input: its backend storage
                // is the original unpermuted vector, reproducing the old defect.
                let permute = |v: &[Scalar]| -> Vec<Scalar> {
                    (0..v.len())
                        .map(|j| v[j.reverse_bits() >> (usize::BITS as usize - n)])
                        .collect()
                };
                let wrong_a = Table::from_logical(&permute(&a), &bounds()).unwrap();
                let wrong_b = Table::from_logical(&permute(&b), &bounds()).unwrap();
                assert_ne!(wrong_a.round_product(&wrong_b).unwrap().as_slice(), q);
                controls += 1;
            }
            ta = ta.restrict_first(*r).unwrap();
            tb = tb.restrict_first(*r).unwrap();
            rounds += 1;
        }
        let values = row(&mut lines, "V");
        assert_eq!(ta.scalar_at_zero_arity().unwrap(), values[0]);
        assert_eq!(tb.scalar_at_zero_arity().unwrap(), values[1]);
        for (c, expected) in [(&committed_a, values[0]), (&committed_b, values[1])] {
            let (v, proof) = c.open(&p).unwrap();
            assert_eq!(v, expected);
            assert!(
                k.verifier_key()
                    .check(c.commitment(), &p, v, &proof)
                    .unwrap()
            );
            assert!(
                !k.verifier_key()
                    .check(c.commitment(), &p, v + Scalar::ONE, &proof)
                    .unwrap()
            );
        }
        assert_eq!(original_a.logical_values().unwrap(), a);
        assert_eq!(original_b.logical_values().unwrap(), b);
        cases += 1;
    }
    assert_eq!((cases, rounds, controls), (20, 60, 16));
}
