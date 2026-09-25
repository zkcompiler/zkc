use super::*;
use ark_ff::{AdditiveGroup, Field};
use ark_std::rand::{SeedableRng, rngs::StdRng};

fn bounds() -> Bounds {
    Bounds::new(5, 32, 10000, 160)
}
fn keys() -> Keys {
    Keys::setup_with_rng(2, &mut StdRng::from_seed([42; 32]), &bounds()).unwrap()
}

#[test]
fn upstream_ignored_nv_and_extra_coordinate_regressions_are_guarded() {
    let k = keys();
    let t = Table::from_logical(
        &[
            Scalar::ZERO,
            Scalar::ONE,
            Scalar::from(3u64),
            Scalar::from(7u64),
        ],
        &bounds(),
    )
    .unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    let point = [Scalar::from(11u64), Scalar::from(17u64)];
    let (value, p) = c.open(&point).unwrap();
    let vk = k.verifier_key();
    let mut raw = c.commitment.raw.clone();
    raw.nv += 1;
    assert!(Pcs::check(&vk.inner.key, &raw, &point, value, &p.raw));
    let forged = Commitment {
        raw,
        metadata: c.commitment.metadata,
    };
    assert_eq!(
        vk.check(&forged, &point, value, &p),
        Err(Error::ArityMismatch {
            expected: 2,
            actual: 3
        })
    );
    let long = [point[0], point[1], Scalar::from(31u64)];
    assert!(Pcs::check(
        &vk.inner.key,
        &c.commitment.raw,
        &long,
        value,
        &p.raw
    ));
    assert!(vk.check(c.commitment(), &long, value, &p).is_err());
    for length in [0, 1, 3] {
        let malformed = OpeningProof {
            metadata: p.metadata,
            raw: Arc::new(upstream::Proof {
                proofs: vec![ark_bls12_381::G2Affine::identity(); length],
            }),
        };
        assert!(vk.check(c.commitment(), &point, value, &malformed).is_err());
    }
}

#[test]
fn setup_fingerprint_binds_bases_absent_from_verifier_projection() {
    let mut params = Pcs::setup(2, &mut StdRng::from_seed([13; 32]));
    let original = codec::fingerprint(b"zkc-arkworks/setup/v1", &[], &params).unwrap();
    params.powers_of_h[0][0] = ark_bls12_381::G2Affine::identity();
    assert_ne!(
        original,
        codec::fingerprint(b"zkc-arkworks/setup/v1", &[], &params).unwrap()
    );
    let (_, vk) = Pcs::trim(&params, 2);
    let key = key_fingerprint(original, &vk).unwrap();
    let mut changed = original;
    changed[0] ^= 1;
    assert_ne!(key, key_fingerprint(changed, &vk).unwrap());
}

#[test]
fn generated_key_shape_guards_cover_all_indexed_arrays() {
    let k = keys();
    let valid = &k.prover_key().inner.key;
    let mut key = valid.clone();
    key.nv = 0;
    assert_eq!(validate_prover(&key), Err(Error::InvalidKey));
    let mut key = valid.clone();
    key.powers_of_g.pop();
    assert_eq!(validate_prover(&key), Err(Error::InvalidKey));
    let mut key = valid.clone();
    key.powers_of_h.pop();
    assert_eq!(validate_prover(&key), Err(Error::InvalidKey));
    for i in 0..2 {
        let mut key = valid.clone();
        key.powers_of_g[i].pop();
        assert_eq!(validate_prover(&key), Err(Error::InvalidKey));
        let mut key = valid.clone();
        key.powers_of_h[i].pop();
        assert_eq!(validate_prover(&key), Err(Error::InvalidKey));
    }
    let mut key = valid.clone();
    key.g = ark_bls12_381::G1Affine::identity();
    assert_eq!(validate_prover(&key), Err(Error::InvalidKey));
    let mut key = valid.clone();
    key.h = ark_bls12_381::G2Affine::identity();
    assert_eq!(validate_prover(&key), Err(Error::InvalidKey));
    let valid = &k.verifier_key().inner.key;
    let mut key = valid.clone();
    key.nv = 0;
    assert_eq!(validate_verifier(&key), Err(Error::InvalidKey));
    let mut key = valid.clone();
    key.g_mask_random.pop();
    assert_eq!(validate_verifier(&key), Err(Error::InvalidKey));
    let mut key = valid.clone();
    key.h = ark_bls12_381::G2Affine::identity();
    assert_eq!(validate_verifier(&key), Err(Error::InvalidKey));
}

#[test]
fn clone_is_actually_shared_and_scratch_is_distinct() {
    let k = keys();
    let t = Table::from_logical(&[Scalar::ZERO; 4], &bounds()).unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    assert!(Arc::ptr_eq(&c.original.polynomial, &t.polynomial));
    assert!(Arc::ptr_eq(&k.prover_key().inner, &c.key.inner));
    assert!(Arc::ptr_eq(
        &k.verifier_key().inner,
        &k.verifier_key().clone().inner
    ));
    let scratch = t.restrict_first(Scalar::ONE).unwrap();
    assert!(!Arc::ptr_eq(&t.polynomial, &scratch.polynomial));
    let (_, p) = c.open(&[Scalar::ONE; 2]).unwrap();
    assert!(Arc::ptr_eq(&p.raw, &p.clone().raw));
}

#[test]
fn malicious_prover_dimensions_are_rejected_without_vector_requests() {
    let k = keys();
    let bytes = k.prover_key().to_bytes(&bounds()).unwrap();
    let pin = k.prover_key().material_fingerprint();
    let all = Bounds::new(usize::MAX, usize::MAX, usize::MAX, usize::MAX);
    for n in [0u64, 1, 3, 40, 58, 59, 63, 64, u64::MAX] {
        let mut bad = bytes.clone();
        bad[9..17].copy_from_slice(&n.to_le_bytes());
        crate::bounds::VECTOR_REQUESTS.with(|count| count.set(0));
        assert!(ProverKey::from_bytes(&bad, pin, k.verifier_key(), &all).is_err());
        crate::bounds::VECTOR_REQUESTS.with(|count| assert_eq!(count.get(), 0, "rank {n}"));
    }
    let too_small = Bounds::new(2, 4, bytes.len() - 1, 0);
    crate::bounds::VECTOR_REQUESTS.with(|count| count.set(0));
    assert_eq!(
        ProverKey::from_bytes(&bytes, pin, k.verifier_key(), &too_small).unwrap_err(),
        Error::ByteLimit
    );
    crate::bounds::VECTOR_REQUESTS.with(|count| assert_eq!(count.get(), 0));
    // A valid load makes precisely two outer plus 2*n row allocation requests.
    crate::bounds::VECTOR_REQUESTS.with(|count| count.set(0));
    let imported = ProverKey::from_bytes(&bytes, pin, k.verifier_key(), &all).unwrap();
    crate::bounds::VECTOR_REQUESTS.with(|count| assert_eq!(count.get(), 6));
    assert_eq!(imported.metadata(), k.prover_key().metadata());
}

#[test]
fn prover_wire_size_arithmetic_is_checked_without_allocation() {
    crate::bounds::VECTOR_REQUESTS.with(|count| count.set(0));
    assert_eq!(
        codec::size(Kind::Prover, 0),
        Err(Error::PositiveArityRequired)
    );
    assert_eq!(codec::size(Kind::Prover, 1), Ok(513));
    assert_eq!(codec::size(Kind::Prover, 2), Ok(1089));
    for rank in [usize::BITS as usize - 1, usize::BITS as usize, usize::MAX] {
        assert_eq!(
            codec::size(Kind::Prover, rank),
            Err(Error::CapacityOverflow)
        );
    }
    // The arithmetic decides the refusal; a rank of usize::MAX must not have
    // been reached by asking for the vector it describes.
    crate::bounds::VECTOR_REQUESTS.with(|count| assert_eq!(count.get(), 0));
}
