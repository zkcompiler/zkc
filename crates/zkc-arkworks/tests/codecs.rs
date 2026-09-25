//! Hostile public wire formats, canonical group decoding and authenticated key pins.
mod common;
use ark_bls12_381::{Fq, Fq2, G1Affine, G2Affine};
use ark_ff::Field;
use ark_serialize::CanonicalSerialize;
use common::{bounds, keys, scalars};
use zkc_arkworks::{Bounds, Error, Scalar, Table, VerifierKey};

const HEADER: usize = 81;
fn encoded<T: CanonicalSerialize>(point: &T) -> Vec<u8> {
    let mut bytes = Vec::new();
    point.serialize_compressed(&mut bytes).unwrap();
    bytes
}
fn non_subgroup_g1() -> G1Affine {
    (0..1000)
        .find_map(|i| {
            G1Affine::get_point_from_x_unchecked(Fq::from(i as u64), false)
                .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        })
        .unwrap()
}
fn non_subgroup_g2() -> G2Affine {
    (0..1000)
        .find_map(|i| {
            G2Affine::get_point_from_x_unchecked(Fq2::new(Fq::from(i as u64), Fq::ONE), false)
                .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        })
        .unwrap()
}

#[test]
fn exact_consumption_for_every_public_codec() {
    let k = keys(2, 14);
    let vk = k.verifier_key();
    let pin = vk.metadata().key_id();
    let t = Table::from_logical(&scalars(&[2, 3, 5, 7]), &bounds()).unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    let (_, p) = c.open(&scalars(&[11, 13])).unwrap();
    let vbytes = vk.to_bytes(&bounds()).unwrap();
    let cbytes = c.commitment().to_bytes(&bounds()).unwrap();
    let pbytes = p.to_bytes(&bounds()).unwrap();
    assert_eq!((vbytes.len(), cbytes.len(), pbytes.len()), (321, 129, 273));
    for end in 0..vbytes.len() {
        assert!(VerifierKey::from_bytes(&vbytes[..end], pin, &bounds()).is_err());
    }
    for end in 0..cbytes.len() {
        assert!(vk.decode_commitment(&cbytes[..end], &bounds()).is_err());
    }
    for end in 0..pbytes.len() {
        assert!(vk.decode_proof(&pbytes[..end], &bounds()).is_err());
    }
    for bytes in [&vbytes, &cbytes, &pbytes] {
        let mut extra = bytes.clone();
        extra.push(0);
        assert!(VerifierKey::from_bytes(&extra, pin, &bounds()).is_err());
        assert!(vk.decode_commitment(&extra, &bounds()).is_err());
        assert!(vk.decode_proof(&extra, &bounds()).is_err());
    }
    assert!(vk.decode_proof(&cbytes, &bounds()).is_err());
    assert!(vk.decode_commitment(&pbytes, &bounds()).is_err());
    assert_eq!(
        VerifierKey::from_bytes(&vbytes, pin, &bounds())
            .unwrap()
            .to_bytes(&bounds())
            .unwrap(),
        vbytes
    );
    assert_eq!(
        vk.decode_commitment(&cbytes, &bounds())
            .unwrap()
            .to_bytes(&bounds())
            .unwrap(),
        cbytes
    );
    assert_eq!(
        vk.decode_proof(&pbytes, &bounds())
            .unwrap()
            .to_bytes(&bounds())
            .unwrap(),
        pbytes
    );
}

#[test]
fn hostile_arity_key_setup_version_and_kind_headers() {
    let k = keys(2, 15);
    let vk = k.verifier_key();
    let pin = vk.metadata().key_id();
    let t = Table::from_logical(&scalars(&[2, 3, 5, 7]), &bounds()).unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    let (_, p) = c.open(&scalars(&[11, 13])).unwrap();
    let vb = vk.to_bytes(&bounds()).unwrap();
    let cb = c.commitment().to_bytes(&bounds()).unwrap();
    let pb = p.to_bytes(&bounds()).unwrap();
    for offset in [0, 7, 8, 17, 48, 49, 80] {
        let mut bytes = vb.clone();
        bytes[offset] ^= 1;
        assert!(VerifierKey::from_bytes(&bytes, pin, &bounds()).is_err());
        let mut bytes = cb.clone();
        bytes[offset] ^= 1;
        assert!(vk.decode_commitment(&bytes, &bounds()).is_err());
        let mut bytes = pb.clone();
        bytes[offset] ^= 1;
        assert!(vk.decode_proof(&bytes, &bounds()).is_err());
    }
    for n in [0u64, 1, 3, 63, 64, u64::MAX] {
        for source in [&vb, &cb, &pb] {
            let mut bytes = source.clone();
            bytes[9..17].copy_from_slice(&n.to_le_bytes());
            assert!(VerifierKey::from_bytes(&bytes, pin, &bounds()).is_err());
            assert!(vk.decode_commitment(&bytes, &bounds()).is_err());
            assert!(vk.decode_proof(&bytes, &bounds()).is_err());
        }
    }
    let mut wrong_nv = cb.clone();
    wrong_nv[9..17].copy_from_slice(&3u64.to_le_bytes());
    assert_eq!(
        vk.decode_commitment(&wrong_nv, &bounds()).unwrap_err(),
        Error::ArityMismatch {
            expected: 2,
            actual: 3
        }
    );
    let foreign = keys(2, 16);
    assert_eq!(
        VerifierKey::from_bytes(&vb, foreign.verifier_key().metadata().key_id(), &bounds())
            .unwrap_err(),
        Error::KeyMismatch
    );
    assert_eq!(
        foreign
            .verifier_key()
            .decode_commitment(&cb, &bounds())
            .unwrap_err(),
        Error::KeyMismatch
    );
    assert_eq!(
        foreign
            .verifier_key()
            .decode_proof(&pb, &bounds())
            .unwrap_err(),
        Error::KeyMismatch
    );
    // Supplying a permissive policy still cannot turn huge declared lengths
    // into a vector allocation: checked shift and exact total length precede it.
    let all = Bounds::new(usize::MAX, usize::MAX, usize::MAX, usize::MAX);
    for n in [40u64, 63, u64::MAX] {
        let mut bytes = pb.clone();
        bytes[9..17].copy_from_slice(&n.to_le_bytes());
        assert!(vk.decode_proof(&bytes, &all).is_err());
    }
}

#[test]
fn byte_and_arity_policies_apply_on_import_and_export() {
    let k = keys(2, 17);
    let vk = k.verifier_key();
    let pin = vk.metadata().key_id();
    let t = Table::from_logical(&scalars(&[1, 2, 3, 4]), &bounds()).unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    let (_, p) = c.open(&scalars(&[7, 8])).unwrap();
    let vb = vk.to_bytes(&bounds()).unwrap();
    let cb = c.commitment().to_bytes(&bounds()).unwrap();
    let pb = p.to_bytes(&bounds()).unwrap();
    for (policy, expected) in [
        (Bounds::new(10, 1024, 100, 10000), Error::ByteLimit),
        (Bounds::new(1, 1024, 10000, 10000), Error::ArityLimit),
        (Bounds::new(10, 3, 10000, 10000), Error::ElementLimit),
    ] {
        assert_eq!(
            VerifierKey::from_bytes(&vb, pin, &policy).unwrap_err(),
            expected
        );
        assert_eq!(vk.decode_commitment(&cb, &policy).unwrap_err(), expected);
        assert_eq!(vk.decode_proof(&pb, &policy).unwrap_err(), expected);
        assert_eq!(vk.to_bytes(&policy).unwrap_err(), expected);
        assert_eq!(c.commitment().to_bytes(&policy).unwrap_err(), expected);
        assert_eq!(p.to_bytes(&policy).unwrap_err(), expected);
    }
}

#[test]
fn reject_invalid_encodings_and_non_subgroup_points_at_every_position() {
    let k = keys(2, 18);
    let vk = k.verifier_key();
    let pin = vk.metadata().key_id();
    let t = Table::from_logical(&scalars(&[1, 2, 4, 8]), &bounds()).unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    let (_, p) = c.open(&scalars(&[7, 9])).unwrap();
    let vb = vk.to_bytes(&bounds()).unwrap();
    let cb = c.commitment().to_bytes(&bounds()).unwrap();
    let pb = p.to_bytes(&bounds()).unwrap();
    let g1 = non_subgroup_g1();
    let g2 = non_subgroup_g2();
    assert!(g1.is_on_curve());
    assert!(g2.is_on_curve());
    let bad_g1 = encoded(&g1);
    let bad_g2 = encoded(&g2);
    for payload in [bad_g1.clone(), vec![255; 48]] {
        let mut bytes = cb.clone();
        bytes[HEADER..].copy_from_slice(&payload);
        assert_eq!(
            vk.decode_commitment(&bytes, &bounds()).unwrap_err(),
            Error::InvalidEncoding
        );
        for offset in [HEADER, HEADER + 144, HEADER + 192] {
            let mut bytes = vb.clone();
            bytes[offset..offset + 48].copy_from_slice(&payload);
            assert_eq!(
                VerifierKey::from_bytes(&bytes, pin, &bounds()).unwrap_err(),
                Error::InvalidEncoding
            );
        }
    }
    for payload in [bad_g2, vec![255; 96]] {
        let mut bytes = vb.clone();
        bytes[HEADER + 48..HEADER + 144].copy_from_slice(&payload);
        assert_eq!(
            VerifierKey::from_bytes(&bytes, pin, &bounds()).unwrap_err(),
            Error::InvalidEncoding
        );
        for offset in [HEADER, HEADER + 96] {
            let mut bytes = pb.clone();
            bytes[offset..offset + 96].copy_from_slice(&payload);
            assert_eq!(
                vk.decode_proof(&bytes, &bounds()).unwrap_err(),
                Error::InvalidEncoding
            );
        }
    }
    // Canonical, subgroup-valid replacements still fail the authenticated key
    // fingerprint. Shape and subgroup admission alone do not identify a key.
    let mut changed = vb.clone();
    changed[HEADER + 144..HEADER + 192].copy_from_slice(&encoded(&G1Affine::identity()));
    assert_eq!(
        VerifierKey::from_bytes(&changed, pin, &bounds()).unwrap_err(),
        Error::KeyMismatch
    );
    let mut zero_generator = vb.clone();
    zero_generator[HEADER..HEADER + 48].copy_from_slice(&encoded(&G1Affine::identity()));
    assert_eq!(
        VerifierKey::from_bytes(&zero_generator, pin, &bounds()).unwrap_err(),
        Error::InvalidKey
    );
}

#[test]
fn noncanonical_infinity_is_rejected() {
    let k = keys(1, 19);
    let vk = k.verifier_key();
    let t = Table::from_logical(&scalars(&[0, 0]), &bounds()).unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    let (_, p) = c.open(&scalars(&[7])).unwrap();
    let mut cb = c.commitment().to_bytes(&bounds()).unwrap();
    let mut pb = p.to_bytes(&bounds()).unwrap();
    // BLS compressed infinity must have zero coordinates and no sign flag.
    cb[HEADER + 47] = 1;
    pb[HEADER + 95] = 1;
    assert!(vk.decode_commitment(&cb, &bounds()).is_err());
    assert!(vk.decode_proof(&pb, &bounds()).is_err());
}

#[test]
fn bounded_byte_mutations_never_reach_unsafe_upstream_shapes() {
    let k = keys(2, 20);
    let vk = k.verifier_key();
    let pin = vk.metadata().key_id();
    let t = Table::from_logical(&scalars(&[2, 3, 5, 7]), &bounds()).unwrap();
    let c = k.prover_key().commit(&t).unwrap();
    let point = scalars(&[17, 19]);
    let (v, p) = c.open(&point).unwrap();
    let vb = vk.to_bytes(&bounds()).unwrap();
    let cb = c.commitment().to_bytes(&bounds()).unwrap();
    let pb = p.to_bytes(&bounds()).unwrap();
    for i in 0..vb.len() {
        let mut bytes = vb.clone();
        bytes[i] ^= 1;
        assert!(VerifierKey::from_bytes(&bytes, pin, &bounds()).is_err());
    }
    for i in 0..cb.len() {
        let mut bytes = cb.clone();
        bytes[i] ^= 1;
        if let Ok(c) = vk.decode_commitment(&bytes, &bounds()) {
            assert_eq!(c.to_bytes(&bounds()).unwrap(), bytes);
            assert!(!vk.check(&c, &point, v, &p).unwrap());
        }
    }
    for i in 0..pb.len() {
        let mut bytes = pb.clone();
        bytes[i] ^= 1;
        if let Ok(proof) = vk.decode_proof(&bytes, &bounds()) {
            assert_eq!(proof.to_bytes(&bounds()).unwrap(), bytes);
            assert!(!vk.check(c.commitment(), &point, v, &proof).unwrap());
        }
    }
    assert!(vk.check(c.commitment(), &point, v, &p).unwrap());
    assert_eq!(
        c.original().logical_values().unwrap(),
        scalars(&[2, 3, 5, 7])
    );
    assert_ne!(v, Scalar::from(0u64));
}
