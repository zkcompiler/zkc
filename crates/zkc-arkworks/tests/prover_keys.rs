//! Independent upstream construction and hostile public prover-key transport.
mod common;
use ark_bls12_381::{Bls12_381, Fq, Fq2, G1Affine, G2Affine};
use ark_ff::Field;
use ark_poly_commit::multilinear_pc::{MultilinearPC, data_structures as upstream};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::{SeedableRng, rngs::StdRng};
use common::{bounds, keys};
use sha2::{Digest, Sha256};
use zkc_arkworks::{Bounds, Error, PROFILE, ProverKey, Scalar, Table, VerifierKey};

const HEADER: usize = 81;

fn encoded<T: CanonicalSerialize>(value: &T) -> Vec<u8> {
    let mut bytes = Vec::new();
    value.serialize_compressed(&mut bytes).unwrap();
    bytes
}

// Independently implement the documented length-framed hash. Only trusted
// fixture objects are serialized upstream; no nested object is deserialized.
fn hash(domain: &[u8], context: &[u8], object: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    for part in [domain, PROFILE.as_bytes(), context] {
        hash.update((part.len() as u64).to_le_bytes());
        hash.update(part);
    }
    hash.update(object);
    hash.finalize().into()
}

fn envelope(n: usize, kind: u8, setup: [u8; 32], key: [u8; 32]) -> Vec<u8> {
    let mut bytes = b"ZKCAR006".to_vec();
    bytes.push(kind);
    bytes.extend_from_slice(&(n as u64).to_le_bytes());
    bytes.extend_from_slice(&setup);
    bytes.extend_from_slice(&key);
    bytes
}

// Manual fixed-shape wire reconstruction, not the wrapper's serializer.
fn prover_bytes(ck: &upstream::CommitterKey<Bls12_381>, setup: [u8; 32], key: [u8; 32]) -> Vec<u8> {
    let mut bytes = envelope(ck.nv, 4, setup, key);
    bytes.extend(encoded(&ck.g));
    bytes.extend(encoded(&ck.h));
    for row in &ck.powers_of_g {
        for point in row {
            bytes.extend(encoded(point));
        }
    }
    for row in &ck.powers_of_h {
        for point in row {
            bytes.extend(encoded(point));
        }
    }
    bytes
}

// Independently reconstruct canonical CommitterKey bytes, including upstream
// u64 vector dimensions, from our fixed wire layout. This is a bounded fixture
// encoder, NOT a production ingress path. It never invokes nested deserialization.
fn material_pin(bytes: &[u8], n: usize) -> [u8; 32] {
    assert_eq!(bytes.len(), 81 + 144 * ((1 << (n + 1)) - 1));
    let mut canonical = (n as u64).to_le_bytes().to_vec();
    let mut offset = HEADER + 144;
    for width in [48, 96] {
        canonical.extend_from_slice(&(n as u64).to_le_bytes());
        for i in 0..n {
            let len = 1 << (n - i);
            canonical.extend_from_slice(&(len as u64).to_le_bytes());
            canonical.extend_from_slice(&bytes[offset..offset + len * width]);
            offset += len * width;
        }
    }
    assert_eq!(offset, bytes.len());
    canonical.extend_from_slice(&bytes[HEADER..HEADER + 144]);
    hash(b"zkc-arkworks/prover/v1", &bytes[17..81], &canonical)
}

fn fixture(params: &upstream::UniversalParams<Bls12_381>) -> (Vec<u8>, [u8; 32], VerifierKey) {
    let setup = hash(b"zkc-arkworks/setup/v1", &[], &encoded(params));
    let (ck, vk) = MultilinearPC::trim(params, params.num_vars);
    let key = hash(b"zkc-arkworks/key/v1", &setup, &encoded(&vk));
    let mut vb = envelope(vk.nv, 1, setup, key);
    vb.extend(encoded(&vk.g));
    vb.extend(encoded(&vk.h));
    for mask in &vk.g_mask_random {
        vb.extend(encoded(mask));
    }
    let verifier = VerifierKey::from_bytes(&vb, key, &bounds()).unwrap();
    let bytes = prover_bytes(&ck, setup, key);
    let pin = material_pin(&bytes, ck.nv);
    // Check the independent manual key preimage against actual upstream serde.
    assert_eq!(
        pin,
        hash(b"zkc-arkworks/prover/v1", &bytes[17..81], &encoded(&ck))
    );
    (bytes, pin, verifier)
}

#[test]
fn independent_upstream_bytes_and_reload_preserve_real_openings() {
    for n in [1, 2, 4] {
        let seed = 51;
        let params = MultilinearPC::<Bls12_381>::setup(n, &mut StdRng::from_seed([seed; 32]));
        let (bytes, pin, vk) = fixture(&params);
        let k = keys(n, seed);
        assert_eq!(bytes, k.prover_key().to_bytes(&bounds()).unwrap());
        assert_eq!(pin, k.prover_key().material_fingerprint());
        let pk = ProverKey::from_bytes(&bytes, pin, &vk, &bounds()).unwrap();
        assert_eq!(pk.metadata(), vk.metadata());
        assert_eq!(pk.material_fingerprint(), pin);
        assert_eq!(pk.to_bytes(&bounds()).unwrap(), bytes);
        let values: Vec<_> = (0..1 << n)
            .map(|i| Scalar::from((i * i + 3) as u64))
            .collect();
        let table = Table::from_logical(&values, &bounds()).unwrap();
        let original = k.prover_key().commit(&table).unwrap();
        let reloaded = pk.commit(&table).unwrap();
        drop(k);
        drop(pk);
        assert_eq!(
            original.commitment().to_bytes(&bounds()).unwrap(),
            reloaded.commitment().to_bytes(&bounds()).unwrap()
        );
        for point in [
            vec![Scalar::from(0); n],
            vec![Scalar::from(1); n],
            (0..n).map(|i| Scalar::from(i as u64 + 7)).collect(),
        ] {
            let (value, proof) = reloaded.open(&point).unwrap();
            let (expected_value, expected_proof) = original.open(&point).unwrap();
            assert_eq!(value, expected_value);
            assert_eq!(
                proof.to_bytes(&bounds()).unwrap(),
                expected_proof.to_bytes(&bounds()).unwrap()
            );
            assert!(
                vk.check(reloaded.commitment(), &point, value, &proof)
                    .unwrap()
            );
            assert!(
                !vk.check(
                    reloaded.commitment(),
                    &point,
                    value + Scalar::from(1),
                    &proof
                )
                .unwrap()
            );
        }
        assert!(reloaded.open(&[]).is_err());
    }
}

#[test]
fn exact_length_headers_dimensions_and_policies_fail_closed() {
    let k = keys(2, 52);
    let pk = k.prover_key();
    let vk = k.verifier_key();
    let pin = pk.material_fingerprint();
    let bytes = pk.to_bytes(&bounds()).unwrap();
    assert_eq!(bytes.len(), 1089);
    for end in 0..bytes.len() {
        assert_eq!(
            ProverKey::from_bytes(&bytes[..end], pin, vk, &bounds()).unwrap_err(),
            Error::InvalidEncoding
        );
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert_eq!(
        ProverKey::from_bytes(&trailing, pin, vk, &bounds()).unwrap_err(),
        Error::InvalidEncoding
    );
    for offset in [0, 7, 8] {
        let mut bad = bytes.clone();
        bad[offset] ^= 1;
        assert_eq!(
            ProverKey::from_bytes(&bad, pin, vk, &bounds()).unwrap_err(),
            Error::InvalidHeader
        );
    }
    for offset in [17, 48, 49, 80] {
        let mut bad = bytes.clone();
        bad[offset] ^= 1;
        assert_eq!(
            ProverKey::from_bytes(&bad, pin, vk, &bounds()).unwrap_err(),
            Error::KeyMismatch
        );
    }
    let all = Bounds::new(usize::MAX, usize::MAX, usize::MAX, usize::MAX);
    // A corrupted rank is refused, and refused before any vector is requested:
    // src/pcs/tests.rs runs the same nine values and counts the requests, which
    // is the part worth having.
    // Upstream-style outer/inner lengths cannot be smuggled into this format.
    for offset in [HEADER + 144, HEADER + 144 + 8] {
        let mut bad = bytes.clone();
        bad.splice(offset..offset, u64::MAX.to_le_bytes());
        assert_eq!(
            ProverKey::from_bytes(&bad, pin, vk, &all).unwrap_err(),
            Error::InvalidEncoding
        );
    }
    for (policy, error) in [
        (Bounds::new(1, 1024, 10000, 0), Error::ArityLimit),
        (Bounds::new(10, 3, 10000, 0), Error::ElementLimit),
        (Bounds::new(10, 1024, bytes.len() - 1, 0), Error::ByteLimit),
    ] {
        assert_eq!(pk.to_bytes(&policy).unwrap_err(), error);
        assert_eq!(
            ProverKey::from_bytes(&bytes, pin, vk, &policy).unwrap_err(),
            error
        );
    }
    // Loading runs no setup and therefore needs no setup-work allowance.
    let exact = Bounds::new(2, 4, bytes.len(), 0);
    assert!(ProverKey::from_bytes(&bytes, pin, vk, &exact).is_ok());
    assert_eq!(pk.to_bytes(&exact).unwrap(), bytes);
    assert_eq!(
        ProverKey::from_bytes(&bytes, [0; 32], vk, &bounds()).unwrap_err(),
        Error::KeyMismatch
    );
    assert_eq!(
        ProverKey::from_bytes(&bytes, vk.metadata().key_id(), vk, &bounds()).unwrap_err(),
        Error::KeyMismatch
    );
    assert_eq!(
        ProverKey::from_bytes(&bytes, pin, keys(2, 53).verifier_key(), &bounds()).unwrap_err(),
        Error::KeyMismatch
    );
    assert_eq!(
        ProverKey::from_bytes(&bytes, pin, keys(1, 54).verifier_key(), &bounds()).unwrap_err(),
        Error::ArityMismatch {
            expected: 1,
            actual: 2
        }
    );
}

#[test]
fn canonical_curve_and_subgroup_checks_cover_every_point_slot() {
    let k = keys(2, 55);
    let vk = k.verifier_key();
    let bytes = k.prover_key().to_bytes(&bounds()).unwrap();
    let bad_g1 = (0..1000)
        .find_map(|i| {
            G1Affine::get_point_from_x_unchecked(Fq::from(i as u64), false)
                .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        })
        .unwrap();
    let bad_g2 = (0..1000)
        .find_map(|i| {
            G2Affine::get_point_from_x_unchecked(Fq2::new(Fq::from(i as u64), Fq::ONE), false)
                .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        })
        .unwrap();
    assert!(bad_g1.is_on_curve());
    assert!(bad_g2.is_on_curve());
    let slots = std::iter::once((HEADER, 48))
        .chain(std::iter::once((HEADER + 48, 96)))
        .chain((0..6).map(|i| (HEADER + 144 + 48 * i, 48)))
        .chain((0..6).map(|i| (HEADER + 144 + 48 * 6 + 96 * i, 96)));
    for (offset, width) in slots {
        let bad_subgroup = if width == 48 {
            encoded(&bad_g1)
        } else {
            encoded(&bad_g2)
        };
        let mut exceptional = if width == 48 {
            encoded(&G1Affine::identity())
        } else {
            encoded(&G2Affine::identity())
        };
        exceptional[width - 1] = 1;
        for replacement in [bad_subgroup, vec![255; width], exceptional] {
            let mut bad = bytes.clone();
            bad[offset..offset + width].copy_from_slice(&replacement);
            // Re-pin to reach point validation independently of fingerprint
            // rejection; this candidate pin is ONLY an adversarial test device.
            let error =
                ProverKey::from_bytes(&bad, material_pin(&bad, 2), vk, &bounds()).unwrap_err();
            assert!(
                matches!(error, Error::InvalidEncoding | Error::NonCanonicalEncoding),
                "slot {offset}: {error}"
            );
        }
    }
}

#[test]
fn pins_do_not_replace_shared_generators_or_full_setup_relation() {
    let k = keys(2, 56);
    let vk = k.verifier_key();
    let bytes = k.prover_key().to_bytes(&bounds()).unwrap();
    // Canonical foreign generators with matching candidate header and a newly
    // computed full pin must still fail against the actual admitted VK.
    let foreign = keys(2, 57).prover_key().to_bytes(&bounds()).unwrap();
    for (offset, width) in [(HEADER, 48), (HEADER + 48, 96)] {
        for replacement in [
            foreign[offset..offset + width].to_vec(),
            if width == 48 {
                encoded(&G1Affine::identity())
            } else {
                encoded(&G2Affine::identity())
            },
        ] {
            let mut bad = bytes.clone();
            bad[offset..offset + width].copy_from_slice(&replacement);
            assert_eq!(
                ProverKey::from_bytes(&bad, material_pin(&bad, 2), vk, &bounds()).unwrap_err(),
                Error::KeyMismatch
            );
        }
    }
    for (offset, replacement) in [
        (HEADER + 144, encoded(&G1Affine::identity())),
        (HEADER + 144 + 6 * 48, encoded(&G2Affine::identity())),
    ] {
        let mut bad = bytes.clone();
        bad[offset..offset + replacement.len()].copy_from_slice(&replacement);
        assert_eq!(
            ProverKey::from_bytes(&bad, k.prover_key().material_fingerprint(), vk, &bounds())
                .unwrap_err(),
            Error::KeyMismatch
        );
        // Even a matching full-material pin cannot waive the setup hash check.
        assert_eq!(
            ProverKey::from_bytes(&bad, material_pin(&bad, 2), vk, &bounds()).unwrap_err(),
            Error::KeyMismatch
        );
    }
}

#[test]
fn correctly_pinned_inconsistent_srs_is_not_an_honest_setup_certificate() {
    let mut params = MultilinearPC::<Bls12_381>::setup(2, &mut StdRng::from_seed([58; 32]));
    // Keep g/h/masks, remove all G2 proving bases. Points remain canonical and
    // subgroup-valid. Recompute ALL identities as a malicious material supplier
    // could. This intentionally admitted fixture documents the remaining trust.
    for row in &mut params.powers_of_h {
        row.fill(G2Affine::identity());
    }
    let (bytes, pin, vk) = fixture(&params);
    let pk = ProverKey::from_bytes(&bytes, pin, &vk, &bounds()).unwrap();
    let table = Table::from_logical(&[1, 2, 4, 8].map(Scalar::from), &bounds()).unwrap();
    let committed = pk.commit(&table).unwrap();
    let point = [7, 11].map(Scalar::from);
    let (value, proof) = committed.open(&point).unwrap();
    assert!(
        !vk.check(committed.commitment(), &point, value, &proof)
            .unwrap()
    );
}

#[test]
fn every_single_byte_mutation_is_rejected_under_original_pin() {
    let k = keys(1, 59);
    let bytes = k.prover_key().to_bytes(&bounds()).unwrap();
    for i in 0..bytes.len() {
        let mut bad = bytes.clone();
        bad[i] ^= 1;
        assert!(
            ProverKey::from_bytes(
                &bad,
                k.prover_key().material_fingerprint(),
                k.verifier_key(),
                &bounds()
            )
            .is_err(),
            "byte {i}"
        );
    }
    assert!(
        ProverKey::from_bytes(
            &bytes,
            k.prover_key().material_fingerprint(),
            k.verifier_key(),
            &bounds()
        )
        .is_ok()
    );
}

#[test]
fn admitted_vk_with_changed_masks_cannot_authorize_an_unrelated_setup_hash() {
    let params = MultilinearPC::<Bls12_381>::setup(2, &mut StdRng::from_seed([60; 32]));
    let (mut bytes, _, original_vk) = fixture(&params);
    let (_, mut raw_vk) = MultilinearPC::trim(&params, 2);
    raw_vk.g_mask_random[0] = G1Affine::identity();
    // Model a separately admitted VK with the original setup label but altered
    // masks. VK import alone cannot reconstruct or verify that setup label.
    let setup = original_vk.metadata().setup_id();
    let key_id = hash(b"zkc-arkworks/key/v1", &setup, &encoded(&raw_vk));
    let mut vb = envelope(2, 1, setup, key_id);
    vb.extend(encoded(&raw_vk.g));
    vb.extend(encoded(&raw_vk.h));
    for mask in &raw_vk.g_mask_random {
        vb.extend(encoded(mask));
    }
    let changed_vk = VerifierKey::from_bytes(&vb, key_id, &bounds()).unwrap();
    bytes[49..81].copy_from_slice(&key_id);
    let pin = material_pin(&bytes, 2);
    // Arity, metadata, shared g/h, and the full prover pin all match; only the
    // reconstructed full setup hash exposes this inconsistent association.
    assert_eq!(
        ProverKey::from_bytes(&bytes, pin, &changed_vk, &bounds()).unwrap_err(),
        Error::KeyMismatch
    );
}
