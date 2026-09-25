//! Replay controls for a format adapter, not key ceremony validation.
use ark_bn254::{Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use zkc_arkworks::bn254::{self, G1, G2};
use zkc_backends::{Policy, Value};
use zkc_tools::snarkjs::{self, Limits};
fn p() -> Policy {
    Policy {
        max_groups: 32768,
        ..Policy::default()
    }
}
fn raw<F: PrimeField>(v: F) -> Vec<u8> {
    v.into_bigint().to_bytes_le()
}
fn container(magic: &[u8; 4], version: u32, parts: &[(u32, Vec<u8>)]) -> Vec<u8> {
    let mut b = magic.to_vec();
    b.extend(version.to_le_bytes());
    b.extend((parts.len() as u32).to_le_bytes());
    for (id, data) in parts {
        b.extend(id.to_le_bytes());
        b.extend((data.len() as u64).to_le_bytes());
        b.extend(data);
    }
    b
}
fn wtns(values: &[Fr]) -> Vec<u8> {
    let mut h = 32u32.to_le_bytes().to_vec();
    h.extend(Fr::MODULUS.to_bytes_le());
    h.extend((values.len() as u32).to_le_bytes());
    container(
        b"wtns",
        2,
        &[(1, h), (2, values.iter().flat_map(|x| raw(*x)).collect())],
    )
}
fn key_parts() -> Vec<(u32, Vec<u8>)> {
    let mut h = 32u32.to_le_bytes().to_vec();
    h.extend(Fq::MODULUS.to_bytes_le());
    h.extend(32u32.to_le_bytes());
    h.extend(Fr::MODULUS.to_bytes_le());
    for n in [2u32, 0, 2] {
        h.extend(n.to_le_bytes());
    }
    h.extend([0u8; 576]);
    let mut c = 2u32.to_le_bytes().to_vec();
    for m in [0u32, 1] {
        for n in [m, 0, 1] {
            c.extend(n.to_le_bytes());
        }
        c.extend(raw(Fr::from(3) * Fr::from(2).pow([512])));
    }
    vec![
        (1, 1u32.to_le_bytes().to_vec()),
        (2, h),
        (3, vec![0; 64]),
        (4, c),
        (5, vec![0; 128]),
        (6, vec![0; 128]),
        (7, vec![0; 256]),
        (8, vec![0; 64]),
        (9, vec![0; 128]),
    ]
}
fn decode(parts: &[(u32, Vec<u8>)]) -> snarkjs::Result<snarkjs::PreparedKey> {
    snarkjs::decode_zkey(&container(b"zkey", 1, parts), &Limits::default(), &p())
}
#[test]
fn nonzero_montgomery_points_and_domain_known_answers() {
    // Frozen zkey little-endian coordinates of the standard BN254 generators.
    // Derived with independent integer arithmetic: x * 2^256 mod q. Do not
    // compute these from the importer's conversion constants in this test.
    let coordinates = [
        "9d0d8fc58d435dd33d0bc7f528eb780a2c4679786fa36e662fdf079ac1770a0e",
        "3a1b1e8b1b87baa67b168eeb51d6f114588cf2f0de46ddcc5ebe0f3483ef141c",
        "2620bc02d1b5838e72017b493519ebdcdf1a81974726b8fb3b5096af41385719",
        "40614ca87d73b4afc4d802585add4360862fa052fc50e9096b7bea3a83f0fe14",
        "f6e96b889dfa9d61789b9ef597d27ffefe7d1b23621a9eff06429eaeeb7efd28",
        "ee5618c7565b0964bb3c7d3222f957dc76103533be35f9558264fd93e6a0a40d",
    ];
    let bytes: Vec<u8> = coordinates
        .iter()
        .flat_map(|s| {
            (0..s.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        })
        .collect();
    let mut parts = key_parts();
    parts[1].1[84..148].copy_from_slice(&bytes[..64]); // alpha1
    parts[1].1[212..340].copy_from_slice(&bytes[64..]); // beta2
    parts[4].1[..64].copy_from_slice(&bytes[..64]); // first A query
    parts[6].1[..128].copy_from_slice(&bytes[64..]); // first B2 query
    let key = decode(&parts).unwrap();
    assert_eq!(key.alpha1, G1::generator());
    assert_eq!(key.beta2, G2::generator());
    assert_eq!(key.a_query[0], G1::generator());
    assert_eq!(key.b2_query[0], G2::generator());
    assert_eq!(
        key.domain_root,
        ark_ff::MontFp!(
            "21888242871839275222246405745257275088548364400416034343698204186575808495616"
        )
    );
    assert_eq!(
        key.coset_shift,
        ark_ff::MontFp!(
            "21888242871839275217838484774961031246007050428528088939761107053157389710902"
        )
    );
}
#[test]
fn bounded_container_field_index_and_policy_controls() {
    let parts = key_parts();
    let good = decode(&parts).unwrap();
    assert_eq!(good.qap_a.entries(), &[(0, 1, Fr::from(3))]);
    assert_eq!(good.qap_b.entries(), &[(0, 1, Fr::from(3))]);
    let bytes = container(b"zkey", 1, &parts);
    for n in [0, 3, 8, 12, bytes.len() - 1] {
        assert!(snarkjs::decode_zkey(&bytes[..n], &Limits::default(), &p()).is_err());
    }
    let mut bad = bytes.clone();
    bad.push(0);
    assert_eq!(
        snarkjs::decode_zkey(&bad, &Limits::default(), &p())
            .unwrap_err()
            .0,
        "import-trailing-bytes"
    );
    let mut bad = bytes.clone();
    bad[4] = 2;
    assert_eq!(
        snarkjs::decode_zkey(&bad, &Limits::default(), &p())
            .unwrap_err()
            .0,
        "import-version"
    );
    let mut bad = bytes.clone();
    bad[0] = 0;
    assert_eq!(
        snarkjs::decode_zkey(&bad, &Limits::default(), &p())
            .unwrap_err()
            .0,
        "import-magic"
    );
    let mut bad = parts.clone();
    bad.push(parts[0].clone());
    assert_eq!(decode(&bad).unwrap_err().0, "import-duplicate-section");
    let mut bad = parts.clone();
    bad.pop();
    assert_eq!(decode(&bad).unwrap_err().0, "import-missing-section");
    let mut bad = parts.clone();
    bad[0].1[0] = 2;
    assert_eq!(decode(&bad).unwrap_err().0, "import-protocol");
    for (offset, value, code) in [
        (0, 31u32, "import-field-width"),
        (72, 0, "import-variable-count"),
        (76, 2, "import-public-count"),
        (80, 3, "import-domain-size"),
    ] {
        let mut bad = parts.clone();
        bad[1].1[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
        assert_eq!(decode(&bad).unwrap_err().0, code);
    }
    let mut bad = parts.clone();
    bad[1].1[4] = 0;
    assert_eq!(decode(&bad).unwrap_err().0, "import-field-modulus");
    let mut bad = parts.clone();
    bad[4].1.push(0);
    assert_eq!(decode(&bad).unwrap_err().0, "import-section-length");
    for offset in [4, 8, 12] {
        let mut bad = parts.clone();
        bad[3].1[offset..offset + 4].copy_from_slice(&2u32.to_le_bytes());
        assert_eq!(decode(&bad).unwrap_err().0, "import-coefficient-index");
    }
    let mut bad = parts.clone();
    bad[3].1[16..48].copy_from_slice(&Fr::MODULUS.to_bytes_le());
    assert_eq!(decode(&bad).unwrap_err().0, "import-noncanonical-field");
    let mut bad = parts.clone();
    bad[1].1[84..116].copy_from_slice(&raw(Fq::from(1)));
    assert_eq!(decode(&bad).unwrap_err().0, "import-invalid-g1");
    for limits in [
        Limits {
            max_file_bytes: bytes.len() - 1,
            ..Limits::default()
        },
        Limits {
            max_decoded_bytes: 100,
            ..Limits::default()
        },
        Limits {
            max_coefficients: 1,
            ..Limits::default()
        },
        Limits {
            max_variables: 1,
            ..Limits::default()
        },
        Limits {
            max_domain_size: 1,
            ..Limits::default()
        },
    ] {
        assert!(snarkjs::decode_zkey(&bytes, &limits, &p()).is_err());
    }
    assert_eq!(
        snarkjs::decode_zkey(
            &bytes,
            &Limits::default(),
            &Policy {
                max_groups: 1,
                ..p()
            }
        )
        .unwrap_err()
        .0,
        "import-element-policy"
    );
    assert!(
        snarkjs::decode_zkey(
            &bytes,
            &Limits::default(),
            &Policy {
                max_value_bytes: 1,
                ..p()
            }
        )
        .is_err()
    );
    let mut duplicate = parts.clone();
    duplicate[3].1 = 3u32.to_le_bytes().to_vec();
    duplicate[3].1.extend_from_slice(&parts[3].1[4..]);
    duplicate[3].1.extend_from_slice(&parts[3].1[4..48]);
    assert_eq!(
        decode(&duplicate).unwrap().qap_a.entries(),
        &[(0, 1, Fr::from(6))]
    );
}
#[test]
fn assignment_exactness_and_binding() {
    let bytes = wtns(&[Fr::one(), Fr::from(7)]);
    let witness = snarkjs::decode_wtns(&bytes, &Limits::default(), &p()).unwrap();
    assert_eq!(witness.0.as_ref(), [Fr::one(), Fr::from(7)]);
    assert!(matches!(
        decode(&key_parts()).unwrap().assignment(&witness).unwrap(),
        Value::Bn254Vector(_)
    ));
    assert_eq!(
        snarkjs::decode_wtns(&wtns(&[Fr::zero()]), &Limits::default(), &p())
            .unwrap_err()
            .0,
        "import-assignment-one"
    );
    let mut bad = bytes;
    let n = bad.len();
    bad[n - 32..].copy_from_slice(&Fr::MODULUS.to_bytes_le());
    assert_eq!(
        snarkjs::decode_wtns(&bad, &Limits::default(), &p())
            .unwrap_err()
            .0,
        "import-noncanonical-field"
    );
    let one = snarkjs::decode_wtns(&wtns(&[Fr::one()]), &Limits::default(), &p()).unwrap();
    assert_eq!(
        decode(&key_parts())
            .unwrap()
            .assignment(&one)
            .unwrap_err()
            .0,
        "import-assignment-length"
    );
}
fn sf(j: &serde_json::Value) -> Fr {
    bn254::parse_decimal(j.as_str().unwrap()).unwrap()
}
fn fq(j: &serde_json::Value) -> Fq {
    j.as_str().unwrap().parse().unwrap()
}
fn g1(j: &serde_json::Value) -> G1 {
    if j[2] == "0" {
        G1::identity()
    } else {
        G1::from_affine(G1Affine::new_unchecked(fq(&j[0]), fq(&j[1]))).unwrap()
    }
}
fn g2(j: &serde_json::Value) -> G2 {
    if j[2][0] == "0" {
        G2::identity()
    } else {
        G2::from_affine(G2Affine::new_unchecked(
            Fq2::new(fq(&j[0][0]), fq(&j[0][1])),
            Fq2::new(fq(&j[1][0]), fq(&j[1][1])),
        ))
        .unwrap()
    }
}
fn vector(path: impl AsRef<std::path::Path>) -> Vec<Fr> {
    std::fs::read(path)
        .unwrap()
        .as_chunks::<32>()
        .0
        .iter()
        .map(|b| bn254::decode_scalar(b).unwrap())
        .collect()
}
#[test]
#[ignore = "requires explicitly supplied ZKC_GROTH16_FIXTURE genuine snarkjs 0.7.5 fixtures"]
fn genuine_files_match_independent_snarkjs_and_bigint_reference() {
    let root = std::path::PathBuf::from(
        std::env::var_os("ZKC_GROTH16_FIXTURE").expect("set ZKC_GROTH16_FIXTURE"),
    );
    for depth in [2, 16] {
        let dir = root.join(format!("artifacts/depth{depth}"));
        let key = snarkjs::read_zkey(dir.join("final.zkey"), &Limits::default(), &p()).unwrap();
        let witness =
            snarkjs::read_wtns(dir.join("witness.wtns"), &Limits::default(), &p()).unwrap();
        key.assignment(&witness).unwrap();
        let j: serde_json::Value =
            serde_json::from_slice(&std::fs::read(dir.join("intermediates.json")).unwrap())
                .unwrap();
        assert_eq!(key.n_vars, j["nVars"].as_u64().unwrap() as usize);
        assert_eq!(key.domain_size, j["domainSize"].as_u64().unwrap() as usize);
        assert_eq!(key.n_public, j["nPublic"].as_u64().unwrap() as usize);
        assert_eq!(key.domain_root, sf(&j["omega"]));
        assert_eq!(key.coset_shift, sf(&j["inc"]));
        assert_eq!(key.alpha1, g1(&j["header"]["alpha1"]));
        assert_eq!(key.beta1, g1(&j["header"]["beta1"]));
        assert_eq!(key.delta1, g1(&j["header"]["delta1"]));
        assert_eq!(key.beta2, g2(&j["header"]["beta2"]));
        assert_eq!(key.gamma2, g2(&j["header"]["gamma2"]));
        assert_eq!(key.delta2, g2(&j["header"]["delta2"]));
        assert_eq!(witness.0.as_ref(), vector(dir.join("vectors/witness.frle")));
        for (m, name) in [(&key.qap_a, "A"), (&key.qap_b, "B")] {
            let mut got = vec![Fr::zero(); key.domain_size];
            for &(r, c, v) in m.entries() {
                got[r as usize] += v * witness.0[c as usize];
            }
            assert_eq!(
                got,
                vector(dir.join(format!("vectors/{name}_evaluations.frle")))
            );
        }
        let a = G1::msm(&witness.0, &key.a_query).unwrap();
        let b1 = G1::msm(&witness.0, &key.b1_query).unwrap();
        let b2 = G2::msm(&witness.0, &key.b2_query).unwrap();
        let l = G1::msm(&witness.0[key.n_public + 1..], &key.l_query).unwrap();
        let h = G1::msm(&vector(dir.join("vectors/P_coset.frle")), &key.h_query).unwrap();
        assert_eq!(a, g1(&j["msm"]["A"]));
        assert_eq!(b1, g1(&j["msm"]["B1"]));
        assert_eq!(b2, g2(&j["msm"]["B2"]));
        assert_eq!(l, g1(&j["msm"]["L"]));
        assert_eq!(h, g1(&j["msm"]["H"]));
        let vk: serde_json::Value =
            serde_json::from_slice(&std::fs::read(dir.join("vk.json")).unwrap()).unwrap();
        assert_eq!(
            key.ic.as_ref(),
            vk["IC"]
                .as_array()
                .unwrap()
                .iter()
                .map(g1)
                .collect::<Vec<_>>()
        );
        let proof: serde_json::Value =
            serde_json::from_slice(&std::fs::read(dir.join("proof-r1-s2.json")).unwrap()).unwrap();
        let pa = a.add(&key.alpha1).add(&key.delta1);
        let pb = b2.add(&key.beta2).add(&key.delta2.scale(Fr::from(2)));
        let bp = b1.add(&key.beta1).add(&key.delta1.scale(Fr::from(2)));
        let pc = l
            .add(&h)
            .add(&pa.scale(Fr::from(2)))
            .add(&bp)
            .add(&key.delta1.scale(-Fr::from(2)));
        assert_eq!(pa, g1(&proof["pi_a"]));
        assert_eq!(pb, g2(&proof["pi_b"]));
        assert_eq!(pc, g1(&proof["pi_c"]));
        let public = G1::msm(&witness.0[..key.n_public + 1], &key.ic).unwrap();
        assert!(
            bn254::pairing_check(
                &[pa.neg(), key.alpha1, public, pc],
                &[pb, key.beta2, key.gamma2, key.delta2]
            )
            .unwrap()
        );
    }
}
