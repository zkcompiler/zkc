//! Content binding through admitted programs, independently encoded JSON and
//! immutable matrix wire roundtrips. No relation or ceremony claim is inferred.
#[path = "domains/support.rs"]
mod support;
use serde_json::json;
use sha2::{Digest, Sha256};
use support::{Controlled, backend, one, program};
use zkc_backends::{Bn254Scalar, KoalaBear, KoalaBearExt8, Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::interactive::{ErrorCode, OperationBinding, Value as _, admit_supplied};

const FIELDS: [(&str, &str, &str); 5] = [
    (
        "bls12-381.fr",
        "arkworks",
        "b705fd8553a70057dbc07b5591e77dc7328c830cb00ac1de439729e45a829c4a",
    ),
    (
        "ristretto255.scalar",
        "dalek",
        "8ee4645c3fbe10d61447c9b316f45106e83bab4b3541f34706c6af82309da697",
    ),
    (
        "koala-bear",
        "plonky3",
        "ca6ac1dbd3527b0815a4cb6fc29d0d2c4f2bcfbf9232924362a6c8cbbffda611",
    ),
    (
        "koala-bear.ext8-binomial3",
        "plonky3",
        "3c3b88a95c23915d5f6b5e09d0aec4a39931171cf54c2b20f42490e0f30fdea4",
    ),
    (
        "bn254.fr",
        "arkworks",
        "1bf0ad4a12f8657d39a40e8407721fce89901fb19013004be47d66b49fecdaa4",
    ),
];
fn binding(d: usize) -> OperationBinding {
    OperationBinding {
        contract: "matrix.identity_check".into(),
        arguments: vec![FIELDS[d].0.into()],
        implementation: format!("{}/matrix.identity_check", FIELDS[d].1),
    }
}
fn matrix(d: usize, rows: usize, columns: usize, entries: &[(u32, u32, u64)]) -> Value {
    let p = Policy::default();
    macro_rules! make {
        ($constructor:ident, $convert:expr) => {
            Value::$constructor(
                rows,
                columns,
                &entries
                    .iter()
                    .map(|&(r, c, a)| (r, c, ($convert)(a)))
                    .collect::<Vec<_>>(),
                &p,
            )
            .unwrap()
        };
    }
    match d {
        0 => make!(matrix, Scalar::from),
        1 => make!(ristretto_matrix, RistrettoScalar::from),
        2 => make!(koala_bear_matrix, |a| KoalaBear::new(a as u32)),
        3 => make!(koala_bear_ext8_matrix, |a| KoalaBearExt8::from(
            KoalaBear::new(a as u32)
        )),
        4 => make!(bn254_matrix, Bn254Scalar::from),
        _ => unreachable!(),
    }
}
fn digest(field: &str, rows: usize, columns: usize, entries: &[(u32, u32, String)]) -> String {
    let entries = entries
        .iter()
        .map(|(r, c, a)| json!([r.to_string(), c.to_string(), a]))
        .collect::<Vec<_>>();
    let bytes = serde_json::to_vec(&json!([
        "zkc.matrix/1",
        field,
        [rows.to_string(), columns.to_string(), entries]
    ]))
    .unwrap();
    format!("{:x}", Sha256::digest(bytes))
}
fn check(d: usize, value: Value, hash: &str) -> bool {
    let out = one(backend(Policy::default()), binding(d), &[hash], vec![value])
        .0
        .unwrap();
    let [Value::Bool(result)] = out.as_slice() else {
        panic!("expected bool")
    };
    *result
}

#[test]
fn exact_content_binding_all_carriers_and_wire_roundtrip() {
    for (d, &(field, _, known)) in FIELDS.iter().enumerate() {
        let expected = digest(field, 4, 8, &[(0, 1, "7".into()), (1, 3, "11".into())]);
        assert_eq!(expected, known); // Independent Python hashlib vectors.
        let m = matrix(d, 4, 8, &[(0, 1, 7), (1, 3, 11)]);
        assert!(check(d, m.clone(), known));
        let b = backend(Policy::default());
        let decoded = b
            .decode_typed_value(m.physical_type(), &b.encode_value(&m).unwrap())
            .unwrap();
        assert!(check(d, decoded, known));
        // Actual same-shape, same-nnz coefficient mismatch, not a shape refusal.
        assert!(!check(d, matrix(d, 4, 8, &[(0, 1, 8), (1, 3, 11)]), known));
        assert!(!check(d, matrix(d, 4, 8, &[(0, 2, 7), (1, 3, 11)]), known));
        assert!(!check(d, matrix(d, 2, 8, &[(0, 1, 7), (1, 3, 11)]), known));
        assert!(!check(d, matrix(d, 4, 4, &[(0, 1, 7), (1, 3, 11)]), known));
        assert!(!check(d, m.clone(), FIELDS[(d + 1) % FIELDS.len()].2));
        assert!(!check(d, m, &"0".repeat(64)));
        for (rows, columns) in [(0, 0), (0, 8), (4, 0), (4, 8), (65536, 65536)] {
            let hash = digest(field, rows, columns, &[]);
            assert!(check(d, matrix(d, rows, columns, &[]), &hash));
        }
    }
}

#[test]
fn canonical_coefficients_ignore_arithmetic_and_storage_spelling() {
    // Same canonical value reached via field arithmetic, not raw limb/wire
    // spelling. Maximal representatives catch accidental u64 truncation and
    // Montgomery hashing. Source COO normalization is tested by the compiler.
    let p = Policy::default();
    let b = Scalar::from(9) + Scalar::from(5) - Scalar::from(7);
    let r = RistrettoScalar::from(9u64) + RistrettoScalar::from(5u64) - RistrettoScalar::from(7u64);
    let k = KoalaBear::new(9) + KoalaBear::new(5) - KoalaBear::new(7);
    let n = Bn254Scalar::from(9) + Bn254Scalar::from(5) - Bn254Scalar::from(7);
    let values = [
        Value::matrix(4, 8, &[(0, 1, b), (1, 3, Scalar::from(11))], &p).unwrap(),
        Value::ristretto_matrix(4, 8, &[(0, 1, r), (1, 3, RistrettoScalar::from(11u64))], &p)
            .unwrap(),
        Value::koala_bear_matrix(4, 8, &[(0, 1, k), (1, 3, KoalaBear::new(11))], &p).unwrap(),
        Value::koala_bear_ext8_matrix(
            4,
            8,
            &[(0, 1, k.into()), (1, 3, KoalaBear::new(11).into())],
            &p,
        )
        .unwrap(),
        Value::bn254_matrix(4, 8, &[(0, 1, n), (1, 3, Bn254Scalar::from(11))], &p).unwrap(),
    ];
    for (d, m) in values.into_iter().enumerate() {
        assert!(check(d, m, FIELDS[d].2));
    }
    let maximal = [
        (
            0,
            Value::matrix(1, 1, &[(0, 0, -Scalar::from(1))], &p).unwrap(),
            "52435875175126190479447740508185965837690552500527637822603658699938581184512",
        ),
        (
            1,
            Value::ristretto_matrix(1, 1, &[(0, 0, -RistrettoScalar::ONE)], &p).unwrap(),
            "7237005577332262213973186563042994240857116359379907606001950938285454250988",
        ),
        (
            2,
            Value::koala_bear_matrix(1, 1, &[(0, 0, -KoalaBear::new(1))], &p).unwrap(),
            "2130706432",
        ),
        (
            4,
            Value::bn254_matrix(1, 1, &[(0, 0, -Bn254Scalar::from(1))], &p).unwrap(),
            "21888242871839275222246405745257275088548364400416034343698204186575808495616",
        ),
    ];
    for (d, m, a) in maximal {
        assert!(check(d, m, &digest(FIELDS[d].0, 1, 1, &[(0, 0, a.into())])));
    }
    // Extension coordinates cannot collapse to the base-field component.
    let ext = KoalaBearExt8::from([
        KoalaBear::new(1),
        KoalaBear::new(2),
        KoalaBear::new(0),
        KoalaBear::new(0),
        KoalaBear::new(0),
        KoalaBear::new(0),
        KoalaBear::new(0),
        KoalaBear::new(0),
    ]);
    let m = Value::koala_bear_ext8_matrix(1, 1, &[(0, 0, ext)], &p).unwrap();
    assert!(check(
        3,
        m.clone(),
        &digest(FIELDS[3].0, 1, 1, &[(0, 0, "4261412867".into())])
    ));
    assert!(!check(
        3,
        m,
        &digest(FIELDS[3].0, 1, 1, &[(0, 0, "1".into())])
    ));
    let ext = KoalaBearExt8::from([KoalaBear::new(2_130_706_432); 8]);
    let m = Value::koala_bear_ext8_matrix(1, 1, &[(0, 0, ext)], &p).unwrap();
    assert!(check(
        3,
        m,
        &digest(
            FIELDS[3].0,
            1,
            1,
            &[(
                0,
                0,
                "424804331891979973455971894938199991873140910988886521584080257519598960640"
                    .into()
            )]
        )
    ));
}

#[test]
fn malformed_digest_refused_by_admission_and_backend() {
    let bad = [
        vec![],
        vec!["".into()],
        vec!["0".repeat(63)],
        vec!["0".repeat(65)],
        vec!["A".repeat(64)],
        vec!["g".repeat(64)],
        vec!["é".repeat(32)],
        vec![format!("{} ", "0".repeat(63))],
        vec!["0".repeat(64), "0".repeat(64)],
    ];
    for (d, &(_, _, expected)) in FIELDS.iter().enumerate() {
        for attrs in &bad {
            let row = binding(d);
            let sig = row.signature().unwrap();
            let bytes = program(
                &[row],
                &sig.inputs,
                vec![json!(["op", "site", "b0", attrs, ["a0"], ["ok"]])],
                &sig.outputs,
                &["ok".into()],
            );
            let b = backend(Policy::default());
            let err = match admit_supplied(&bytes, &b) {
                Ok(_) => panic!("admitted bad digest"),
                Err(e) => e,
            };
            assert_eq!(err.code, ErrorCode::Attributes);
            let mut controlled = Controlled::new(b);
            controlled.attributes = Some(attrs.clone());
            assert_eq!(
                one(
                    controlled,
                    binding(d),
                    &[expected],
                    vec![matrix(d, 4, 8, &[(0, 1, 7), (1, 3, 11)])]
                )
                .0
                .unwrap_err(),
                "refused:kernel-attributes"
            );
        }
    }
}

#[test]
fn identity_check_preserves_carrier_and_output_policy_checks() {
    for (d, &(_, _, expected)) in FIELDS.iter().enumerate() {
        let mut b = Controlled::new(backend(Policy::default()));
        b.substitute = Some(matrix(
            (d + 1) % FIELDS.len(),
            4,
            8,
            &[(0, 1, 7), (1, 3, 11)],
        ));
        assert_eq!(
            one(
                b,
                binding(d),
                &[expected],
                vec![matrix(d, 4, 8, &[(0, 1, 7), (1, 3, 11)])]
            )
            .0
            .unwrap_err(),
            "refused:kernel-operands"
        );
        let mut b = Controlled::new(backend(Policy::default()));
        b.output_limit = Some(0);
        assert!(
            one(
                b,
                binding(d),
                &[expected],
                vec![matrix(d, 4, 8, &[(0, 1, 7), (1, 3, 11)])]
            )
            .0
            .unwrap_err()
            .starts_with("exhausted:")
        );
    }
}
