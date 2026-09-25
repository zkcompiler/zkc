use super::support::*;
use zkc_backends::{Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::interactive::{Backend, PhysicalType, Representation, Value as RuntimeValue};
#[test]
fn new_codecs_are_domain_distinct_exact_and_canonical() {
    let backend = backend(Policy::default());
    let values = vec![
        (11, vector(false, &[2, 3])),
        (12, Value::Polynomial(vec![Scalar::from(2)].into())),
        (13, field(true, 2)),
        (14, vector(true, &[2, 3])),
        (
            15,
            Value::RistrettoPolynomial(vec![RistrettoScalar::from(2u64)].into()),
        ),
        (16, call(true, "curve.generator", &[], vec![]).remove(0)),
        (17, groups(true, &[1, 2])),
        (
            18,
            Value::RistrettoRound([1u64, 2, 3].map(RistrettoScalar::from)),
        ),
    ];
    for (tag, v) in values {
        let bytes = backend.encode_value(&v).unwrap();
        assert_eq!(&bytes[..6], &[b'Z', b'K', b'C', b'V', 1, tag]);
        let decoded = backend
            .decode_typed_value(v.physical_type(), &bytes)
            .unwrap();
        assert_value(&v, &decoded);
        assert!(
            Value::typed_wire_retained_bytes_bound(
                v.physical_type(),
                bytes.len(),
                backend.policy()
            )
            .unwrap()
                >= decoded.retained_bytes()
        );
        for n in 0..bytes.len() {
            assert!(
                backend
                    .decode_typed_value(v.physical_type(), &bytes[..n])
                    .is_err()
            );
        }
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_eq!(
            backend
                .decode_typed_value(v.physical_type(), &trailing)
                .unwrap_err()
                .code,
            "refused:wire-length"
        );
        let mut wrong = bytes.clone();
        wrong[5] = if tag == 11 { 14 } else { 11 };
        assert_eq!(
            backend
                .decode_typed_value(v.physical_type(), &wrong)
                .unwrap_err()
                .code,
            "refused:wire-header"
        );
        let mut malformed = bytes;
        malformed[6..].fill(255);
        assert!(
            backend
                .decode_typed_value(v.physical_type(), &malformed)
                .is_err()
        );
    }
    assert_eq!(
        backend.encode_value(&field(true, 2)).unwrap()[6..],
        [vec![2], vec![0; 31]].concat()
    );
    for d in [false, true] {
        let empty = call(d, "poly.from_coefficients", &[], vec![vector(d, &[0])]).remove(0);
        let mut bytes = backend.encode_value(&empty).unwrap();
        assert_eq!(bytes.len(), 10);
        bytes[6..10].copy_from_slice(&1u32.to_le_bytes());
        bytes.extend([0; 32]);
        assert_eq!(
            backend
                .decode_typed_value(empty.physical_type(), &bytes)
                .unwrap_err()
                .code,
            "refused:polynomial-normalization"
        );
        let v = if d {
            Value::RistrettoPolynomial(vec![RistrettoScalar::ZERO].into())
        } else {
            Value::Polynomial(vec![Scalar::from(0)].into())
        };
        assert_eq!(
            backend.validate_value(&v).unwrap_err().code,
            "refused:polynomial-normalization"
        );
        assert!(backend.encode_value(&v).is_err());
        let mut huge = backend.encode_value(&vector(d, &[])).unwrap();
        huge[6..10].copy_from_slice(&u32::MAX.to_le_bytes());
        assert_eq!(
            backend
                .decode_typed_value(vector(d, &[]).physical_type(), &huge)
                .unwrap_err()
                .code,
            "refused:wire-length"
        );
    }
    let view = PhysicalType::new(
        vector(false, &[]).physical_type().logical(),
        Representation::FrDiagonal,
    )
    .unwrap();
    assert_eq!(
        backend
            .decode_typed_value(view, &backend.encode_value(&vector(false, &[])).unwrap())
            .unwrap_err()
            .code,
        "refused:nonserializable"
    );
}
#[test]
fn scalar_modulus_and_noncanonical_point_are_refused() {
    let b = backend(Policy::default());
    let mut bytes = b.encode_value(&field(true, 0)).unwrap();
    // Dalek scalar order: 2^252 + 27742317777372353535851937790883648493.
    bytes[6..].copy_from_slice(&[
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
    ]);
    assert_eq!(
        b.decode_typed_value(field(true, 0).physical_type(), &bytes)
            .unwrap_err()
            .code,
        "refused:noncanonical-scalar"
    );
    bytes[6] -= 1;
    assert!(
        b.decode_typed_value(field(true, 0).physical_type(), &bytes)
            .is_ok()
    );
    let g = call(true, "curve.generator", &[], vec![]).remove(0);
    let mut bytes = b.encode_value(&g).unwrap();
    bytes[6..].fill(255);
    assert_eq!(
        b.decode_typed_value(g.physical_type(), &bytes)
            .unwrap_err()
            .code,
        "refused:noncanonical-point"
    );
}
#[test]
fn tool_json_ingress_uses_admitted_domain_and_checks_polynomial_normalization() {
    use serde_json::json;
    use zkc_backends::InputBindings;
    use zkc_runtime::interactive::admit_supplied;
    for d in [false, true] {
        let b = super::support::backend(Policy::default());
        let bind = binding(d, "poly.univariate_evaluate");
        let sig = bind.signature().unwrap();
        let bytes = program(
            &[bind],
            &sig.inputs,
            vec![json!(["op", "site", "b0", [], ["a0", "a1"], ["x"]])],
            &sig.outputs,
            &["x".into()],
        );
        let admitted = admit_supplied(&bytes, &b).unwrap();
        let role = admitted.entry("main").unwrap().remove(0);
        let input = json!([
            "zkc.inputs/1",
            [["a0", ["polynomial", ["2", "3"]]], ["a1", ["field", "5"]]]
        ]);
        let values = b
            .inputs_from_json(
                &role,
                &serde_json::to_vec(&input).unwrap(),
                &InputBindings::new(),
            )
            .unwrap();
        assert_value(
            &super::support::run_program(b, &bytes, values).0.unwrap()[0],
            &field(d, 17),
        );
        let b = super::support::backend(Policy::default());
        let mut invalid = input;
        invalid[1][0][1][1] = json!(["2", "0"]);
        assert_eq!(
            b.inputs_from_json(
                &role,
                &serde_json::to_vec(&invalid).unwrap(),
                &InputBindings::new()
            )
            .unwrap_err()
            .code,
            "refused:polynomial-normalization"
        );
    }
}

#[test]
fn fixed_vector_polynomial_round_bytes_do_not_depend_on_decoder_agreement() {
    let b = backend(Policy::default());
    let scalar_bytes = |n: u64| [n.to_le_bytes().to_vec(), vec![0; 24]].concat();
    for d in [false, true] {
        for (tag, v) in [
            (if d { 14 } else { 11 }, vector(d, &[2, 3])),
            (
                if d { 15 } else { 12 },
                call(
                    d,
                    "poly.from_coefficients",
                    &[],
                    vec![vector(d, &[2, 3, 0])],
                )
                .remove(0),
            ),
        ] {
            let expected = [
                b"ZKCV\x01".to_vec(),
                vec![tag],
                2u32.to_le_bytes().to_vec(),
                scalar_bytes(2),
                scalar_bytes(3),
            ]
            .concat();
            assert_eq!(b.encode_value(&v).unwrap(), expected);
        }
    }
    let round = Value::RistrettoRound([1u64, 2, 3].map(RistrettoScalar::from));
    assert_eq!(
        b.encode_value(&round).unwrap(),
        [
            b"ZKCV\x01\x12".to_vec(),
            scalar_bytes(1),
            scalar_bytes(2),
            scalar_bytes(3)
        ]
        .concat()
    );
    let generator = call(true, "curve.generator", &[], vec![]).remove(0);
    let hex = zkc_test_support::hex(&b.encode_value(&generator).unwrap());
    assert_eq!(
        hex,
        "5a4b43560110e2f2ae0a6abc4e71a884a961c500515f58e30b6aa582dd8db6a65945e08d2d76"
    );
}
