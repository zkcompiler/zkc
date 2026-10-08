use super::support::*;
use zkc_backends::{Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::interactive::{Backend, PhysicalType, Representation, Value as RuntimeValue};
#[test]
fn new_codecs_are_domain_distinct_exact_and_canonical() {
    let backend = backend(Policy::default());
    let values = vec![
        (66, vector(false, &[2, 3])),
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
        if !zkc_backends::has_native_wire(&v.physical_type()) {
            assert!(backend.encode_native_value(&v).is_err());
            continue;
        }
        let bytes = backend.encode_native_value(&v).unwrap();
        assert_eq!(&bytes[..6], &[b'Z', b'K', b'C', b'V', 1, tag]);
        let decoded = backend
            .decode_native_value(&v.physical_type(), &bytes)
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
                    .decode_native_value(&v.physical_type(), &bytes[..n])
                    .is_err()
            );
        }
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_eq!(
            backend
                .decode_native_value(&v.physical_type(), &trailing)
                .unwrap_err()
                .to_string(),
            "native-wire-invalid:length"
        );
        let mut wrong = bytes.clone();
        wrong[5] = if tag == 66 { 14 } else { 66 };
        assert_eq!(
            backend
                .decode_native_value(&v.physical_type(), &wrong)
                .unwrap_err()
                .to_string(),
            "native-wire-invalid:header"
        );
        let mut malformed = bytes;
        malformed[6..].fill(255);
        assert!(
            backend
                .decode_native_value(&v.physical_type(), &malformed)
                .is_err()
        );
    }
    assert_eq!(
        backend.encode_native_value(&field(true, 2)).unwrap()[6..],
        [vec![2], vec![0; 31]].concat()
    );
    for d in [false, true] {
        let empty = call(d, "poly.from_coefficients", &[], vec![vector(d, &[0])]).remove(0);
        assert!(backend.encode_native_value(&empty).is_err());
        let v = if d {
            Value::RistrettoPolynomial(vec![RistrettoScalar::ZERO].into())
        } else {
            Value::Polynomial(vec![Scalar::from(0)].into())
        };
        assert_eq!(
            backend.validate_value(&v).unwrap_err().code,
            "refused:polynomial-normalization"
        );
        assert!(backend.encode_native_value(&v).is_err());
        let mut huge = backend.encode_native_value(&vector(d, &[])).unwrap();
        huge[6..10].copy_from_slice(&u32::MAX.to_le_bytes());
        assert_eq!(
            backend
                .decode_native_value(&vector(d, &[]).physical_type(), &huge)
                .unwrap_err()
                .to_string(),
            "native-wire-limit"
        );
    }
    let view = PhysicalType::new(
        vector(false, &[]).physical_type().logical(),
        Representation::FrDiagonal,
    )
    .unwrap();
    assert_eq!(
        backend
            .decode_native_value(
                &view,
                &backend.encode_native_value(&vector(false, &[])).unwrap()
            )
            .unwrap_err()
            .to_string(),
        "native-wire-backend:native-wire-type"
    );
}
#[test]
fn scalar_modulus_and_noncanonical_point_are_refused() {
    let b = backend(Policy::default());
    let mut bytes = b.encode_native_value(&field(true, 0)).unwrap();
    // Dalek scalar order: 2^252 + 27742317777372353535851937790883648493.
    bytes[6..].copy_from_slice(&[
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
    ]);
    assert_eq!(
        b.decode_native_value(&field(true, 0).physical_type(), &bytes)
            .unwrap_err()
            .to_string(),
        "native-wire-invalid:scalar"
    );
    bytes[6] -= 1;
    assert!(
        b.decode_native_value(&field(true, 0).physical_type(), &bytes)
            .is_ok()
    );
    let g = call(true, "curve.generator", &[], vec![]).remove(0);
    let mut bytes = b.encode_native_value(&g).unwrap();
    bytes[6..].fill(255);
    assert_eq!(
        b.decode_native_value(&g.physical_type(), &bytes)
            .unwrap_err()
            .to_string(),
        "native-wire-invalid:group"
    );
}
#[test]
fn native_inputs_keep_polynomial_normalization_local() {
    for d in [false, true] {
        let b = super::support::backend(Policy::default());
        let polynomial = call(d, "poly.from_coefficients", &[], vec![vector(d, &[2, 3])]).remove(0);
        assert!(!zkc_backends::has_native_wire(&polynomial.physical_type()));
        assert!(b.encode_native_value(&polynomial).is_err());
        assert_value(
            &call(
                d,
                "poly.univariate_evaluate",
                &[],
                vec![polynomial, field(d, 5)],
            )[0],
            &field(d, 17),
        );
        let invalid = if d {
            Value::RistrettoPolynomial(vec![RistrettoScalar::ZERO].into())
        } else {
            Value::Polynomial(vec![Scalar::from(0)].into())
        };
        assert_eq!(
            b.validate_value(&invalid).unwrap_err().code,
            "refused:polynomial-normalization"
        );
    }
}

#[test]
fn fixed_native_bytes_and_local_only_values_do_not_depend_on_decoder_agreement() {
    let b = backend(Policy::default());
    let scalar_bytes = |n: u64| [n.to_le_bytes().to_vec(), vec![0; 24]].concat();
    for d in [false, true] {
        for (tag, v) in [
            (if d { 14 } else { 66 }, vector(d, &[2, 3])),
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
            if !zkc_backends::has_native_wire(&v.physical_type()) {
                assert!(b.encode_native_value(&v).is_err());
                continue;
            }
            let expected = [
                b"ZKCV\x01".to_vec(),
                vec![tag],
                2u32.to_le_bytes().to_vec(),
                scalar_bytes(2),
                scalar_bytes(3),
            ]
            .concat();
            assert_eq!(b.encode_native_value(&v).unwrap(), expected);
        }
    }
    let round = Value::RistrettoRound([1u64, 2, 3].map(RistrettoScalar::from));
    assert!(b.encode_native_value(&round).is_err());
    let generator = call(true, "curve.generator", &[], vec![]).remove(0);
    let hex = zkc_test_support::hex(&b.encode_native_value(&generator).unwrap());
    assert_eq!(
        hex,
        "5a4b43560110e2f2ae0a6abc4e71a884a961c500515f58e30b6aa582dd8db6a65945e08d2d76"
    );
}
