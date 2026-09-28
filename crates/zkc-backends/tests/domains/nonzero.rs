use super::support::*;
use zkc_arkworks::NonzeroScalar;
use zkc_backends::{Policy, Scalar, Value};
use zkc_runtime::interactive::{Backend, LogicalType, PhysicalType, Value as RuntimeValue};

fn nonzero(n: u64) -> Value {
    Value::NonzeroField(NonzeroScalar::new(Scalar::from(n)).unwrap())
}

#[test]
fn nonzero_wire_refuses_zero_noncanonical_bytes_and_field_confusion() {
    let backend = backend(Policy::default());
    let value = nonzero(7);
    let bytes = backend.encode_value(&value).unwrap();
    assert_eq!(&bytes[..6], b"ZKCV\x01\x32");
    assert_eq!(bytes.len(), 38);
    assert_value(
        &backend
            .decode_typed_value(value.physical_type(), &bytes)
            .unwrap(),
        &value,
    );
    assert!(
        Value::typed_wire_retained_bytes_bound(
            value.physical_type(),
            bytes.len(),
            backend.policy()
        )
        .unwrap()
            >= value.retained_bytes()
    );
    for payload in [[0; 32], [255; 32]] {
        let mut bad = bytes.clone();
        bad[6..].copy_from_slice(&payload);
        assert!(
            backend
                .decode_typed_value(value.physical_type(), &bad)
                .is_err()
        );
    }
    for length in 0..bytes.len() {
        assert!(
            backend
                .decode_typed_value(value.physical_type(), &bytes[..length])
                .is_err()
        );
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(
        backend
            .decode_typed_value(value.physical_type(), &trailing)
            .is_err()
    );
    let scalar = field(false, 7);
    assert!(
        backend
            .decode_typed_value(scalar.physical_type(), &bytes)
            .is_err()
    );
    assert!(
        backend
            .decode_typed_value(
                value.physical_type(),
                &backend.encode_value(&scalar).unwrap()
            )
            .is_err()
    );
    assert_value(
        &call(false, "field.from_nonzero", &[], vec![value])[0],
        &scalar,
    );
    for domain in ["bn254.fr", "ristretto255.scalar", "koala-bear"] {
        assert!(LogicalType::parse(&format!("nonzero_field:{domain}")).is_err());
    }
    assert!(PhysicalType::parse("nonzero_field:bls12-381.fr@arkworks.fr/1").is_err());
    for name in ["field.from_nonzero", "random.draw_nonzero"] {
        let b = binding(false, name);
        assert_eq!(backend.binding_signature(&b), Some(b.signature().unwrap()));
        assert!(binding(true, name).signature().is_err());
    }
}

#[cfg(feature = "test-utils")]
#[test]
fn nonzero_queries_advance_once_and_equal_answers_are_permitted() {
    let mut backend = backend(Policy::default());
    let rng = backend
        .issue_test_tape(
            domain(),
            2,
            vec![Scalar::from(0), Scalar::from(7), Scalar::from(7)],
        )
        .unwrap();
    let Value::Rng(handle) = &rng else { panic!() };
    let handle = handle.clone();
    let (first, backend) = one(
        backend,
        binding(false, "random.draw_nonzero"),
        &[],
        vec![rng],
    );
    let first = first.unwrap();
    assert_value(&first[0], &nonzero(7));
    let (second, backend) = one(
        backend,
        binding(false, "random.draw_nonzero"),
        &[],
        vec![first[1].clone()],
    );
    assert_value(&second.unwrap()[0], &nonzero(7));
    let state = backend.observe(&handle).unwrap();
    assert_eq!(
        (state.generation, state.draw_count, state.budget),
        (2, 2, 0)
    );
}

#[cfg(feature = "test-utils")]
#[test]
fn nonzero_exhaustion_keeps_the_consumed_generation() {
    let mut backend = backend(Policy::default());
    let rng = backend
        .issue_test_tape(
            domain(),
            1,
            vec![Scalar::from(0); zkc_arkworks::NONZERO_SAMPLING_ATTEMPTS],
        )
        .unwrap();
    let Value::Rng(handle) = &rng else { panic!() };
    let handle = handle.clone();
    let (result, backend) = one(
        backend,
        binding(false, "random.draw_nonzero"),
        &[],
        vec![rng],
    );
    assert_eq!(result.unwrap_err(), "exhausted:sampling-limit");
    let state = backend.observe(&handle).unwrap();
    assert_eq!(
        (state.generation, state.draw_count, state.budget),
        (1, 1, 0)
    );
}
