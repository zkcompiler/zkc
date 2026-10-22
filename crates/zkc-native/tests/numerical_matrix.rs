//! Reached numerical calls through the existing physical binding and VM path.
#[path = "domains/support.rs"]
mod support;

use p3_field::BasedVectorSpace;
use std::ops::{Add, Mul};
use support::{Controlled, assert_value, backend, one};
use zkc_native::{
    Bn254Scalar, KoalaBear, KoalaBearExt4, KoalaBearExt8, Policy, RistrettoScalar, Scalar, Value,
    domains,
};
use zkc_runtime::vm::OperationBinding;

fn binding(domain: domains::NativeDomain, operation: &str) -> OperationBinding {
    OperationBinding {
        contract: operation.into(),
        arguments: vec![domain.field.name().into()],
        implementation: format!("{}/{operation}", domain.provider),
        physical_arguments: vec![],
    }
}

fn matrix<F: Copy + Add<Output = F> + Mul<Output = F>>(
    domain: domains::NativeDomain,
    values: [F; 6],
    zero: F,
    vector: fn(Vec<F>) -> Value,
) {
    let [a, b, c, d, e, f] = values;
    let input = vector(values.to_vec());
    let cases = [
        (
            ["2", "3", "0"],
            vec![d, e, f],
            vec![a * d + b * e + c * f, d * d + e * e + f * f],
        ),
        (
            ["2", "3", "1"],
            vec![e, f],
            vec![a * e + d * f, b * e + e * f, c * e + f * f],
        ),
    ];
    for (shape, right, expected) in cases {
        let (result, native) = one(
            backend(Policy::default()),
            binding(domain, "vector.matvec"),
            &shape,
            vec![input.clone(), vector(right)],
        );
        assert_value(&result.unwrap()[0], &vector(expected));
        assert_eq!(native.active_frames(), 0);
        assert_value(&input, &vector(values.to_vec()));
    }
    // The same backing can be borrowed twice. No uniqueness is required.
    let aliased = vector(vec![a, b, c]);
    let result = one(
        backend(Policy::default()),
        binding(domain, "vector.matvec"),
        &["1", "3", "0"],
        vec![aliased.clone(), aliased.clone()],
    )
    .0
    .unwrap();
    assert_value(&result[0], &vector(vec![a * a + b * b + c * c]));
    assert_value(&aliased, &vector(vec![a, b, c]));
    for shape in [["3", "0", "0"], ["0", "3", "1"]] {
        assert_value(
            &one(
                backend(Policy::default()),
                binding(domain, "vector.matvec"),
                &shape,
                vec![vector(vec![]), vector(vec![])],
            )
            .0
            .unwrap()[0],
            &vector(vec![zero; 3]),
        );
    }
}

#[test]
fn dense_views_preserve_all_eight_field_families() {
    matrix(
        domains::BLS,
        [1u64, 2, 3, 5, 8, 13].map(Scalar::from),
        Scalar::from(0),
        |v| Value::Vector(v.into()),
    );
    matrix(
        domains::BN254_G1,
        [1u64, 2, 3, 5, 8, 13].map(Bn254Scalar::from),
        Bn254Scalar::from(0),
        |v| Value::Bn254Vector(v.into()),
    );
    matrix(
        domains::RISTRETTO,
        [1u64, 2, 3, 5, 8, 13].map(RistrettoScalar::from),
        RistrettoScalar::from(0u64),
        |v| Value::RistrettoVector(v.into()),
    );
    matrix(
        domains::KOALA_BEAR,
        [1, 2, 3, 5, 8, 13].map(KoalaBear::new),
        KoalaBear::new(0),
        |v| Value::KoalaBearVector(v.into()),
    );
    matrix(
        domains::KOALA_BEAR_EXT4,
        [1, 2, 3, 5, 8, 13]
            .map(|n| KoalaBearExt4::from_basis_coefficients_fn(|i| KoalaBear::new(n + i as u32))),
        KoalaBearExt4::from(KoalaBear::new(0)),
        |v| Value::KoalaBearExt4Vector(v.into()),
    );
    matrix(
        domains::KOALA_BEAR_EXT8,
        [1, 2, 3, 5, 8, 13]
            .map(|n| KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new(n + i as u32))),
        KoalaBearExt8::from(KoalaBear::new(0)),
        |v| Value::KoalaBearExt8Vector(v.into()),
    );
    use zkc_kernels::plonky3::binary::ext3_from_bits;
    use zkc_kernels::plonky3::binary::from_bits;
    matrix(
        domains::BINARY64,
        [1, 2, 3, 5, 8, 1 << 63].map(from_bits),
        from_bits(0),
        |v| Value::Binary64Vector(v.into()),
    );
    matrix(
        domains::BINARY64_EXT3,
        [1, 2, 3, 5, 8, 13].map(|n| ext3_from_bits([n, n + 1, n + 3])),
        ext3_from_bits([0; 3]),
        |v| Value::Binary64Ext3Vector(v.into()),
    );
}

fn bls(values: &[u64]) -> Value {
    Value::Vector(
        values
            .iter()
            .copied()
            .map(Scalar::from)
            .collect::<Vec<_>>()
            .into(),
    )
}

#[test]
fn matrix_limits_are_reached_after_existing_shape_and_output_checks() {
    let args = vec![bls(&[1, 2, 3, 4, 5, 6]), bls(&[2, 3, 4])];
    let exact = Policy {
        max_numerical_work: 14,
        max_numerical_bytes: 384,
        ..Policy::default()
    };
    let cases = [
        (exact, 320, None),
        (
            Policy {
                max_numerical_work: 13,
                ..exact
            },
            320,
            Some("exhausted:numerical-work"),
        ),
        (
            Policy {
                max_numerical_bytes: 383,
                ..exact
            },
            320,
            Some("exhausted:numerical-bytes"),
        ),
        (
            Policy {
                max_numerical_work: 0,
                ..exact
            },
            319,
            Some("exhausted:output-bytes"),
        ),
    ];
    for (policy, available, error) in cases {
        let mut controlled = Controlled::new(backend(policy));
        controlled.output_limit = Some(available);
        let (result, observed) = one(
            controlled,
            binding(domains::BLS, "vector.matvec"),
            &["2", "3", "0"],
            args.clone(),
        );
        if let Some(error) = error {
            assert_eq!(result.unwrap_err(), error);
            assert!(observed.outputs.is_empty());
        } else {
            assert_value(&result.unwrap()[0], &bls(&[20, 47]));
        }
        assert_eq!(observed.inner.active_frames(), 0);
    }
    let mut controlled = Controlled::new(backend(Policy {
        max_numerical_work: 0,
        ..exact
    }));
    controlled.output_limit = Some(0);
    assert_eq!(
        one(
            controlled,
            binding(domains::BLS, "vector.matvec"),
            &["2", "2", "0"],
            args
        )
        .0
        .unwrap_err(),
        "refused:length-mismatch"
    );
}

#[test]
fn split_preflights_the_result_tuple_and_overlapping_construction() {
    let exact = Policy {
        max_numerical_work: 8,
        max_numerical_bytes: 768,
        ..Policy::default()
    };
    for (policy, available, error) in [
        (exact, 640, None),
        (exact, 639, Some("exhausted:output-bytes")),
        (
            Policy {
                max_value_bytes: 640,
                ..exact
            },
            4096,
            None,
        ),
        (
            Policy {
                max_value_bytes: 639,
                ..exact
            },
            4096,
            Some("exhausted:output-bytes"),
        ),
        (
            Policy {
                max_numerical_bytes: 767,
                ..exact
            },
            640,
            Some("exhausted:numerical-bytes"),
        ),
    ] {
        let mut controlled = Controlled::new(backend(policy));
        controlled.output_limit = Some(available);
        let (result, observed) = one(
            controlled,
            binding(domains::BLS, "vector.split"),
            &[],
            vec![bls(&[1, 2, 3, 4])],
        );
        if let Some(error) = error {
            assert_eq!(result.unwrap_err(), error);
            assert!(observed.outputs.is_empty());
        } else {
            let result = result.unwrap();
            assert_value(&result[0], &bls(&[1, 2]));
            assert_value(&result[1], &bls(&[3, 4]));
        }
        assert_eq!(observed.inner.active_frames(), 0);
    }
}

#[test]
fn equal_width_fields_do_not_share_a_numerical_view() {
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.substitute = Some(Value::Bn254Vector(vec![Bn254Scalar::from(1); 6].into()));
    let (result, observed) = one(
        controlled,
        binding(domains::BLS, "vector.matvec"),
        &["2", "3", "0"],
        vec![bls(&[1, 2, 3, 4, 5, 6]), bls(&[1, 2, 3])],
    );
    assert!(result.is_err());
    assert!(observed.outputs.is_empty());
    assert_eq!(observed.inner.active_frames(), 0);
}
