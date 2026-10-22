//! General dense primitives through reached native calls, with exact scope limits.
#[path = "domains/support.rs"]
mod support;

use p3_field::BasedVectorSpace;
use std::{
    mem::size_of,
    ops::{Add, Mul, Neg, Sub},
    sync::Arc,
};
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
    }
}

struct Limits {
    output: usize,
    memory: usize,
    work: u64,
}

fn check_limits(
    domain: domains::NativeDomain,
    operation: &str,
    attributes: &[&str],
    args: Vec<Value>,
    expected: Value,
    limits: Limits,
) {
    let exact = Policy {
        max_numerical_bytes: limits.memory,
        max_numerical_work: limits.work,
        ..Policy::default()
    };
    let encoder = backend(Policy::default());
    let original: Vec<_> = args
        .iter()
        .map(|value| encoder.encode_native_value(value).unwrap())
        .collect();
    for (policy, available, error) in [
        (exact, limits.output, None),
        (exact, limits.output - 1, Some("exhausted:output-bytes")),
        (
            Policy {
                max_numerical_work: limits.work - 1,
                ..exact
            },
            limits.output,
            Some("exhausted:numerical-work"),
        ),
        (
            Policy {
                max_numerical_bytes: limits.memory - 1,
                ..exact
            },
            limits.output,
            Some("exhausted:numerical-bytes"),
        ),
    ] {
        let mut controlled = Controlled::new(backend(policy));
        controlled.output_limit = Some(available);
        let (result, observed) = one(
            controlled,
            binding(domain, operation),
            attributes,
            args.clone(),
        );
        if let Some(error) = error {
            assert_eq!(result.unwrap_err(), error, "{operation}");
            assert!(observed.outputs.is_empty(), "{operation}");
        } else {
            let result = result.unwrap();
            assert_eq!(result.len(), 1, "{operation}");
            assert_value(&result[0], &expected);
            assert_eq!(observed.outputs.len(), 1, "{operation}");
        }
        assert_eq!(observed.inner.active_frames(), 0, "{operation}");
        for (value, original) in args.iter().zip(&original) {
            assert_eq!(
                encoder.encode_native_value(value).unwrap(),
                *original,
                "{operation} mutated an input"
            );
        }
    }
}

fn storage<F>(
    domain: domains::NativeDomain,
    samples: [F; 3],
    zero: F,
    identity: F,
    field: fn(F) -> Value,
    vector: fn(Vec<F>) -> Value,
) where
    F: Copy + Add<Output = F> + Sub<Output = F> + Mul<Output = F> + Neg<Output = F>,
{
    // Odd and packed-tail lengths, plus the empty identities and singleton case.
    for n in [0usize, 1, 3, 17] {
        let values: Vec<_> = (0..n).map(|i| samples[i % samples.len()]).collect();
        let input = vector(values.clone());
        let payload = n * size_of::<F>();
        let retained = payload + 256;
        let output_limits = |per_element| Limits {
            output: retained,
            memory: payload + retained,
            work: 1 + n as u64 * per_element,
        };
        for operation in ["vector.add", "vector.sub", "vector.mul"] {
            let different: Vec<_> = (0..n).map(|i| samples[(i + 1) % samples.len()]).collect();
            for (right, right_values) in [
                (input.clone(), &values),
                (vector(different.clone()), &different),
            ] {
                let expected = values
                    .iter()
                    .zip(right_values)
                    .map(|(left, right)| match operation {
                        "vector.add" => *left + *right,
                        "vector.sub" => *left - *right,
                        _ => *left * *right,
                    })
                    .collect();
                // Exercise both repeated Arc aliases and distinct typed backings.
                check_limits(
                    domain,
                    operation,
                    &[],
                    vec![input.clone(), right],
                    vector(expected),
                    output_limits(6),
                );
            }
        }
        // Scaling by -1 exercises pointwise negation, including characteristic two.
        for factor in [samples[2], -identity] {
            check_limits(
                domain,
                "vector.scale",
                &[],
                vec![input.clone(), field(factor)],
                vector(values.iter().map(|x| *x * factor).collect()),
                output_limits(5),
            );
        }
        for operation in [
            "vector.fill",
            "vector.splat",
            "vector.geometric",
            "vector.powers",
        ] {
            let constant = matches!(operation, "vector.fill" | "vector.splat");
            let mut power = identity;
            let expected = (0..n)
                .map(|_| {
                    if constant {
                        samples[2]
                    } else {
                        let value = power;
                        power = power * samples[2];
                        value
                    }
                })
                .collect();
            let count = n.to_string();
            let (attributes, args) = if matches!(operation, "vector.splat" | "vector.powers") {
                (vec![count.as_str()], vec![field(samples[2])])
            } else {
                (vec![], vec![field(samples[2]), Value::Index(n as u64)])
            };
            check_limits(
                domain,
                operation,
                &attributes,
                args,
                vector(expected),
                output_limits(if constant { 2 } else { 4 }),
            );
        }
        for operation in ["vector.sum", "vector.product", "vector.dot"] {
            let expected = match operation {
                "vector.sum" => values.iter().fold(zero, |sum, x| sum + *x),
                "vector.product" => values.iter().fold(identity, |product, x| product * *x),
                _ => values.iter().fold(zero, |sum, x| sum + *x * *x),
            };
            let mut args = vec![input.clone()];
            let mut setup = 1;
            if operation == "vector.dot" {
                args.push(input.clone());
                if domain.field == zkc_runtime::vm::Identity::KoalaBear {
                    setup += zkc_kernels::plonky3::PACKING_WIDTH as u64;
                }
            }
            check_limits(
                domain,
                operation,
                &[],
                args,
                field(expected),
                Limits {
                    output: 512,
                    // Inline reductions reserve final scalar storage only.
                    memory: 512,
                    work: setup + n as u64 * if operation == "vector.dot" { 4 } else { 2 },
                },
            );
        }
        assert_value(&input, &vector(values));
    }
}

#[test]
fn general_storage_preserves_all_eight_fields_at_exact_and_one_short_limits() {
    storage(
        domains::BLS,
        [2u64, 5, 11].map(Scalar::from),
        Scalar::from(0),
        Scalar::from(1),
        Value::Field,
        |values| Value::Vector(values.into()),
    );
    storage(
        domains::BN254_G1,
        [2u64, 5, 11].map(Bn254Scalar::from),
        Bn254Scalar::from(0),
        Bn254Scalar::from(1),
        Value::Bn254Field,
        |values| Value::Bn254Vector(values.into()),
    );
    storage(
        domains::RISTRETTO,
        [2u64, 5, 11].map(RistrettoScalar::from),
        RistrettoScalar::from(0u64),
        RistrettoScalar::from(1u64),
        Value::RistrettoField,
        |values| Value::RistrettoVector(values.into()),
    );
    storage(
        domains::KOALA_BEAR,
        [2, 5, 11].map(KoalaBear::new),
        KoalaBear::new(0),
        KoalaBear::new(1),
        Value::KoalaBearField,
        |values| Value::KoalaBearVector(values.into()),
    );
    storage(
        domains::KOALA_BEAR_EXT4,
        [2, 5, 11]
            .map(|n| KoalaBearExt4::from_basis_coefficients_fn(|i| KoalaBear::new(n + i as u32))),
        KoalaBearExt4::from(KoalaBear::new(0)),
        KoalaBearExt4::from(KoalaBear::new(1)),
        Value::KoalaBearExt4Field,
        |values| Value::KoalaBearExt4Vector(values.into()),
    );
    storage(
        domains::KOALA_BEAR_EXT8,
        [2, 5, 11]
            .map(|n| KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new(n + i as u32))),
        KoalaBearExt8::from(KoalaBear::new(0)),
        KoalaBearExt8::from(KoalaBear::new(1)),
        Value::KoalaBearExt8Field,
        |values| Value::KoalaBearExt8Vector(values.into()),
    );
    use zkc_kernels::plonky3::binary::ext3_from_bits;
    use zkc_kernels::plonky3::binary::from_bits;
    storage(
        domains::BINARY64,
        [2, 5, 1 << 63].map(from_bits),
        from_bits(0),
        from_bits(1),
        Value::Binary64Field,
        |values| Value::Binary64Vector(values.into()),
    );
    storage(
        domains::BINARY64_EXT3,
        [2, 5, 1 << 63].map(|n| ext3_from_bits([n, n + 1, n + 3])),
        ext3_from_bits([0; 3]),
        ext3_from_bits([1, 0, 0]),
        Value::Binary64Ext3Field,
        |values| Value::Binary64Ext3Vector(values.into()),
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
fn reached_refusals_preserve_each_operations_shape_and_output_order() {
    let unavailable = Policy {
        max_numerical_work: 0,
        max_numerical_bytes: 0,
        ..Policy::default()
    };
    for operation in ["vector.add", "vector.sub", "vector.mul", "vector.dot"] {
        for available in [0, 512] {
            let mut controlled = Controlled::new(backend(unavailable));
            controlled.output_limit = Some(available);
            let (result, observed) = one(
                controlled,
                binding(domains::BLS, operation),
                &[],
                vec![bls(&[2, 5, 11]), bls(&[3, 7])],
            );
            let error = if operation == "vector.dot" && available < 512 {
                "exhausted:output-bytes"
            } else {
                "refused:length-mismatch"
            };
            assert_eq!(result.unwrap_err(), error, "{operation}");
            assert!(observed.outputs.is_empty());
            assert_eq!(observed.inner.active_frames(), 0);
        }
    }
    for (operation, args, attrs, output) in [
        ("vector.add", vec![bls(&[2, 5, 11]); 2], vec![], 352),
        ("vector.sub", vec![bls(&[2, 5, 11]); 2], vec![], 352),
        ("vector.mul", vec![bls(&[2, 5, 11]); 2], vec![], 352),
        (
            "vector.scale",
            vec![bls(&[2, 5, 11]), Value::Field(Scalar::from(7))],
            vec![],
            352,
        ),
        (
            "vector.fill",
            vec![Value::Field(Scalar::from(7)), Value::Index(3)],
            vec![],
            352,
        ),
        (
            "vector.geometric",
            vec![Value::Field(Scalar::from(7)), Value::Index(3)],
            vec![],
            352,
        ),
        (
            "vector.splat",
            vec![Value::Field(Scalar::from(7))],
            vec!["3"],
            352,
        ),
        (
            "vector.powers",
            vec![Value::Field(Scalar::from(7))],
            vec!["3"],
            352,
        ),
        ("vector.sum", vec![bls(&[2, 5, 11])], vec![], 512),
        ("vector.product", vec![bls(&[2, 5, 11])], vec![], 512),
        ("vector.dot", vec![bls(&[2, 5, 11]); 2], vec![], 512),
    ] {
        for (available, error) in [
            (output - 1, "exhausted:output-bytes"),
            (output, "exhausted:numerical-work"),
        ] {
            let mut controlled = Controlled::new(backend(unavailable));
            controlled.output_limit = Some(available);
            let (result, observed) = one(
                controlled,
                binding(domains::BLS, operation),
                &attrs,
                args.clone(),
            );
            assert_eq!(result.unwrap_err(), error, "{operation}");
            assert!(observed.outputs.is_empty());
            assert_eq!(observed.inner.active_frames(), 0);
        }
    }
}

#[test]
fn construction_keeps_element_ceilings_before_output_work_and_memory() {
    for operation in [
        "vector.fill",
        "vector.geometric",
        "vector.splat",
        "vector.powers",
    ] {
        for (limit, n) in [(2usize, 3usize), (usize::MAX, (1 << 20) + 1)] {
            // Static extents are rejected by program admission before a native
            // call exists. Dynamic extents reach the backend's element ceiling.
            if n > 1 << 20 && matches!(operation, "vector.splat" | "vector.powers") {
                let binding = binding(domains::BLS, operation);
                let signature = binding.signature().unwrap();
                let bytes = support::program(
                    &[binding],
                    &signature.inputs,
                    vec![serde_json::json!([
                        "op",
                        "site",
                        "b0",
                        [n.to_string()],
                        ["a0"],
                        ["out"]
                    ])],
                    &signature.outputs,
                    &["out".into()],
                );
                let error = zkc_runtime::vm::Program::decode(&bytes).err().unwrap();
                assert_eq!(error.code, zkc_runtime::vm::ErrorCode::Attributes);
                assert_eq!(error.detail, "interactive-kernel-parameters");
                continue;
            }
            let policy = Policy {
                max_table_elements: limit,
                max_numerical_work: 0,
                max_numerical_bytes: 0,
                ..Policy::default()
            };
            let mut controlled = Controlled::new(backend(policy));
            controlled.output_limit = Some(0);
            let count = n.to_string();
            let (attrs, args) = if matches!(operation, "vector.splat" | "vector.powers") {
                (vec![count.as_str()], vec![Value::Field(Scalar::from(7))])
            } else {
                (
                    vec![],
                    vec![Value::Field(Scalar::from(7)), Value::Index(n as u64)],
                )
            };
            let (result, observed) =
                one(controlled, binding(domains::BLS, operation), &attrs, args);
            assert_eq!(
                result.unwrap_err(),
                "exhausted:element-limit",
                "{operation}"
            );
            assert!(observed.outputs.is_empty());
            assert_eq!(observed.inner.active_frames(), 0);
        }
    }
}

#[test]
fn aliased_inputs_and_unique_last_uses_never_become_result_destinations() {
    let original = bls(&[2, 5, 11]);
    let alias = original.clone();
    let result = one(
        backend(Policy::default()),
        binding(domains::BLS, "vector.add"),
        &[],
        vec![original.clone(), alias.clone()],
    )
    .0
    .unwrap();
    let (Value::Vector(input), Value::Vector(other), Value::Vector(output)) =
        (&original, &alias, &result[0])
    else {
        panic!("expected BLS vectors");
    };
    assert!(Arc::ptr_eq(input, other));
    assert!(!Arc::ptr_eq(input, output));
    assert_value(&original, &bls(&[2, 5, 11]));
    assert_value(&result[0], &bls(&[4, 10, 22]));

    let unique = bls(&[3, 7, 13]);
    let Value::Vector(input) = &unique else {
        unreachable!()
    };
    assert_eq!(Arc::strong_count(input), 1);
    let backing = Arc::as_ptr(input);
    let result = one(
        backend(Policy::default()),
        binding(domains::BLS, "vector.scale"),
        &[],
        vec![unique, Value::Field(-Scalar::from(1))],
    )
    .0
    .unwrap();
    let Value::Vector(output) = &result[0] else {
        unreachable!()
    };
    assert!(!std::ptr::eq(backing, Arc::as_ptr(output)));
    assert_value(
        &result[0],
        &Value::Vector([3u64, 7, 13].map(|n| -Scalar::from(n)).into()),
    );
}

#[test]
fn equal_width_and_base_extension_values_do_not_gain_dense_access() {
    for operation in [
        "vector.add",
        "vector.sub",
        "vector.mul",
        "vector.sum",
        "vector.product",
        "vector.dot",
    ] {
        let mut controlled = Controlled::new(backend(Policy {
            max_numerical_work: 0,
            max_numerical_bytes: 0,
            ..Policy::default()
        }));
        controlled.substitute = Some(Value::Bn254Vector(vec![Bn254Scalar::from(2); 3].into()));
        let mut args = vec![bls(&[2, 5, 11])];
        if matches!(
            operation,
            "vector.add" | "vector.sub" | "vector.mul" | "vector.dot"
        ) {
            args.push(bls(&[2, 5, 11]));
        }
        let (result, observed) = one(controlled, binding(domains::BLS, operation), &[], args);
        assert_eq!(
            result.unwrap_err(),
            "refused:kernel-operands",
            "{operation}"
        );
        assert!(observed.outputs.is_empty());
    }
    let mut controlled = Controlled::new(backend(Policy::default()));
    controlled.substitute = Some(Value::KoalaBearField(KoalaBear::new(7)));
    let (result, observed) = one(
        controlled,
        binding(domains::KOALA_BEAR_EXT8, "vector.fill"),
        &[],
        vec![
            Value::KoalaBearExt8Field(KoalaBearExt8::from(KoalaBear::new(7))),
            Value::Index(3),
        ],
    );
    assert_eq!(result.unwrap_err(), "refused:kernel-operands");
    assert!(observed.outputs.is_empty());
}
