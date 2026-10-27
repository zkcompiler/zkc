//! Total list restriction is independent of table-shape and native capacity checks.
#[path = "domains/support.rs"]
mod support;
use support::{backend, one};
use zkc_cpu::{Bn254Scalar, KoalaBear, Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::vm::{OperationBinding, Value as _};

fn binding(provider: &str, vector: &Value) -> OperationBinding {
    OperationBinding {
        contract: "multilinear.restrict_prefix".into(),
        arguments: vec![vector.physical_type().logical().identity().name().into()],
        implementation: format!("{provider}/multilinear.restrict_prefix"),
        physical_arguments: vec![],
    }
}

#[test]
fn total_edges_and_msb_order_across_field_carriers() {
    let p = Policy::default();
    let cases: &[(&[u64], &[u64], &[u64])] = &[
        (&[], &[], &[]),
        (&[], &[2], &[]),
        (&[9], &[], &[9]),
        (&[9], &[2], &[]),
        (&[1, 7, 2], &[], &[1, 7, 2]),
        (&[1, 7, 2], &[2], &[13]),
        (&[1, 7, 2, 9, 99], &[2], &[3, 11]),
        (&[1, 7, 2, 9], &[2], &[3, 11]),
        (&[1, 7, 2, 9], &[2, 3], &[27]),
        (&[1, 7, 2, 9], &[3, 2], &[22]),
        (&[1, 7, 2, 9], &[2, 3, 4], &[]),
        (&[1, 7, 2, 9], &[0, 1], &[7]),
        (&[1, 7, 2, 9], &[1, 0], &[2]),
        (&[1, 2, 3, 4, 5, 6], &[2, 3], &[10]),
    ];
    for &(values, point, expected) in cases {
        macro_rules! check {
            ($provider:expr, $constructor:ident, $scalar:expr) => {{
                let make = |xs: &[u64]| {
                    Value::$constructor(&xs.iter().copied().map($scalar).collect::<Vec<_>>(), &p)
                        .unwrap()
                };
                let input = make(values);
                let output = one(
                    backend(p),
                    binding($provider, &input),
                    &[],
                    vec![input, make(point)],
                )
                .0
                .unwrap();
                assert_eq!(output.len(), 1);
                let b = backend(p);
                assert_eq!(
                    b.encode_native_value(&output[0]).unwrap(),
                    b.encode_native_value(&make(expected)).unwrap(),
                    "{}: {values:?} at {point:?}",
                    $provider,
                );
            }};
        }
        check!("arkworks", vector, Scalar::from);
        check!("arkworks", bn254_vector, Bn254Scalar::from);
        check!("dalek", ristretto_vector, RistrettoScalar::from);
        check!("plonky3", koala_bear_vector, |x| KoalaBear::new(x as u32));
        check!("plonky3", koala_bear_ext8_vector, |x| KoalaBear::new(
            x as u32
        )
        .into());
    }
}

#[test]
fn characteristic_two_uses_field_arithmetic() {
    let p = Policy::default();
    for (values, point, expected) in [
        (vec![0, 1, 1, 0], vec![1, 0], vec![1]),
        (vec![1, 7, 2, 9], vec![2, 3], vec![35]),
        (vec![1, 7, 2, 9], vec![3, 2], vec![38]),
        (vec![1, 7, 2], vec![2], vec![13]),
    ] {
        for extension in [false, true] {
            let make = |xs: &[u64]| {
                if extension {
                    Value::binary64_ext3_vector(
                        &xs.iter()
                            .map(|x| zkc_kernels::plonky3::binary::ext3_from_bits([*x, 0, 0]))
                            .collect::<Vec<_>>(),
                        &p,
                    )
                    .unwrap()
                } else {
                    Value::binary64_vector(
                        &xs.iter()
                            .map(|x| zkc_kernels::plonky3::binary::from_bits(*x))
                            .collect::<Vec<_>>(),
                        &p,
                    )
                    .unwrap()
                }
            };
            let input = make(&values);
            let result = one(
                backend(p),
                binding("plonky3", &input),
                &[],
                vec![input, make(&point)],
            )
            .0
            .unwrap();
            let b = backend(p);
            assert_eq!(
                b.encode_native_value(&result[0]).unwrap(),
                b.encode_native_value(&make(&expected)).unwrap()
            );
        }
    }
}

#[test]
fn resource_guards_and_malformed_invocations_are_separate() {
    let p = Policy::default();
    let make = |xs: &[u64]| {
        Value::vector(
            &xs.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
            &p,
        )
        .unwrap()
    };
    let values = make(&[1, 7, 2, 9]);
    let operation = binding("arkworks", &values);
    for (policy, code) in [
        (
            Policy {
                max_numerical_work: 0,
                ..p
            },
            "exhausted:numerical-work",
        ),
        (
            Policy {
                max_numerical_bytes: 0,
                ..p
            },
            "exhausted:numerical-bytes",
        ),
    ] {
        let (result, driver) = one(
            backend(policy),
            operation.clone(),
            &[],
            vec![values.clone(), make(&[2])],
        );
        assert_eq!(result.unwrap_err(), code);
        assert_eq!(driver.active_frames(), 0);
    }
    let resolved = zkc_cpu::cpu_contracts().resolve(operation.clone()).unwrap();
    let sig = resolved.signature();
    let bytes = support::program(
        std::slice::from_ref(&operation),
        &sig.inputs,
        vec![serde_json::json!([
            "op",
            "restrict",
            "b0",
            [],
            ["a0", "a1"],
            ["out"]
        ])],
        &sig.outputs,
        &["out".into()],
    );
    let admitted = zkc_runtime::vm::Program::decode(&bytes, zkc_cpu::cpu_contracts()).unwrap();
    for inputs in [
        vec![values.clone()],
        vec![values.clone(), Value::Field(Scalar::from(2))],
        vec![values.clone(), make(&[2]), make(&[])],
    ] {
        assert!(
            zkc_runtime::interpreter::Runner::new(
                &admitted,
                "main",
                "P",
                "session",
                backend(p),
                inputs
            )
            .is_err()
        );
    }
    let malformed = support::program(
        &[operation],
        &sig.inputs,
        vec![serde_json::json!([
            "op",
            "restrict",
            "b0",
            ["1"],
            ["a0", "a1"],
            ["out"]
        ])],
        &sig.outputs,
        &["out".into()],
    );
    assert!(zkc_runtime::vm::Program::decode(&malformed, zkc_cpu::cpu_contracts()).is_err());
}
