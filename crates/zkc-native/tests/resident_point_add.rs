//! Resident vector addition through installed Native admission and publication.
#[path = "domains/support.rs"]
mod support;

use std::sync::Arc;
use zkc_native::{CpuExecution, Policy, Value};
use zkc_runtime::{
    interpreter::Runner,
    vm::{OperationBinding, Program, RuntimeError, StopKind},
};

struct Case {
    provider: &'static str,
    domain: &'static str,
    len: usize,
    width: usize,
    left: Value,
    right: Value,
    identity: Value,
    expected: Value,
    doubled: Value,
}

impl Case {
    fn binding(&self) -> OperationBinding {
        OperationBinding {
            contract: "curve.vector_add".into(),
            arguments: vec![self.domain.into()],
            implementation: format!("{}/resident/curve.vector_add", self.provider),
            physical_arguments: vec![],
        }
    }

    fn bytes(&self) -> usize {
        256 + self.len * self.width
    }
}

fn cases(len: usize) -> Vec<Case> {
    macro_rules! case {
        ($kernel:path, $provider:literal, $domain:literal, $point:ident, $bulk:ident,
         $value:ident) => {{
            use $kernel as kernel;
            let g = kernel::$point::generator();
            let scale = |n| g.scale(kernel::Scalar::from(n));
            let left = [kernel::$point::identity(), g, g.neg(), scale(7), scale(19)];
            let right = [g, kernel::$point::identity(), g, scale(11), scale(3)];
            // Scalar multiplication supplies a different arithmetic path from
            // the addition kernel, including cancellation and identity cases.
            let expected = [g, g, kernel::$point::identity(), scale(18), scale(22)];
            let doubled = [
                kernel::$point::identity(),
                scale(2),
                scale(2).neg(),
                scale(14),
                scale(38),
            ];
            let value = |samples: &[kernel::$point]| {
                Value::$value(Arc::new(
                    kernel::$bulk::try_from_fn(len, |index| Ok(samples[index % samples.len()]))
                        .unwrap(),
                ))
            };
            Case {
                provider: $provider,
                domain: $domain,
                len,
                width: size_of::<kernel::$point>(),
                left: value(&left),
                right: value(&right),
                identity: value(&[kernel::$point::identity()]),
                expected: value(&expected),
                doubled: value(&doubled),
            }
        }};
    }
    vec![
        case!(
            zkc_kernels::blst::bls12_381,
            "blst",
            "bls12-381.g1",
            G1,
            G1Vector,
            BlstG1Vector
        ),
        case!(
            zkc_kernels::blst::bls12_381,
            "blst",
            "bls12-381.g2",
            G2,
            G2Vector,
            BlstG2Vector
        ),
        case!(
            zkc_kernels::halo2curves::bn254,
            "halo2curves-axiom",
            "bn254.g1",
            G1,
            G1Vector,
            HaloG1Vector
        ),
        case!(
            zkc_kernels::halo2curves::bn254,
            "halo2curves-axiom",
            "bn254.g2",
            G2,
            G2Vector,
            HaloG2Vector
        ),
    ]
}

// Unlike support::one, also return entry-admission refusals: an oversized
// operand is rejected while loading, before an addition can be reached.
fn run_addition(
    driver: support::Controlled,
    case: &Case,
    args: Vec<Value>,
) -> (Result<Vec<Value>, String>, support::Controlled) {
    let binding = case.binding();
    let resolved = zkc_native::native_contracts()
        .resolve(binding.clone())
        .unwrap();
    let signature = resolved.signature();
    let bytes = support::program(
        &[binding],
        &signature.inputs,
        vec![serde_json::json!([
            "op",
            "sum",
            "b0",
            [],
            ["a0", "a1"],
            ["out"]
        ])],
        &signature.outputs,
        &["out".into()],
    );
    let program = Program::decode(&bytes, zkc_native::native_contracts()).unwrap();
    program.check_installation(&driver).unwrap();
    match Runner::new(&program, "main", "P", "session", driver, args) {
        Ok(runner) => {
            let (result, driver) = support::drive(runner);
            (
                result.map_err(|stop| match stop.kind {
                    StopKind::Backend(error) => error.code,
                    other => format!("{other:?}"),
                }),
                driver,
            )
        }
        Err(error) => (
            Err(match error.error {
                RuntimeError::Backend(error) => error.code,
                other => format!("{other:?}"),
            }),
            error.backend,
        ),
    }
}

fn check_addition(case: &Case, cpu: &CpuExecution, left: &Value, right: &Value, expected: &Value) {
    let encoder = support::backend(Policy::default());
    let original = [left, right].map(|value| encoder.encode_native_value(value).unwrap());
    let expected = encoder.encode_native_value(expected).unwrap();
    let backend = support::backend(Policy {
        max_groups: case.len,
        max_numerical_bytes: case.bytes(),
        max_numerical_work: 0,
        ..Policy::default()
    })
    .with_cpu(cpu.clone())
    .unwrap();
    let mut driver = support::Controlled::new(backend);
    driver.output_limit = Some(case.bytes());
    // Exactly one managed allocation reserves the final point buffer. Neither
    // arithmetic nor publication needs an additional managed staging buffer.
    let guard = zkc_kernels::allocation::failure::after(1);
    let (result, driver) = support::one(
        driver,
        case.binding(),
        &[],
        vec![left.clone(), right.clone()],
    );
    result
        .unwrap_or_else(|error| panic!("{}/{}/{}: {error}", case.provider, case.domain, case.len));
    assert!(zkc_kernels::allocation::reserve::<u8>(1).is_err());
    drop(guard);
    assert_eq!(driver.outputs.len(), 1);
    assert_eq!(driver.outputs[0].len(), 1);
    let output = &driver.outputs[0][0];
    assert_eq!(encoder.encode_native_value(output).unwrap(), expected);
    macro_rules! storage {
        ($left:expr, $right:expr, $output:expr) => {{
            assert!(!Arc::ptr_eq($left, $output));
            assert!(!Arc::ptr_eq($right, $output));
            assert_eq!($output.len(), case.len);
            assert_eq!($output.storage_bytes(), case.len * case.width);
        }};
    }
    match (left, right, output) {
        (Value::BlstG1Vector(a), Value::BlstG1Vector(b), Value::BlstG1Vector(c)) => {
            storage!(a, b, c)
        }
        (Value::BlstG2Vector(a), Value::BlstG2Vector(b), Value::BlstG2Vector(c)) => {
            storage!(a, b, c)
        }
        (Value::HaloG1Vector(a), Value::HaloG1Vector(b), Value::HaloG1Vector(c)) => {
            storage!(a, b, c)
        }
        (Value::HaloG2Vector(a), Value::HaloG2Vector(b), Value::HaloG2Vector(c)) => {
            storage!(a, b, c)
        }
        _ => panic!("changed resident group or provider"),
    }
    for (input, bytes) in [left, right].into_iter().zip(original) {
        assert_eq!(encoder.encode_native_value(input).unwrap(), bytes);
    }
    assert_eq!(driver.inner.active_frames(), 0);
}

#[test]
fn resident_addition_covers_groups_identities_aliases_and_worker_boundaries() {
    for workers in [1, 4] {
        let cpu = CpuExecution::new(workers).unwrap();
        for len in [0, 1, 31, 32, 33, 63, 64, 65, 255, 256, 257, 513] {
            for case in cases(len) {
                for (left, right, expected) in [
                    (&case.left, &case.right, &case.expected),
                    (&case.right, &case.left, &case.expected),
                    (&case.left, &case.identity, &case.left),
                    (&case.identity, &case.left, &case.left),
                    (&case.identity, &case.identity, &case.identity),
                    (&case.left, &case.left, &case.doubled),
                ] {
                    check_addition(&case, &cpu, left, right, expected);
                }
            }
        }
    }
}

#[test]
fn resident_addition_refusals_preserve_order_inputs_and_complete_publication() {
    for workers in [1, 4] {
        let cpu = CpuExecution::new(workers).unwrap();
        for len in [0, 1, 65, 257] {
            for case in cases(len) {
                let encoder = support::backend(Policy::default());
                let defaults = Policy {
                    max_numerical_work: 0,
                    ..Policy::default()
                };
                let mut controls = vec![
                    (
                        case.left.clone(),
                        case.right.clone(),
                        defaults,
                        0,
                        "exhausted:output-bytes",
                    ),
                    (
                        case.left.clone(),
                        case.right.clone(),
                        Policy {
                            max_numerical_bytes: case.bytes() - 1,
                            ..defaults
                        },
                        case.bytes(),
                        "exhausted:numerical-bytes",
                    ),
                    (
                        case.left.clone(),
                        case.right.clone(),
                        defaults,
                        case.bytes(),
                        "exhausted:allocation",
                    ),
                ];
                if len > 0 {
                    controls.push((
                        case.left.clone(),
                        case.right.clone(),
                        Policy {
                            max_groups: len - 1,
                            max_numerical_bytes: 0,
                            ..defaults
                        },
                        0,
                        "exhausted:group-limit",
                    ));
                }
                let empty = cases(0)
                    .into_iter()
                    .find(|other| other.domain == case.domain)
                    .unwrap();
                let other = if len == 0 {
                    cases(1)
                        .into_iter()
                        .find(|other| other.domain == case.domain)
                        .unwrap()
                        .left
                } else {
                    empty.left
                };
                for (left, right) in [
                    (case.left.clone(), other.clone()),
                    (other, case.left.clone()),
                ] {
                    controls.push((
                        left,
                        right,
                        Policy {
                            max_numerical_bytes: 0,
                            ..defaults
                        },
                        0,
                        "refused:length-mismatch",
                    ));
                }
                for (left, right, policy, output, expected) in controls {
                    let args = vec![left, right];
                    let original: Vec<_> = args
                        .iter()
                        .map(|value| encoder.encode_native_value(value).unwrap())
                        .collect();
                    let backend = support::backend(policy).with_cpu(cpu.clone()).unwrap();
                    let mut driver = support::Controlled::new(backend);
                    driver.output_limit = Some(output);
                    let guard = zkc_kernels::allocation::failure::after(0);
                    let (result, driver) = run_addition(driver, &case, args.clone());
                    assert_eq!(result.unwrap_err(), expected, "{}/{len}", case.domain);
                    assert!(driver.outputs.is_empty());
                    assert_eq!(driver.inner.active_frames(), 0);
                    assert_eq!(
                        zkc_kernels::allocation::reserve::<u8>(1).is_err(),
                        expected != "exhausted:allocation"
                    );
                    drop(guard);
                    for (value, bytes) in args.iter().zip(original) {
                        assert_eq!(encoder.encode_native_value(value).unwrap(), bytes);
                    }
                }
            }
        }
    }
}
