//! Reached resident MSM/pairing calls preserve shape and output precedence.
#[path = "domains/support.rs"]
mod support;

use serde_json::json;
use std::sync::Arc;
use zkc_cpu::{Policy, Value, cpu_contracts_with_policy};
use zkc_runtime::vm::{Backend, ExecutionPolicy, InstalledOperation, OperationBinding, Value as _};

struct Case {
    binding: OperationBinding,
    args: Vec<Value>,
    mismatched: Vec<Value>,
    expected: Value,
    work: u64,
    workspace: usize,
}

fn cases(len: usize) -> Vec<Case> {
    macro_rules! msm {
        ($kernel:path, $provider:literal, $domain:literal, $group:ident, $bulk:ident,
         $scalars:ident, $points:ident, $point:ident, $wrap:expr, $work:expr) => {{
            use $kernel as kernel;
            let generator = kernel::$group::generator();
            let bases = [generator, kernel::$group::identity(), generator.neg()];
            let coefficients = [2, 3, 5];
            // Repeated addition is independent of MSM and scalar multiplication.
            let mut expected = kernel::$group::identity();
            for index in 0..len {
                for _ in 0..coefficients[index % coefficients.len()] {
                    expected = expected.add(&bases[index % bases.len()]);
                }
            }
            let scalars = Value::$scalars(Arc::new(
                kernel::ScalarVector::try_from_fn(len, |index| {
                    Ok(kernel::Scalar::from(
                        coefficients[index % coefficients.len()],
                    ))
                })
                .unwrap(),
            ));
            let points = |n| {
                Value::$points(Arc::new(
                    kernel::$bulk::try_from_fn(n, |index| Ok(bases[index % bases.len()])).unwrap(),
                ))
            };
            Case {
                binding: binding($provider, "curve.msm", $domain),
                args: vec![scalars.clone(), points(len)],
                mismatched: vec![scalars, points(len.saturating_sub(1))],
                expected: Value::$point(($wrap)(expected)),
                work: ($work)(len),
                workspace: kernel::msm_workspace_bytes(len).unwrap(),
            }
        }};
    }
    macro_rules! pairing {
        ($kernel:path, $provider:literal, $domain:literal, $g1:ident, $g2:ident,
         $work:expr, $workspace:expr) => {{
            use $kernel as kernel;
            let generator = kernel::G1::generator();
            let left = Value::$g1(Arc::new(
                kernel::G1Vector::try_from_fn(len, |index| {
                    Ok(if index % 2 == 0 {
                        generator
                    } else {
                        generator.neg()
                    })
                })
                .unwrap(),
            ));
            let right = |n| {
                Value::$g2(Arc::new(
                    kernel::G2Vector::try_from_fn(n, |_| Ok(kernel::G2::generator())).unwrap(),
                ))
            };
            Case {
                binding: binding($provider, "pairing.check", $domain),
                args: vec![left.clone(), right(len)],
                mismatched: vec![left, right(len.saturating_sub(1))],
                // Opposite G1 factors cancel; an unpaired generator does not.
                expected: Value::Bool(len.is_multiple_of(2)),
                work: ($work)(len),
                workspace: ($workspace)(len),
            }
        }};
    }
    vec![
        msm!(
            zkc_kernels::blst::bls12_381,
            "blst",
            "bls12-381.g1",
            G1,
            G1Vector,
            BlstVector,
            BlstG1Vector,
            BlstG1,
            Arc::new,
            |n: usize| 256 * n as u64 + 1
        ),
        msm!(
            zkc_kernels::blst::bls12_381,
            "blst",
            "bls12-381.g2",
            G2,
            G2Vector,
            BlstVector,
            BlstG2Vector,
            BlstG2,
            Arc::new,
            |n: usize| 256 * n as u64 + 1
        ),
        pairing!(
            zkc_kernels::blst::bls12_381,
            "blst",
            "bls12-381.fr",
            BlstG1Vector,
            BlstG2Vector,
            |n: usize| 8192 * (n as u64 + 1),
            |_| zkc_kernels::blst::bls12_381::PAIRING_WORKSPACE_BYTES
        ),
        msm!(
            zkc_kernels::halo2curves::bn254,
            "halo2curves-axiom",
            "bn254.g1",
            G1,
            G1Vector,
            HaloVector,
            HaloG1Vector,
            HaloG1,
            |v| v,
            |n| zkc_kernels::halo2curves::bn254::msm_work(n).unwrap()
        ),
        msm!(
            zkc_kernels::halo2curves::bn254,
            "halo2curves-axiom",
            "bn254.g2",
            G2,
            G2Vector,
            HaloVector,
            HaloG2Vector,
            HaloG2,
            Arc::new,
            |n| zkc_kernels::halo2curves::bn254::msm_work(n).unwrap()
        ),
        pairing!(
            zkc_kernels::halo2curves::bn254,
            "halo2curves-axiom",
            "bn254.fr",
            HaloG1Vector,
            HaloG2Vector,
            |n| zkc_kernels::halo2curves::bn254::pairing_work(n).unwrap(),
            |n| zkc_kernels::halo2curves::bn254::pairing_workspace_bytes(n).unwrap()
        ),
    ]
}

fn binding(provider: &str, name: &str, domain: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![domain.into()],
        implementation: format!("{provider}/resident/{name}"),
        physical_arguments: vec![],
    }
}

fn check(
    case: &Case,
    args: &[Value],
    policy: Policy,
    available: usize,
    expected_error: Option<&str>,
) {
    let contracts = cpu_contracts_with_policy(ExecutionPolicy::general_purpose());
    let encoder = support::backend(Policy::default());
    let originals: Vec<_> = args
        .iter()
        .map(|value| encoder.encode_native_value(value).unwrap())
        .collect();
    let native = support::backend(policy)
        .with_contracts(contracts.clone())
        .unwrap();
    for value in args {
        native
            .validate_value(value)
            .expect("admitted resident input");
    }
    let operation = native
        .prepare_binding(&case.binding)
        .expect("installed resident call");
    let signature = operation.signature();
    let carrier = support::program(
        std::slice::from_ref(&case.binding),
        &signature.inputs,
        vec![json!(["op", "resident", "b0", [], ["a0", "a1"], ["out"]])],
        &signature.outputs,
        &["out".into()],
    );
    let mut driver = support::Controlled::new(native);
    driver.output_limit = Some(available);
    // All policy refusals must leave the first provider allocation untouched.
    let guard = expected_error.map(|_| zkc_kernels::allocation::failure::after(0));
    let (result, driver) =
        support::run_program_with_contracts(driver, &carrier, args.to_vec(), &contracts);
    let context = format!("{:?}/{policy:?}/available={available}", case.binding);
    if let Some(expected) = expected_error {
        assert_eq!(result.unwrap_err(), expected, "{context}");
        assert!(driver.outputs.is_empty(), "{context}");
        assert_eq!(
            zkc_kernels::allocation::reserve::<u8>(1).is_err(),
            expected != "exhausted:allocation",
            "allocation injection was consumed out of order: {context}"
        );
    } else {
        let values = result.unwrap();
        assert_eq!(values.len(), 1, "{context}");
        assert_eq!(driver.outputs.len(), 1, "{context}");
        support::assert_value(&values[0], &case.expected);
    }
    drop(guard);
    assert_eq!(driver.inner.active_frames(), 0, "{context}");
    for (value, bytes) in args.iter().zip(originals) {
        assert_eq!(
            encoder.encode_native_value(value).unwrap(),
            bytes,
            "{context}"
        );
    }
}

#[test]
fn output_tuple_and_invocation_limits_precede_work_memory_and_allocation() {
    for case in cases(0).into_iter().chain(cases(1)) {
        for (tuple, available) in [
            ((case.expected.retained_bytes() - 1), usize::MAX),
            (usize::MAX, (case.expected.retained_bytes() - 1)),
            (
                (case.expected.retained_bytes() - 1),
                (case.expected.retained_bytes() - 1),
            ),
        ] {
            // Nonempty BLST G2 inputs already exceed the result charge. Exercise their
            // tuple ceiling with empty inputs, and invocation ceiling at both
            // lengths, so input validation cannot mask the handler preflight.
            if case.args.iter().any(|value| value.retained_bytes() > tuple) {
                continue;
            }
            for (work, memory) in [
                (0, 0),
                (0, case.expected.retained_bytes() + case.workspace),
                (case.work, 0),
            ] {
                check(
                    &case,
                    &case.args,
                    Policy {
                        max_value_bytes: tuple,
                        max_numerical_work: work,
                        max_numerical_bytes: memory,
                        ..Policy::default()
                    },
                    available,
                    Some("exhausted:output-bytes"),
                );
            }
        }
    }
}

#[test]
fn shape_mismatch_precedes_output_work_memory_and_allocation() {
    for case in cases(1) {
        for (tuple, available, work, memory) in [
            ((case.expected.retained_bytes() - 1), 0, 0, 0),
            (
                (case.expected.retained_bytes() - 1),
                usize::MAX,
                case.work,
                case.expected.retained_bytes() + case.workspace,
            ),
            (
                usize::MAX,
                0,
                case.work,
                case.expected.retained_bytes() + case.workspace,
            ),
            (usize::MAX, case.expected.retained_bytes(), 0, 0),
            (usize::MAX, case.expected.retained_bytes(), case.work, 0),
        ] {
            if case
                .mismatched
                .iter()
                .any(|value| value.retained_bytes() > tuple)
            {
                continue;
            }
            check(
                &case,
                &case.mismatched,
                Policy {
                    max_value_bytes: tuple,
                    max_numerical_work: work,
                    max_numerical_bytes: memory,
                    ..Policy::default()
                },
                available,
                Some("refused:length-mismatch"),
            );
        }
    }
}

#[test]
fn work_precedes_shared_result_workspace_memory_and_provider_allocation() {
    for case in cases(1) {
        for (work, memory, expected) in [
            (case.work - 1, 0, "exhausted:numerical-work"),
            (
                case.work - 1,
                case.expected.retained_bytes() + case.workspace,
                "exhausted:numerical-work",
            ),
            (
                case.work,
                (case.expected.retained_bytes() - 1),
                "exhausted:numerical-bytes",
            ),
            // Workspace alone fits, but the live result also counts.
            (case.work, case.workspace, "exhausted:numerical-bytes"),
            (
                case.work,
                case.expected.retained_bytes() + case.workspace - 1,
                "exhausted:numerical-bytes",
            ),
        ] {
            check(
                &case,
                &case.args,
                Policy {
                    max_numerical_work: work,
                    max_numerical_bytes: memory,
                    ..Policy::default()
                },
                case.expected.retained_bytes(),
                Some(expected),
            );
        }
        // Halo pairing reserves fallible staging. Bulk MSM and BLST pairing
        // allocate inside their providers, outside this injection hook.
        if case
            .binding
            .implementation
            .starts_with("halo2curves-axiom/")
            && case.binding.contract == "pairing.check"
        {
            check(
                &case,
                &case.args,
                Policy {
                    max_numerical_work: case.work,
                    max_numerical_bytes: case.expected.retained_bytes() + case.workspace,
                    ..Policy::default()
                },
                case.expected.retained_bytes(),
                Some("exhausted:allocation"),
            );
        }
    }
}

#[test]
fn exact_admission_preserves_msm_values_and_true_false_pairing_results() {
    for len in [0, 1, 2, 3] {
        for case in cases(len) {
            check(
                &case,
                &case.args,
                Policy {
                    max_numerical_work: case.work,
                    max_numerical_bytes: case.expected.retained_bytes() + case.workspace,
                    ..Policy::default()
                },
                case.expected.retained_bytes(),
                None,
            );
        }
    }
    for case in cases(0).into_iter().chain(cases(1)) {
        if case
            .args
            .iter()
            .any(|value| value.retained_bytes() > case.expected.retained_bytes())
        {
            continue;
        }
        check(
            &case,
            &case.args,
            Policy {
                max_value_bytes: case.expected.retained_bytes(),
                max_numerical_work: case.work,
                max_numerical_bytes: case.expected.retained_bytes() + case.workspace,
                ..Policy::default()
            },
            case.expected.retained_bytes(),
            None,
        );
    }
}
