//! Reached resident conversions preserve admission and exact resource precedence.
#[path = "domains/support.rs"]
mod support;

use zkc_cpu::{Bls12381G2, Bn254G1, Bn254G2, Bn254Scalar, G1, Policy, Scalar, Value};
use zkc_runtime::vm::{Backend, Identity, OperationBinding, PhysicalType, Type, Value as _};

struct Case {
    binding: OperationBinding,
    input: Value,
    expected: Value,
    len: usize,
    bulk: bool,
    importing: bool,
}
impl Case {
    fn retained(&self) -> usize {
        self.expected.retained_bytes()
    }
    fn work(&self) -> u64 {
        4096 * self.len.max(1) as u64 + 1
    }
    fn memory(&self) -> usize {
        self.retained() * if self.bulk && !self.importing { 2 } else { 1 }
    }
    fn policy(&self) -> Policy {
        Policy {
            max_numerical_work: self.work(),
            max_numerical_bytes: self.memory(),
            ..Policy::default()
        }
    }
}

fn binding(source: &PhysicalType, target: &PhysicalType) -> OperationBinding {
    OperationBinding {
        contract: "representation.convert".into(),
        arguments: vec![source.logical().spelling()],
        implementation: "native/representation.convert".into(),
        physical_arguments: vec![source.spelling(), target.spelling()],
    }
}

fn cases(len: usize) -> Vec<Case> {
    let native = support::backend(Policy::default());
    let values = (0..len).map(|i| [0, 1, 19][i % 3]).collect::<Vec<_>>();
    let mut cases = Vec::new();
    for ordinary in [
        Value::Field(Scalar::from(19)),
        Value::vector(
            &values.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap(),
        Value::Curve(G1::generator()),
        Value::Groups(
            (0..len)
                .map(|i| {
                    if i % 2 == 0 {
                        G1::identity()
                    } else {
                        G1::generator()
                    }
                })
                .collect::<Vec<_>>()
                .into(),
        ),
        Value::Bls12381G2((Bls12381G2::generator()).into()),
        Value::Bls12381G2Vector(vec![Bls12381G2::generator(); len].into()),
        Value::Bn254Field(Bn254Scalar::from(19)),
        Value::Bn254Vector(
            values
                .iter()
                .copied()
                .map(Bn254Scalar::from)
                .collect::<Vec<_>>()
                .into(),
        ),
        Value::Bn254G1(Bn254G1::generator()),
        Value::Bn254G1Vector(
            (0..len)
                .map(|i| {
                    if i % 2 == 0 {
                        Bn254G1::identity()
                    } else {
                        Bn254G1::generator()
                    }
                })
                .collect::<Vec<_>>()
                .into(),
        ),
        Value::Bn254G2((Bn254G2::generator()).into()),
        Value::Bn254G2Vector(vec![Bn254G2::generator(); len].into()),
    ] {
        let source = ordinary.physical_type();
        let representation = match source.logical().identity() {
            Identity::Bls12381Fr => "blst/fr",
            Identity::Bls12381G1 => "blst/g1",
            Identity::Bls12381G2 => "blst/g2",
            Identity::Bn254Fr => "halo2curves-axiom/bn254.fr",
            Identity::Bn254G1 => "halo2curves-axiom/bn254.g1",
            Identity::Bn254G2 => "halo2curves-axiom/bn254.g2",
            _ => unreachable!(),
        };
        let target = zkc_cpu::cpu_contracts()
            .physical_type(&format!("{}@{representation}", source.logical().spelling()))
            .unwrap();
        // Independent wire admission supplies expected values without executing
        // the conversion being tested, including subgroup-checked resident ports.
        let bytes = native.encode_native_value(&ordinary).unwrap();
        let resident = native.decode_native_value(&target, &bytes).unwrap();
        let bulk = matches!(source.kind(), Type::Vector | Type::Groups);
        for (input, expected, importing) in [
            (ordinary.clone(), resident.clone(), true),
            (resident, ordinary, false),
        ] {
            cases.push(Case {
                binding: binding(&input.physical_type(), &expected.physical_type()),
                input,
                expected,
                len: if bulk { len } else { 0 },
                bulk,
                importing,
            });
        }
    }
    cases
}

fn check(
    case: &Case,
    policy: Policy,
    available: usize,
    expected_error: Option<&str>,
    substitute: Option<Value>,
    replace_binding: bool,
) {
    let encoder = support::backend(Policy::default());
    let original = encoder.encode_native_value(&case.input).unwrap();
    let native = support::backend(policy);
    // A small tuple ceiling must not accidentally turn a handler test into
    // refusal of its original input at Runner construction.
    native.validate_value(&case.input).unwrap();
    let mut driver = support::Controlled::new(native);
    driver.output_limit = Some(available);
    driver.substitute = substitute;
    if replace_binding {
        driver.binding = Some(binding(
            &case.expected.physical_type(),
            &case.input.physical_type(),
        ));
    }
    let guard = expected_error.map(|_| zkc_kernels::allocation::failure::after(0));
    let (result, driver) =
        support::one(driver, case.binding.clone(), &[], vec![case.input.clone()]);
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
        let output = result.unwrap();
        assert_eq!(output.len(), 1, "{context}");
        assert_eq!(driver.outputs.len(), 1, "{context}");
        support::assert_value(&output[0], &case.expected);
    }
    drop(guard);
    assert_eq!(driver.inner.active_frames(), 0, "{context}");
    assert_eq!(
        encoder.encode_native_value(&case.input).unwrap(),
        original,
        "{context}"
    );
}

#[test]
fn exact_output_preflight_precedes_work_memory_and_allocation() {
    for case in [0, 1, 3].into_iter().flat_map(cases) {
        for (work, memory) in [(0, 0), (0, case.memory()), (case.work(), 0)] {
            for tuple_limit in [false, true] {
                let retained = case.retained();
                if tuple_limit && case.input.retained_bytes() >= retained {
                    continue;
                }
                check(
                    &case,
                    Policy {
                        max_value_bytes: if tuple_limit {
                            retained - 1
                        } else {
                            usize::MAX
                        },
                        max_numerical_work: work,
                        max_numerical_bytes: memory,
                        ..Policy::default()
                    },
                    if tuple_limit {
                        usize::MAX
                    } else {
                        retained - 1
                    },
                    Some("exhausted:output-bytes"),
                    None,
                    false,
                );
            }
        }
    }
}

#[test]
fn independent_work_and_memory_boundaries_follow_output_admission() {
    for case in [0, 1, 3].into_iter().flat_map(cases) {
        for (work, memory, error) in [
            (case.work() - 1, 0, "exhausted:numerical-work"),
            (case.work() - 1, case.memory(), "exhausted:numerical-work"),
            (case.work(), case.memory() - 1, "exhausted:numerical-bytes"),
        ] {
            check(
                &case,
                Policy {
                    max_numerical_work: work,
                    max_numerical_bytes: memory,
                    ..Policy::default()
                },
                case.retained(),
                Some(error),
                None,
                false,
            );
        }
    }
}

#[test]
fn exact_admission_preserves_values_ports_and_conservative_export_staging() {
    for case in [0, 1, 3].into_iter().flat_map(cases) {
        for tuple_limit in [false, true] {
            if tuple_limit && case.input.retained_bytes() > case.retained() {
                continue;
            }
            check(
                &case,
                Policy {
                    max_value_bytes: if tuple_limit {
                        case.retained()
                    } else {
                        usize::MAX
                    },
                    ..case.policy()
                },
                case.retained(),
                None,
                None,
                false,
            );
        }
    }
}

#[test]
fn admitted_operands_and_shapes_precede_output_and_numerical_refusals() {
    for (empty, nonempty) in cases(0).into_iter().zip(cases(1)) {
        let policy = Policy {
            max_numerical_work: 0,
            max_numerical_bytes: 0,
            ..Policy::default()
        };
        check(
            &empty,
            policy,
            0,
            Some("refused:kernel-operands"),
            Some(Value::Bool(false)),
            false,
        );
        if empty.bulk {
            let (policy, error) = if empty.input.ty() == Type::Vector {
                (
                    Policy {
                        max_table_elements: 0,
                        ..policy
                    },
                    "exhausted:element-limit",
                )
            } else {
                (
                    Policy {
                        max_groups: 0,
                        ..policy
                    },
                    "exhausted:group-limit",
                )
            };
            check(&empty, policy, 0, Some(error), Some(nonempty.input), false);
        }
    }
}

#[test]
fn exact_binding_authority_precedes_output_and_numerical_refusals() {
    for case in cases(1) {
        check(
            &case,
            Policy {
                max_numerical_work: 0,
                max_numerical_bytes: 0,
                ..Policy::default()
            },
            0,
            Some("refused:kernel-binding"),
            None,
            true,
        );
    }
}

#[test]
fn admitted_bulk_conversions_reach_the_first_fallible_allocation() {
    for case in cases(3).into_iter().filter(|case| case.bulk) {
        check(
            &case,
            case.policy(),
            case.retained(),
            Some("exhausted:allocation"),
            None,
            false,
        );
    }
}

#[test]
fn vm_retained_value_allowance_reaches_native_output_preflight() {
    use serde_json::json;
    use zkc_runtime::{
        interpreter::Runner,
        vm::{Program, ValueBudget},
    };

    for case in cases(1) {
        let contracts = zkc_cpu::cpu_contracts();
        let signature = contracts.resolve(case.binding.clone()).unwrap();
        let carrier = support::program(
            std::slice::from_ref(&case.binding),
            &signature.signature().inputs,
            vec![json!(["op", "convert", "b0", [], ["a0"], ["out"]])],
            &signature.signature().outputs,
            &["out".into()],
        );
        let native = support::backend(Policy {
            max_numerical_work: 0,
            max_numerical_bytes: 0,
            ..Policy::default()
        });
        let program = Program::decode(&carrier, contracts).unwrap();
        program.check_installation(&native).unwrap();
        // The local argument alias adds only its owned inline bytes; its
        // backing is already retained. Leave no room for a fresh result,
        // keeping the actual VM allowance without a Controlled override.
        let budget = ValueBudget {
            live_bytes: case.input.retained_bytes() + case.input.retained_parts(&mut |_| true),
            total_bytes: usize::MAX,
        };
        let driver = support::Controlled::new(native);
        let runner = Runner::new_with_value_budget(
            &program,
            "main",
            "P",
            "session",
            driver,
            vec![case.input.clone()],
            budget,
        )
        .unwrap_or_else(|error| panic!("{}", error.error));
        let guard = zkc_kernels::allocation::failure::after(0);
        let (result, driver) = support::drive(runner);
        let stop = result.unwrap_err();
        assert_eq!(
            support::code(&stop),
            "exhausted:output-bytes",
            "{:?}",
            case.binding
        );
        assert!(driver.outputs.is_empty());
        assert_eq!(driver.inner.active_frames(), 0);
        assert!(zkc_kernels::allocation::reserve::<u8>(1).is_err());
        drop(guard);
    }
}
