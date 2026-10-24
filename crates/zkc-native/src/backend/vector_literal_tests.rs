//! Vector literal controls share the scalar Runner and invocation harness.
use super::*;
use crate::operations::field::Family;
use zkc_runtime::vm::{AttributeRule, Backing};

struct VectorCase {
    binding: OperationBinding,
    value: Value,
    overflow: String,
    error: &'static str,
    resident: bool,
}

fn case<S: Family>(field: &str, provider: &str, overflow: &str, error: &'static str) -> VectorCase {
    VectorCase {
        binding: OperationBinding {
            contract: "vector.constant".into(),
            arguments: vec![field.into()],
            implementation: format!("{provider}/vector.constant"),
            physical_arguments: vec![],
        },
        value: S::vector_value(vec![S::zero(), S::one(), S::one()]),
        overflow: overflow.into(),
        error,
        resident: S::RESIDENT_STORAGE,
    }
}

fn vector_cases() -> Vec<VectorCase> {
    let mut cases = vec![
        case::<crate::Scalar>(
            "bls12-381.fr",
            "arkworks",
            zkc_kernels::arkworks::bls12_381::SCALAR_MODULUS_DECIMAL,
            "refused:invalid-encoding",
        ),
        case::<crate::Bn254Scalar>(
            "bn254.fr",
            "arkworks",
            zkc_kernels::arkworks::bn254::MODULUS,
            "refused:noncanonical-encoding",
        ),
        case::<crate::RistrettoScalar>(
            "ristretto255.scalar",
            "dalek",
            zkc_kernels::dalek::ristretto255::SCALAR_MODULUS_DECIMAL,
            "refused:noncanonical-scalar",
        ),
        case::<crate::Binary64>(
            "gf2-64.pentanomial-4-3-1",
            "plonky3",
            "0x10000000000000000",
            "refused:noncanonical-scalar",
        ),
        case::<crate::Binary64Ext3>(
            "gf2-64.pentanomial-4-3-1.ext3-trinomial1",
            "plonky3",
            "0x1000000000000000000000000000000000000000000000000",
            "refused:noncanonical-scalar",
        ),
        case::<zkc_kernels::blst::bls12_381::ScalarElement>(
            "bls12-381.fr",
            "blst/resident",
            zkc_kernels::arkworks::bls12_381::SCALAR_MODULUS_DECIMAL,
            "refused:noncanonical-scalar",
        ),
        case::<zkc_kernels::halo2curves::bn254::ScalarElement>(
            "bn254.fr",
            "halo2curves-axiom/resident",
            zkc_kernels::arkworks::bn254::MODULUS,
            "refused:noncanonical-scalar",
        ),
    ];
    macro_rules! residues {
        ((); $(($s:ty, $id:ident, $base:ident, $($rest:tt)*),)*) => { $(
            cases.push(case::<$s>(
                Identity::$id.name(), "plonky3",
                &<crate::$base as p3_field::PrimeField64>::ORDER_U64.to_string(),
                "refused:noncanonical-scalar",
            ));
        )* };
    }
    crate::fields::inventory!([residues], ());
    cases
}

fn vector_program(case: &VectorCase, attributes: &[String]) -> Vec<u8> {
    let operation = backend().prepare_binding(&case.binding).unwrap();
    assert!(
        operation.prepared_handler.is_some(),
        "{}",
        case.binding.implementation
    );
    program(
        std::slice::from_ref(&case.binding),
        &[],
        vec![json!(["op", "literal", "b0", attributes, [], ["v"]])],
        &operation.binding.signature.outputs,
        &["v".into()],
    )
}

fn one_vector(
    caller: Caller,
    case: &VectorCase,
) -> (std::result::Result<Vec<Value>, Stop>, Usage, Caller) {
    let bytes = vector_program(case, &["0".into(), "1".into(), "1".into()]);
    let (result, usage, caller) = run(
        caller,
        &bytes,
        vec![],
        Default::default(),
        Default::default(),
    );
    assert_eq!(caller.inner.active_frames(), 0);
    (result, usage, caller)
}

fn backings(value: &Value) -> Vec<Backing> {
    let mut result = vec![];
    assert_eq!(
        value.retained_parts(&mut |backing| {
            result.push(backing);
            true
        }),
        0
    );
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].bytes(), value.retained_bytes());
    result
}

#[test]
fn every_vector_family_decodes_once_and_publishes_fresh_results() {
    let cases = vector_cases();
    assert_eq!(cases.len(), 14);
    for case in cases {
        let mut observations = vec![];
        for prepared in [false, true] {
            let mut caller = Caller::new(prepared);
            let mut previous = None;
            let mut usages = vec![];
            LITERAL_DECODES.set(0);
            for visit in 1..=3 {
                let (result, usage, next) = one_vector(caller, &case);
                caller = next;
                let value = result.unwrap().remove(0);
                equal(&value, &case.value);
                assert_eq!(LITERAL_DECODES.get(), if prepared { 3 } else { visit * 3 });
                assert_eq!(value.retained_bytes(), case.value.retained_bytes());
                assert_eq!(backings(&value), backings(&value.clone()));
                if prepared {
                    assert_ne!(
                        backings(&value),
                        backings(caller.call.as_ref().unwrap().literal().unwrap())
                    );
                }
                if let Some(previous) = previous.replace(value.clone()) {
                    assert_ne!(backings(&value), backings(&previous));
                }
                usages.push(usage);
            }
            // The retained native slot is not runtime retained-value evidence;
            // each independent Runner still admits and charges its own result.
            observations.push(usages);
        }
        assert_eq!(observations[0], observations[1]);
    }
}

#[cfg(feature = "test-utils")]
#[test]
fn warm_vector_publication_still_allocates_and_recovers_after_failure() {
    for case in vector_cases() {
        let (result, _, caller) = one_vector(Caller::new(true), &case);
        result.unwrap();
        let prepared = backings(caller.call.as_ref().unwrap().literal().unwrap());
        LITERAL_DECODES.set(0);
        let failure = zkc_kernels::allocation::failure::after(0);
        let (result, _, caller) = one_vector(caller, &case);
        assert_eq!(code(&result.unwrap_err()), "exhausted:allocation");
        assert_eq!(
            backings(caller.call.as_ref().unwrap().literal().unwrap()),
            prepared
        );
        assert_eq!(LITERAL_DECODES.get(), 0);
        drop(failure);
        let (result, _, caller) = one_vector(caller, &case);
        equal(&result.unwrap()[0], &case.value);
        assert_eq!(LITERAL_DECODES.get(), 0);
        assert_eq!(caller.inner.active_frames(), 0);
    }
}

#[test]
fn vector_replacement_failures_never_publish_or_execute_stale_values() {
    for case in vector_cases() {
        for prepared in [false, true] {
            let (result, _, mut caller) = one_vector(Caller::new(prepared), &case);
            result.unwrap();
            let old = caller.call.as_ref().map(|c| backings(c.literal().unwrap()));
            for invalid in ["", "00", "+1", "-1", "1 ", "１", &case.overflow] {
                caller.attributes = Some(vec!["1".into(), invalid.into()]);
                caller.output_limit = Some(0);
                let (result, _, mut next) = one_vector(caller, &case);
                let stop = result.unwrap_err();
                assert_eq!(
                    code(&stop),
                    case.error,
                    "{}: {invalid}",
                    case.binding.implementation
                );
                assert!(stop.cleanup_errors.is_empty());
                assert_eq!(
                    next.call.as_ref().map(|c| backings(c.literal().unwrap())),
                    old
                );
                next.attributes = None;
                next.output_limit = None;
                LITERAL_DECODES.set(0);
                let (result, _, next) = one_vector(next, &case);
                equal(&result.unwrap()[0], &case.value);
                assert_eq!(LITERAL_DECODES.get(), if prepared { 0 } else { 3 });
                caller = next;
            }
        }
    }
}

#[test]
fn empty_and_changed_vector_attributes_replace_only_the_exact_key() {
    for case in vector_cases() {
        let mut caller = Caller::new(true);
        for attributes in [vec![], vec!["1".into()], vec!["0".into(), "1".into()]] {
            let bytes = vector_program(&case, &attributes);
            LITERAL_DECODES.set(0);
            let mut previous = None;
            for _ in 0..2 {
                let (result, _, next) = run(
                    caller,
                    &bytes,
                    vec![],
                    Default::default(),
                    Default::default(),
                );
                caller = next;
                let value = result.unwrap().remove(0);
                assert_eq!(LITERAL_DECODES.get(), attributes.len());
                assert_ne!(
                    backings(&value),
                    backings(caller.call.as_ref().unwrap().literal().unwrap())
                );
                if let Some(previous) = previous.replace(value.clone()) {
                    assert_ne!(backings(&value), backings(&previous));
                }
                assert_eq!(
                    caller.call.as_ref().unwrap().attributes.as_ref(),
                    attributes
                );
            }
        }
    }
}

#[test]
fn vector_limits_apply_cold_and_warm_without_reparsing_on_hits() {
    for case in vector_cases() {
        let bytes = case.value.retained_bytes();
        for warm in [false, true] {
            for boundary in 0..4 {
                let mut caller = Caller::new(true);
                if warm {
                    let (result, _, next) = one_vector(caller, &case);
                    result.unwrap();
                    caller = next;
                }
                let old = caller.call.as_ref().map(|c| backings(c.literal().unwrap()));
                let policy = &mut caller.inner.core.policy;
                let error = match boundary {
                    0 => {
                        policy.max_table_elements = 2;
                        "exhausted:element-limit"
                    }
                    1 => {
                        policy.max_value_bytes = bytes - 1;
                        "exhausted:output-bytes"
                    }
                    2 => {
                        caller.output_limit = Some(bytes - 1);
                        "exhausted:output-bytes"
                    }
                    3 => {
                        policy.max_numerical_bytes = bytes - 1;
                        "exhausted:numerical-bytes"
                    }
                    _ => unreachable!(),
                };
                LITERAL_DECODES.set(0);
                let (result, _, mut caller) = one_vector(caller, &case);
                if boundary == 3 && !case.resident {
                    result.unwrap();
                } else {
                    assert_eq!(
                        code(&result.unwrap_err()),
                        error,
                        "{}",
                        case.binding.implementation
                    );
                    assert_eq!(
                        caller.call.as_ref().map(|c| backings(c.literal().unwrap())),
                        old
                    );
                }
                assert_eq!(LITERAL_DECODES.get(), if warm { 0 } else { 3 });
                caller.inner.core.policy = Policy {
                    max_table_elements: 3,
                    max_value_bytes: bytes,
                    max_numerical_bytes: if case.resident { bytes } else { 0 },
                    max_numerical_work: 0,
                    ..Policy::default()
                };
                caller.output_limit = Some(bytes);
                let (result, _, _) = one_vector(caller, &case);
                equal(&result.unwrap()[0], &case.value);
            }
        }
    }
}

#[test]
fn oversized_vector_attributes_are_validated_without_publishing_storage() {
    for case in vector_cases() {
        for invalid in [false, true] {
            let mut caller = Caller::new(true);
            caller.inner.core.policy.max_table_elements = 1;
            caller.inner.core.policy.max_numerical_bytes = 0;
            caller.output_limit = Some(0);
            caller.attributes = Some(vec![
                "1".into(),
                "1".into(),
                if invalid {
                    case.overflow.clone()
                } else {
                    "1".into()
                },
            ]);
            LITERAL_DECODES.set(0);
            let (result, _, caller) = one_vector(caller, &case);
            assert_eq!(
                code(&result.unwrap_err()),
                if invalid {
                    case.error
                } else {
                    "exhausted:element-limit"
                }
            );
            assert_eq!(LITERAL_DECODES.get(), 3);
            assert!(caller.call.is_none());
        }
    }
    assert_eq!(
        crate::value::size(usize::MAX, 32),
        Err(crate::exhausted("size-overflow"))
    );
}

#[test]
fn one_vector_slot_distinguishes_nominal_fields_resident_providers_and_scalars() {
    let mut caller = Caller::new(true);
    for case in vector_cases()
        .into_iter()
        .chain(vector_cases().into_iter().rev())
    {
        let same = caller.call.as_ref().is_some_and(|c| matches!(&c.payload, CallPayload::Literal(l) if l.binding.declaration == case.binding));
        LITERAL_DECODES.set(0);
        let (result, _, next) = one_vector(caller, &case);
        equal(&result.unwrap()[0], &case.value);
        assert_eq!(LITERAL_DECODES.get(), if same { 0 } else { 3 });
        caller = next;
    }
    let (result, mut caller) = one(caller, "koala-bear", "1");
    equal(&result.unwrap()[0], &small("koala-bear", true));
    let case = vector_cases().pop().unwrap();
    LITERAL_DECODES.set(0);
    let (result, _, next) = one_vector(caller, &case);
    equal(&result.unwrap()[0], &case.value);
    assert_eq!(LITERAL_DECODES.get(), 3);
    caller = next;
    assert_eq!(
        caller
            .call
            .as_ref()
            .unwrap()
            .literal()
            .unwrap()
            .physical_type(),
        case.value.physical_type()
    );
}

#[test]
fn vector_hits_require_complete_declaration_signature_and_attribute_rule() {
    let case = vector_cases().pop().unwrap();
    let (result, _, mut caller) = one_vector(Caller::new(true), &case);
    result.unwrap();
    for changed in 0..7 {
        let CallPayload::Literal(literal) = &mut caller.call.as_mut().unwrap().payload else {
            panic!("typed literal")
        };
        let key = Arc::make_mut(&mut literal.binding);
        match changed {
            0 => key.signature.attributes = AttributeRule::None,
            1 => key.signature.inputs.push(Value::Index(0).physical_type()),
            2 => key.signature.outputs[0] = small("koala-bear", true).physical_type(),
            3 => key.declaration.implementation = "other/vector.constant".into(),
            4 => key.declaration.contract = "vector.empty".into(),
            5 => key.declaration.arguments[0] = "koala-bear".into(),
            6 => key.declaration.physical_arguments.push("other".into()),
            _ => unreachable!(),
        }
        LITERAL_DECODES.set(0);
        let (result, _, next) = one_vector(caller, &case);
        equal(&result.unwrap()[0], &case.value);
        assert_eq!(LITERAL_DECODES.get(), 3);
        caller = next;
    }
    let first = backend().prepare_binding(&case.binding).unwrap();
    let second = backend().prepare_binding(&case.binding).unwrap();
    assert!(!Arc::ptr_eq(&first.binding, &second.binding));
    LITERAL_DECODES.set(0);
    NativeCall::prepare_literal(
        &mut caller.call,
        &second.binding,
        &["0".into(), "1".into(), "1".into()],
        &Policy::default(),
        usize::MAX,
    )
    .unwrap();
    assert_eq!(LITERAL_DECODES.get(), 0);
}

#[test]
fn vector_binding_and_operand_faults_precede_literal_and_capacity_faults() {
    for case in vector_cases() {
        let (result, _, mut caller) = one_vector(Caller::new(true), &case);
        result.unwrap();
        caller.attributes = Some(vec![case.overflow.clone()]);
        caller.output_limit = Some(0);
        caller.operation = Some(binding("koala-bear", "field.constant"));
        LITERAL_DECODES.set(0);
        let (result, _, mut caller) = one_vector(caller, &case);
        assert_eq!(code(&result.unwrap_err()), "refused:kernel-binding");
        assert_eq!(LITERAL_DECODES.get(), 0);
        caller.operation = None;
        caller.arguments = Some(vec![Value::Index(0)]);
        let (result, _, mut caller) = one_vector(caller, &case);
        assert_eq!(code(&result.unwrap_err()), "refused:kernel-operands");
        assert_eq!(LITERAL_DECODES.get(), 0);
        caller.arguments = None;
        let mut signature = backend()
            .prepare_binding(&case.binding)
            .unwrap()
            .binding
            .signature
            .clone();
        signature.outputs[0] = Value::Index(0).physical_type();
        caller.signature = Some(signature);
        let (result, _, _) = one_vector(caller, &case);
        assert_eq!(code(&result.unwrap_err()), "refused:kernel-operands");
        assert_eq!(LITERAL_DECODES.get(), 0);
    }
}

#[test]
fn warm_vector_preparation_never_grants_current_execution_permission() {
    for case in vector_cases() {
        for warm in [false, true] {
            let mut caller = Caller::new(true);
            if warm {
                let (result, _, next) = one_vector(caller, &case);
                result.unwrap();
                caller = next;
            }
            let old = caller.call.as_ref().map(|c| backings(c.literal().unwrap()));
            caller.revoke = true;
            caller.attributes = Some(vec![case.overflow.clone()]);
            caller.output_limit = Some(0);
            LITERAL_DECODES.set(0);
            let (result, _, caller) = one_vector(caller, &case);
            assert_eq!(
                code(&result.unwrap_err()),
                "refused:implementation-permission"
            );
            assert_eq!(LITERAL_DECODES.get(), 0);
            assert_eq!(
                caller.call.as_ref().map(|c| backings(c.literal().unwrap())),
                old
            );
        }
    }
}

#[test]
fn dormant_vector_sites_acquire_no_preparation_or_backend_failure() {
    for case in vector_cases() {
        let output = case.value.physical_type();
        let bytes = program(
            std::slice::from_ref(&case.binding),
            &[Value::Bool(false).physical_type()],
            vec![json!([
                "if",
                "branch",
                "a0",
                [],
                [["op", "literal", "b0", ["1"], [], ["v"]], ["yield", []]],
                [["yield", []]],
                []
            ])],
            &[],
            &[],
        );
        assert_eq!(
            output,
            backend()
                .prepare_binding(&case.binding)
                .unwrap()
                .binding
                .signature
                .outputs[0]
        );
        let mut caller = Caller::new(true);
        caller.attributes = Some(vec![case.overflow.clone()]);
        LITERAL_DECODES.set(0);
        let (result, _, caller) = run(
            caller,
            &bytes,
            vec![Value::Bool(false)],
            Default::default(),
            Default::default(),
        );
        result.unwrap();
        assert_eq!(caller.attempts, 0);
        assert!(caller.call.is_none());
        assert_eq!(LITERAL_DECODES.get(), 0);
        let (result, _, caller) = run(
            caller,
            &bytes,
            vec![Value::Bool(true)],
            Default::default(),
            Default::default(),
        );
        assert_eq!(code(&result.unwrap_err()), case.error);
        assert_eq!(caller.attempts, 1);
        assert!(caller.call.is_none());
        assert_eq!(LITERAL_DECODES.get(), 1);
        assert_eq!(caller.inner.active_frames(), 0);
    }
}

#[test]
fn reached_vector_slots_decode_once_and_preserve_fresh_result_charges() {
    for case in vector_cases() {
        let index = Value::Index(0).physical_type();
        let output = case.value.physical_type();
        let bytes = program(
            std::slice::from_ref(&case.binding),
            &[index.clone(), index],
            vec![
                json!(["op", "initial", "b0", ["0", "1", "1"], [], ["initial"]]),
                json!([
                    "for",
                    "repeat",
                    "i",
                    "a0",
                    "a1",
                    [["previous", "initial"]],
                    [],
                    [
                        ["op", "literal", "b0", ["0", "1", "1"], [], ["next"]],
                        ["yield", ["next"]]
                    ],
                    ["out"]
                ]),
            ],
            &[output],
            &["out".into()],
        );
        let admitted = Program::decode(&bytes, crate::native_contracts()).unwrap();
        let mut observations = vec![];
        for _ in 0..2 {
            LITERAL_DECODES.set(0);
            let mut runner = Runner::new(
                &admitted,
                "main",
                "P",
                "session",
                RecordingBackend {
                    inner: backend(),
                    reached: vec![],
                },
                vec![Value::Index(0), Value::Index(3)],
            )
            .unwrap_or_else(|e| panic!("{}", e.error));
            assert_eq!(LITERAL_DECODES.get(), 0);
            loop {
                match runner.poll() {
                    Action::Local(action) => runner.execute_local(&action.cut).unwrap(),
                    Action::Returned(values) => {
                        equal(&values[0], &case.value);
                        break;
                    }
                    other => panic!("unexpected {other:?}"),
                }
            }
            assert_eq!(LITERAL_DECODES.get(), 6);
            let usage = runner.usage();
            let recorder = runner.into_backend();
            assert_eq!(recorder.inner.active_frames(), 0);
            assert_eq!(recorder.reached.len(), 4);
            for (_, owner, value) in &recorder.reached {
                assert!(Arc::ptr_eq(owner, &recorder.reached[0].1));
                equal(value, &case.value);
            }
            assert_ne!(
                backings(&recorder.reached[0].2),
                backings(&recorder.reached[1].2)
            );
            for visit in 2..4 {
                assert_ne!(
                    backings(&recorder.reached[1].2),
                    backings(&recorder.reached[visit].2)
                );
            }
            observations.push((usage, recorder.reached));
        }
        assert_eq!(observations[0].0, observations[1].0);
        assert_ne!(
            backings(&observations[0].1[1].2),
            backings(&observations[1].1[1].2)
        );
        let (result, direct, _) = run(
            Caller::new(false),
            &bytes,
            vec![Value::Index(0), Value::Index(3)],
            Default::default(),
            Default::default(),
        );
        equal(&result.unwrap()[0], &case.value);
        let warm = observations[0].0;
        assert_eq!(direct, warm);
        for (values, work) in [
            (
                ValueBudget {
                    live_bytes: 1024 + 2 * case.value.retained_bytes() - 1,
                    ..Default::default()
                },
                WorkBudget::default(),
            ),
            (
                ValueBudget {
                    total_bytes: direct.total_value_bytes - 1,
                    ..Default::default()
                },
                WorkBudget::default(),
            ),
            (
                ValueBudget::default(),
                WorkBudget {
                    logical_bytes: direct.logical_bytes - 1,
                    ..Default::default()
                },
            ),
        ] {
            let (expected, expected_usage, _) = run(
                Caller::new(false),
                &bytes,
                vec![Value::Index(0), Value::Index(3)],
                values,
                work,
            );
            let (prepared, prepared_usage, _) = run(
                Caller::new(true),
                &bytes,
                vec![Value::Index(0), Value::Index(3)],
                values,
                work,
            );
            assert_eq!(expected_usage, prepared_usage);
            assert_eq!(expected.as_ref().map(|_| ()), prepared.as_ref().map(|_| ()));
        }
    }
}

#[test]
fn vector_failure_preserves_prior_rng_effect_and_reverse_cleanup() {
    let case = vector_cases().remove(0);
    let draw = binding("bls12-381.fr", "random.draw");
    let ports = draw.signature().unwrap();
    let bytes = program(
        &[draw, case.binding.clone()],
        &ports.inputs,
        vec![
            json!(["op", "draw", "b0", [], ["a0"], ["sample", "next"]]),
            json!(["op", "literal", "b1", ["0", "1", "1"], [], ["v"]]),
        ],
        &[ports.outputs[1].clone()],
        &["next".into()],
    );
    for prepared in [false, true] {
        for warm in [false, true] {
            for invalid in [false, true] {
                let mut caller = Caller::new(prepared);
                if warm {
                    let (result, _, next) = one_vector(caller, &case);
                    result.unwrap();
                    caller = next;
                }
                caller.leaves.clear();
                caller.cleanup_error = true;
                caller.output_limit = Some(case.value.retained_bytes() - 1);
                if invalid {
                    caller.attributes = Some(vec!["1".into(), case.overflow.clone()]);
                }
                let rng = caller
                    .inner
                    .issue_rng_for(
                        Identity::Bls12381Fr,
                        Domain::new("P", "session", "main", None),
                        3,
                    )
                    .unwrap();
                let outside = caller
                    .inner
                    .issue_rng_for(
                        Identity::Bls12381Fr,
                        Domain::new("P", "session", "main", None),
                        9,
                    )
                    .unwrap();
                let Value::Rng(token) = &rng else {
                    panic!("rng")
                };
                let Value::Rng(outside) = &outside else {
                    panic!("rng")
                };
                let before = caller.inner.observe(outside).unwrap();
                let (result, usage, caller) = run(
                    caller,
                    &bytes,
                    vec![rng.clone()],
                    Default::default(),
                    Default::default(),
                );
                let stop = result.unwrap_err();
                assert_eq!(
                    code(&stop),
                    if invalid {
                        case.error
                    } else {
                        "exhausted:output-bytes"
                    }
                );
                assert_eq!(
                    stop.cleanup_errors,
                    vec![crate::refused("literal-test-cleanup")]
                );
                let observed = caller.inner.observe(token).unwrap();
                assert_eq!(
                    (observed.generation, observed.draw_count, observed.budget),
                    (1, 1, 2)
                );
                assert_eq!(caller.inner.observe(outside).unwrap(), before);
                assert!(caller.inner.validate_value(&rng).is_err());
                assert_eq!((usage.live_values, usage.live_value_bytes), (0, 0));
                assert_eq!(
                    caller.leaves,
                    vec![
                        (
                            FrameKind::Local {
                                site: "local".into(),
                                function: "testfn".into()
                            },
                            FrameExit::Stopped
                        ),
                        (FrameKind::Entry, FrameExit::Stopped),
                    ]
                );
                assert_eq!(caller.inner.active_frames(), 0);
            }
        }
    }
}
