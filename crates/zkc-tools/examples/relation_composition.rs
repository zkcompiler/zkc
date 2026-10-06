//! Execute compiler-generated static composition. Expected arithmetic comes from
//! an independent finite-field evaluator, including explicitly accepted bad events.
use serde::Deserialize;
use std::{collections::BTreeMap, path::Path};
use zkc_backends::services::ServiceRegistry;
use zkc_backends::{
    Domain, EntryPolicy, FieldArray, NativeBackend, Policy, PublicInputs, Scalar, Value,
};
use zkc_runtime::interactive::{DecodeReason, Identity, LogicalType, Value as RuntimeValue};
use zkc_tools::protocol::run::*;

#[derive(Deserialize)]
struct Experiment {
    runs: Vec<Run>,
    exact: Vec<Exact>,
}
#[derive(Deserialize)]
struct Run {
    bundle: String,
    values: Vec<String>,
    tape: Vec<String>,
    arity: usize,
    accepted: bool,
    rounds: Vec<Vec<String>>,
}
#[derive(Deserialize)]
struct Exact {
    bundle: String,
    z: Vec<String>,
    statement: Vec<String>,
    products: Vec<Vec<String>>,
    bound: bool,
    satisfied: bool,
}
fn scalar(value: &str) -> Scalar {
    zkc_arkworks::parse_decimal(value).unwrap()
}
fn scalars(values: &[String]) -> Vec<Scalar> {
    values.iter().map(|v| scalar(v)).collect()
}
fn array(values: &[Scalar]) -> Value {
    Value::FieldArray(
        FieldArray::new(
            LogicalType::field_array(Identity::Bls12381Fr, values.len() as u64).unwrap(),
            values.into(),
        )
        .unwrap(),
    )
}
fn elements(value: &Value) -> &[Scalar] {
    let Value::FieldArray(array) = value else {
        panic!("field array")
    };
    array.elements()
}
fn backend(role: &str, entry: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new(role, "composition", entry, None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap()
}
fn bundle(directory: &Path, name: &str) -> Bundle {
    Bundle::admit(
        &std::fs::read(directory.join(format!("{name}.bundle"))).unwrap(),
        &backend("admission", "main"),
        BundleLimits::default(),
    )
    .unwrap()
}
#[derive(Default)]
struct Wire {
    messages: Vec<(String, Vec<u8>)>,
    replacement: Option<Vec<u8>>,
}
impl Hooks<NativeBackend> for Wire {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        _: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        self.messages.push((exchange.site.into(), bytes.into()));
        Ok(if exchange.site.contains("round") {
            self.replacement.clone()
        } else {
            None
        })
    }
}
fn execute(
    bundle: &Bundle,
    values: &[Value],
    tape: &[Scalar],
    budget: u64,
    wire: &mut Wire,
    limits: RunLimits,
    changed_prover: Option<Vec<Value>>,
) -> (Report<NativeBackend>, u64) {
    let registry = ServiceRegistry::new(Policy::default());
    let verifier = bundle
        .roles()
        .iter()
        .find(|r| !r.entry.services.is_empty())
        .map(|r| r.entry.role.as_str());
    let reference = verifier.map(|v| registry.issue_test_tape(v, budget, tape.into()).unwrap());
    let inputs = bundle
        .roles()
        .iter()
        .map(|role| {
            let mut b = backend(&role.entry.role, bundle.entry());
            if let Some(reference) = &reference
                && !role.entry.services.is_empty()
            {
                assert_eq!(role.entry.services.len(), 1);
                b = b
                    .with_services(
                        registry.clone(),
                        BTreeMap::from([(role.entry.services[0].name.clone(), reference.clone())]),
                    )
                    .unwrap();
            }
            RoleInput {
                role: role.entry.role.clone(),
                backend: b,
                values: if Some(role.entry.role.as_str()) != verifier {
                    changed_prover.clone().unwrap_or_else(|| values.into())
                } else {
                    values.into()
                },
            }
        })
        .collect();
    let report = run(bundle, "composition", inputs, limits, wire).unwrap();
    let count = reference
        .map(|reference| {
            let state = registry.observe(&reference).unwrap();
            assert!(!state.leased);
            state.state.unwrap().draw_count
        })
        .unwrap_or(0);
    (report, count)
}
fn decision(report: &Report<NativeBackend>, role: &str) -> bool {
    assert_eq!(report.outcome, Outcome::Completed);
    match report
        .roles
        .iter()
        .find(|r| r.role == role)
        .unwrap()
        .outputs
        .as_slice()
    {
        [Value::Bool(value)] => *value,
        _ => panic!("one actual decision"),
    }
}
fn stopped<'a>(report: &'a Report<NativeBackend>, site: &str) -> &'a StopSummary {
    let role = report.roles.iter().find(|r| r.role == "Checker").unwrap();
    let State::Stopped(stop) = &role.before else {
        panic!("expected Checker stop: {:?}", report.outcome)
    };
    assert_eq!(stop.site.as_deref(), Some(site));
    assert!(role.outputs.is_empty());
    stop
}
fn evaluate(coefficients: &[Scalar], x: Scalar) -> Scalar {
    coefficients
        .iter()
        .rev()
        .fold(Scalar::from(0), |a, c| a * x + c)
}
fn main() {
    let directory = std::env::args().nth(1).expect("generated directory");
    let directory = Path::new(&directory);
    let experiments: Experiment =
        serde_json::from_slice(&std::fs::read(directory.join("execution.json")).unwrap()).unwrap();
    for case in &experiments.exact {
        let bundle = bundle(directory, &case.bundle);
        let mut values = vec![array(&scalars(&case.z))];
        values.extend(scalars(&case.statement).into_iter().map(Value::Field));
        let (report, count) = execute(
            &bundle,
            &values,
            &[],
            0,
            &mut Wire::default(),
            RunLimits::default(),
            None,
        );
        assert_eq!(count, 0);
        assert_eq!(report.outcome, Outcome::Completed);
        let outputs = &report.roles[0].outputs;
        for (actual, expected) in outputs[..3].iter().zip(&case.products) {
            assert_eq!(elements(actual), scalars(expected));
        }
        assert!(matches!(outputs[3],Value::Bool(x) if x==case.bound));
        assert!(matches!(outputs[4],Value::Bool(x) if x==case.satisfied));
    }
    for case in &experiments.runs {
        let b = bundle(directory, &case.bundle);
        let values: Vec<_> = scalars(&case.values)
            .into_iter()
            .map(Value::Field)
            .collect();
        let tape = scalars(&case.tape);
        let mut wire = Wire::default();
        let (report, count) = execute(
            &b,
            &values,
            &tape,
            tape.len() as u64,
            &mut wire,
            RunLimits::default(),
            None,
        );
        if case.accepted {
            assert!(decision(&report, "Checker"));
            assert_eq!(count, tape.len() as u64);
        } else {
            stopped(&report, "apply_6_reduce_guard0");
            assert_eq!(count, case.arity as u64);
        }
        let codec = backend("Checker", "inspect");
        let ty = array(&[Scalar::from(0); 4]).physical_type();
        for ((_, bytes), expected) in wire
            .messages
            .iter()
            .filter(|(site, _)| site.contains("round"))
            .zip(&case.rounds)
        {
            let coefficients = codec.decode_native_value(&ty, bytes).unwrap();
            for (x, expected) in [0, 1, 2, 11].into_iter().zip(expected) {
                assert_eq!(
                    evaluate(elements(&coefficients), Scalar::from(x)),
                    scalar(expected)
                );
            }
        }
        assert_eq!(
            wire.messages
                .iter()
                .filter(|(s, _)| s.contains("round"))
                .count(),
            if case.accepted { case.arity } else { 1 }
        );
    }
    let values = vec![
        Value::Field(Scalar::from(6)),
        Value::Field(Scalar::from(2)),
        Value::Field(Scalar::from(3)),
    ];
    let tape = [Scalar::from(2), Scalar::from(5)];
    for name in [
        "multiply",
        "multiply_plain",
        "multiply_release",
        "multiply_factored",
    ] {
        let b = bundle(directory, name);
        assert!(decision(
            &execute(
                &b,
                &values,
                &tape,
                2,
                &mut Wire::default(),
                RunLimits::default(),
                None
            )
            .0,
            "Checker"
        ));
    }
    let b = bundle(directory, "multiply");
    let codec = backend("Checker", "faults");
    let mut wire = Wire {
        replacement: Some(
            codec
                .encode_native_value(&array(&[Scalar::from(0); 4]))
                .unwrap(),
        ),
        ..Wire::default()
    };
    let (false_terminal, count) =
        execute(&b, &values, &tape, 2, &mut wire, RunLimits::default(), None);
    assert!(!decision(&false_terminal, "Checker"));
    assert_eq!(count, 2);
    let mut wire = Wire {
        replacement: Some(vec![0]),
        ..Wire::default()
    };
    let (malformed, count) = execute(&b, &values, &tape, 2, &mut wire, RunLimits::default(), None);
    assert_eq!(
        stopped(&malformed, "apply_6_reduce_round0").cause,
        StopCause::Decode(DecodeReason::Length)
    );
    assert_eq!(count, 1);
    let (exhausted, count) = execute(
        &b,
        &values,
        &tape,
        1,
        &mut Wire::default(),
        RunLimits::default(),
        None,
    );
    assert!(matches!(
        stopped(&exhausted, "apply_6_reduce_query0").cause,
        StopCause::Backend(_)
    ));
    assert_eq!(count, 2);
    let (limited, _) = execute(
        &b,
        &values,
        &tape,
        2,
        &mut Wire::default(),
        RunLimits {
            steps: 1,
            ..RunLimits::default()
        },
        None,
    );
    assert!(matches!(
        limited.outcome,
        Outcome::DriverFailed(Failure {
            kind: FailureKind::Limit,
            ..
        })
    ));
    let mut changed = values.clone();
    changed[2] = Value::Field(Scalar::from(4));
    let (mismatch, _) = execute(
        &b,
        &values,
        &tape,
        2,
        &mut Wire::default(),
        RunLimits::default(),
        Some(changed),
    );
    stopped(&mismatch, "apply_6_reduce_guard0");
    let aliased = bundle(directory, "service_alias");
    let (alias_report, count) = execute(
        &aliased,
        &[],
        &tape,
        2,
        &mut Wire::default(),
        RunLimits::default(),
        None,
    );
    assert_eq!(alias_report.outcome, Outcome::Completed);
    assert_eq!(count, 2);
    for (output, expected) in alias_report.roles[0].outputs.iter().zip(tape) {
        assert!(matches!(output, Value::Field(value) if *value == expected));
    }
    let tables = bundle(directory, "tables");
    let values = vec![
        array(&[1, 2, 3, 4].map(Scalar::from)),
        array(&[5, 6, 7, 8].map(Scalar::from)),
        Value::Field(Scalar::from(100)),
    ];
    let mut composed = Wire::default();
    assert!(decision(
        &execute(
            &tables,
            &values,
            &tape,
            2,
            &mut composed,
            RunLimits::default(),
            None
        )
        .0,
        "Checker"
    ));
    let standalone = bundle(directory, "tables_reduction");
    let mut separate = Wire::default();
    let (residual, _) = execute(
        &standalone,
        &values,
        &tape,
        2,
        &mut separate,
        RunLimits::default(),
        None,
    );
    assert_eq!(residual.outcome, Outcome::Completed);
    assert_eq!(composed.messages.len(), separate.messages.len());
    for ((prefix, actual), (site, expected)) in composed.messages.iter().zip(&separate.messages) {
        assert_eq!(prefix, &format!("apply_6_reduce_{site}"));
        assert_eq!(actual, expected);
    }
    println!(
        "{} independent exact evaluations, {} weighted runs, composition/transcript and failure controls passed",
        experiments.exact.len(),
        experiments.runs.len()
    );
}
