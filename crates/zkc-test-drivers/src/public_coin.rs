//! Compare source-derived verifier views with actual generated joint execution.
use serde::Deserialize;
use serde_json::Value as Json;
use std::{collections::BTreeMap, path::Path};
use zkc_backends::services::ServiceRegistry;
use zkc_backends::{Domain, EntryPolicy, FieldArray, NativeBackend, Policy, Scalar, Value};
use zkc_runtime::interactive::{Identity, LogicalType, ProgramAction};
use zkc_tools::run::*;

#[derive(Deserialize)]
struct Experiments {
    cases: Vec<Case>,
}
#[derive(Deserialize)]
struct Case {
    name: String,
    inputs: Vec<Json>,
    tape: Vec<String>,
    decision: bool,
}
#[derive(Deserialize)]
struct View {
    verifier: String,
    anchors: Vec<Anchor>,
    events: Vec<usize>,
    draws: Vec<Draw>,
}
#[derive(Deserialize)]
struct Anchor {
    kind: String,
    site: Option<String>,
}
#[derive(Deserialize)]
struct Draw {
    site: String,
    prefix_length: usize,
}
fn scalar(s: &str) -> Scalar {
    zkc_arkworks::parse_decimal(s).unwrap()
}
fn array(values: Vec<Scalar>) -> Value {
    Value::FieldArray(
        FieldArray::new(
            LogicalType::field_array(Identity::Bls12381Fr, values.len() as u64).unwrap(),
            values.into(),
        )
        .unwrap(),
    )
}
fn value(v: &Json) -> Value {
    if let Some(s) = v.as_str() {
        Value::Field(scalar(s))
    } else {
        array(
            v.as_array()
                .unwrap()
                .iter()
                .map(|v| scalar(v.as_str().unwrap()))
                .collect(),
        )
    }
}
fn backend(role: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "views", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
#[derive(Default)]
struct Wire {
    changed: bool,
    malformed: bool,
    coins: Vec<Scalar>,
}
impl Hooks<NativeBackend> for Wire {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        _: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        let codec = backend("codec");
        let decoded = codec.decode_native(exchange.ty, bytes).unwrap();
        if exchange.sender == "Checker" {
            let Value::Field(coin) = decoded else {
                panic!("coin delivery");
            };
            self.coins.push(coin);
            return Ok(None);
        }
        if self.malformed {
            return Ok(Some(vec![]));
        }
        if self.changed {
            self.changed = false;
            let changed = match decoded {
                Value::Field(x) => Value::Field(x + Scalar::from(1)),
                Value::FieldArray(a) => {
                    let mut elements = a.elements().to_vec();
                    elements[0] += Scalar::from(1);
                    array(elements)
                }
                _ => panic!("selected field messages"),
            };
            return Ok(Some(codec.encode_native(&changed).unwrap()));
        }
        Ok(None)
    }
}
fn execute(
    bundle: &Bundle,
    case: &Case,
    tape: &[Scalar],
    budget: u64,
    wire: &mut Wire,
    limits: RunLimits,
) -> (Report<NativeBackend>, u64) {
    let registry = ServiceRegistry::new(Policy::default());
    let reference = registry
        .issue_test_tape("Checker", budget, tape.into())
        .unwrap();
    let inputs = bundle
        .roles()
        .iter()
        .map(|role| {
            let mut backend = backend(&role.entry.role);
            if !role.entry.services.is_empty() {
                assert_eq!(role.entry.services.len(), 1);
                backend = backend
                    .with_services(
                        registry.clone(),
                        BTreeMap::from([(role.entry.services[0].name.clone(), reference.clone())]),
                    )
                    .unwrap();
            }
            RoleInput {
                role: role.entry.role.clone(),
                backend,
                values: case.inputs.iter().map(value).collect(),
            }
        })
        .collect();
    let report = run(bundle, "views", inputs, limits, wire).unwrap();
    let state = registry.observe(&reference).unwrap();
    assert!(!state.leased);
    (report, state.state.unwrap().draw_count)
}
fn trace(bundle: &Bundle, view: &View, report: &Report<NativeBackend>) -> usize {
    let mut observed: Vec<(&str, &str)> = vec![];
    let mut queries = 0;
    for reached in &report.reached {
        if bundle.roles()[reached.step.role].entry.role != view.verifier {
            continue;
        }
        match bundle.action(&reached.step).unwrap() {
            ProgramAction::Query { site, .. } => {
                let draw = &view.draws[queries];
                assert_eq!(site, &draw.site);
                let expected: Vec<_> = view.events[..draw.prefix_length]
                    .iter()
                    .filter_map(|i| {
                        let a = &view.anchors[*i];
                        a.site.as_deref().map(|site| (a.kind.as_str(), site))
                    })
                    .collect();
                assert_eq!(observed, expected, "actual prefix before {site}");
                if reached.progress == Progress::Completed {
                    observed.push(("draw", site));
                    queries += 1;
                }
            }
            ProgramAction::Receive { site, .. } if reached.progress == Progress::Completed => {
                observed.push(("receive", site))
            }
            _ => {}
        }
    }
    queries
}
fn decision(report: &Report<NativeBackend>) -> bool {
    assert_eq!(report.outcome, Outcome::Completed);
    let output = &report
        .roles
        .iter()
        .find(|r| r.role == "Checker")
        .unwrap()
        .outputs;
    match output.as_slice() {
        [Value::Bool(b)] => *b,
        _ => panic!("selected Boolean decision"),
    }
}
fn stopped(report: &Report<NativeBackend>) -> &StopSummary {
    assert!(matches!(report.outcome, Outcome::ParticipantStopped { .. }));
    let verifier = report.roles.iter().find(|r| r.role == "Checker").unwrap();
    assert!(verifier.outputs.is_empty());
    let State::Stopped(stop) = &verifier.before else {
        panic!("verifier stop");
    };
    stop
}
fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("generated artifact directory");
    let directory = Path::new(&directory);
    let tests: Experiments =
        serde_json::from_slice(&std::fs::read(directory.join("execution.json")).unwrap()).unwrap();
    for case in tests.cases {
        let bundle = Bundle::admit(
            &std::fs::read(directory.join(format!("{}.bundle", case.name))).unwrap(),
            &backend("admission"),
            BundleLimits::default(),
        )
        .unwrap();
        let view: View = serde_json::from_slice(
            &std::fs::read(directory.join(format!("{}.view.json", case.name))).unwrap(),
        )
        .unwrap();
        let tape: Vec<_> = case.tape.iter().map(|s| scalar(s)).collect();
        let mut wire = Wire::default();
        let (report, count) = execute(
            &bundle,
            &case,
            &tape,
            tape.len() as u64,
            &mut wire,
            RunLimits::default(),
        );
        assert_eq!(decision(&report), case.decision);
        assert_eq!(trace(&bundle, &view, &report), tape.len());
        assert_eq!(count as usize, tape.len());
        assert_eq!(
            wire.coins, tape,
            "delivered V coins equal issued tape values"
        );
        // Valid but altered prover messages preserve receive identity. Sumcheck
        // stops at its guard; the shadow client returns false normally.
        let (report, count) = execute(
            &bundle,
            &case,
            &tape,
            tape.len() as u64,
            &mut Wire {
                changed: true,
                ..Wire::default()
            },
            RunLimits::default(),
        );
        assert_eq!(trace(&bundle, &view, &report), count as usize);
        if case.name == "shadow" {
            assert!(!decision(&report));
        } else {
            assert!(matches!(stopped(&report).cause, StopCause::Explicit(_)));
            assert_eq!(count, if case.name == "r1cs" { 1 } else { 0 });
        }
        // A draw failure is reached but is not a completed challenge event.
        let budget = tape.len() as u64 - 1;
        let (report, count) = execute(
            &bundle,
            &case,
            &tape,
            budget,
            &mut Wire::default(),
            RunLimits::default(),
        );
        assert!(matches!(stopped(&report).cause, StopCause::Backend(_)));
        // The service counts attempted draws, including the failed attempt.
        assert_eq!(count, budget + 1);
        assert_eq!(trace(&bundle, &view, &report), budget as usize);
        // A missing tape response has the same prefix boundary, with budget
        // still available; decoding and driver limits remain separate outcomes.
        let (report, _) = execute(
            &bundle,
            &case,
            &tape[..tape.len() - 1],
            tape.len() as u64,
            &mut Wire::default(),
            RunLimits::default(),
        );
        assert!(matches!(stopped(&report).cause, StopCause::Backend(_)));
        trace(&bundle, &view, &report);
        let (report, _) = execute(
            &bundle,
            &case,
            &tape,
            tape.len() as u64,
            &mut Wire {
                malformed: true,
                ..Wire::default()
            },
            RunLimits::default(),
        );
        assert!(matches!(stopped(&report).cause, StopCause::Decode(_)));
        trace(&bundle, &view, &report);
        let (report, _) = execute(
            &bundle,
            &case,
            &tape,
            tape.len() as u64,
            &mut Wire::default(),
            RunLimits {
                steps: 1,
                ..RunLimits::default()
            },
        );
        assert!(matches!(
            report.outcome,
            Outcome::DriverFailed(Failure {
                kind: FailureKind::Limit,
                ..
            })
        ));
        trace(&bundle, &view, &report);
        if case.name == "r1cs" {
            // The same fixed w=8 stops if tau changes from 7 to 8. The accepted
            // run above is the explicit weighted bad event for an unsatisfiable
            // relation, not proof that its original rows are satisfied.
            let changed = [Scalar::from(8), tape[1]];
            let (report, count) = execute(
                &bundle,
                &case,
                &changed,
                2,
                &mut Wire::default(),
                RunLimits::default(),
            );
            assert!(matches!(stopped(&report).cause, StopCause::Explicit(_)));
            assert_eq!(count, 1);
            trace(&bundle, &view, &report);
        }
    }
    println!("native public-coin prefixes, binding counterexample and stop boundaries passed");
}
