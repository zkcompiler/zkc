//! Joint completion and partial-peer outcomes over compiler-produced schedules.
use serde_json::Value as Json;
use std::path::Path;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Scalar, Value};
use zkc_runtime::interactive::PathElement;
use zkc_tools::run::*;
fn backend(role: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "test", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
struct CancelImmediately;
impl Hooks<NativeBackend> for CancelImmediately {
    fn cancel_before(&mut self, _: usize, _: &Step, _: &[PathElement]) -> Option<String> {
        Some("inspect completion".into())
    }
}
fn main() {
    let directory = std::env::args().nth(1).unwrap();
    let directory = Path::new(&directory);
    let cases: Vec<Json> =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    for case in &cases {
        let name = case["name"].as_str().unwrap();
        let depth = case["depth"].as_u64().unwrap();
        let bytes = std::fs::read(directory.join(format!("{name}.bundle"))).unwrap();
        let bundle = Bundle::admit(&bytes, &backend("P"), BundleLimits::default()).unwrap();
        if depth == 0 && name == "completion_0" {
            let inputs = ["P", "V"]
                .into_iter()
                .map(|role| RoleInput {
                    role: role.into(),
                    backend: backend(role),
                    values: vec![
                        Value::Bool(true),
                        Value::Index(2),
                        Value::Field(Scalar::from(9)),
                    ],
                })
                .collect();
            let report = run(
                &bundle,
                "test",
                inputs,
                RunLimits::default(),
                &mut CancelImmediately,
            )
            .unwrap();
            assert!(matches!(report.outcome, Outcome::HostCancelled(_)));
            assert!(
                matches!(&report.roles[0].before, State::ReturnIf { site } if site == "exit_P")
            );
            assert!(report.roles.iter().all(|role| role.return_at.is_none()));
        }
        for (p, v) in [(false, false), (true, true), (true, false), (false, true)] {
            let inputs = [("P", p), ("V", v)]
                .into_iter()
                .map(|(role, stop)| RoleInput {
                    role: role.into(),
                    backend: backend(role),
                    values: vec![
                        Value::Bool(stop),
                        Value::Index(2),
                        Value::Field(Scalar::from(9)),
                    ],
                })
                .collect();
            let report = run(&bundle, "test", inputs, RunLimits::default(), &mut NoHooks).unwrap();
            if p == v {
                assert_eq!(report.outcome, Outcome::Completed, "{name}: {p}/{v}");
                assert!(report.roles.iter().all(|r| !r.cancelled));
                assert_eq!(
                    report.wire.sends,
                    if p {
                        0
                    } else {
                        case["sends"].as_u64().unwrap() as usize
                    }
                );
            } else {
                let returned = usize::from(v);
                let blocked = 1 - returned;
                assert_eq!(
                    report.outcome,
                    Outcome::ReturnedEarly {
                        role: returned,
                        blocked
                    },
                    "{name}"
                );
                assert!(!report.roles[returned].cancelled);
                assert!(report.roles[blocked].cancelled);
                assert_eq!(report.wire.sends, 0);
            }
            for (row, stop) in report.roles.iter().zip([p, v]) {
                if stop {
                    assert_eq!(row.return_at.as_ref().unwrap().0.path.len(), depth as usize);
                    assert_eq!(row.usage.unwrap().iterations, depth);
                    assert!(matches!(row.outputs.as_slice(), [Value::Bool(true)]));
                } else {
                    assert!(row.return_at.is_none());
                }
            }
        }
    }
    let bytes = std::fs::read(directory.join("independent_counts.bundle")).unwrap();
    let bundle = Bundle::admit(&bytes, &backend("P"), BundleLimits::default()).unwrap();
    for last_count in [2, 3] {
        let inputs = [("P", 99), ("Q", 2), ("V", last_count)]
            .into_iter()
            .map(|(role, count)| {
                let mut values = Vec::new();
                if role == "P" {
                    values.push(Value::Bool(true));
                }
                values.push(Value::Index(count));
                RoleInput {
                    role: role.into(),
                    backend: backend(role),
                    values,
                }
            })
            .collect();
        let report = run(&bundle, "test", inputs, RunLimits::default(), &mut NoHooks).unwrap();
        assert!(matches!(
            report.roles[0].outputs.as_slice(),
            [Value::Bool(false)]
        ));
        assert_eq!(report.roles[0].usage.unwrap().iterations, 0);
        assert!(!report.roles[0].cancelled);
        if last_count == 2 {
            assert_eq!(report.outcome, Outcome::Completed);
            for peer in &report.roles[1..] {
                assert!(matches!(peer.outputs.as_slice(), [Value::Bool(true)]));
                assert_eq!(peer.usage.unwrap().iterations, 2);
            }
        } else {
            assert!(matches!(&report.outcome, Outcome::DriverFailed(failure)
                if failure.kind == FailureKind::Contract
                    && failure.detail.text == "loop-count-disagreement"
                    && failure.detail.omitted_bytes == 0));
            let headers: Vec<_> = report
                .reached
                .iter()
                .filter_map(|row| row.loop_count.map(|count| (row.step.role, count)))
                .collect();
            // P returned before the loop. Its out-of-bound 99 is never reached;
            // only the live Q/V counts participate in the agreement check.
            assert_eq!(headers, [(1, 2), (2, 3)]);
            assert!(report.reached.iter().all(|row| !row.loop_started));
            assert!(report.roles[1..].iter().all(|peer| peer.cancelled));
        }
    }
    println!(
        "joint entry completion: {} schedules, four return combinations",
        cases.len()
    );
}
