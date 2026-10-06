//! Executes compiler-generated mixed math/local participants with real custody.
use std::path::Path;
use zkc_backends::{
    Capability, Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Scalar, Value,
};
use zkc_runtime::interactive::{Action, Runner, StopKind, admit_supplied};
fn domain(role: &str) -> Domain {
    Domain::new(role, "mixed_test", "main", None)
}
fn backend() -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(domain("P"), None, PublicInputs::LocalOnly),
        None,
    )
    .unwrap()
}
fn token(value: &Value) -> &Capability {
    match value {
        Value::Rng(token) => token,
        _ => panic!("expected RNG"),
    }
}
fn next(runner: &mut Runner<NativeBackend>) -> Action<Value> {
    for _ in 0..16 {
        match runner.poll() {
            Action::Local(local) => {
                runner.execute_local(&local.cut).unwrap();
            }
            action => return action,
        }
    }
    panic!("mixed example exceeded its expected local calls")
}
fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("generated mixed candidate directory");
    for (file, draws, stop_after) in [
        ("mixed", 0, false),
        ("mixed-draw", 1, false),
        ("mixed-stop-after", 1, true),
    ] {
        let bytes = std::fs::read(Path::new(&directory).join(format!("{file}.json"))).unwrap();
        for go in [true, false] {
            let mut native = backend();
            let rng = native
                .issue_test_tape(domain("P"), 7, vec![Scalar::from(5u64)])
                .unwrap();
            let before = native.observe(token(&rng)).unwrap();
            let admitted = admit_supplied(&bytes, &native).unwrap();
            let mut runner = Runner::new(
                &admitted,
                "main",
                "P",
                "mixed_test",
                native,
                vec![
                    Value::Field(Scalar::from(3u64)),
                    rng.clone(),
                    Value::Bool(go),
                ],
            )
            .map_err(|failure| failure.error)
            .unwrap();
            if !go {
                let Action::Stopped(stop) = next(&mut runner) else {
                    panic!("guard did not stop")
                };
                assert_eq!(stop.kind, StopKind::Explicit("reject".into()));
                assert_eq!(stop.site.as_deref(), Some("before_work"));
                assert!(stop.cleanup_errors.is_empty());
                let after = runner.backend().observe(token(&rng)).unwrap();
                assert_eq!(after.draw_count, if stop_after { draws } else { 0 });
                assert_eq!(after.budget, 7 - after.draw_count);
                assert_eq!(runner.backend().active_frames(), 0);
                assert_eq!(runner.usage().live_values, 0);
                let usage = runner.usage();
                assert!(matches!(runner.poll(), Action::Stopped(again) if again == stop));
                assert_eq!(runner.usage(), usage);
                continue;
            }
            let Action::Send(packet) = next(&mut runner) else {
                panic!("expected result send")
            };
            let payload = runner
                .take_send(&Action::Send(packet).cut().unwrap())
                .unwrap()
                .payload;
            assert!(matches!(payload, Value::Field(value) if value == Scalar::from(12u64)));
            let Action::Returned(values) = next(&mut runner) else {
                panic!("expected returned RNG")
            };
            assert_eq!(values.len(), 2);
            let returned = token(&values[1]);
            assert_eq!(returned.issued_id(), token(&rng).issued_id());
            assert_eq!(returned.generation(), token(&rng).generation() + draws);
            let after = runner.backend().observe(returned).unwrap();
            assert_eq!(after.draw_count, draws);
            assert_eq!(after.budget, 7 - draws);
            assert_eq!(runner.backend().active_frames(), 0);
            if draws == 0 {
                assert_eq!(after, before);
            }
        }
        // Cancellation at an interaction boundary keeps consumed registry state.
        let mut native = backend();
        let rng = native
            .issue_test_tape(domain("P"), 7, vec![Scalar::from(5u64)])
            .unwrap();
        let admitted = admit_supplied(&bytes, &native).unwrap();
        let mut runner = Runner::new(
            &admitted,
            "main",
            "P",
            "mixed_test",
            native,
            vec![
                Value::Field(Scalar::from(3u64)),
                rng.clone(),
                Value::Bool(true),
            ],
        )
        .map_err(|failure| failure.error)
        .unwrap();
        assert!(matches!(next(&mut runner), Action::Send(_)));
        runner.cancel();
        assert!(matches!(runner.poll(), Action::Stopped(_)));
        assert_eq!(runner.backend().active_frames(), 0);
        let after = runner.backend().observe(token(&rng)).unwrap();
        assert_eq!(after.draw_count, draws);
        assert_eq!(after.budget, 7 - draws);
        // A correctly typed resource issued to another owner is still refused.
        let mut native = backend();
        let wrong = native.issue_rng(domain("V"), 7).unwrap();
        let admitted = admit_supplied(&bytes, &native).unwrap();
        assert!(
            Runner::new(
                &admitted,
                "main",
                "P",
                "mixed_test",
                native,
                vec![Value::Field(Scalar::from(3u64)), wrong, Value::Bool(true)]
            )
            .is_err()
        );
    }
    custody_boundaries(&directory);
    mixed_service(&directory);
    println!(
        "mixed generated participants: ordered calls, resource return, guard stops, cancellation and entry custody passed"
    );
}

fn field(value: u64) -> Value {
    Value::Field(Scalar::from(value))
}
fn finish_local(runner: &mut Runner<NativeBackend>) -> Vec<Value> {
    let Action::Returned(values) = next(runner) else {
        panic!("normal return expected")
    };
    assert_eq!(runner.backend().active_frames(), 0);
    values
}
fn custody_boundaries(directory: &str) {
    use zkc_backends::GroupPoint;
    use zkc_runtime::interactive::{Packet, Value as RuntimeValue};
    // The host deliberately supplies a reply different from the earlier send.
    // This also ensures the calculation uses the actual received component.
    for name in [
        "mixed-unit",
        "mixed-inverse",
        "mixed-nonce",
        "mixed-transcript",
    ] {
        let bytes = std::fs::read(Path::new(directory).join(format!("{name}.json"))).unwrap();
        for mode in ["normal", "guard", "cancel", "zero"] {
            if mode == "zero" && name != "mixed-inverse" {
                continue;
            }
            let mut native = backend();
            let go = mode != "guard";
            let mut observed = None;
            let inputs = match name {
                "mixed-nonce" => {
                    let nonce = native
                        .issue_test_nonce(domain("P"), 7, Scalar::from(5u64))
                        .unwrap();
                    let Value::Nonce(handle) = &nonce else {
                        panic!("nonce")
                    };
                    observed = Some(handle.clone());
                    vec![
                        Value::Groups(vec![GroupPoint::generator()].into()),
                        nonce,
                        field(3),
                        Value::Bool(go),
                    ]
                }
                "mixed-transcript" => {
                    let root = zkc_runtime::logical::encode_tree(&serde_json::json!([
                        "mixed-custody-root"
                    ]))
                    .unwrap();
                    let transcript = native.issue_transcript(domain("P"), 7, &root).unwrap();
                    let Value::Transcript(handle) = &transcript else {
                        panic!("transcript")
                    };
                    observed = Some(handle.clone());
                    vec![transcript, field(9), Value::Bool(go)]
                }
                _ => vec![field(9), Value::Bool(go)],
            };
            let admitted = admit_supplied(&bytes, &native).unwrap();
            let mut runner = Runner::new(&admitted, "main", "P", "mixed_test", native, inputs)
                .unwrap_or_else(|failure| panic!("entry: {:?}", failure.error));
            let Action::Send(send) = next(&mut runner) else {
                panic!("send must precede receive and guard")
            };
            if name == "mixed-nonce" {
                assert!(
                    matches!(&send.payload, Value::Groups(v) if v.len() == 1 && v[0] == GroupPoint::generator().scale(Scalar::from(5u64)))
                );
            } else {
                assert!(matches!(&send.payload, Value::Field(v) if *v == Scalar::from(9u64)));
            }
            runner
                .take_send(&Action::Send(send).cut().unwrap())
                .unwrap();
            let Action::Receive(receive) = next(&mut runner) else {
                panic!("received value must precede local work")
            };
            assert_eq!(
                runner.backend().live_resource_units(),
                usize::from(name == "mixed-unit")
            );
            if let Some(handle) = &observed {
                let before = runner.backend().observe(handle).unwrap();
                assert_eq!(before.draw_count, u64::from(name == "mixed-nonce"));
                assert_eq!(
                    before.stage,
                    if name == "mixed-nonce" {
                        "committed"
                    } else {
                        "transcript"
                    }
                );
            }
            if mode == "cancel" {
                runner.cancel();
            } else {
                let value = field(if mode == "zero" { 0 } else { 4 });
                runner
                    .deliver(Packet {
                        envelope: receive.envelope,
                        ty: value.physical_type(),
                        payload: value,
                    })
                    .unwrap();
            }
            if mode == "normal" {
                let values = finish_local(&mut runner);
                match name {
                    "mixed-unit" => {
                        assert!(matches!(&values[0], Value::Field(v) if *v == Scalar::from(4u64)))
                    }
                    "mixed-inverse" => {
                        assert!(matches!(&values[0], Value::Field(v) if *v == Scalar::from(1u64)))
                    }
                    "mixed-nonce" => {
                        assert!(matches!(&values[0], Value::Field(v) if *v == Scalar::from(17u64)))
                    }
                    "mixed-transcript" => {
                        let Value::Transcript(returned) = &values[1] else {
                            panic!("returned transcript")
                        };
                        assert_eq!(returned.issued_id(), observed.as_ref().unwrap().issued_id());
                        assert_eq!(
                            returned.generation(),
                            observed.as_ref().unwrap().generation() + 1
                        );
                    }
                    _ => unreachable!(),
                }
            } else {
                let Action::Stopped(stop) = next(&mut runner) else {
                    panic!("must stop")
                };
                if mode == "guard" {
                    assert_eq!(stop.kind, StopKind::Explicit("reject".into()));
                    assert_eq!(stop.site.as_deref(), Some("after_receive"));
                } else if mode == "zero" {
                    assert!(
                        matches!(&stop.kind, StopKind::Backend(error) if error.code == "refused:zero-inverse")
                    );
                    assert_eq!(stop.site.as_deref(), Some("inverse"));
                }
                assert!(stop.cleanup_errors.is_empty());
                assert_eq!(runner.usage().live_values, 0);
                assert!(matches!(runner.poll(), Action::Stopped(again) if again == stop));
            }
            assert_eq!(runner.backend().active_frames(), 0);
            assert_eq!(runner.backend().live_resource_units(), 0);
            if let Some(handle) = &observed {
                let after = runner.backend().observe(handle).unwrap();
                let expected = if name == "mixed-nonce" {
                    1 + u64::from(mode == "normal")
                } else {
                    u64::from(mode == "normal")
                };
                assert_eq!(after.draw_count, expected);
                assert_eq!(after.budget, 7 - expected);
                if name == "mixed-nonce" {
                    assert_eq!(
                        after.stage,
                        if mode == "normal" {
                            "spent"
                        } else {
                            "committed"
                        }
                    );
                }
            }
        }
    }
}

fn mixed_service(directory: &str) {
    use std::collections::BTreeMap;
    use zkc_backends::services::ServiceRegistry;
    let bytes = std::fs::read(Path::new(directory).join("mixed-service.json")).unwrap();
    for go in [true, false] {
        let registry = ServiceRegistry::new(Policy::default());
        let root = registry
            .issue_test_tape("P", 3, vec![Scalar::from(7u64)])
            .unwrap();
        let mut native = backend();
        let rng = native
            .issue_test_tape(domain("P"), 7, vec![Scalar::from(5u64)])
            .unwrap();
        let admitted = admit_supplied(&bytes, &native).unwrap();
        let entry = admitted
            .entry("main")
            .unwrap()
            .into_iter()
            .find(|p| p.role == "P")
            .unwrap();
        let port = entry.services[0].name.clone();
        let native = native
            .with_services(registry.clone(), BTreeMap::from([(port, root.clone())]))
            .unwrap();
        let mut runner = Runner::new(
            &admitted,
            "main",
            "P",
            "mixed_test",
            native,
            vec![field(3), rng.clone(), Value::Bool(go)],
        )
        .unwrap_or_else(|failure| panic!("service + affine entry: {:?}", failure.error));
        let Action::Query(query) = next(&mut runner) else {
            panic!("query")
        };
        runner.execute_query(&query.cut).unwrap();
        if go {
            let Action::Send(send) = next(&mut runner) else {
                panic!("send")
            };
            assert!(matches!(&send.payload, Value::Field(v) if *v == Scalar::from(20u64)));
            runner
                .take_send(&Action::Send(send).cut().unwrap())
                .unwrap();
            finish_local(&mut runner);
        } else {
            assert!(
                matches!(next(&mut runner), Action::Stopped(stop) if stop.kind == StopKind::Explicit("reject".into()))
            );
        }
        let service = registry.observe(&root).unwrap();
        assert!(!service.leased && !service.poisoned);
        assert_eq!(service.state.unwrap().draw_count, 1);
        let affine = runner.backend().observe(token(&rng)).unwrap();
        assert_eq!(affine.draw_count, u64::from(go));
        assert_eq!(affine.budget, 7 - u64::from(go));
        assert_eq!(runner.backend().active_frames(), 0);
    }
}
