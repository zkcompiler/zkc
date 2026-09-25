//! Admission of unchanged handles at protocol boundaries, including lazy roles.
use super::*;
use zkc_backends::Domain;

fn compare(kind: &str, restricted: bool, joint: bool) {
    let identity = if kind == "transcript" {
        "merlin3.bls12-381.fr64be/1"
    } else {
        "bls12-381.fr"
    };
    let ty = format!("{kind}:{identity}");
    let label = if kind == "rng" { "draws" } else { kind };
    let mut fixture = Fixture::new();
    let (roles, inputs, outputs, names, body, functions, bindings) = if joint {
        (
            json!(["P", "V"]),
            json!([["n", "P", ty], ["b", "V", "bool"]]),
            json!([["P", ty], ["V", "bool"]]),
            json!(["n", "b"]),
            json!([
                ["call", "pass", "child", ["n", "b"], ["next", "other"]],
                ["local", "work", "V", "Both", ["other", "other"], ["same"]],
                ["message", "send", "boolean", "V", "P", "same", "seen"],
                ["return", ["next", "same"]]
            ]),
            json!([[
                "function",
                "Both",
                [["a", "bool"], ["b", "bool"]],
                ["bool"],
                [
                    ["op", "and", "and", [], ["a", "b"], ["out"]],
                    ["return", ["out"]]
                ],
                ["Both", []]
            ]]),
            json!([["and", "bool.and", [], ""]]),
        )
    } else {
        (
            json!(["P"]),
            json!([["n", "P", ty]]),
            json!([["P", ty]]),
            json!(["n"]),
            json!([
                ["call", "pass", "child", ["n"], ["next"]],
                ["return", ["next"]]
            ]),
            json!([]),
            json!([]),
        )
    };
    let role_map: Vec<_> = roles
        .as_array()
        .unwrap()
        .iter()
        .map(|r| json!([r, r]))
        .collect();
    fixture.set_source(&json!([
        "zkc.protocol/1",
        bindings,
        functions,
        [
            [
                "protocol",
                "Child",
                roles,
                [],
                inputs,
                outputs,
                [],
                [["return", names]]
            ],
            [
                "protocol",
                "Root",
                roles,
                [],
                inputs,
                outputs,
                [["child", "Child", []]],
                body
            ]
        ],
        [
            ["instance", "kid", "Child", [], [], role_map],
            ["instance", "root", "Root", [], [["child", "kid"]], role_map]
        ],
        [["entry", "main", "root"]]
    ]));
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted =
        admit_physical(&fixture.source, &fixture.candidate, &backend(), &checker).unwrap();
    let mut p_backend = backend();
    let restriction = restricted.then(|| "root".to_owned());
    let domain = Domain::new("P", "test", "main", restriction.as_deref());
    let (resource, initializer) = match kind {
        "rng" => (
            p_backend
                .issue_test_tape(domain, 2, vec![Scalar::from(5)])
                .unwrap(),
            json!(["rng", ["5"]]),
        ),
        "nonce" => (
            p_backend
                .issue_test_nonce(domain, 2, Scalar::from(5))
                .unwrap(),
            json!(["nonce", "5"]),
        ),
        "transcript" => {
            let root = json!(["binding"]);
            (
                p_backend
                    .issue_transcript(
                        domain,
                        2,
                        &zkc_runtime::logical::encode_tree(&root).unwrap(),
                    )
                    .unwrap(),
                json!(["transcript", root]),
            )
        }
        _ => unreachable!(),
    };
    let token = match &resource {
        Value::Rng(t) | Value::Nonce(t) | Value::Transcript(t) => t.clone(),
        _ => unreachable!(),
    };
    let trace = Trace::new(&fixture.source);
    let mut runners = BTreeMap::new();
    let mut supplied = vec![json!(["P", [["n", value_json(&resource)]]])];
    for (role, inner, values) in std::iter::once(("P", p_backend, vec![resource]))
        .chain(joint.then(|| ("V", backend_for("V"), vec![Value::Bool(true)])))
    {
        let observed = Observed {
            inner,
            source_map: admitted.source_map().unwrap().clone(),
            events: trace.clone(),
            conversions: 0,
        };
        runners.insert(
            role.to_owned(),
            Runner::new(&admitted, "main", role, "test", observed, values)
                .unwrap_or_else(|e| panic!("{}", e.error)),
        );
    }
    if joint {
        supplied.push(json!(["V", [["b", value_json(&Value::Bool(true))]]]));
    }
    let mut schedule = Schedule::new(&admitted, "main", "test").unwrap();
    let report = drive(&mut schedule, &mut runners, &mut trace.clone());
    let reference_inputs = json!([
        "zkc.reference-inputs/1",
        "main",
        "test",
        supplied,
        [[
            label,
            "P",
            restriction.map_or(json!([]), |s| json!(s)),
            "2",
            initializer
        ]],
        [],
        []
    ]);
    let result = fixture.reference(&reference_inputs);
    assert_eq!(result[4], json!(trace.snapshot()));
    match report.outcome {
        JointOutcome::Returned(values) => {
            assert!(!restricted);
            let ordered: Vec<_> = values
                .values()
                .flat_map(|vs| vs.iter().map(value_json))
                .collect();
            assert_eq!(result[3], json!(["returned", ordered]));
        }
        JointOutcome::Stopped(stop) => {
            assert!(restricted);
            assert_eq!(result[3][0], "refused");
            assert_eq!(result[3][1], "capability-domain");
            assert_eq!(
                stop.kind,
                StopKind::Backend(zkc_runtime::interactive::BackendError::new(
                    "refused:capability-domain"
                ))
            );
            assert_stop_location(&trace, &stop, &result[3][2], false);
            assert_eq!(stop.origin.instance, "kid");
            assert_eq!(report.wire.messages, u64::from(joint));
        }
        JointOutcome::Failed(error) => panic!("{error}"),
    }
    let observed = runners["P"].backend().inner.observe(&token).unwrap();
    assert_eq!(
        result[5],
        json!([[
            label,
            "P",
            if restricted { json!("root") } else { json!([]) },
            "0",
            "0",
            "2",
            observed.stage
        ]])
    );
    assert_eq!(observed.generation, 0);
    assert_eq!(observed.draw_count, 0);
    for runner in runners.values() {
        assert_eq!(runner.backend().inner.active_frames(), 0);
    }
}

#[test]
fn unchanged_handles_obey_child_domains_and_role_order() {
    for kind in ["rng", "nonce", "transcript"] {
        for restricted in [false, true] {
            for joint in [false, true] {
                compare(kind, restricted, joint);
            }
        }
    }
}
