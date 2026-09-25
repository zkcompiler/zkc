//! The native machine and independent Lean machine execute the same admitted
//! local alternatives, including their dormant arms and terminal failure paths.
#![cfg(feature = "test-utils")]

use serde_json::{Value as Json, json};
use std::{fs, process::Command};
use zkc_backends::{Domain, Scalar, Value};
use zkc_runtime::interactive::{Action, ErrorCode, Runner, StopKind, admit_physical};
use zkc_tools::protocol::ParticipantChecker;

#[path = "common/backend.rs"]
mod fixture;
#[path = "common/observed.rs"]
mod observed;
use observed::PhysicalObserved;

use zkc_test_support::variants::logical as variant;

fn source() -> Json {
    let ty = variant(
        "zkc.tests.ValidatedDraw/1",
        json!([
            ["Ready", ["rng:bls12-381.fr"]],
            ["Retry", ["bool", "rng:bls12-381.fr"]]
        ]),
    );
    json!([
        "zkc.protocol/1",
        [
            ["draw", "random.draw", ["bls12-381.fr"], ""],
            ["require", "control.require", [], ""]
        ],
        [
            [
                "function",
                "Prepare",
                [["r", "rng:bls12-381.fr"], ["ready", "bool"], ["ok", "bool"]],
                [ty],
                [
                    [
                        "if",
                        "choose",
                        "ready",
                        ["r", "ok"],
                        [
                            ["variant", "ready", ty, "Ready", ["r"], "prepared"],
                            ["yield", ["prepared"]]
                        ],
                        [
                            ["variant", "retry", ty, "Retry", ["ok", "r"], "retry"],
                            ["yield", ["retry"]]
                        ],
                        ["result"]
                    ],
                    ["return", ["result"]]
                ],
                ["Prepare", []]
            ],
            [
                "function",
                "Use",
                [["result", ty]],
                ["rng:bls12-381.fr"],
                [
                    [
                        "match",
                        "handle",
                        "result",
                        [],
                        [
                            [
                                "Ready",
                                ["r"],
                                [
                                    ["op", "first", "draw", [], ["r"], ["first", "r1"]],
                                    ["op", "second", "draw", [], ["r1"], ["second", "r2"]],
                                    ["yield", ["r2"]]
                                ]
                            ],
                            [
                                "Retry",
                                ["ok", "r"],
                                [["op", "guard", "require", [], ["ok"], []], ["yield", ["r"]]]
                            ]
                        ],
                        ["next"]
                    ],
                    ["return", ["next"]]
                ],
                ["Use", []]
            ],
            [
                "function",
                "Work",
                [["r", "rng:bls12-381.fr"], ["ready", "bool"], ["ok", "bool"]],
                ["rng:bls12-381.fr"],
                [
                    [
                        "apply",
                        "prepare",
                        "Prepare",
                        [],
                        ["r", "ready", "ok"],
                        ["result"]
                    ],
                    ["apply", "use", "Use", [], ["result"], ["next"]],
                    ["return", ["next"]]
                ],
                ["Work", []]
            ]
        ],
        [[
            "protocol",
            "Root",
            ["P"],
            [],
            [
                ["r", "P", "rng:bls12-381.fr"],
                ["ready", "P", "bool"],
                ["ok", "P", "bool"]
            ],
            [["P", "rng:bls12-381.fr"]],
            [],
            [
                ["local", "work", "P", "Work", ["r", "ready", "ok"], ["next"]],
                ["return", ["next"]]
            ]
        ]],
        [["instance", "root", "Root", [], [], [["P", "P"]]]],
        [["entry", "main", "root"]]
    ])
}

#[test]
fn selected_payload_and_terminal_stops_match_reference_state_and_effect_order() {
    let lean = zkc_test_support::checker("interactive-protocol");
    let checker = ParticipantChecker::new(&lean).unwrap();
    let directory = zkc_test_support::evidence(module_path!());
    let source_path = directory.path().join("source.json");
    let candidate_path = directory.path().join("candidate.json");
    let input_path = directory.path().join("inputs.json");
    let storage_path = directory.path().join("storage.json");
    let source = serde_json::to_vec(&source()).unwrap();
    fs::write(&source_path, &source).unwrap();
    let candidate = zkc_test_support::compile("protocol-compile", &source_path);
    fs::write(&candidate_path, &candidate).unwrap();
    fs::write(
        &storage_path,
        serde_json::to_vec(&json!(["zkc.local-resources/1", "67108864", []])).unwrap(),
    )
    .unwrap();

    // Success, recoverable retry, terminal guard rejection, and exhaustion both
    // before a draw and after an already-consumed draw. No test changes a budget
    // to turn an inconvenient stopped execution into a successful one. The
    // resource counter includes the consuming attempt that exhausts its budget.
    for (ready, ok, budget, expected_consumes) in [
        (true, false, 2, 2),
        (false, true, 0, 0),
        (false, false, 2, 0),
        (true, true, 0, 1),
        (true, true, 1, 2),
    ] {
        let mut native = fixture::backend();
        let resource = native
            .issue_test_tape(
                Domain::new("P", "test", "main", None),
                budget,
                vec![Scalar::from(2), Scalar::from(3)],
            )
            .unwrap();
        let Value::Rng(token) = &resource else {
            panic!("rng")
        };
        let token = token.clone();
        let admitted = admit_physical(&source, &candidate, &native, &checker).unwrap();
        let mut runner = Runner::new(
            &admitted,
            "main",
            "P",
            "test",
            PhysicalObserved {
                inner: native,
                steps: vec![],
                requests: vec![],
            },
            vec![resource, Value::Bool(ready), Value::Bool(ok)],
        )
        .unwrap_or_else(|e| panic!("{}", e.error));
        let terminal = loop {
            match runner.poll() {
                Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
                terminal => break terminal,
            }
        };
        fs::write(
            &input_path,
            serde_json::to_vec(&json!([
                "zkc.reference-inputs/1",
                "main",
                "test",
                [[
                    "P",
                    [
                        ["r", ["rng:bls12-381.fr", ["draws", "0"]]],
                        ["ready", ["bool", ready.to_string()]],
                        ["ok", ["bool", ok.to_string()]]
                    ]
                ]],
                [["draws", "P", [], budget.to_string(), ["rng", ["2", "3"]]]],
                [],
                []
            ]))
            .unwrap(),
        )
        .unwrap();
        let output = Command::new(&lean)
            .arg("--physical-local-reference")
            .args([&source_path, &candidate_path, &input_path, &storage_path])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let reference: Json = serde_json::from_slice(&output.stdout).unwrap();
        match terminal {
            Action::Returned(values) => {
                let [Value::Rng(next)] = values.as_slice() else {
                    panic!("returned payload")
                };
                assert_eq!(
                    reference[1],
                    json!([
                        "returned",
                        [["rng:bls12-381.fr", ["draws", next.generation().to_string()]]]
                    ])
                );
            }
            Action::Stopped(stop) => {
                let StopKind::Backend(error) = stop.kind else {
                    panic!("unexpected stop: {:?}", stop.kind)
                };
                let reason = if reference[1][0] == "reject" {
                    "rejected"
                } else {
                    reference[1][0].as_str().unwrap()
                };
                assert_eq!(
                    error.code,
                    format!("{reason}:{}", reference[1][1].as_str().unwrap())
                );
                assert_eq!(stop.site.as_deref(), reference[1][2][5].as_str());
                assert!(stop.cleanup_errors.is_empty());
            }
            other => panic!("unexpected action {other:?}"),
        }
        let state = runner.backend().inner.observe(&token).unwrap();
        assert_eq!(state.draw_count, expected_consumes);
        assert_eq!(reference[3][0][3], state.generation.to_string());
        assert_eq!(reference[3][0][4], state.draw_count.to_string());
        assert_eq!(reference[3][0][5], state.budget.to_string());
        let requests = reference[2]
            .as_array()
            .unwrap()
            .iter()
            .filter(|event| event[0] == "request")
            .map(|event| {
                let path = event[1][1][4].as_array().unwrap();
                json!([event[1][1][5], &path[1..], event[1][2]])
            })
            .collect::<Vec<_>>();
        assert_eq!(requests, runner.backend().requests);
        assert_eq!(reference[5], json!(runner.backend().steps));
        let usage = runner.usage();
        assert_eq!(
            reference[4],
            json!([
                usage.instructions.to_string(),
                usage.live_values.to_string(),
                usage.live_value_bytes.to_string(),
                usage.total_value_bytes.to_string(),
                "0"
            ])
        );
        assert_eq!(runner.into_backend().inner.active_frames(), 0);
    }
}

#[test]
fn portable_affinity_is_independent_of_variant_syntax() {
    use zkc_runtime::interactive::admit_supplied;
    let lean = zkc_test_support::checker("interactive-protocol");
    let directory = zkc_test_support::evidence(module_path!());
    let path = directory.path().join("source.json");
    let original = source();
    let ty = original[2][0][3][0].clone();
    let native = fixture::backend();
    for pack in [false, true] {
        let mut source = original.clone();
        let mut function = source[2][2].clone();
        function[3] = json!(["bool"]);
        let mut body = vec![];
        if pack {
            body.push(json!(["variant", "unused", ty, "Ready", ["r"], "boxed"]));
        }
        body.push(json!(["return", ["ready"]]));
        function[4] = json!(body);
        source[2] = json!([function]);
        source[3][0][5] = json!([["P", "bool"]]);
        fs::write(&path, serde_json::to_vec(&source).unwrap()).unwrap();
        let candidate = zkc_test_support::compile("protocol-compile", &path);
        admit_supplied(&candidate, &native).unwrap();
        let output = Command::new(&lean)
            .arg("--admit")
            .arg(&path)
            .output()
            .unwrap();
        let result: Json = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result[0], "checked", "pack={pack}: {result}");
    }
}

#[test]
fn malformed_local_alternatives_are_rejected_by_independent_consumers() {
    use zkc_runtime::interactive::admit_supplied;
    let compiler = zkc_test_support::compiler();
    let lean = zkc_test_support::checker("interactive-protocol");
    let directory = zkc_test_support::evidence(module_path!());
    let path = directory.path().join("source.json");
    let original = source();
    fs::write(&path, serde_json::to_vec(&original).unwrap()).unwrap();
    let candidate: Json =
        serde_json::from_slice(&zkc_test_support::compile("protocol-compile", &path)).unwrap();
    let native = fixture::backend();
    admit_supplied(&serde_json::to_vec(&candidate).unwrap(), &native).unwrap();
    for case in [
        "missing",
        "duplicate",
        "unknown",
        "payload",
        "isolation",
        "order",
    ] {
        let mutate = |node: &mut Json| {
            let input = node[2].clone();
            let arms = node[4].as_array_mut().unwrap();
            match case {
                "missing" => {
                    arms.pop();
                }
                "duplicate" => {
                    arms[1][0] = arms[0][0].clone();
                }
                "unknown" => {
                    arms[1][0] = json!("Unknown");
                }
                "payload" => {
                    arms[0][1] = json!([]);
                }
                "isolation" => {
                    arms[1][2] = json!([["yield", [input]]]);
                }
                "order" => {
                    arms.swap(0, 1);
                }
                _ => unreachable!(),
            }
        };
        let mut source = original.clone();
        mutate(&mut source[2][1][4][0]);
        fs::write(&path, serde_json::to_vec(&source).unwrap()).unwrap();
        let cpp = Command::new(&compiler)
            .arg("protocol-admit")
            .arg(&path)
            .output()
            .unwrap();
        let expected_cpp = match case {
            "missing" => "local-match-arms",
            "isolation" => "interactive-unavailable",
            _ => "local-match-arm",
        };
        assert!(
            !cpp.status.success() && String::from_utf8_lossy(&cpp.stderr).contains(expected_cpp),
            "C++ {case}: {}",
            String::from_utf8_lossy(&cpp.stderr)
        );
        let reference = Command::new(&lean)
            .arg("--admit")
            .arg(&path)
            .output()
            .unwrap();
        let result: Json = serde_json::from_slice(&reference.stdout).unwrap();
        let expected_lean = match case {
            "payload" => "result-arity",
            "isolation" => "unbound:result",
            _ => "variant-arms",
        };
        assert_eq!(result, json!(["refused", expected_lean]), "Lean {case}");
        let mut physical = candidate.clone();
        mutate(&mut physical[3][1][4][0]);
        let error = admit_supplied(&serde_json::to_vec(&physical).unwrap(), &native).unwrap_err();
        let unavailable = format!(
            "unavailable operand {}",
            physical[3][1][4][0][2].as_str().unwrap()
        );
        let expected = match case {
            "missing" => (ErrorCode::Signature, "match-exhaustive"),
            "isolation" => (ErrorCode::Ssa, unavailable.as_str()),
            _ => (ErrorCode::Signature, "match-alternative"),
        };
        assert_eq!((error.code, error.detail.as_str()), expected, "Rust {case}");
    }
}

#[test]
fn authored_checked_variants_and_traversals_execute_in_both_machines() {
    let lean = zkc_test_support::checker("interactive-protocol");
    let checker = ParticipantChecker::new(&lean).unwrap();
    let directory = zkc_test_support::evidence(module_path!());
    let authored = directory.path().join("author.pir");
    let source_path = directory.path().join("source.json");
    let candidate_path = directory.path().join("candidate.json");
    let input_path = directory.path().join("inputs.json");
    let storage_path = directory.path().join("storage.json");
    let original = fs::read_to_string(
        zkc_test_support::root().join("examples/protocols/checked-variants.pir"),
    )
    .unwrap();
    fs::write(
        &storage_path,
        serde_json::to_vec(&json!(["zkc.local-resources/1", "67108864", []])).unwrap(),
    )
    .unwrap();
    // Each selected component has the same abstract signature but a different
    // state layout. Stops are injected into the actual selected source arm;
    // none can be caught by the enclosing match or followed by its return.
    let mut cases: Vec<(String, Option<&str>, &[&str])> = vec![(original.clone(), None, &[])];
    for reason in ["reject", "abort", "exhausted", "incomplete", "refused"] {
        cases.push((
            original
                .replace("let next = C::step(state);", &format!("stop {reason};"))
                .replace(
                    "        let answer = C::finish(next, ok);\n        yield (answer);",
                    "",
                ),
            Some(reason),
            &["ready", "stored"],
        ));
    }
    let all_stopping = original
        .replacen(
            "match result capture(ok) -> (answer)",
            "match result capture(ok) -> ()",
            1,
        )
        .replacen("let next = C::step(state);", "stop abort;", 1)
        .replacen(
            "        let answer = C::finish(next, ok);\n        yield (answer);",
            "",
            1,
        )
        .replacen(
            "Invalid(error) => { yield (error); }",
            "Invalid(error) => { stop reject; }",
            1,
        )
        .replacen("    return answer;", "", 1);
    cases.push((all_stopping, Some("abort"), &["ready", "stored"]));
    let (prefix, stored) = original.split_once("component StoredCell").unwrap();
    let stopping_member = format!(
        "{prefix}component StoredCell{}",
        stored.replacen(
            "local step(state: State) -> State { return state; }",
            "local step(state: State) -> State { stop refused; }",
            1
        )
    );
    cases.push((stopping_member, Some("refused"), &["stored"]));
    for (index, (text, stop, stop_entries)) in cases.iter().enumerate() {
        fs::write(&authored, text).unwrap();
        let source = zkc_test_support::compile("protocol-source", &authored);
        fs::write(&source_path, &source).unwrap();
        let candidate = zkc_test_support::compile("protocol-compile", &source_path);
        fs::write(&candidate_path, &candidate).unwrap();
        for entry in ["ready", "stored", "error", "walk", "zero"] {
            for value in [false, true] {
                let native = fixture::backend_at("Prover", "test", entry);
                let admitted = admit_physical(&source, &candidate, &native, &checker).unwrap();
                let mut runner = Runner::new(
                    &admitted,
                    entry,
                    "Prover",
                    "test",
                    PhysicalObserved {
                        inner: native,
                        steps: vec![],
                        requests: vec![],
                    },
                    vec![Value::Bool(value)],
                )
                .unwrap_or_else(|e| panic!("{}", e.error));
                let terminal = loop {
                    match runner.poll() {
                        Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
                        terminal => break terminal,
                    }
                };
                let port = if entry == "error" { "error" } else { "ok" };
                fs::write(
                    &input_path,
                    serde_json::to_vec(&json!([
                        "zkc.reference-inputs/1",
                        entry,
                        "test",
                        [["Prover", [[port, ["bool", value.to_string()]]]]],
                        [],
                        [],
                        []
                    ]))
                    .unwrap(),
                )
                .unwrap();
                let output = Command::new(&lean)
                    .arg("--physical-local-reference")
                    .args([&source_path, &candidate_path, &input_path, &storage_path])
                    .output()
                    .unwrap();
                assert!(
                    output.status.success(),
                    "case {index}/{entry}: {}{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                let reference: Json = serde_json::from_slice(&output.stdout).unwrap();
                // The runtime conditional selects Invalid(false) without entering
                // Ready's stopping arm. The all-stopping variant also stops
                // its Invalid arm with a distinct reason.
                if stop_entries.contains(&entry) && (value || index == 6) {
                    let reason = if !value { "reject" } else { stop.unwrap() };
                    let Action::Stopped(stopped) = terminal else {
                        panic!("terminal stop recovered: {terminal:?}")
                    };
                    assert_eq!(stopped.kind, StopKind::Explicit(reason.into()));
                    assert_eq!(reference[1][0], reason);
                    assert!(stopped.cleanup_errors.is_empty());
                } else {
                    let Action::Returned(values) = terminal else {
                        panic!("unexpected terminal: {terminal:?}")
                    };
                    assert!(matches!(values.as_slice(), [Value::Bool(actual)] if *actual == value));
                    assert_eq!(
                        reference[1],
                        json!(["returned", [["bool", value.to_string()]]])
                    );
                }
                assert_eq!(
                    reference[5],
                    json!(runner.backend().steps),
                    "case {index}/{entry}"
                );
                let usage = runner.usage();
                assert_eq!(
                    reference[4],
                    json!([
                        usage.instructions.to_string(),
                        usage.live_values.to_string(),
                        usage.live_value_bytes.to_string(),
                        usage.total_value_bytes.to_string(),
                        "0"
                    ]),
                    "case {index}/{entry}"
                );
                assert_eq!(runner.into_backend().inner.active_frames(), 0);
            }
        }
    }
}
