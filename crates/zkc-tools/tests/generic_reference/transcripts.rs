//! Compare source-owned transcript history with actual native Merlin execution.
//! The provider supplies hash bytes only; Lean reduces them into the field.
use super::*;
use std::process::Command;
use zkc_backends::Domain;

fn unhex(value: &Json) -> Vec<u8> {
    zkc_test_support::unhex(value.as_str().unwrap())
}

// Merlin requires static labels. This finite vocabulary does not prescribe the
// call sequence: the explicit request selects every label, value and call.
fn label(value: &Json) -> &'static [u8] {
    match unhex(value).as_slice() {
        b"zkc.artifact/1" => b"zkc.artifact/1",
        b"binding" => b"binding",
        b"origin" => b"origin",
        b"value" => b"value",
        b"challenge" => b"challenge",
        _ => panic!("unsupported Merlin label"),
    }
}

/// Interpret the complete request without supplying a protocol or field answer.
fn hash_reply(request: &Json) -> Json {
    assert_eq!(request[0], "zkc.transcript-request/3");
    let mut transcript = merlin::Transcript::new(label(&request[2]));
    let mut bytes = [0u8; 64];
    for action in request[3].as_array().unwrap() {
        match action[0].as_str().unwrap() {
            "append" => transcript.append_message(label(&action[1]), &unhex(&action[2])),
            "challenge" => {
                assert_eq!(action[2], "64");
                transcript.challenge_bytes(label(&action[1]), &mut bytes);
            }
            kind => panic!("unknown action {kind}"),
        }
    }
    json!(["ok", zkc_test_support::hex(&bytes)])
}

// Expected calls from the native history; equality with Lean's independent
// request pins domain separation as well as origins and mathematical values.
fn request(root: &[u8], history: &[Json]) -> Json {
    let mut calls = vec![json!([
        "append",
        zkc_test_support::hex(b"binding"),
        zkc_test_support::hex(root)
    ])];
    for action in history {
        calls.push(json!([
            "append",
            zkc_test_support::hex(b"origin"),
            action[1]
        ]));
        calls.push(if action[0] == "message" {
            json!(["append", zkc_test_support::hex(b"value"), action[2]])
        } else {
            json!(["challenge", zkc_test_support::hex(b"challenge"), "64"])
        });
    }
    json!([
        "zkc.transcript-request/3",
        "merlin3.bls12-381.fr64be/1",
        zkc_test_support::hex(b"zkc.artifact/1"),
        calls
    ])
}

fn compare(fixture: &Fixture, root: Json, value: bool, budget: u64, allowed: bool, session: &str) {
    compare_value(
        fixture,
        root,
        [Value::Bool(value), Value::Bool(!value)],
        budget,
        allowed,
        session,
    );
}

fn compare_value(
    fixture: &Fixture,
    root: Json,
    values: [Value; 2],
    budget: u64,
    allowed: bool,
    session: &str,
) {
    let [value, changed_value] = values;
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted =
        admit_physical(&fixture.source, &fixture.candidate, &backend(), &checker).unwrap();
    let mut inner = backend_in("P", session);
    let root_bytes = zkc_runtime::logical::encode_tree(&root).unwrap();
    let transcript = inner
        .issue_transcript(Domain::new("P", session, "main", None), budget, &root_bytes)
        .unwrap();
    let Value::Transcript(token) = &transcript else {
        unreachable!()
    };
    let token = token.clone();
    let untouched = inner
        .issue_test_tape(
            Domain::new("P", session, "main", None),
            3,
            vec![Scalar::from(7)],
        )
        .unwrap();
    let Value::Rng(untouched) = untouched else {
        unreachable!()
    };
    let values = vec![transcript, value, Value::Bool(allowed)];
    let ports: Vec<_> = ["state", "value", "allowed"]
        .into_iter()
        .zip(&values)
        .map(|(n, v)| json!([n, value_json(v)]))
        .collect();
    let observer = Observed {
        inner,
        source_map: admitted.source_map().unwrap().clone(),
        events: Trace::new(&fixture.source),
        conversions: 0,
    };
    let mut runner = Runner::new(&admitted, "main", "P", session, observer, values)
        .unwrap_or_else(|e| panic!("{}", e.error));
    let terminal = loop {
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            action @ (Action::Returned(_) | Action::Stopped(_)) => break action,
            action => panic!("unexpected {action:?}"),
        }
    };
    let native = runner.backend().events.snapshot();
    let mut history = Vec::new();
    let mut answers = Vec::new();
    for action in runner.backend().events.transcript_steps() {
        let challenge = action[0] == "challenge";
        history.push(action);
        if challenge {
            let request = request(&root_bytes, &history);
            answers.push(json!([request, hash_reply(&request)]));
        }
    }
    let inputs = json!([
        "zkc.reference-inputs/1",
        "main",
        session,
        [["P", ports]],
        [
            [
                "transcript",
                "P",
                [],
                budget.to_string(),
                ["transcript", root]
            ],
            ["untouched", "P", [], "3", ["rng", ["7"]]]
        ],
        answers,
        []
    ]);
    let result = fixture.reference(&inputs);
    let logical: Vec<_> = result[4]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e[0] != "external")
        .cloned()
        .collect();
    assert_eq!(logical, native);
    let requests: Vec<_> = result[4]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e[0] == "external")
        .map(|e| e[1].clone())
        .collect();
    assert_eq!(
        requests,
        answers.iter().map(|a| a[0].clone()).collect::<Vec<_>>()
    );
    match terminal {
        Action::Returned(values) => assert_eq!(
            result[3],
            json!([
                "returned",
                values.iter().map(value_json).collect::<Vec<_>>()
            ])
        ),
        Action::Stopped(stop) => {
            let StopKind::Backend(error) = &stop.kind else {
                panic!("backend stop")
            };
            let (reason, detail) = error.code.split_once(':').unwrap();
            assert_eq!(
                result[3][0],
                if reason == "rejected" {
                    "reject"
                } else {
                    reason
                }
            );
            assert_eq!(result[3][1], detail);
            assert_stop_location(&runner.backend().events, &stop, &result[3][2], true);
            assert_eq!(
                result[3][2],
                native.iter().rev().find(|e| e[0] == "request").unwrap()[1][1]
            );
            assert_eq!(runner.usage().live_value_bytes, 0);
        }
        _ => unreachable!(),
    }
    let observations: Vec<_> = [("transcript", &token), ("untouched", &untouched)]
        .into_iter()
        .map(|(name, token)| {
            let r = runner.backend().inner.observe(token).unwrap();
            json!([
                name,
                "P",
                [],
                r.generation.to_string(),
                r.draw_count.to_string(),
                r.budget.to_string(),
                r.stage
            ])
        })
        .collect();
    assert_eq!(result[5], json!(observations));
    assert_eq!(runner.backend().inner.active_frames(), 0);

    if !answers.is_empty() {
        for mutate in 0..2 {
            let mut different = inputs.clone();
            if mutate == 0 {
                different[4][0][4][1] = json!(["another-root"]);
            } else {
                different[3][0][1][1][1] = value_json(&changed_value);
            }
            let pending = fixture.reference(&different);
            assert_eq!(pending[3][0], "pending-primitive");
            assert_eq!(pending[5][0][3], "2");
        }
        for width in [0, 63, 65] {
            let mut wrong = inputs.clone();
            wrong[5][0][1] = json!(["ok", "ff".repeat(width)]);
            let failed = fixture.reference(&wrong);
            assert_eq!(failed[3][1], "transcript-challenge-width");
            assert_eq!(failed[5][0][3], "2");
        }
        // Changed labels or call order cannot stand in for the original request.
        for change in 0..2 {
            let mut wrong = inputs.clone();
            if change == 0 {
                wrong[5][0][0][3][1][1] = json!(zkc_test_support::hex(b"value"));
            } else {
                wrong[5][0][0][3].as_array_mut().unwrap().swap(1, 2);
            }
            assert_eq!(fixture.reference(&wrong)[3][0], "pending-primitive");
        }
    }
}

#[test]
fn transcript_history_and_consumption_match_native_execution() {
    let mut fixture = Fixture::from_fixture("generic-transcripts.pir");
    for root in [json!(["binding", "a"]), json!(["binding", ["b", "c"]])] {
        for value in [false, true] {
            for session in ["test", "1.bad_"] {
                compare(&fixture, root.clone(), value, 3, true, session);
            }
        }
    }
    for budget in 0..3 {
        compare(&fixture, json!(["binding"]), true, budget, true, "test");
    }
    compare(&fixture, json!(["binding"]), true, 3, false, "test");

    // Reject invalid labels during original-source formation. The runtime's
    // installed alphabet is stricter than arbitrary nonempty UTF-8 strings.
    let original: Json = serde_json::from_slice(&fixture.source).unwrap();
    for definition in 0..2 {
        for label in ["bad/path", "with space", "é", "a\nb"] {
            let mut bad = original.clone();
            bad[1][definition][6][0][4][0] = json!(label);
            let path = fixture.directory.path().join("source.json");
            std::fs::write(&path, serde_json::to_vec(&bad).unwrap()).unwrap();
            let compiled = Command::new(&fixture.compiler)
                .arg("protocol-compile")
                .arg(&path)
                .output()
                .unwrap();
            assert!(!compiled.status.success());
            assert!(
                String::from_utf8_lossy(&compiled.stderr).contains("interactive-transcript-origin")
            );
            let (success, result) = fixture.reference_as(&json!([]), None);
            assert!(!success);
            assert!(result.to_string().contains("kernel-attributes"));
        }
    }
    fixture.set_source(&original);

    let mut source: Json = serde_json::from_slice(&fixture.source).unwrap();
    let child = source[3][3][0].clone();
    let mut root = child.clone();
    root[1] = json!("Repeated");
    root[5] = json!([["P", "transcript:merlin3.bls12-381.fr64be/1"]]);
    root[6] = json!([["child", "Round", []]]);
    root[7] = json!([
        [
            "loop",
            "rounds",
            ["constant", "2"],
            [["t", "state"]],
            ["value", "allowed"],
            [
                [
                    "call",
                    "child_step",
                    "child",
                    ["t", "value", "allowed"],
                    ["a", "b", "next"]
                ],
                ["yield", ["next"]]
            ],
            ["last"]
        ],
        ["return", ["last"]]
    ]);
    source[3][3] = json!([child, root]);
    source[3][4] = json!([
        ["instance", "child_instance", "Round", [], [], [["P", "P"]]],
        [
            "instance",
            "concrete",
            "Repeated",
            [],
            [["child", "child_instance"]],
            [["P", "P"]]
        ]
    ]);
    fixture.set_source(&source);
    compare(&fixture, json!(["binding"]), true, 6, true, "test");
    compare(&fixture, json!(["binding"]), true, 4, true, "test");
}

#[test]
fn transcript_absorbs_canonical_field_and_table_payloads() {
    let table = |cells: &[u64]| {
        Value::table(
            &cells.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap()
    };
    for (kind, values) in [
        (
            "field",
            [
                Value::Field(Scalar::from(23)),
                Value::Field(Scalar::from(24)),
            ],
        ),
        ("table", [table(&[0, 1, 4, 9]), table(&[0, 1, 4, 10])]),
    ] {
        // The fixture observes a bool; each case turns it into one that observes
        // this kind. Every string below is text the fixture actually contains,
        // so a replacement that stops matching is a source that stops compiling
        // rather than one that quietly keeps observing a bool.
        let generic = written(kind, "F");
        let concrete = written(kind, "\"bls12-381.fr\"");
        let source = include_str!("../../../../tests/fixtures/generic-transcripts.pir")
            .replace(
                "Observe<T: domain Transcript, E: domain Codec>",
                "Observe<T: domain Transcript, F: domain Field, E: domain Codec>",
            )
            .replace("value: bool", &format!("value: {generic}"))
            .replace("Encodes.bool(E)", &format!("Encodes.{kind}(E, F)"))
            .replace(
                "transcript::observe::bool::<T, E>",
                &format!("transcript::observe::{kind}::<T, F, E>"),
            )
            .replace("ObserveBool", "ObserveValue")
            .replace("boolean,\n      P,\n      V", "payload,\n      P,\n      V")
            .replace(
                "E = \"zkcv.bool/1\"",
                &format!("F = bls12-381.fr, E = \"zkcv.{kind}.bls12-381.fr/1\""),
            )
            .replace(
                &format!("P value: {generic}"),
                &format!("P value: {concrete}"),
            );
        let fixture = Fixture::from_text(&source);
        for budget in [1, 3] {
            compare_value(
                &fixture,
                json!(["binding", kind]),
                values.clone(),
                budget,
                true,
                "test",
            );
        }
    }
}
