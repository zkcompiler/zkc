use super::*;
use serde_json::json;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Value};
use zkc_runtime::interpreter::Runner;

fn fresh(role: &str) -> Runner<NativeBackend> {
    let boolean = "bool@native.bool/0";
    let bytes = serde_json::to_vec(&json!([
        "zkc.program/0",
        [],
        [],
        [
            [
                "participant",
                "p",
                "root",
                "P",
                [["x", boolean]],
                [],
                [["send", "message", "s", "V", "x"], ["return", []]],
                []
            ],
            [
                "participant",
                "v",
                "root",
                "V",
                [],
                [boolean],
                [
                    ["receive", "message", "s", "P", "x", boolean],
                    ["return", ["x"]]
                ],
                []
            ]
        ],
        [["entry", "main", [["P", "p"], ["V", "v"]]]]
    ]))
    .unwrap();
    let backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "session", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let admitted = zkc_runtime::vm::Program::decode(&bytes)
        .and_then(|program| {
            program.check_installation(&backend)?;
            Ok(program)
        })
        .unwrap();
    Runner::new(
        &admitted,
        "main",
        role,
        "session",
        backend,
        if role == "P" {
            vec![Value::Bool(true)]
        } else {
            vec![]
        },
    )
    .unwrap_or_else(|_| panic!("entry"))
}
fn produce(runner: &mut Runner<NativeBackend>) -> ArtifactReport<Produced<Value>> {
    produce_native(
        runner,
        &[7; 32],
        Transport::Messages(ProofFormat::Native),
        super::super::MAX_PROOF_BYTES,
    )
}
#[test]
fn native_proof_framing_and_decision() {
    let proof = produce(&mut fresh("P")).outcome.unwrap().proof;
    assert!(
        validate_native(
            &mut fresh("V"),
            &proof,
            &[7; 32],
            Transport::Messages(ProofFormat::Native),
            0
        )
        .outcome
        .is_ok()
    );
    assert!(matches!(
        validate_native(
            &mut fresh("V"),
            &proof,
            &[8; 32],
            Transport::Messages(ProofFormat::Native),
            0
        )
        .outcome,
        Err(ArtifactFailure::Format(_))
    ));
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(
        validate_native(
            &mut fresh("V"),
            &trailing,
            &[7; 32],
            Transport::Messages(ProofFormat::Native),
            0
        )
        .outcome
        .is_err()
    );
    assert!(
        validate_native(
            &mut fresh("V"),
            &proof[..proof.len() - 1],
            &[7; 32],
            Transport::Messages(ProofFormat::Native),
            0
        )
        .outcome
        .is_err()
    );
}
#[test]
fn proof_drivers_refuse_reuse_and_preserve_terminal_stops() {
    let mut producer = fresh("P");
    assert!(produce(&mut producer).outcome.is_ok());
    assert!(matches!(
        produce(&mut producer).outcome,
        Err(ArtifactFailure::StartedRunner)
    ));
    let mut stopped = fresh("V");
    stopped.cancel();
    let previous = stopped.stop().unwrap().clone();
    let report = validate_native(
        &mut stopped,
        &[],
        &[7; 32],
        Transport::Messages(ProofFormat::Native),
        0,
    );
    assert_eq!(report.stop(), Some(&previous));
    assert_eq!(report.bytes, 0);
    let mut started = fresh("P");
    let cut = started.poll().cut().unwrap();
    started.take_send(&cut).unwrap();
    let report = produce(&mut started);
    assert!(matches!(
        report.outcome,
        Err(ArtifactFailure::StartedRunner)
    ));
    assert!(report.cancelled.is_some());
}

#[test]
fn record_publication_is_exact_bounded_and_requires_return() {
    fn record(stopped: bool) -> Runner<NativeBackend> {
        let ty = "bytes@native.bytes/0";
        let body = if stopped {
            json!([["local", "stop", "stop", [], []], ["return", ["proof"]]])
        } else {
            json!([["return", ["proof"]]])
        };
        let program = serde_json::to_vec(&json!([
            "zkc.program/0",
            [],
            [[
                "function",
                "stop",
                [],
                [],
                [["stop", "failed", "reject"]],
                ["stop", []]
            ]],
            [[
                "participant",
                "p",
                "root",
                "P",
                [["proof", ty]],
                [ty],
                body,
                []
            ]],
            [["entry", "main", [["P", "p"]]]]
        ]))
        .unwrap();
        let backend = NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(Domain::new("P", "session", "main", None), None),
            Default::default(),
        )
        .unwrap();
        let admitted = zkc_runtime::vm::Program::decode(&program)
            .and_then(|program| {
                program.check_installation(&backend)?;
                Ok(program)
            })
            .unwrap();
        Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            backend,
            vec![Value::Bytes(std::sync::Arc::from([1, 2, 3]))],
        )
        .unwrap_or_else(|_| panic!("record entry"))
    }
    let success = produce_native(&mut record(false), &[7; 32], Transport::Record, 3);
    assert_eq!(success.outcome.unwrap().proof, [1, 2, 3]);
    assert_eq!((success.messages, success.bytes), (1, 3));
    assert!(success.cancelled.is_none());
    let limited = produce_native(&mut record(false), &[7; 32], Transport::Record, 2);
    assert!(matches!(limited.outcome, Err(ArtifactFailure::Format(_))));
    assert_eq!((limited.messages, limited.bytes), (0, 0));
    let failed = produce_native(&mut record(true), &[7; 32], Transport::Record, 3);
    assert!(matches!(failed.outcome, Err(ArtifactFailure::Stopped(_))));
    assert_eq!((failed.messages, failed.bytes), (0, 0));
}
