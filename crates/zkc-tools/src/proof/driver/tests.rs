use super::*;
use serde_json::json;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Value};
use zkc_runtime::interactive::{Runner, admit_supplied};

fn fresh(role: &str) -> Runner<NativeBackend> {
    let boolean = "bool@native.bool/1";
    let bytes = serde_json::to_vec(&json!([
        "zkc.program",
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
    let admitted = admit_supplied(&bytes, &backend).unwrap();
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
    produce_admitted(runner, &[7; 32], |backend, value| {
        backend
            .encode_native_value(value)
            .map_err(ArtifactFailure::NativeWire)
    })
}
#[test]
fn native_proof_framing_and_decision() {
    let proof = produce(&mut fresh("P")).outcome.unwrap().proof;
    assert!(
        validate_native(&mut fresh("V"), &proof, &[7; 32], 0)
            .outcome
            .is_ok()
    );
    assert!(matches!(
        validate_native(&mut fresh("V"), &proof, &[8; 32], 0).outcome,
        Err(ArtifactFailure::Format(_))
    ));
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(
        validate_native(&mut fresh("V"), &trailing, &[7; 32], 0)
            .outcome
            .is_err()
    );
    assert!(
        validate_native(&mut fresh("V"), &proof[..proof.len() - 1], &[7; 32], 0)
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
    let report = validate_native(&mut stopped, &[], &[7; 32], 0);
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
