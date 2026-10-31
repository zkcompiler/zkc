use serde_json::json;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Value};
use zkc_format::proof::{MAX_PROOF_BYTES, ProofFormat};
use zkc_runtime::host::proof::*;
use zkc_runtime::host::wire::*;
use zkc_runtime::interpreter::Runner;

fn fresh(role: &str) -> Runner<CpuBackend> {
    fresh_with_policy(role, Policy::default())
}
fn fresh_with_policy(role: &str, policy: Policy) -> Runner<CpuBackend> {
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
    let backend = CpuBackend::new(
        policy,
        EntryPolicy::new(Domain::new(role, "session", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let admitted = zkc_runtime::vm::Program::decode(&bytes, zkc_cpu::cpu_contracts())
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
fn produce(runner: &mut Runner<CpuBackend>) -> ArtifactReport<Produced<Value>> {
    zkc_runtime::host::proof::produce(
        runner,
        &[7; 32],
        Transport::Messages(ProofFormat::Native),
        MAX_PROOF_BYTES,
        None,
    )
}
#[test]
fn native_proof_framing_and_decision() {
    let proof = produce(&mut fresh("P")).outcome.unwrap().proof;
    assert!(
        validate(
            &mut fresh("V"),
            &proof,
            &[7; 32],
            Transport::Messages(ProofFormat::Native),
            0,
            None
        )
        .outcome
        .is_ok()
    );
    assert!(matches!(
        validate(
            &mut fresh("V"),
            &proof,
            &[8; 32],
            Transport::Messages(ProofFormat::Native),
            0,
            None
        )
        .outcome,
        Err(ArtifactFailure::Format(_))
    ));
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(
        validate(
            &mut fresh("V"),
            &trailing,
            &[7; 32],
            Transport::Messages(ProofFormat::Native),
            0,
            None
        )
        .outcome
        .is_err()
    );
    assert!(
        validate(
            &mut fresh("V"),
            &proof[..proof.len() - 1],
            &[7; 32],
            Transport::Messages(ProofFormat::Native),
            0,
            None
        )
        .outcome
        .is_err()
    );
}

#[test]
fn fixed_frame_length_and_header_precede_native_capacity_in_proof_receive() {
    for shared in [false, true] {
        for (payload, reason) in [
            (
                b"ZKCV\0\x05\x01\0".as_slice(),
                Some(zkc_runtime::vm::DecodeReason::Length),
            ),
            (
                b"bad!\0\x05\x01".as_slice(),
                Some(zkc_runtime::vm::DecodeReason::Header),
            ),
            (b"ZKCV\0\x05\x01".as_slice(), None),
        ] {
            let mut writer = ProofWriter::new(ProofFormat::Native, &[7; 32]);
            writer.message(payload).unwrap();
            let proof = writer.finish().unwrap();
            let policy = Policy {
                max_wire_bytes: 6,
                ..Policy::default()
            };
            let mut validator = fresh_with_policy("V", policy);
            let report = validate(
                &mut validator,
                &proof,
                &[7; 32],
                Transport::Messages(ProofFormat::Native),
                0,
                shared.then(|| {
                    zkc_runtime::vm::ExecutionLedger::new(Default::default(), Default::default())
                }),
            );
            assert_eq!((report.messages, report.bytes), (1, proof.len()));
            match reason {
                Some(reason) => {
                    assert!(
                        matches!(&report.outcome, Err(ArtifactFailure::Stopped(stop))
                        if stop.kind == zkc_runtime::vm::StopKind::Decode(reason))
                    );
                    assert!(report.cancelled.is_none());
                }
                None => {
                    assert!(matches!(
                        report.outcome,
                        Err(ArtifactFailure::Wire(WireError::Limit))
                    ));
                    assert!(report.cancelled.is_some());
                }
            }
        }
    }
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
    let report = validate(
        &mut stopped,
        &[],
        &[7; 32],
        Transport::Messages(ProofFormat::Native),
        0,
        None,
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
    fn record(stopped: bool) -> Runner<CpuBackend> {
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
        let backend = CpuBackend::new(
            Policy::default(),
            EntryPolicy::new(Domain::new("P", "session", "main", None), None),
            Default::default(),
        )
        .unwrap();
        let admitted = zkc_runtime::vm::Program::decode(&program, zkc_cpu::cpu_contracts())
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
            vec![Value::Bytes([1, 2, 3].into())],
        )
        .unwrap_or_else(|_| panic!("record entry"))
    }
    let success =
        zkc_runtime::host::proof::produce(&mut record(false), &[7; 32], Transport::Record, 3, None);
    assert_eq!(success.outcome.unwrap().proof, [1, 2, 3]);
    assert_eq!((success.messages, success.bytes), (1, 3));
    assert!(success.cancelled.is_none());
    let limited =
        zkc_runtime::host::proof::produce(&mut record(false), &[7; 32], Transport::Record, 2, None);
    assert!(matches!(limited.outcome, Err(ArtifactFailure::Format(_))));
    assert_eq!((limited.messages, limited.bytes), (0, 0));
    let failed =
        zkc_runtime::host::proof::produce(&mut record(true), &[7; 32], Transport::Record, 3, None);
    assert!(matches!(failed.outcome, Err(ArtifactFailure::Stopped(_))));
    assert_eq!((failed.messages, failed.bytes), (0, 0));
}
