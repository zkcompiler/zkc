//! Portable joint and proof consumers with no native dependency or native Value.
#[path = "support/host.rs"]
mod support;
use serde_json::json;
use support::{BOOL, BYTES, Fault, Host, TestValue, Unmeasured};
use zkc_runtime::{
    host::{
        joint::*,
        proof::{self, ArtifactFailure, Transport},
        wire::*,
    },
    interpreter::Runner,
    vm::*,
};

fn program() -> Program {
    Program::decode(
        &serde_json::to_vec(&json!([
            "zkc.program/0",
            [],
            [],
            [
                [
                    "participant",
                    "p",
                    "root",
                    "P",
                    [["x", BOOL]],
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
                    [BOOL],
                    [
                        ["receive", "message", "s", "P", "x", BOOL],
                        ["return", ["x"]]
                    ],
                    []
                ]
            ],
            [["entry", "main", [["P", "p"], ["V", "v"]]]]
        ]))
        .unwrap(),
    )
    .unwrap()
}
fn bundle() -> Bundle {
    let candidate = String::from_utf8(program().bytes().to_vec()).unwrap();
    Bundle::admit(&serde_json::to_vec(&json!({
        "format":"zkc.run/0", "candidate":candidate, "entry":"main", "roles":["P","V"],
        "steps":[{"role":0,"instruction":0,"anchor":0}, {"role":1,"instruction":0,"anchor":0},
                 {"role":0,"instruction":1,"anchor":null}, {"role":1,"instruction":1,"anchor":null}]
    })).unwrap(), &Host::default(), BundleLimits::default()).unwrap()
}
fn run_limits() -> RunLimits {
    RunLimits {
        values: ValueBudget {
            live_bytes: 64,
            total_bytes: 1024,
        },
        ..RunLimits::default()
    }
}
fn ledger() -> ExecutionLedger {
    ExecutionLedger::new(
        ValueBudget {
            live_bytes: 1024,
            total_bytes: 65536,
        },
        WorkBudget::default(),
    )
}
fn inputs<B: Backend<Value = TestValue>>(producer: B, validator: B) -> Vec<RoleInput<B>> {
    vec![
        RoleInput {
            role: "P".into(),
            backend: producer,
            values: vec![TestValue::Bool(true)],
        },
        RoleInput {
            role: "V".into(),
            backend: validator,
            values: vec![],
        },
    ]
}
fn runner<B: Backend<Value = TestValue>>(
    role: &str,
    backend: B,
    ledger: Option<ExecutionLedger>,
) -> Runner<B> {
    Runner::new_for_role_with_ledger(
        &program(),
        "main",
        role,
        "session",
        backend,
        if role == "P" {
            vec![TestValue::Bool(true)]
        } else {
            vec![]
        },
        run_limits().values,
        WorkBudget::default(),
        ledger,
    )
    .unwrap_or_else(|_| panic!("runner"))
}
fn format() -> Transport {
    Transport::Messages(ProofFormat::Native)
}
fn proof_bytes() -> Vec<u8> {
    let report = proof::produce(
        &mut runner("P", Host::default(), None),
        &[7; 32],
        format(),
        MAX_PROOF_BYTES,
        None,
    );
    report.outcome.unwrap().proof
}

#[test]
fn independent_values_complete_joint_and_proof_and_preserve_wire() {
    let ledger = ledger();
    let report = run_with_ledger(
        &bundle(),
        "session",
        inputs(Host::default(), Host::default()),
        run_limits(),
        &mut NoHooks,
        Some(ledger.clone()),
    )
    .unwrap();
    assert_eq!(report.outcome, Outcome::Completed);
    assert_eq!(report.roles[1].outputs, [TestValue::Bool(true)]);
    assert_eq!(
        (
            report.wire.sends,
            report.wire.receives,
            report.wire.sent_bytes
        ),
        (1, 1, 7)
    );
    assert!(
        report
            .backends
            .iter()
            .all(|(_, b)| b.frames.is_empty() && b.leaves == [FrameExit::Returned])
    );
    let before = ledger.snapshot();
    assert!(before.live_reserved_bytes > 0);
    drop(report);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    assert_eq!(
        ledger.snapshot().total_value_bytes,
        before.total_value_bytes
    );

    let mut producer = runner("P", Host::default(), Some(ledger.clone()));
    let produced = proof::produce(
        &mut producer,
        &[7; 32],
        format(),
        MAX_PROOF_BYTES,
        Some(ledger.clone()),
    );
    assert_eq!((produced.messages, produced.bytes), (1, 55));
    let produced = produced.outcome.unwrap();
    let mut expected = b"ZKCPRF00".to_vec();
    expected.extend([7; 32]);
    expected.extend(7u64.to_le_bytes());
    expected.extend(b"ZKCV\0\x05\x01");
    assert_eq!(produced.proof, expected);
    let validated = proof::validate(
        &mut runner("V", Host::default(), None),
        &produced.proof,
        &[7; 32],
        format(),
        0,
        None,
    );
    assert_eq!(validated.outcome.unwrap(), [TestValue::Bool(true)]);
    assert_eq!((validated.messages, validated.bytes), (1, 55));
    drop(producer);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 55);
    let (_, _, guards) = produced.into_parts();
    assert_eq!(ledger.snapshot().live_reserved_bytes, 55);
    drop(guards);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}

#[test]
fn actual_role_wire_profiles_refuse_before_entering_any_runner() {
    let bundle = bundle();
    for restricted in [0, 1] {
        let mut inputs = inputs(Host::default(), Host::default());
        inputs[restricted].backend.wire_disabled = true;
        let ledger = ledger();
        let error = run_with_ledger(
            &bundle,
            "session",
            inputs,
            run_limits(),
            &mut NoHooks,
            Some(ledger.clone()),
        )
        .err()
        .expect("actual backend must admit its role's messages");
        assert_eq!(error.failure.kind, FailureKind::Setup);
        assert_eq!(error.failure.detail.text, "role-wire-type");
        assert_eq!(error.inputs[0].values, [TestValue::Bool(true)]);
        assert!(error.inputs[1].values.is_empty());
        assert!(
            error
                .inputs
                .iter()
                .all(|input| input.backend.frames.is_empty()
                    && input.backend.leaves.is_empty()
                    && input.backend.encodes.get() == 0
                    && input.backend.decodes.get() == 0)
        );
        assert_eq!(ledger.snapshot().total_value_bytes, 0);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    }
}

struct Change(&'static [u8]);
impl Hooks<Host> for Change {
    fn transfer(&mut self, _: Exchange<'_>, _: &[u8], _: usize) -> Result<Option<Vec<u8>>, String> {
        Ok(Some(self.0.to_vec()))
    }
}
#[test]
fn invalid_measurement_and_decode_are_accepted_stops_while_host_failures_preserve_handoff() {
    for shared in [false, true] {
        for fault in [
            Fault::None,
            Fault::DecodeInvalid,
            Fault::MeasureLimit,
            Fault::MeasureBackend,
            Fault::DecodeLimit,
            Fault::DecodeBackend,
            Fault::DecodeWrongType,
        ] {
            let validator = Host {
                fault,
                cleanup_failure: true,
                ..Host::default()
            };
            let bytes: &'static [u8] = if matches!(fault, Fault::None) {
                b"bad"
            } else {
                b"ZKCV\0\x05\x01"
            };
            let report = run_with_ledger(
                &bundle(),
                "session",
                inputs(Host::default(), validator),
                run_limits(),
                &mut Change(bytes),
                shared.then(ledger),
            )
            .unwrap();
            assert_eq!(report.wire.sends, 1);
            assert!(report.backends.iter().all(|(_, b)| b.frames.is_empty()));
            if matches!(fault, Fault::None | Fault::DecodeInvalid) {
                assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 1 });
                assert!(report.pending.is_none());
                assert_eq!(report.wire.receives, 1);
                assert_eq!(
                    report.reached[1].receive_completion,
                    Some(ReceiveCompletion::Stopped)
                );
                let State::Stopped(stop) = &report.roles[1].before else {
                    panic!("stop")
                };
                assert!(matches!(stop.cause, StopCause::Decode(_)));
                assert_eq!(stop.cleanup_errors[0].text, "cleanup");
            } else {
                let Outcome::DriverFailed(failure) = &report.outcome else {
                    panic!("Host failure")
                };
                assert_eq!(
                    failure.kind,
                    match fault {
                        Fault::MeasureLimit | Fault::DecodeLimit => FailureKind::Limit,
                        Fault::DecodeWrongType => FailureKind::Contract,
                        _ => FailureKind::Codec,
                    }
                );
                assert!(report.pending.is_some());
                assert_eq!(report.wire.receives, 0);
                assert!(matches!(
                    report.roles[1].before,
                    State::Pending {
                        kind: CutKind::Receive,
                        ..
                    }
                ));
                assert_eq!(report.reached[1].receive_completion, None);
            }
        }
    }
}
#[test]
fn proof_failure_categories_keep_consumed_prefix_and_cleanup() {
    let bytes = proof_bytes();
    for shared in [false, true] {
        for fault in [
            Fault::None,
            Fault::DecodeInvalid,
            Fault::MeasureLimit,
            Fault::MeasureBackend,
            Fault::DecodeLimit,
            Fault::DecodeBackend,
            Fault::DecodeWrongType,
        ] {
            let mut bytes = bytes.clone();
            if matches!(fault, Fault::None) {
                bytes[54] = 2;
            }
            let mut validator = runner(
                "V",
                Host {
                    fault,
                    cleanup_failure: true,
                    ..Host::default()
                },
                None,
            );
            let report = proof::validate(
                &mut validator,
                &bytes,
                &[7; 32],
                format(),
                0,
                shared.then(ledger),
            );
            assert_eq!((report.messages, report.bytes), (1, 55));
            match (fault, &report.outcome) {
                (Fault::None | Fault::DecodeInvalid, Err(ArtifactFailure::Stopped(stop))) => {
                    assert!(matches!(stop.kind, StopKind::Decode(_)));
                    assert_eq!(stop.cleanup_errors[0].code, "cleanup");
                    assert!(report.cancelled.is_none());
                }
                (
                    Fault::MeasureLimit | Fault::DecodeLimit,
                    Err(ArtifactFailure::Wire(WireError::Limit)),
                ) => (),
                (
                    Fault::MeasureBackend | Fault::DecodeBackend,
                    Err(ArtifactFailure::Wire(WireError::Backend(_))),
                ) => (),
                (Fault::DecodeWrongType, Err(ArtifactFailure::Runtime(RuntimeError::Payload))) => {}
                _ => panic!("wrong failure: {:?}", report.outcome),
            }
            assert!(validator.backend().frames.is_empty());
            if !matches!(fault, Fault::None | Fault::DecodeInvalid) {
                let stop = report.cancelled.as_ref().unwrap();
                assert_eq!(stop.kind, StopKind::Cancelled);
                assert_eq!(stop.cleanup_errors[0].code, "cleanup");
            }
        }
    }
}
#[test]
fn missing_measurement_refuses_both_drivers_before_decode_even_without_shared_capacity() {
    for shared in [false, true] {
        let report = run_with_ledger(
            &bundle(),
            "session",
            inputs(Unmeasured::default(), Unmeasured::default()),
            run_limits(),
            &mut NoHooks,
            shared.then(ledger),
        )
        .unwrap();
        assert!(matches!(
            report.outcome,
            Outcome::DriverFailed(Failure {
                kind: FailureKind::Limit,
                ..
            })
        ));
        assert_eq!(report.wire.receives, 0);
        assert!(report.pending.is_some());
        assert_eq!(report.backends[1].1.0.decodes.get(), 0);
        let mut validator = runner("V", Unmeasured::default(), None);
        let report = proof::validate(
            &mut validator,
            &proof_bytes(),
            &[7; 32],
            format(),
            0,
            shared.then(ledger),
        );
        assert!(matches!(
            report.outcome,
            Err(ArtifactFailure::Wire(WireError::Limit))
        ));
        assert_eq!(validator.backend().0.decodes.get(), 0);
        assert!(report.cancelled.is_some());
        assert!(matches!(
            Unmeasured::default().raw_decoding_bound(&PhysicalType::parse(BYTES).unwrap(), b""),
            Err(WireError::Limit)
        ));
    }
}

struct Cancel;
impl Hooks<Host> for Cancel {
    fn cancel_before(&mut self, index: usize, _: &Step, _: &[PathElement]) -> Option<String> {
        (index == 1).then(|| "host".into())
    }
}
#[test]
fn cancellation_and_encoding_failure_preserve_exact_committed_prefix() {
    let report = run(
        &bundle(),
        "session",
        inputs(Host::default(), Host::default()),
        run_limits(),
        &mut Cancel,
    )
    .unwrap();
    assert!(matches!(report.outcome, Outcome::HostCancelled(_)));
    assert_eq!(report.reached.len(), 1);
    assert_eq!(report.wire.sends, 1);
    assert!(report.pending.is_some());
    assert!(matches!(
        report.roles[1].before,
        State::Unpolled {
            kind: Some(CutKind::Receive),
            ..
        }
    ));
    assert!(
        report
            .backends
            .iter()
            .all(|(_, b)| b.leaves == [FrameExit::Cancelled])
    );
    for fault in [Fault::EncodeLimit, Fault::EncodeBackend] {
        let report = run(
            &bundle(),
            "session",
            inputs(
                Host {
                    fault,
                    ..Host::default()
                },
                Host::default(),
            ),
            run_limits(),
            &mut NoHooks,
        )
        .unwrap();
        assert!(matches!(report.outcome, Outcome::DriverFailed(_)));
        assert_eq!(report.wire.sends, 0);
        assert!(report.pending.is_none());
        let mut producer = runner(
            "P",
            Host {
                fault,
                ..Host::default()
            },
            None,
        );
        let report = proof::produce(&mut producer, &[7; 32], format(), MAX_PROOF_BYTES, None);
        assert!(matches!(report.outcome, Err(ArtifactFailure::Wire(_))));
        assert_eq!((report.messages, report.bytes), (0, 40));
        assert!(report.cancelled.is_some());
        // Proof production commits take_send before encoding, unlike joint handoff.
        assert_eq!(producer.usage().instructions, 1);
    }
}
#[test]
fn acceptance_requires_selected_boolean_and_complete_framing() {
    let mut bytes = proof_bytes();
    bytes[54] = 0;
    let report = proof::validate(
        &mut runner("V", Host::default(), None),
        &bytes,
        &[7; 32],
        format(),
        0,
        None,
    );
    assert!(matches!(report.outcome, Err(ArtifactFailure::Rejected)));
    assert!(report.cancelled.is_none());
    bytes.push(0);
    let report = proof::validate(
        &mut runner("V", Host::default(), None),
        &bytes,
        &[7; 32],
        format(),
        0,
        None,
    );
    assert!(matches!(
        report.outcome,
        Err(ArtifactFailure::Format(FormatError::Trailing))
    ));
    let report = proof::validate(
        &mut runner("V", Host::default(), None),
        &proof_bytes(),
        &[7; 32],
        format(),
        1,
        None,
    );
    assert!(matches!(
        report.outcome,
        Err(ArtifactFailure::AcceptanceType)
    ));
    let report = proof::validate(
        &mut runner("V", Host::default(), None),
        &proof_bytes(),
        &[8; 32],
        format(),
        0,
        None,
    );
    assert!(matches!(
        report.outcome,
        Err(ArtifactFailure::Format(FormatError::Header))
    ));
    assert_eq!((report.messages, report.bytes), (0, 40));
}
#[test]
fn raw_record_borrows_payload_and_respects_publication_limit() {
    let value = TestValue::Bytes(std::sync::Arc::from(*b"abc"));
    let backend = Host::default();
    let borrowed = backend.raw_bytes(&value).unwrap();
    let TestValue::Bytes(ref bytes) = value else {
        unreachable!()
    };
    assert_eq!(borrowed.as_ptr(), bytes.as_ptr());
    let program = Program::decode(
        &serde_json::to_vec(&json!([
            "zkc.program/0",
            [],
            [],
            [[
                "participant",
                "p",
                "root",
                "P",
                [["proof", BYTES]],
                [BYTES],
                [["return", ["proof"]]],
                []
            ]],
            [["entry", "main", [["P", "p"]]]]
        ]))
        .unwrap(),
    )
    .unwrap();
    for limit in [2, 3] {
        let mut runner = Runner::new(
            &program,
            "main",
            "P",
            "session",
            Host::default(),
            vec![value.clone()],
        )
        .unwrap_or_else(|_| panic!("raw"));
        let report = proof::produce(&mut runner, &[1; 32], Transport::Record, limit, None);
        if limit == 3 {
            assert_eq!(report.outcome.unwrap().proof, b"abc");
            assert_eq!((report.messages, report.bytes), (1, 3));
        } else {
            assert!(matches!(
                report.outcome,
                Err(ArtifactFailure::Format(FormatError::Limit))
            ));
            assert_eq!((report.messages, report.bytes), (0, 0));
        }
        assert_eq!(runner.backend().encodes.get(), 0);
        assert_eq!(runner.backend().raw_encodes.get(), 1);
    }
}

#[test]
fn shared_decode_capacity_refuses_before_materialization_and_keeps_consumed_work() {
    let ledger = ExecutionLedger::new(
        ValueBudget {
            live_bytes: 135,
            total_bytes: 65536,
        },
        WorkBudget::default(),
    );
    let report = run_with_ledger(
        &bundle(),
        "session",
        inputs(Host::default(), Host::default()),
        run_limits(),
        &mut NoHooks,
        Some(ledger.clone()),
    )
    .unwrap();
    assert!(matches!(
        report.outcome,
        Outcome::DriverFailed(Failure {
            kind: FailureKind::Limit,
            ..
        })
    ));
    assert_eq!((report.wire.sends, report.wire.receives), (1, 0));
    assert!(report.pending.is_some());
    assert_eq!(report.backends[1].1.decodes.get(), 0);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 7);
    let cumulative = ledger.snapshot().total_value_bytes;
    drop(report);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    assert_eq!(ledger.snapshot().total_value_bytes, cumulative);

    let ledger = ExecutionLedger::new(
        ValueBudget {
            live_bytes: 64,
            total_bytes: 65536,
        },
        WorkBudget::default(),
    );
    let mut validator = runner("V", Host::default(), Some(ledger.clone()));
    let report = proof::validate(
        &mut validator,
        &proof_bytes(),
        &[7; 32],
        format(),
        0,
        Some(ledger.clone()),
    );
    assert!(matches!(
        report.outcome,
        Err(ArtifactFailure::Format(FormatError::Limit))
    ));
    assert_eq!((report.messages, report.bytes), (1, 55));
    assert!(report.cancelled.is_some());
    assert_eq!(validator.backend().decodes.get(), 0);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    assert!(ledger.snapshot().total_value_bytes > 0);
}

#[test]
fn raw_message_proof_uses_borrowed_bytes_and_measured_receive_without_header() {
    let program = Program::decode(
        &serde_json::to_vec(&json!([
            "zkc.program/0",
            [],
            [],
            [
                [
                    "participant",
                    "p",
                    "root",
                    "P",
                    [["x", BYTES]],
                    [],
                    [["send", "message", "s", "V", "x"], ["return", []]],
                    []
                ],
                [
                    "participant",
                    "v",
                    "root",
                    "V",
                    [["ok", BOOL]],
                    [BOOL],
                    [
                        ["receive", "message", "s", "P", "x", BYTES],
                        ["return", ["ok"]]
                    ],
                    []
                ]
            ],
            [["entry", "main", [["P", "p"], ["V", "v"]]]]
        ]))
        .unwrap(),
    )
    .unwrap();
    for payload in [b"".as_slice(), b"ZKCPRF00arbitrary", b"\xff\x00"] {
        let mut producer = Runner::new(
            &program,
            "main",
            "P",
            "session",
            Host::default(),
            vec![TestValue::Bytes(payload.into())],
        )
        .unwrap_or_else(|_| panic!("producer"));
        let produced = proof::produce(
            &mut producer,
            &[1; 32],
            Transport::Messages(ProofFormat::RawBytes),
            payload.len(),
            None,
        );
        assert_eq!((produced.messages, produced.bytes), (1, payload.len()));
        let produced = produced.outcome.unwrap();
        assert_eq!(produced.proof, payload);
        assert_eq!(producer.backend().encodes.get(), 0);
        assert_eq!(producer.backend().raw_encodes.get(), 1);
        let mut validator = Runner::new(
            &program,
            "main",
            "V",
            "session",
            Host::default(),
            vec![TestValue::Bool(true)],
        )
        .unwrap_or_else(|_| panic!("validator"));
        let validated = proof::validate(
            &mut validator,
            &produced.proof,
            &[2; 32],
            Transport::Messages(ProofFormat::RawBytes),
            0,
            None,
        );
        assert_eq!(validated.outcome.unwrap(), [TestValue::Bool(true)]);
        assert_eq!((validated.messages, validated.bytes), (1, payload.len()));
        let mut unmeasured = Runner::new(
            &program,
            "main",
            "V",
            "session",
            Unmeasured::default(),
            vec![TestValue::Bool(true)],
        )
        .unwrap_or_else(|_| panic!("validator"));
        let refused = proof::validate(
            &mut unmeasured,
            &produced.proof,
            &[2; 32],
            Transport::Messages(ProofFormat::RawBytes),
            0,
            None,
        );
        assert!(matches!(
            refused.outcome,
            Err(ArtifactFailure::Wire(WireError::Limit))
        ));
        assert!(refused.cancelled.is_some());
    }
}
