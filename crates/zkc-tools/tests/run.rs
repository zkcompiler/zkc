//! Driver policy controls. Generated mathematical clients live in native_joint.
use serde_json::{Value as Json, json};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, NativeWireError, Policy, Value};
use zkc_runtime::interactive::Value as RuntimeValue;
use zkc_runtime::interactive::{
    Action, Backend, BackendError, CutKind, DecodeReason, Frame, FrameExit, Invocation,
    PhysicalType, Runner, Stop, StopKind, ValueBudget,
};
use zkc_tools::run::*;
const BOOL: &str = "bool@native.bool/1";
#[derive(Clone, Copy, Debug, Default)]
enum Decode {
    #[default]
    Normal,
    Limit,
    Backend,
    WrongType,
}
struct Host {
    codec: NativeBackend,
    enters: usize,
    leaves: usize,
    enter_failure: bool,
    leave_failure: bool,
    encode_failure: bool,
    bad_width: bool,
    validate_failure: bool,
    decode: Decode,
}
impl Default for Host {
    fn default() -> Self {
        Self {
            codec: NativeBackend::new(
                Policy::default(),
                EntryPolicy::new(Domain::new("Alice", "session", "main", None), None),
                Default::default(),
            )
            .unwrap(),
            enters: 0,
            leaves: 0,
            enter_failure: false,
            leave_failure: false,
            encode_failure: false,
            bad_width: false,
            validate_failure: false,
            decode: Decode::Normal,
        }
    }
}
impl Backend for Host {
    type Value = Value;
    fn supports_boolean_literals(&self) -> bool {
        true
    }
    fn validate_value(&self, _: &Value) -> Result<(), BackendError> {
        if self.validate_failure {
            Err(BackendError::new("validation"))
        } else {
            Ok(())
        }
    }
    fn enter_frame(&mut self, _: &Frame, _: &[Value]) -> Result<(), BackendError> {
        if self.enter_failure {
            return Err(BackendError::new("entry"));
        }
        self.enters += 1;
        Ok(())
    }
    fn leave_frame(&mut self, _: &Frame, _: FrameExit, _: &[Value]) -> Result<(), BackendError> {
        self.leaves += 1;
        if self.leave_failure {
            Err(BackendError::new("cleanup"))
        } else {
            Ok(())
        }
    }
    fn apply(&mut self, _: &Invocation<'_>, _: &[Value]) -> Result<Vec<Value>, BackendError> {
        panic!("identity has no kernel")
    }
}
impl WireBackend for Host {
    fn encode_native(&self, value: &Value) -> Result<Vec<u8>, NativeWireError> {
        if self.bad_width {
            return Ok(vec![0; 6]);
        }
        if self.encode_failure {
            Err(NativeWireError::Limit)
        } else {
            self.codec.encode_native_value(value)
        }
    }
    fn decode_native(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<Value, NativeWireError> {
        match self.decode {
            Decode::Normal => self.codec.decode_native_value(ty, bytes),
            Decode::Limit => Err(NativeWireError::Limit),
            Decode::Backend => Err(NativeWireError::Backend(BackendError::new("codec"))),
            Decode::WrongType => Ok(Value::Field(zkc_backends::Scalar::from(1))),
        }
    }
}
fn carrier() -> Json {
    typed_carrier(BOOL)
}
fn typed_carrier(ty: &str) -> Json {
    json!([
        "zkc.program/2",
        [],
        [[
            "function",
            "id",
            [["x", ty]],
            [ty],
            [["return", ["x"]]],
            ["id", []]
        ]],
        [
            [
                "participant",
                "a",
                "root",
                "Alice",
                [["x", ty]],
                [],
                [
                    ["local", "identity", "id", ["x"], ["y"]],
                    ["send", "message", "message", "Bob", "y"],
                    ["return", []]
                ],
                []
            ],
            [
                "participant",
                "b",
                "root",
                "Bob",
                [],
                [ty],
                [
                    ["receive", "message", "message", "Alice", "z", ty],
                    ["return", ["z"]]
                ],
                []
            ]
        ],
        [["entry", "main", [["Alice", "a"], ["Bob", "b"]]]]
    ])
}
fn raw() -> Json {
    message_bundle(BOOL)
}
fn message_bundle(ty: &str) -> Json {
    json!({"format":"zkc.run/1", "candidate":typed_carrier(ty).to_string(), "entry":"main", "roles":["Alice","Bob"],
        "steps":[step(0,0,Some(0)),step(0,1,Some(0)),step(1,0,Some(0)),step(0,2,None),step(1,1,None)]})
}
fn step(role: usize, instruction: usize, anchor: Option<usize>) -> Json {
    json!({"role":role, "instruction":instruction, "anchor":anchor})
}
fn admit(raw: &Json) -> Result<Bundle, BundleError> {
    Bundle::admit(
        raw.to_string().as_bytes(),
        &Host::default(),
        BundleLimits::default(),
    )
}
fn inputs() -> Vec<RoleInput<Host>> {
    vec![
        RoleInput {
            role: "Bob".into(),
            backend: Host::default(),
            values: vec![],
        },
        RoleInput {
            role: "Alice".into(),
            backend: Host::default(),
            values: vec![Value::Bool(false)],
        },
    ]
}
fn execute(
    hooks: &mut impl Hooks<Host>,
    inputs: Vec<RoleInput<Host>>,
    limits: RunLimits,
) -> Report<Host> {
    run(&admit(&raw()).unwrap(), "session", inputs, limits, hooks).unwrap()
}
#[derive(Default)]
struct Controls {
    cancel: Option<usize>,
    hook_error: bool,
    replacement: Option<Vec<u8>>,
    observation_error: bool,
    transfers: usize,
}
impl Hooks<Host> for Controls {
    fn cancel_before(
        &mut self,
        index: usize,
        _: &Step,
        _: &[zkc_runtime::interactive::PathElement],
    ) -> Option<String> {
        (self.cancel == Some(index)).then(|| "host interruption".into())
    }
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        _: &[u8],
        _: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        self.transfers += 1;
        assert_eq!(
            (exchange.sender, exchange.receiver, exchange.site),
            ("Alice", "Bob", "message")
        );
        if self.hook_error {
            Err("hostile wire".into())
        } else {
            Ok(self.replacement.take())
        }
    }
    fn observe(&mut self, _: &str, backend: &Host, _: Phase) -> Result<Option<String>, String> {
        if self.observation_error {
            Err("observation".into())
        } else {
            Ok(Some(format!("{}:{}", backend.enters, backend.leaves)))
        }
    }
}
fn stopped(report: &Report<Host>, role: usize) -> &StopSummary {
    assert_eq!(report.outcome, Outcome::ParticipantStopped { role });
    let State::Stopped(stop) = &report.roles[role].before else {
        panic!("stopped snapshot")
    };
    stop
}
fn failed(report: &Report<Host>, kind: FailureKind) {
    assert!(
        matches!(&report.outcome, Outcome::DriverFailed(f) if f.kind == kind),
        "{:?}",
        report.outcome
    );
}
#[test]
fn completed_false_is_an_output_and_roster_is_source_order() {
    admit(&raw()).unwrap();
    let report = execute(&mut NoHooks, inputs(), RunLimits::default());
    assert_eq!(report.outcome, Outcome::Completed);
    assert_eq!(report.reached.len(), 5);
    assert!(
        report
            .reached
            .iter()
            .all(|r| r.progress == Progress::Completed)
    );
    assert!(matches!(
        report.roles[1].outputs.as_slice(),
        [Value::Bool(false)]
    ));
    assert!(
        report
            .roles
            .iter()
            .all(|r| r.before == State::Returned && !r.cancelled)
    );
    assert_eq!(
        report.wire,
        WireUsage {
            sends: 1,
            receives: 1,
            sent_bytes: 7,
            replacement_bytes: 0
        }
    );
    assert!(report.pending.is_none());
    assert_eq!(
        report
            .backends
            .iter()
            .map(|(r, b)| (r.as_str(), b.enters, b.leaves))
            .collect::<Vec<_>>(),
        [("Alice", 2, 2), ("Bob", 1, 1)]
    );
}
#[test]
fn admission_refuses_coverage_group_and_envelope_mutations() {
    let mut cases = Vec::new();
    let mut x = raw();
    x["steps"].as_array_mut().unwrap().remove(1);
    cases.push(x);
    let mut x = raw();
    x["steps"][1]["instruction"] = json!(0);
    cases.push(x);
    let mut x = raw();
    x["steps"][2]["role"] = json!(0);
    cases.push(x);
    let mut x = raw();
    x["steps"][0]["anchor"] = json!(1);
    cases.push(x);
    let mut x = raw();
    x["steps"][2]["anchor"] = json!(1);
    cases.push(x);
    let mut x = raw();
    x["steps"].as_array_mut().unwrap().swap(3, 4);
    cases.push(x);
    let mut x = raw();
    x["steps"][3]["anchor"] = json!(1);
    cases.push(x);
    let mut x = raw();
    x["roles"] = json!(["Alice", "Alice"]);
    cases.push(x);
    let mut x = raw();
    x["entry"] = json!("absent");
    cases.push(x);
    let mut x = raw();
    let mut c = carrier();
    c[3][1][6][0][2] = json!("other-schema");
    x["candidate"] = json!(c.to_string());
    cases.push(x);
    let mut x = raw();
    x["format"] = json!("invalid.run");
    cases.push(x);
    let mut x = raw();
    let mut c = carrier();
    c[0] = json!("invalid.program");
    x["candidate"] = json!(c.to_string());
    cases.push(x);
    for (index, x) in cases.iter().enumerate() {
        assert!(admit(x).is_err(), "mutation {index}");
    }
}
#[test]
fn outer_decoder_checks_duplicates_unknown_missing_and_bounds() {
    let text = raw().to_string();
    for bad in [
        text.replacen("{", "{\"entry\":\"main\",", 1),
        text.replacen("{", "{\"surprise\":0,", 1),
        text.replace("\"anchor\":null,", ""),
        text.replace("\"role\":0", "\"role\":-1"),
        text.replace("\"role\":0", "\"role\":999999999999999999999999"),
        text.replace("\"role\":0", "\"role\":0.0"),
        format!("{text} true"),
        format!("{}0", "[".repeat(512)),
    ] {
        assert!(
            Bundle::admit(bad.as_bytes(), &Host::default(), BundleLimits::default()).is_err(),
            "{bad}"
        );
    }
    for limits in [
        BundleLimits {
            bytes: 1,
            ..Default::default()
        },
        BundleLimits {
            candidate_bytes: 1,
            ..Default::default()
        },
        BundleLimits {
            roles: 1,
            ..Default::default()
        },
        BundleLimits {
            steps: 4,
            ..Default::default()
        },
        BundleLimits {
            depth: 2,
            ..Default::default()
        },
        BundleLimits {
            nodes: 3,
            ..Default::default()
        },
        BundleLimits {
            string_bytes: 3,
            ..Default::default()
        },
    ] {
        assert_eq!(
            Bundle::admit(text.as_bytes(), &Host::default(), limits).unwrap_err(),
            BundleError::Limit
        );
    }
}
#[test]
fn coherent_cross_role_reordering_remains_supplied_only() {
    let c = json!([
        "zkc.program/2",
        [],
        [[
            "function",
            "id",
            [["x", BOOL]],
            [BOOL],
            [["return", ["x"]]],
            ["id", []]
        ]],
        [
            [
                "participant",
                "a",
                "root",
                "Alice",
                [["x", BOOL]],
                [BOOL],
                [["local", "alice", "id", ["x"], ["y"]], ["return", ["y"]]],
                []
            ],
            [
                "participant",
                "b",
                "root",
                "Bob",
                [["x", BOOL]],
                [BOOL],
                [["local", "bob", "id", ["x"], ["y"]], ["return", ["y"]]],
                []
            ]
        ],
        [["entry", "main", [["Alice", "a"], ["Bob", "b"]]]]
    ]);
    let mut x = raw();
    x["candidate"] = json!(c.to_string());
    for order in [[0, 1], [1, 0]] {
        x["steps"] = json!([
            step(order[0], 0, Some(0)),
            step(order[1], 0, Some(1)),
            step(0, 1, None),
            step(1, 1, None)
        ]);
    }
    x["steps"] = json!([
        step(0, 0, Some(0)),
        step(1, 0, Some(0)),
        step(0, 1, None),
        step(1, 1, None)
    ]);
    assert!(admit(&x).is_err());
    x["steps"] = json!([
        step(0, 0, None),
        step(1, 0, None),
        step(0, 1, None),
        step(1, 1, None)
    ]);
    assert!(admit(&x).is_err());
}
#[test]
fn cancellation_between_halves_keeps_bytes_and_unpolled_receiver() {
    let mut hook = Controls {
        cancel: Some(2),
        ..Default::default()
    };
    let report = execute(&mut hook, inputs(), RunLimits::default());
    assert!(
        matches!(&report.outcome, Outcome::HostCancelled(reason) if reason.text == "host interruption")
    );
    assert_eq!(hook.transfers, 0);
    assert_eq!(report.pending.as_ref().unwrap().bytes, b"ZKCV\x01\x05\0");
    assert_eq!(
        report.roles[0].before,
        State::Unpolled {
            kind: None,
            site: None
        }
    );
    assert_eq!(
        report.roles[1].before,
        State::Unpolled {
            kind: Some(CutKind::Receive),
            site: Some("message".into())
        }
    );
    assert_eq!(
        report.roles[0].observation.value.as_ref().unwrap().text,
        "2:1"
    );
    assert_eq!(
        report.roles[0]
            .after_observation
            .value
            .as_ref()
            .unwrap()
            .text,
        "2:2"
    );
    assert!(report.roles.iter().all(|r| r.cancelled));
}
#[test]
fn malformed_bytes_stop_receive_and_consume_slot_with_prior_effects() {
    for (bytes, reason) in [
        (vec![], DecodeReason::Length),
        (b"ZKCV\x01\x05\x02".to_vec(), DecodeReason::Boolean),
    ] {
        let report = execute(
            &mut Controls {
                replacement: Some(bytes),
                ..Default::default()
            },
            inputs(),
            RunLimits::default(),
        );
        assert_eq!(stopped(&report, 1).cause, StopCause::Decode(reason));
        assert_eq!(stopped(&report, 1).site.as_deref(), Some("message"));
        assert_eq!(report.wire.sends, 1);
        assert_eq!(report.wire.receives, 1);
        assert!(report.pending.is_none());
        assert_eq!(
            report.roles[0].before,
            State::Unpolled {
                kind: None,
                site: None
            }
        );
        assert!(report.roles[0].cancelled);
    }
}
#[test]
fn typed_message_change_is_distinct_from_bad_encoding() {
    let report = execute(
        &mut Controls {
            replacement: Some(b"ZKCV\x01\x05\x01".to_vec()),
            ..Default::default()
        },
        inputs(),
        RunLimits::default(),
    );
    assert_eq!(report.outcome, Outcome::Completed);
    assert!(matches!(
        report.roles[1].outputs.as_slice(),
        [Value::Bool(true)]
    ));
    assert_eq!(report.wire.replacement_bytes, 7);
}
#[test]
fn codec_and_hook_failures_preserve_the_exact_handoff_state() {
    let mut i = inputs();
    i[1].backend.encode_failure = true;
    let report = execute(&mut NoHooks, i, RunLimits::default());
    failed(&report, FailureKind::Limit);
    assert!(matches!(
        report.roles[0].before,
        State::Pending {
            kind: CutKind::Send,
            ..
        }
    ));
    assert!(report.pending.is_none());
    assert_eq!(report.wire.sends, 0);
    for (decode, kind) in [
        (Decode::Limit, FailureKind::Limit),
        (Decode::Backend, FailureKind::Codec),
        (Decode::WrongType, FailureKind::Contract),
    ] {
        let mut i = inputs();
        i[0].backend.decode = decode;
        let report = execute(&mut NoHooks, i, RunLimits::default());
        failed(&report, kind);
        assert!(matches!(
            report.roles[1].before,
            State::Pending {
                kind: CutKind::Receive,
                ..
            }
        ));
        assert_eq!(report.pending.as_ref().unwrap().bytes, b"ZKCV\x01\x05\0");
        assert_eq!(report.wire.receives, 0);
    }
    for (hook, kind) in [
        (
            Controls {
                hook_error: true,
                ..Default::default()
            },
            FailureKind::Hook,
        ),
        (
            Controls {
                replacement: Some(vec![0; 4097]),
                ..Default::default()
            },
            FailureKind::Limit,
        ),
    ] {
        let report = execute(&mut { hook }, inputs(), RunLimits::default());
        failed(&report, kind);
        assert!(matches!(
            report.roles[1].before,
            State::Unpolled {
                kind: Some(CutKind::Receive),
                ..
            }
        ));
        assert_eq!(report.pending.as_ref().unwrap().bytes, b"ZKCV\x01\x05\0");
    }
}
#[test]
fn accepted_validation_failure_clears_slot_and_cleanup_cannot_replace_cause() {
    let mut i = inputs();
    i[0].backend.validate_failure = true;
    i[0].backend.leave_failure = true;
    let report = execute(
        &mut Controls {
            observation_error: true,
            ..Default::default()
        },
        i,
        RunLimits::default(),
    );
    assert!(matches!(stopped(&report,1).cause,StopCause::Backend(ref e) if e.text=="validation"));
    assert_eq!(stopped(&report, 1).cleanup_errors[0].text, "cleanup");
    assert!(report.pending.is_none());
    assert!(report.roles.iter().all(|r| r.observation.error.is_some()));
}
#[test]
fn preflight_reserves_both_dispatches_before_exposing_send() {
    let report = execute(
        &mut NoHooks,
        inputs(),
        RunLimits {
            steps: 2,
            ..Default::default()
        },
    );
    failed(&report, FailureKind::Limit);
    assert_eq!(report.reached.len(), 1);
    assert_eq!(report.wire.sends, 0);
    assert!(matches!(
        report.roles[0].before,
        State::Unpolled {
            kind: Some(CutKind::Send),
            ..
        }
    ));
    let report = execute(
        &mut NoHooks,
        inputs(),
        RunLimits {
            steps: 0,
            ..Default::default()
        },
    );
    assert!(report.reached.is_empty());
    assert!(matches!(
        report.roles[0].before,
        State::Unpolled {
            kind: Some(CutKind::Local),
            ..
        }
    ));
}
#[test]
fn setup_failure_recovers_every_backend_and_cancels_entered_peer() {
    let mut i = inputs();
    i[0].backend.enter_failure = true;
    let report = execute(&mut NoHooks, i, RunLimits::default());
    failed(&report, FailureKind::Setup);
    assert_eq!(report.roles[1].before, State::NotStarted);
    assert!(report.roles[0].cancelled);
    assert_eq!(report.backends.len(), 2);
    assert_eq!(report.backends[0].1.leaves, 1);
    assert_eq!(report.backends[1].1.enters, 0);
    let mut i = inputs();
    i[0].role = "Alice".into();
    let error = run(
        &admit(&raw()).unwrap(),
        "session",
        i,
        RunLimits::default(),
        &mut NoHooks,
    )
    .err()
    .unwrap();
    assert!(error.inputs.iter().all(|i| i.backend.enters == 0));
}
#[test]
fn receive_retention_limit_is_an_accepted_stopping_completion() {
    let mut c = carrier();
    c[3][0][6] = json!([["send", "message", "message", "Bob", "x"], ["return", []]]);
    c[3][1][4] = json!([["unused", BOOL]]);
    let mut x = raw();
    x["candidate"] = json!(c.to_string());
    x["steps"] = json!([
        step(0, 0, Some(0)),
        step(1, 0, Some(0)),
        step(0, 1, None),
        step(1, 1, None)
    ]);
    let bundle = admit(&x).unwrap();
    let mut i = inputs();
    i[0].values = vec![Value::Bool(true)];
    let report = run(
        &bundle,
        "session",
        i,
        RunLimits {
            values: ValueBudget {
                live_bytes: zkc_runtime::interactive::Value::retained_bytes(&Value::Bool(false)),
                total_bytes: 10000,
            },
            ..Default::default()
        },
        &mut NoHooks,
    )
    .unwrap();
    assert_eq!(stopped(&report, 1).cause, StopCause::Limit);
    assert!(report.pending.is_none());
    assert_eq!(report.wire.receives, 1);
}

#[test]
fn malformed_data_inputs_refuse_before_any_entry() {
    for missing in [false, true] {
        let mut i = inputs();
        if missing {
            i[1].values.clear();
        } else {
            i[0].values.push(Value::Bool(true));
        }
        let error = run(
            &admit(&raw()).unwrap(),
            "session",
            i,
            RunLimits::default(),
            &mut NoHooks,
        )
        .err()
        .unwrap();
        assert_eq!(error.failure.kind, FailureKind::Setup);
        assert!(error.inputs.iter().all(|i| i.backend.enters == 0));
    }
    let mut i = inputs();
    i[1].values = vec![Value::Field(zkc_backends::Scalar::from(1))];
    let error = run(
        &admit(&raw()).unwrap(),
        "session",
        i,
        RunLimits::default(),
        &mut NoHooks,
    )
    .err()
    .unwrap();
    assert!(error.inputs.iter().all(|i| i.backend.enters == 0));
}
#[test]
fn final_return_failure_and_cumulative_wire_limit_preserve_prefix() {
    let mut i = inputs();
    i[0].backend.leave_failure = true;
    let report = execute(&mut NoHooks, i, RunLimits::default());
    assert!(matches!(&stopped(&report,1).cause,StopCause::Backend(e) if e.text=="cleanup"));
    assert_eq!(report.roles[0].before, State::Returned);
    assert!(!report.roles[0].cancelled);
    assert_eq!(report.wire.receives, 1);
    assert!(report.pending.is_none());
    let report = execute(
        &mut Controls {
            replacement: Some(b"ZKCV\x01\x05\x01".to_vec()),
            ..Default::default()
        },
        inputs(),
        RunLimits {
            total_wire_bytes: 13,
            ..Default::default()
        },
    );
    failed(&report, FailureKind::Limit);
    assert!(matches!(report.roles[1].before, State::Unpolled { .. }));
    assert_eq!(report.pending.as_ref().unwrap().bytes, b"ZKCV\x01\x05\0");
    assert_eq!(report.wire.replacement_bytes, 0);
}
#[test]
fn supplied_roster_order_controls_return_and_cleanup_order() {
    struct Order(Vec<String>);
    impl Hooks<Host> for Order {
        fn observe(
            &mut self,
            role: &str,
            _: &Host,
            phase: Phase,
        ) -> Result<Option<String>, String> {
            self.0.push(format!("{phase:?}:{role}"));
            Ok(None)
        }
    }
    let mut x = raw();
    x["roles"] = json!(["Bob", "Alice"]);
    x["steps"] = json!([
        step(1, 0, Some(0)),
        step(1, 1, Some(0)),
        step(0, 0, Some(0)),
        step(0, 1, None),
        step(1, 2, None)
    ]);
    let mut hook = Order(vec![]);
    let report = run(
        &admit(&x).unwrap(),
        "session",
        inputs(),
        RunLimits::default(),
        &mut hook,
    )
    .unwrap();
    assert_eq!(report.outcome, Outcome::Completed);
    assert_eq!(report.roles[0].role, "Bob");
    assert_eq!(
        hook.0,
        [
            "BeforeCancellation:Bob",
            "BeforeCancellation:Alice",
            "AfterCancellation:Bob",
            "AfterCancellation:Alice"
        ]
    );
}

#[test]
fn wrong_encoder_width_refuses_before_commit_and_unknown_observations_stay_unknown() {
    let mut i = inputs();
    i[1].backend.bad_width = true;
    let report = execute(&mut NoHooks, i, RunLimits::default());
    failed(&report, FailureKind::Codec);
    assert_eq!(report.wire.sends, 0);
    assert!(report.pending.is_none());
    assert!(matches!(
        report.roles[0].before,
        State::Pending {
            kind: CutKind::Send,
            ..
        }
    ));
    struct Unknown;
    impl Hooks<Host> for Unknown {
        fn observe(&mut self, _: &str, _: &Host, _: Phase) -> Result<Option<String>, String> {
            Ok(Some("state: unknown".into()))
        }
    }
    let report = execute(&mut Unknown, inputs(), RunLimits::default());
    assert_eq!(report.outcome, Outcome::Completed);
    assert!(
        report.roles.iter().all(
            |r| r.observation.value.as_ref().unwrap().text == "state: unknown"
                && r.after_observation.value.as_ref().unwrap().text == "state: unknown"
        )
    );
    assert_eq!(
        report.reached[2].receive_completion,
        Some(zkc_runtime::interactive::ReceiveCompletion::Delivered)
    );
    let report = execute(
        &mut Controls {
            replacement: Some(vec![]),
            ..Default::default()
        },
        inputs(),
        RunLimits::default(),
    );
    assert_eq!(
        report.reached[2].receive_completion,
        Some(zkc_runtime::interactive::ReceiveCompletion::Stopped)
    );
}

fn loop_bundle() -> Json {
    let index = Value::Index(0).physical_type().spelling();
    let participants: Vec<_> = [("a", "Alice"), ("b", "Bob")]
        .into_iter()
        .map(|(symbol, role)| {
            json!([
                "participant",
                symbol,
                "root",
                role,
                [["n", index]],
                [],
                [
                    [
                        "loop",
                        "rounds",
                        ["value", "n", "8", "i"],
                        [],
                        [],
                        [["yield", []]],
                        []
                    ],
                    ["return", []]
                ],
                []
            ])
        })
        .collect();
    let candidate = json!([
        "zkc.program/2",
        [],
        [],
        participants,
        [["entry", "main", [["Alice", "a"], ["Bob", "b"]]]]
    ]);
    json!({"format": "zkc.run/1", "candidate": candidate.to_string(), "entry":"main",
        "roles":["Alice","Bob"], "steps":[
            {"loop":[step(0,0,Some(0)),step(1,0,Some(0))], "body":[],
             "yield":[step(0,1,None),step(1,1,None)]},
            step(0,2,None),step(1,2,None)]})
}
#[test]
fn loop_roster_cannot_be_split_to_bypass_count_agreement() {
    let raw = loop_bundle();
    let bundle = admit(&raw).unwrap();
    let inputs = [("Alice", 3), ("Bob", 5)]
        .into_iter()
        .map(|(role, count)| RoleInput {
            role: role.into(),
            backend: Host::default(),
            values: vec![Value::Index(count)],
        })
        .collect();
    let report = run(
        &bundle,
        "counts",
        inputs,
        RunLimits::default(),
        &mut NoHooks,
    )
    .unwrap();
    failed(&report, FailureKind::Contract);
    assert!(matches!(&report.outcome, Outcome::DriverFailed(f)
        if f.detail.text == "loop-count-disagreement" && f.detail.omitted_bytes == 0));
    assert_eq!(
        report
            .reached
            .iter()
            .map(|r| r.loop_count)
            .collect::<Vec<_>>(),
        [Some(3), Some(5)]
    );
    assert!(report.reached.iter().all(|r| !r.loop_started));
    assert!(
        report
            .backends
            .iter()
            .all(|(_, b)| b.enters == 1 && b.leaves == 1)
    );
    let mut split = raw.clone();
    split["steps"] = json!([
        {"loop":[step(0,0,Some(0))], "body":[], "yield":[step(0,1,None)]},
        {"loop":[step(1,0,Some(1))], "body":[], "yield":[step(1,1,None)]},
        step(0,2,None),step(1,2,None)]);
    assert_eq!(admit(&split).unwrap_err(), BundleError::Coverage);
}
#[test]
fn loop_reports_distinguish_zero_trips_and_bound_failure() {
    for (a, b, expected, started) in [
        (0, 0, Outcome::Completed, true),
        (3, 9, Outcome::ParticipantStopped { role: 1 }, false),
    ] {
        let bundle = admit(&loop_bundle()).unwrap();
        let inputs = [("Alice", a), ("Bob", b)]
            .into_iter()
            .map(|(role, count)| RoleInput {
                role: role.into(),
                backend: Host::default(),
                values: vec![Value::Index(count)],
            })
            .collect();
        let report = run(
            &bundle,
            "counts",
            inputs,
            RunLimits::default(),
            &mut NoHooks,
        )
        .unwrap();
        assert_eq!(report.outcome, expected);
        assert_eq!(report.reached[0].loop_started, started);
        assert_eq!(report.reached[1].loop_started, started);
        assert!(
            report
                .backends
                .iter()
                .all(|(_, b)| b.enters == 1 && b.leaves == 1)
        );
    }
}
#[test]
fn every_nested_schedule_field_has_closed_bounded_object_grammar() {
    let mut raw = loop_bundle();
    raw["steps"][0]["loop"][0] = json!([0, 0, 0]);
    assert_eq!(admit(&raw).unwrap_err(), BundleError::Json);
    raw = loop_bundle();
    raw["steps"][0]["loop"][0]["unknown"] = json!(0);
    assert_eq!(admit(&raw).unwrap_err(), BundleError::Json);
    let limits = BundleLimits {
        steps: 3,
        ..BundleLimits::default()
    };
    assert_eq!(
        Bundle::admit(
            loop_bundle().to_string().as_bytes(),
            &Host::default(),
            limits
        )
        .unwrap_err(),
        BundleError::Limit
    );
}

#[test]
fn structured_participant_admission_checks_every_nested_body() {
    for body in [
        json!([["stop", "bad", "reject"]]),
        json!([["incomplete", "bad"]]),
        json!([["call", "bad", "a", ["n"], []], ["yield", []]]),
    ] {
        let mut raw = loop_bundle();
        let mut candidate: Json = serde_json::from_str(raw["candidate"].as_str().unwrap()).unwrap();
        candidate[3][0][6][0][5] = body;
        raw["candidate"] = json!(candidate.to_string());
        assert!(matches!(admit(&raw), Err(BundleError::Candidate(_))));
    }
    let mut raw = loop_bundle();
    let mut candidate: Json = serde_json::from_str(raw["candidate"].as_str().unwrap()).unwrap();
    candidate[3][0][6][0][2] = json!("1");
    raw["candidate"] = json!(candidate.to_string());
    assert!(matches!(admit(&raw), Err(BundleError::Candidate(_))));
}
#[test]
fn structured_runner_poll_cannot_cross_control_cuts() {
    let raw = loop_bundle();
    let admitted = zkc_runtime::interactive::admit_supplied(
        raw["candidate"].as_str().unwrap().as_bytes(),
        &Host::default(),
    )
    .unwrap();
    for at_yield in [false, true] {
        let mut runner = Runner::new(
            &admitted,
            "main",
            "Alice",
            "cut",
            Host::default(),
            vec![Value::Index(1)],
        )
        .unwrap_or_else(|_| panic!("load structured runner"));
        if at_yield {
            let origin = runner.root_origin().clone();
            assert_eq!(runner.loop_count(&origin, "rounds").unwrap(), Some(1));
            runner.enter_loop(&origin, "rounds", 1).unwrap();
        }
        let before = runner.usage();
        let stale = zkc_runtime::interactive::Cut {
            origin: runner.root_origin().clone(),
            role: "Alice".into(),
            site: "stale".into(),
            kind: CutKind::Local,
        };
        assert_eq!(
            runner.execute_local(&stale),
            Err(zkc_runtime::interactive::RuntimeError::WrongAction)
        );
        let packet = zkc_runtime::interactive::Packet {
            envelope: zkc_runtime::interactive::Envelope {
                origin: stale.origin,
                site: "stale".into(),
                schema: "bool".into(),
                sender: "Bob".into(),
                receiver: "Alice".into(),
            },
            ty: Value::Bool(false).physical_type(),
            payload: Value::Bool(false),
        };
        assert_eq!(
            runner.check_delivery(&packet),
            Err(zkc_runtime::interactive::RuntimeError::WrongAction)
        );
        assert_eq!(runner.usage(), before);
        if at_yield {
            assert!(matches!(
                runner.inspect_program().unwrap(),
                zkc_runtime::interactive::ProgramState::Yield
            ));
        } else {
            assert!(matches!(
                runner.inspect_program().unwrap(),
                zkc_runtime::interactive::ProgramState::Unpolled {
                    kind: None,
                    site: Some("rounds")
                }
            ));
        }
        assert!(
            matches!(runner.poll(), Action::Stopped(Stop { kind: StopKind::Backend(ref error), .. }) if error.code=="program-control-cut")
        );
        assert_eq!(runner.usage().instructions, before.instructions);
        assert_eq!(runner.usage().live_values, 0);
    }
}

#[test]
fn entering_native_loop_preserves_count_failure_as_stopped_outcome() {
    let raw = loop_bundle();
    let admitted = zkc_runtime::interactive::admit_supplied(
        raw["candidate"].as_str().unwrap().as_bytes(),
        &Host::default(),
    )
    .unwrap();
    let mut runner = Runner::new(
        &admitted,
        "main",
        "Alice",
        "bound",
        Host::default(),
        vec![Value::Index(9)],
    )
    .unwrap_or_else(|_| panic!("load structured runner"));
    let origin = runner.root_origin().clone();
    runner.enter_loop(&origin, "rounds", 9).unwrap();
    assert!(
        matches!(runner.poll(), Action::Stopped(Stop {kind: StopKind::Backend(ref error), ..}) if error.code == "loop-count-bound")
    );
    assert_eq!(runner.usage().live_values, 0);
}

#[test]
fn unknown_formats_and_wrong_participant_shapes_refuse() {
    admit(&raw()).unwrap();
    for format in ["invalid.run", ""] {
        let mut raw = raw();
        raw["format"] = json!(format);
        assert_eq!(admit(&raw).unwrap_err(), BundleError::Format, "{format}");
    }
    for format in ["invalid.program", ""] {
        let mut candidate = carrier();
        candidate[0] = json!(format);
        let mut raw = raw();
        raw["candidate"] = json!(candidate.to_string());
        assert!(
            matches!(admit(&raw), Err(BundleError::Candidate(_))),
            "{format}"
        );
        let error = zkc_runtime::interactive::admit_supplied(
            candidate.to_string().as_bytes(),
            &Host::default(),
        )
        .err()
        .unwrap();
        assert_eq!(
            error.code,
            zkc_runtime::interactive::ErrorCode::Record,
            "{format}"
        );
        assert_eq!(
            error.detail, "unknown participant module format",
            "{format}"
        );
    }
    let mut candidate = carrier();
    for role in candidate[3].as_array_mut().unwrap() {
        role.as_array_mut().unwrap().pop();
    }
    let mut raw = raw();
    raw["candidate"] = json!(candidate.to_string());
    assert!(matches!(admit(&raw), Err(BundleError::Candidate(_))));
}

#[test]
fn proof_policies_check_messages_and_loops_independently_of_program_format() {
    use zkc_runtime::interactive::{NativeProofEntry, admit_supplied};
    let admit =
        |program: &Json| admit_supplied(program.to_string().as_bytes(), &Host::default()).unwrap();
    NativeProofEntry::new(admit(&carrier()), "main", "Alice", "Bob", 0, None, &[]).unwrap();

    let vector = Value::Vector(vec![].into()).physical_type().spelling();
    let mut program = typed_carrier(&vector);
    program[3][1][4] = json!([["accepted", BOOL]]);
    program[3][1][5] = json!([BOOL]);
    program[3][1][6][1] = json!(["return", ["accepted"]]);
    NativeProofEntry::new(admit(&program), "main", "Alice", "Bob", 0, None, &[]).unwrap();
    let mut unsupported = program.clone();
    let polynomial = Value::Polynomial(vec![].into()).physical_type().spelling();
    unsupported[2][0][2][0][1] = json!(&polynomial);
    unsupported[2][0][3][0] = json!(&polynomial);
    unsupported[3][0][4][0][1] = json!(&polynomial);
    unsupported[3][1][6][0][5] = json!(&polynomial);
    assert_eq!(
        NativeProofEntry::new(admit(&unsupported), "main", "Alice", "Bob", 0, None, &[])
            .unwrap_err()
            .to_string(),
        "native-proof-wire-type"
    );

    let mut program = carrier();
    for role in program[3].as_array_mut().unwrap() {
        role[4]
            .as_array_mut()
            .unwrap()
            .push(json!(["n", "index@native.index/1"]));
        role[6].as_array_mut().unwrap().insert(
            0,
            json!([
                "loop",
                "rounds",
                ["value", "n", "2", "i"],
                [],
                [],
                [["yield", []]],
                []
            ]),
        );
    }
    NativeProofEntry::new(admit(&program), "main", "Alice", "Bob", 0, None, &[]).unwrap();
}

#[test]
fn structured_bundles_transfer_dynamic_and_nested_messages() {
    use zkc_backends::{GroupPoint, Scalar, Sequence, Variant};
    use zkc_runtime::interactive::LogicalType;
    use zkc_test_support::variants::logical;
    let optional = logical("Optional", json!([["none", []], ["some", ["indices"]]]));
    let record = logical(
        "Packet",
        json!([["record", [optional, "vector:bls12-381.fr"]]]),
    );
    let variant = |ty: &str, tag, values| {
        let ty = LogicalType::parse(ty).unwrap();
        Value::Variant(Variant::new(ty.variant_descriptor().unwrap().clone(), tag, values).unwrap())
    };
    let codec = Host::default();
    let mut values =
        vec![Value::table(&[Scalar::from(1), Scalar::from(2)], &Policy::default()).unwrap()];
    values.push(Value::Bn254Field(zkc_backends::Bn254Scalar::from(9)));
    values.extend([
        Value::Bn254Vector(vec![zkc_backends::Bn254Scalar::from(9); 3].into()),
        Value::Bn254G2Vector(vec![zkc_backends::Bn254G2::generator(); 2].into()),
        Value::Bn254Gt(zkc_backends::Bn254Gt::generator()),
        Value::bn254_matrix(
            2,
            3,
            &[(1, 2, zkc_backends::Bn254Scalar::from(7))],
            &Policy::default(),
        )
        .unwrap(),
        Value::OracleRoot(zkc_backends::oracle::Domain::Extension, [7; 32]),
        Value::OraclePath(
            zkc_backends::oracle::Domain::Extension,
            vec![[11; 32]; 2].into(),
        ),
    ]);
    values.push(Value::Sequence(
        Sequence::new(
            LogicalType::parse("field:bn254.fr").unwrap(),
            vec![Value::Bn254Field(zkc_backends::Bn254Scalar::from(11))],
            &Policy::default(),
        )
        .unwrap(),
    ));
    for n in [0, 2] {
        let fields = Value::Vector(vec![Scalar::from(9); n].into());
        values.extend([
            fields.clone(),
            Value::Groups(vec![GroupPoint::generator(); n].into()),
            Value::Indices(vec![u64::MAX; n].into()),
        ]);
        for tag in 0..2 {
            let payload = if tag == 0 {
                vec![]
            } else {
                vec![Value::Indices(vec![u64::MAX; n].into())]
            };
            values.push(variant(
                &record,
                0,
                vec![variant(&optional, tag, payload), fields.clone()],
            ));
        }
    }
    let records: Vec<_> = values
        .iter()
        .filter(|v| matches!(v, Value::Variant(_)))
        .cloned()
        .collect();
    for elements in [vec![], records] {
        values.push(Value::Sequence(
            Sequence::new(
                LogicalType::parse(&record).unwrap(),
                elements,
                &Policy::default(),
            )
            .unwrap(),
        ));
    }
    values.push(Value::Sequence(
        Sequence::new(
            LogicalType::parse("matrix:bls12-381.fr").unwrap(),
            vec![
                Value::matrix(0, 3, &[], &Policy::default()).unwrap(),
                Value::matrix(2, 0, &[], &Policy::default()).unwrap(),
                Value::matrix(1, 2, &[(0, 1, Scalar::from(9))], &Policy::default()).unwrap(),
            ],
            &Policy::default(),
        )
        .unwrap(),
    ));
    for value in values {
        let ty = value.physical_type().spelling();
        let mut inputs = inputs();
        inputs[1].values = vec![value.clone()];
        let report = run(
            &admit(&message_bundle(&ty)).unwrap(),
            "session",
            inputs,
            RunLimits::default(),
            &mut NoHooks,
        )
        .unwrap();
        assert_eq!(report.outcome, Outcome::Completed, "{ty}");
        assert_eq!(
            codec.encode_native(&report.roles[1].outputs[0]).unwrap(),
            codec.encode_native(&value).unwrap()
        );
        assert!(report.pending.is_none());
        assert_eq!(report.wire.receives, 1);
        assert!(report.backends.iter().all(|(_, b)| b.enters == b.leaves));
    }
    // A serializable logical value does not automatically authorize its wire grammar.
    assert_eq!(
        admit(&message_bundle(
            "polynomial:bn254.fr@arkworks.bn254-fr-polynomial/1"
        ))
        .unwrap_err(),
        BundleError::WireType
    );
}

#[test]
fn structured_wire_failures_preserve_handoff_and_cleanup() {
    let value = Value::Vector(vec![zkc_backends::Scalar::from(9); 2].into());
    let codec = Host::default();
    let wire = codec.encode_native(&value).unwrap();
    let bundle = admit(&message_bundle(&value.physical_type().spelling())).unwrap();
    for scenario in [
        "short",
        "send-limit",
        "replace-limit",
        "total-limit",
        "replace",
    ] {
        let mut inputs = inputs();
        inputs[1].values = vec![value.clone()];
        let mut hooks = Controls::default();
        let mut limits = RunLimits::default();
        match scenario {
            "short" => hooks.replacement = Some(wire[..wire.len() - 1].to_vec()),
            "send-limit" => limits.wire_bytes = wire.len() - 1,
            "replace-limit" => {
                limits.wire_bytes = wire.len();
                hooks.replacement = Some(vec![0; wire.len() + 1]);
            }
            "total-limit" => {
                limits.total_wire_bytes = 2 * wire.len() - 1;
                hooks.replacement = Some(wire.clone());
            }
            "replace" => {
                limits.total_wire_bytes = 2 * wire.len();
                hooks.replacement = Some(
                    codec
                        .encode_native(&Value::Vector(
                            vec![zkc_backends::Scalar::from(7); 2].into(),
                        ))
                        .unwrap(),
                );
            }
            _ => unreachable!(),
        }
        let replacement = hooks.replacement.clone();
        let report = run(&bundle, "session", inputs, limits, &mut hooks).unwrap();
        assert!(
            report.backends.iter().all(|(_, b)| b.enters == b.leaves),
            "{scenario}"
        );
        match scenario {
            "short" => {
                assert_eq!(
                    stopped(&report, 1).cause,
                    StopCause::Decode(DecodeReason::Length)
                );
                assert_eq!(report.wire.receives, 1);
                assert!(report.pending.is_none());
            }
            "replace" => {
                assert_eq!(report.outcome, Outcome::Completed);
                assert_eq!(
                    codec.encode_native(&report.roles[1].outputs[0]).unwrap(),
                    replacement.unwrap()
                );
                assert_eq!(
                    report.wire.sent_bytes + report.wire.replacement_bytes,
                    2 * wire.len()
                );
                assert!(report.pending.is_none());
            }
            _ => {
                failed(&report, FailureKind::Limit);
                assert_eq!(report.wire.receives, 0);
                assert_eq!(report.wire.replacement_bytes, 0);
                if scenario == "send-limit" {
                    assert_eq!(report.wire.sends, 0);
                    assert!(report.pending.is_none());
                } else {
                    assert_eq!(report.wire.sends, 1);
                    assert_eq!(report.pending.unwrap().bytes, wire);
                }
            }
        }
    }
}

#[test]
fn excessive_sequence_count_preserves_pending_frame_and_cleanup() {
    let value = Value::Sequence(
        zkc_backends::Sequence::new(
            zkc_runtime::interactive::LogicalType::parse("index").unwrap(),
            vec![Value::Index(7)],
            &Policy::default(),
        )
        .unwrap(),
    );
    let wire = Host::default().encode_native(&value).unwrap();
    let mut replacement = wire.clone();
    replacement[6..10].fill(255);
    let mut hooks = Controls {
        replacement: Some(replacement.clone()),
        ..Controls::default()
    };
    let mut inputs = inputs();
    inputs[1].values = vec![value.clone()];
    let report = run(
        &admit(&message_bundle(&value.physical_type().spelling())).unwrap(),
        "session",
        inputs,
        RunLimits::default(),
        &mut hooks,
    )
    .unwrap();
    failed(&report, FailureKind::Limit);
    assert_eq!(report.wire.sends, 1);
    assert_eq!(report.wire.receives, 0);
    assert_eq!(report.wire.replacement_bytes, replacement.len());
    assert_eq!(report.pending.unwrap().bytes, replacement);
    assert!(report.backends.iter().all(|(_, b)| b.enters == b.leaves));
}

#[test]
fn structured_bundles_retain_fixed_width_send_checks() {
    let mut inputs = inputs();
    inputs[1].backend.bad_width = true;
    let report = run(
        &admit(&message_bundle(BOOL)).unwrap(),
        "session",
        inputs,
        RunLimits::default(),
        &mut NoHooks,
    )
    .unwrap();
    failed(&report, FailureKind::Codec);
    assert_eq!(report.wire.sends, 0);
    assert!(report.pending.is_none());
    assert!(report.backends.iter().all(|(_, b)| b.enters == b.leaves));
}

#[test]
fn exact_pin_precedes_parsing_and_limit_requests_are_not_clamped() {
    use sha2::{Digest, Sha256};
    let bytes = raw().to_string();
    let pin: [u8; 32] = Sha256::digest(bytes.as_bytes()).into();
    assert!(
        Bundle::admit_pinned(
            bytes.as_bytes(),
            &pin,
            &Host::default(),
            BundleLimits::default()
        )
        .is_ok()
    );
    assert!(matches!(
        Bundle::admit_pinned(b"not json", &pin, &Host::default(), BundleLimits::default()),
        Err(BundleError::Identity)
    ));
    assert!(matches!(
        Bundle::admit_pinned(
            format!("{bytes}\n").as_bytes(),
            &pin,
            &Host::default(),
            BundleLimits::default()
        ),
        Err(BundleError::Identity)
    ));
    let mut limits = RunLimits {
        steps: usize::MAX,
        ..RunLimits::default()
    };
    limits.work.instructions = 0;
    limits.values.live_bytes = usize::MAX;
    limits.values.total_bytes = usize::MAX;
    let rejected = run(&admit(&raw()).unwrap(), "s", inputs(), limits, &mut NoHooks)
        .err()
        .unwrap();
    assert_eq!(rejected.failure.kind, FailureKind::Limit);
    assert_eq!(rejected.inputs.len(), 2);
    assert!(
        rejected
            .inputs
            .iter()
            .all(|r| r.backend.enters == 0 && r.backend.leaves == 0)
    );
    assert_eq!(rejected.inputs[0].role, "Bob");
    assert_eq!(rejected.inputs[1].values.len(), 1);
    let mut limits = RunLimits::default();
    limits.work.instructions = 0;
    let report = execute(&mut NoHooks, inputs(), limits);
    assert_eq!(report.limits.work.instructions, 0);
    assert!(matches!(
        report.outcome,
        Outcome::ParticipantStopped { role: 0 }
    ));
    assert_eq!(report.roles[0].usage.unwrap().instructions, 0);
    let report = execute(
        &mut NoHooks,
        inputs(),
        RunLimits {
            values: ValueBudget {
                live_bytes: 0,
                total_bytes: 0,
            },
            ..RunLimits::default()
        },
    );
    assert!(report.roles[0].usage.is_some());
    assert_eq!(report.roles[0].usage.unwrap().instructions, 0);
}

#[test]
fn pure_partition_needs_distinct_anchors_and_changes_finite_cost() {
    let mut candidate = carrier();
    let body = candidate[3][0][6].as_array_mut().unwrap();
    body.insert(1, json!(["local", "second", "id", ["y"], ["z"]]));
    body[2][4] = json!("z");
    let mut split = raw();
    split["candidate"] = json!(candidate.to_string());
    split["steps"] = json!([
        step(0, 0, Some(0)),
        step(0, 1, Some(0)),
        step(0, 2, Some(0)),
        step(1, 0, Some(0)),
        step(0, 3, None),
        step(1, 1, None)
    ]);
    assert!(
        admit(&split).is_err(),
        "an exchange group admits at most one local prefix"
    );
    for i in 1..4 {
        split["steps"][i]["anchor"] = json!(1);
    }
    let bundle = admit(&split).unwrap();
    let report = run(
        &bundle,
        "session",
        inputs(),
        RunLimits::default(),
        &mut NoHooks,
    )
    .unwrap();
    let original = execute(&mut NoHooks, inputs(), RunLimits::default());
    assert_eq!(report.outcome, Outcome::Completed);
    assert!(matches!(
        report.roles[1].outputs.as_slice(),
        [Value::Bool(false)]
    ));
    assert_eq!(report.wire, original.wire);
    assert!(
        report.roles[0].usage.unwrap().instructions > original.roles[0].usage.unwrap().instructions
    );
    assert_eq!(
        report.backends[0].1.enters,
        original.backends[0].1.enters + 1
    );
    assert_eq!(report.reached.len(), original.reached.len() + 1);
    let limits = RunLimits {
        steps: 5,
        ..RunLimits::default()
    };
    assert_eq!(
        execute(&mut NoHooks, inputs(), limits).outcome,
        Outcome::Completed
    );
    let report = run(&bundle, "session", inputs(), limits, &mut NoHooks).unwrap();
    assert_ne!(report.outcome, Outcome::Completed);
}
