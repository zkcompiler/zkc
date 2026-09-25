//! Ownership/state checks use a fixture checker here; the integration suite
//! separately drives actual Lean admission and MLIR-exported candidates.

mod support;
use serde_json::{Value, json};
use std::sync::Arc;
use support::entry;
use zkc_runtime::{
    AdmittedJob, AdmittedProgram, Bindings, Budget, CheckFailure, CheckRequest, Checker, Error,
    Outcome, PhaseEvidence, Stop,
    table::{
        ChallengeProvider, ENDPOINT_PROFILE, Operation, Phase, SmallPrimeKernel, State,
        TableBindings, TableLibrary,
    },
};
struct Exact;
impl Checker for Exact {
    fn check(&self, request: CheckRequest<'_>) -> Result<(), CheckFailure> {
        let source: Value = serde_json::from_slice(request.source).unwrap();
        let plan: Value = serde_json::from_slice(request.candidate).unwrap();
        assert_eq!(source[5], plan[9]);
        Ok(())
    }
}
fn admitted(body: Value, phase: Option<Phase>) -> Arc<AdmittedProgram<Operation>> {
    let context = json!([
        "prover",
        [["x", ["scalar", "f7"], ["private", "prover"], "argument"]],
        ["scalar", "f7"],
        [["table-protocol", "1"]]
    ]);
    let source = json!(["zkc-request", 1, "finite-source-1", context, [], body]);
    let plan = json!([
        "zkc-plan",
        1,
        "finite-source-1",
        [],
        "direct-logical-plan",
        "direct-lowering",
        [
            "equality",
            "logical-outcome-state-events",
            "all-inputs-and-handlers"
        ],
        context,
        [],
        body
    ]);
    AdmittedProgram::admit(
        source.to_string().into_bytes(),
        plan.to_string().into_bytes(),
        phase.map(|p| PhaseEvidence {
            profile: ENDPOINT_PROFILE.into(),
            certificate: br#"["terminal"]"#.to_vec(),
            entry: Some(entry(p)),
        }),
        &TableLibrary,
        &Exact,
    )
    .unwrap_or_else(|e| panic!("{}", e.reason))
}
fn bindings(phase: Phase) -> TableBindings {
    let (state, provider) = State::decode(&json!([0, 0, 0, [], [3, 4]])).unwrap();
    TableBindings::new(SmallPrimeKernel, provider, state)
        .unwrap()
        .with_endpoint("prover".into(), phase)
        .unwrap()
}
fn inputs() -> Value {
    json!([["x", ["scalar", "f7"], 2]])
}
fn execute<P: ChallengeProvider>(
    program: Arc<AdmittedProgram<Operation>>,
    bindings: TableBindings<SmallPrimeKernel, P>,
) -> zkc_runtime::Completed<TableBindings<SmallPrimeKernel, P>> {
    AdmittedJob::bind(program, inputs(), bindings)
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute()
}
#[test]
fn retained_phase_controls_owned_reentry_and_no_evidence_cannot_downgrade() {
    let stopped = admitted(
        json!(["apply", ["send"], [0, 0], ["stop", "abort"]]),
        Some(Phase::Ready),
    );
    let done = execute(stopped.clone(), bindings(Phase::Ready));
    assert!(matches!(done.outcome(), Ok(Outcome::Stopped(Stop::Abort))));
    assert_eq!(done.bindings().endpoint_entry(), Some(entry(Phase::Sent)));
    let state = done.bindings().state_json();
    let (_, bindings) = done.into_parts();
    let failure = AdmittedJob::bind(stopped, inputs(), bindings)
        .err()
        .unwrap();
    assert_eq!(failure.reason, Error("endpoint-entry-mismatch"));
    assert_eq!(failure.bindings.state_json(), state);
    assert_eq!(failure.bindings.events(), &[json!(["sent", 2, 2])]);
    let no_policy = admitted(json!(["return", 0]), None);
    let failure = AdmittedJob::bind(no_policy, inputs(), failure.bindings)
        .err()
        .unwrap();
    assert_eq!(failure.reason, Error("endpoint-evidence-required"));
    let draw = admitted(
        json!(["apply", ["draw"], [], ["return", 0]]),
        Some(Phase::Sent),
    );
    let done = execute(draw, failure.bindings);
    assert_eq!(done.bindings().endpoint_entry(), Some(entry(Phase::Ready)));
    assert_eq!(done.bindings().events(), &[json!(["drawn", 3])]);
    assert_eq!(
        done.bindings().state_json(),
        json!(["prover", "ready", [0, 0, 0, [[2, 2]], [4]]])
    );
}
#[test]
fn entry_check_precedes_loading_private_inputs_and_rejects_plain_bindings() {
    let program = admitted(json!(["return", 0]), Some(Phase::Ready));
    let failure = AdmittedJob::bind(
        program.clone(),
        json!("malformed inputs"),
        bindings(Phase::Sent),
    )
    .err()
    .unwrap();
    assert_eq!(failure.reason, Error("endpoint-entry-mismatch"));
    let (state, provider) = State::decode(&json!([0, 0, 0, [], []])).unwrap();
    let plain = TableBindings::new(SmallPrimeKernel, provider, state).unwrap();
    let failure = AdmittedJob::bind(program, inputs(), plain).err().unwrap();
    assert_eq!(failure.reason, Error("unsupported-endpoint-binding"));
}
struct Faulty {
    kind: u8,
    consumed: bool,
}
impl ChallengeProvider for Faulty {
    fn draw(&mut self) -> Result<Outcome<u8>, Error> {
        self.consumed = true;
        match self.kind {
            0 => Err(Error("provider-io")),
            1 => Ok(Outcome::Returned(7)),
            _ => panic!("provider panic after effect"),
        }
    }
    fn remaining(&self) -> &[u8] {
        if self.consumed { &[] } else { &[3] }
    }
}
#[test]
fn host_failure_after_provider_effect_leaves_unknown_phase() {
    for kind in 0..3 {
        let (state, _) = State::decode(&json!([0, 0, 0, [], []])).unwrap();
        let bindings = TableBindings::new(
            SmallPrimeKernel,
            Faulty {
                kind,
                consumed: false,
            },
            state,
        )
        .unwrap()
        .with_endpoint("prover".into(), Phase::Sent)
        .unwrap();
        let program = admitted(
            json!(["apply", ["draw"], [], ["return", 0]]),
            Some(Phase::Sent),
        );
        let done = execute(program.clone(), bindings);
        assert!(done.outcome().is_err());
        assert_eq!(
            done.bindings().state_json(),
            json!(["prover", "unknown", [0, 0, 0, [], []]])
        );
        let (_, bindings) = done.into_parts();
        let failure = AdmittedJob::bind(program, inputs(), bindings)
            .err()
            .unwrap();
        assert_eq!(failure.reason, Error("unknown-endpoint-state"));
    }
}
#[test]
fn stopped_calls_keep_phase_and_failed_write_effects() {
    let (state, provider) = State::decode(&json!([0, 0, 0, [], []])).unwrap();
    let b = TableBindings::new(SmallPrimeKernel, provider, state)
        .unwrap()
        .with_endpoint("prover".into(), Phase::Sent)
        .unwrap();
    let p = admitted(
        json!(["apply", ["draw"], [], ["return", 0]]),
        Some(Phase::Sent),
    );
    let done = execute(p, b);
    assert!(matches!(
        done.outcome(),
        Ok(Outcome::Stopped(Stop::Exhausted))
    ));
    assert_eq!(done.bindings().endpoint_entry(), Some(entry(Phase::Sent)));
    let (_, b) = done.into_parts();
    let p = admitted(
        json!(["apply", ["abort_write", "f7"], [0], ["return", 1]]),
        Some(Phase::Sent),
    );
    let done = execute(p, b);
    assert!(matches!(done.outcome(), Ok(Outcome::Stopped(Stop::Abort))));
    assert_eq!(
        done.bindings().state_json(),
        json!(["prover", "sent", [0, 2, 1, [], []]])
    );
    assert_eq!(done.bindings().events(), &[json!(["write", "f7", 2])]);
}
#[test]
fn local_primitive_ownership_is_checked_before_effects() {
    let (state, provider) = State::decode(&json!([0, 0, 0, [], [3]])).unwrap();
    let mut b = TableBindings::new(SmallPrimeKernel, provider, state)
        .unwrap()
        .with_endpoint("verifier".into(), Phase::Sent)
        .unwrap();
    assert!(matches!(
        b.invoke(&Operation::Draw, &[]),
        Err(Error("primitive-owner-mismatch"))
    ));
    assert_eq!(
        b.state_json(),
        json!(["verifier", "sent", [0, 0, 0, [], [3]]])
    );
}

#[test]
fn stateful_binding_requires_its_policy_and_cannot_be_relabelled() {
    let program = admitted(json!(["return", 0]), Some(Phase::Ready));
    let b = bindings(Phase::Ready);
    let trace = PhaseEvidence {
        profile: "table-round/1".into(),
        certificate: b"[]".to_vec(),
        entry: None,
    };
    assert_eq!(
        b.validate_entry("prover", Some(&trace)),
        Err(Error("endpoint-policy-mismatch"))
    );
    let absent = PhaseEvidence {
        profile: ENDPOINT_PROFILE.into(),
        ..trace
    };
    assert_eq!(
        b.validate_entry("prover", Some(&absent)),
        Err(Error("endpoint-evidence-required"))
    );
    assert_eq!(
        b.validate_entry("verifier", program.phase_evidence()),
        Err(Error("endpoint-role-mismatch"))
    );
    assert!(matches!(
        b.with_endpoint("prover".into(), Phase::Sent),
        Err(Error("endpoint-already-bound"))
    ));
}

#[test]
fn actual_call_guards_reject_bad_phase_without_provider_effects() {
    let mut b = bindings(Phase::Ready);
    let original = b.state_json();
    assert!(matches!(
        b.invoke(&Operation::Draw, &[]),
        Err(Error("endpoint-call-not-enabled"))
    ));
    assert_eq!(b.state_json(), original);
    let mut b = bindings(Phase::Unknown);
    assert!(matches!(
        b.invoke(&Operation::Draw, &[]),
        Err(Error("unknown-endpoint-state"))
    ));
    assert_eq!(
        Phase::decode(&json!("foreign")),
        Err(Error("invalid-endpoint-phase"))
    );
}

struct BrokenAdd;
impl zkc_runtime::table::FieldKernel for BrokenAdd {
    fn add(&self, _: zkc_runtime::table::Domain, _: u8, _: u8) -> u8 {
        7
    }
    fn sub(&self, d: zkc_runtime::table::Domain, a: u8, b: u8) -> u8 {
        SmallPrimeKernel.sub(d, a, b)
    }
    fn mul(&self, d: zkc_runtime::table::Domain, a: u8, b: u8) -> u8 {
        SmallPrimeKernel.mul(d, a, b)
    }
}

#[test]
fn failure_between_calls_keeps_known_phase_and_permits_new_admission() {
    let (state, provider) = State::decode(&json!([0, 0, 0, [], [3]])).unwrap();
    let b = TableBindings::new(BrokenAdd, provider, state)
        .unwrap()
        .with_endpoint("prover".into(), Phase::Ready)
        .unwrap();
    let p = admitted(
        json!([
            "apply",
            ["send"],
            [0, 0],
            ["apply", ["add", "f7"], [1, 1], ["return", 0]]
        ]),
        Some(Phase::Ready),
    );
    let done = AdmittedJob::bind(p, inputs(), b)
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .reserve(Budget::default())
        .unwrap_or_else(|e| panic!("{}", e.reason))
        .execute();
    assert!(done.started());
    assert!(matches!(
        done.outcome(),
        Err(Error("field-contract-violation"))
    ));
    assert_eq!(done.bindings().endpoint_entry(), Some(entry(Phase::Sent)));
    assert_eq!(done.bindings().events(), &[json!(["sent", 2, 2])]);
    let (_, b) = done.into_parts();
    let p = admitted(
        json!(["apply", ["draw"], [], ["return", 0]]),
        Some(Phase::Sent),
    );
    assert!(AdmittedJob::bind(p, inputs(), b).is_ok());
}

// Synthetic composite adapter path: the outer function does not expose the
// send result to its caller. It uses the real table call boundaries twice.
fn send_then_draw<P: ChallengeProvider>(
    b: &mut TableBindings<SmallPrimeKernel, P>,
) -> Result<Outcome<zkc_runtime::table::Value>, Error> {
    use zkc_runtime::table::{Domain, Value};
    let sent = b.invoke(
        &Operation::Send,
        &[
            Value::Scalar(Domain::Seven, 2),
            Value::Scalar(Domain::Seven, 5),
        ],
    )?;
    if let Outcome::Stopped(why) = sent {
        return Ok(Outcome::Stopped(why));
    }
    b.invoke(&Operation::Draw, &[])
}
#[test]
fn composite_adapter_retains_the_second_calls_entry_and_first_calls_effects() {
    let (state, provider) = State::decode(&json!([0, 0, 0, [], []])).unwrap();
    let mut b = TableBindings::new(SmallPrimeKernel, provider, state)
        .unwrap()
        .with_endpoint("prover".into(), Phase::Ready)
        .unwrap();
    // Direct adapter invocation needs the same reservation as the dispatcher.
    let resources = zkc_runtime::Resources {
        events: 2,
        ..Default::default()
    };
    b.reserve(resources, &Budget::default()).unwrap();
    assert!(matches!(
        send_then_draw(&mut b),
        Ok(Outcome::Stopped(Stop::Exhausted))
    ));
    assert_eq!(
        b.state_json(),
        json!(["prover", "sent", [0, 0, 0, [[2, 5]], []]])
    );
    assert_eq!(b.events(), &[json!(["sent", 2, 5])]);
    let (state, _) = State::decode(&json!([0, 0, 0, [], []])).unwrap();
    let mut b = TableBindings::new(
        SmallPrimeKernel,
        Faulty {
            kind: 0,
            consumed: false,
        },
        state,
    )
    .unwrap()
    .with_endpoint("prover".into(), Phase::Ready)
    .unwrap();
    b.reserve(resources, &Budget::default()).unwrap();
    assert!(matches!(send_then_draw(&mut b), Err(Error("provider-io"))));
    assert_eq!(
        b.state_json(),
        json!(["prover", "unknown", [0, 0, 0, [[2, 5]], []]])
    );
    assert_eq!(b.events(), &[json!(["sent", 2, 5])]);
}

#[test]
fn normally_returned_endpoint_can_reuse_the_same_admitted_program() {
    let p = admitted(
        json!([
            "apply",
            ["send"],
            [0, 0],
            ["apply", ["draw"], [], ["return", 0]]
        ]),
        Some(Phase::Ready),
    );
    let done = execute(p.clone(), bindings(Phase::Ready));
    let (_, b) = done.into_parts();
    let done = execute(p, b);
    assert!(matches!(done.outcome(), Ok(Outcome::Returned(_))));
    assert_eq!(
        done.bindings().state_json(),
        json!(["prover", "ready", [0, 0, 0, [[2, 2], [2, 2]], []]])
    );
    assert_eq!(
        done.bindings().events(),
        &[json!(["sent", 2, 2]), json!(["drawn", 4])]
    );
}
