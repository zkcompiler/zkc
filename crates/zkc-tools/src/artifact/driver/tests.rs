use super::*;
use serde_json::json;
use zkc_backends::Value;
use zkc_runtime::interactive::{
    Backend, BackendError, Frame, FrameExit, Invocation, StopKind, admit_supplied,
};

#[derive(Debug, Default)]
struct CleanupFailure {
    active: usize,
}
impl Backend for CleanupFailure {
    type Value = Value;
    fn validate_value(&self, _: &Value) -> Result<(), BackendError> {
        Ok(())
    }
    fn enter_frame(&mut self, _: &Frame, _: &[Value]) -> Result<(), BackendError> {
        self.active += 1;
        Ok(())
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        _: FrameExit,
        _: &[Value],
    ) -> Result<(), BackendError> {
        self.active -= 1;
        Err(BackendError::new(format!("cleanup.{}", frame.id().get())))
    }
    fn apply(&mut self, _: &Invocation<'_>, _: &[Value]) -> Result<Vec<Value>, BackendError> {
        panic!("no kernel in this client")
    }
}
impl WireBackend for CleanupFailure {
    fn encode(&self, _: &Value) -> Result<Vec<u8>, BackendError> {
        panic!("no proof message after an ingress stop")
    }
    fn decode(
        &self,
        _: zkc_runtime::interactive::PhysicalType,
        _: &[u8],
    ) -> Result<Value, BackendError> {
        panic!("no proof message after an ingress stop")
    }
}
fn stopped_at_ingress() -> Runner<CleanupFailure> {
    let index = "index@native.index/1";
    let carrier = json!([
        "zkc.participants/1",
        [],
        "physical",
        [[
            "function",
            "count",
            [],
            [index],
            [["stop", "ingress_failure", "reject"]],
            ["count", []]
        ]],
        [[
            "participant",
            "producer",
            "root",
            "P",
            [["n", ["ingress", "8", [["P", "count", []]]]]],
            [],
            [],
            [["return", []]]
        ]],
        [["entry", "main", [["P", "producer"]]]]
    ]);
    let backend = CleanupFailure::default();
    let admitted = admit_supplied(&serde_json::to_vec(&carrier).unwrap(), &backend).unwrap();
    let runner = Runner::new(&admitted, "main", "P", "test", backend, vec![]).unwrap();
    assert_eq!(runner.backend().active, 0);
    assert!(runner.stop().is_some());
    runner
}
fn assert_ingress_stop<T>(report: ArtifactReport<T>) {
    let Err(ArtifactFailure::Stopped(stop)) = report.outcome else {
        panic!("the ingress failure must survive later proof-format refusal");
    };
    assert_eq!(stop.kind, StopKind::Explicit("reject".into()));
    assert_eq!(stop.site.as_deref(), Some("ingress.n"));
    assert_eq!(
        stop.cleanup_errors
            .iter()
            .map(|e| e.code.as_str())
            .collect::<Vec<_>>(),
        ["cleanup.2", "cleanup.1"]
    );
    assert_eq!((report.messages, report.bytes), (0, 0));
    assert!(report.cancelled.is_none());
}
#[test]
fn ingress_stop_precedes_producer_buffer_refusal() {
    for limit in [39, 40, 4096] {
        let mut runner = stopped_at_ingress();
        assert_ingress_stop(produce_admitted_with_limit(
            &mut runner,
            &[0; 32],
            false,
            limit,
            |_, _| panic!("stopped producer"),
        ));
    }
}
#[test]
fn ingress_stop_precedes_validator_header_refusal() {
    let valid_header = ProofWriter::new(&[0; 32]).finish();
    for proof in [b"invalid proof".as_slice(), valid_header.as_slice()] {
        let mut runner = stopped_at_ingress();
        assert_ingress_stop(validate(&mut runner, proof, &[0; 32], 0, |_| None));
    }
}

fn fresh(with_message: bool, role: &str) -> Runner<zkc_backends::NativeBackend> {
    use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs};
    let backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new(role, "test", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let ty = "bool@native.bool/1";
    let send = if with_message {
        json!([["send", "m", "m", "V", "x"], ["return", []]])
    } else {
        json!([["return", []]])
    };
    let receive = if with_message {
        json!([
            ["receive", "m", "m", "P", "received", ty],
            ["return", ["received"]]
        ])
    } else {
        json!([["return", ["x"]]])
    };
    let carrier = json!([
        "zkc.participants/1",
        [],
        "physical",
        [],
        [
            ["participant", "p", "root", "P", [], [["x", ty]], [], send],
            [
                "participant",
                "v",
                "root",
                "V",
                [],
                [["x", ty]],
                [ty],
                receive
            ]
        ],
        [["entry", "main", [["P", "p"], ["V", "v"]]]]
    ]);
    let admitted = admit_supplied(&serde_json::to_vec(&carrier).unwrap(), &backend).unwrap();
    Runner::new(
        &admitted,
        "main",
        role,
        "test",
        backend,
        vec![Value::Bool(true)],
    )
    .unwrap_or_else(|e| panic!("{}", e.error))
}
fn boolean(v: &Value) -> Option<bool> {
    if let Value::Bool(b) = v {
        Some(*b)
    } else {
        None
    }
}
#[test]
fn proof_drivers_reject_reuse_and_partly_consumed_runners() {
    let binding = [7; 32];
    let header = ProofWriter::new(&binding).finish();
    for messages in [false, true] {
        let mut producer = fresh(messages, "P");
        if messages {
            assert!(matches!(producer.poll(), Action::Send(_)));
        }
        let proof = produce(&mut producer, &binding).outcome.unwrap().proof;
        assert_eq!(proof.len() == 40, !messages);
        assert!(matches!(
            produce(&mut producer, &binding).outcome,
            Err(ArtifactFailure::StartedRunner)
        ));
        let mut verifier = fresh(messages, "V");
        if messages {
            assert!(matches!(verifier.poll(), Action::Receive(_)));
        }
        assert!(
            validate(&mut verifier, &proof, &binding, 0, boolean)
                .outcome
                .is_ok()
        );
        let reused = validate(&mut verifier, &header, &binding, 0, boolean);
        assert!(matches!(
            reused.outcome,
            Err(ArtifactFailure::StartedRunner)
        ));
        assert_eq!((reused.messages, reused.bytes), (0, 0));
    }
    let mut producer = fresh(true, "P");
    let cut = producer.poll().cut().unwrap();
    producer.take_send(&cut).unwrap();
    let report = produce(&mut producer, &binding);
    assert!(matches!(
        report.outcome,
        Err(ArtifactFailure::StartedRunner)
    ));
    assert!(report.cancelled.is_some());
    let mut verifier = fresh(true, "V");
    let Action::Receive(request) = verifier.poll() else {
        panic!("receive")
    };
    verifier
        .deliver(Packet {
            envelope: request.envelope,
            ty: request.ty,
            payload: Value::Bool(true),
        })
        .unwrap();
    assert!(matches!(
        validate(&mut verifier, &header, &binding, 0, boolean).outcome,
        Err(ArtifactFailure::StartedRunner)
    ));
}

#[test]
fn proof_entry_allows_successful_ingress_work() {
    use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs};
    let backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("P", "test", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let ty = "index@native.index/1";
    let carrier = json!([
        "zkc.participants/1",
        [],
        "physical",
        [[
            "function",
            "count",
            [["n", ty]],
            [ty],
            [["return", ["n"]]],
            ["count", []]
        ]],
        [[
            "participant",
            "p",
            "root",
            "P",
            [["n", ["ingress", "8", [["P", "count", ["x"]]]]]],
            [["x", ty]],
            [],
            [["return", []]]
        ]],
        [["entry", "main", [["P", "p"]]]]
    ]);
    let admitted = admit_supplied(&serde_json::to_vec(&carrier).unwrap(), &backend).unwrap();
    let mut runner = Runner::new(
        &admitted,
        "main",
        "P",
        "test",
        backend,
        vec![Value::Index(2)],
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    assert!(runner.usage().instructions > 0);
    assert!(runner.is_at_entry());
    let proof = produce(&mut runner, &[0; 32]).outcome.unwrap().proof;
    assert_eq!(proof.len(), 40);
}

#[test]
fn proof_entry_preserves_an_already_stopped_runner_without_consuming_a_new_proof() {
    let mut verifier = fresh(true, "V");
    let first = validate(&mut verifier, b"bad", &[0; 32], 0, boolean);
    let stop = first.stop().unwrap().clone();
    let second = validate(
        &mut verifier,
        &ProofWriter::new(&[0; 32]).finish(),
        &[0; 32],
        0,
        boolean,
    );
    assert!(matches!(second.outcome,Err(ArtifactFailure::Stopped(ref s)) if **s==stop));
    assert_eq!((second.messages, second.bytes), (0, 0));
    assert!(second.cancelled.is_none());
}
