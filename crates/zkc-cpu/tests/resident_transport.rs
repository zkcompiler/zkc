//! Exact resident transport through the shared Host, including stopped prefixes.
use serde_json::{Value as Json, json};
use zkc_cpu::{
    Bls12381G2, CpuBackend, Domain, EntryPolicy, G1, Policy, Scalar, Value, cpu_contracts,
};
use zkc_format::proof::{MAX_PROOF_BYTES, ProofFormat};
use zkc_runtime::{
    host::{
        joint::*,
        proof,
        wire::{ProofBackend, WireBackend, WireError},
    },
    interpreter::Runner,
    vm::{
        self, Backend, BackendError, DecodeReason, Frame, FrameExit, Identity, Invocation,
        PhysicalType, Program, Value as _, WireCodec,
    },
};

const BOOL: &str = "bool@native.bool/0";
fn native(role: &str) -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new(role, "session", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn selected(value: &Value) -> PhysicalType {
    let ty = value.physical_type();
    let logical = ty.logical();
    let representation = match logical.identity() {
        Identity::Bls12381Fr => "blst/fr",
        Identity::Bls12381G1 => "blst/g1",
        Identity::Bls12381G2 => "blst/g2",
        _ => panic!("unsupported test layout"),
    };
    cpu_contracts()
        .physical_type(&format!("{}@{representation}", logical.spelling()))
        .unwrap()
}
fn samples() -> Vec<Value> {
    vec![
        Value::Field(Scalar::from(7)),
        Value::Vector(vec![Scalar::from(0), Scalar::from(7)].into()),
        Value::Curve(G1::generator()),
        Value::Groups(vec![G1::identity(), G1::generator()].into()),
        Value::Bls12381G2(Bls12381G2::generator()),
        Value::Bls12381G2Vector(vec![Bls12381G2::identity(), Bls12381G2::generator()].into()),
        Value::Vector(vec![].into()),
        Value::Groups(vec![].into()),
        Value::Bls12381G2Vector(vec![].into()),
    ]
}
fn carrier(ty: &PhysicalType, count: usize) -> Json {
    let ty = ty.spelling();
    let mut send = Vec::new();
    let mut receive = Vec::new();
    for index in 0..count {
        let site = format!("message{index}");
        send.push(json!(["send", site, site, "V", "x"]));
        receive.push(json!(["receive", site, site, "P", format!("x{index}"), ty]));
    }
    send.push(json!(["return", []]));
    receive.push(json!(["return", [format!("x{}", count - 1), "ok"]]));
    json!([
        "zkc.program/0",
        [],
        [],
        [
            ["participant", "p", "root", "P", [["x", ty]], [], send, []],
            [
                "participant",
                "v",
                "root",
                "V",
                [["ok", BOOL]],
                [ty, BOOL],
                receive,
                []
            ],
        ],
        [["entry", "main", [["P", "p"], ["V", "v"]]]]
    ])
}
fn bundle(ty: &PhysicalType, count: usize) -> Bundle {
    let mut steps = Vec::new();
    for index in 0..count {
        steps.push(json!({"role":0, "instruction":index, "anchor":index}));
        steps.push(json!({"role":1, "instruction":index, "anchor":index}));
    }
    for role in 0..2 {
        steps.push(json!({"role":role, "instruction":count, "anchor":null}));
    }
    let bytes = serde_json::to_vec(&json!({"format":"zkc.run/0", "candidate":carrier(ty, count).to_string(), "entry":"main", "roles":["P","V"], "steps":steps})).unwrap();
    Bundle::admit(
        &bytes,
        &native("P"),
        cpu_contracts(),
        BundleLimits::default(),
    )
    .unwrap()
}

/// Test independent codec capability and post-decode validation separately from
/// the trusted contract permission. The wire implementation itself is reused.
struct Host {
    native: CpuBackend,
    supports: bool,
    reject_received: bool,
    wrong_decoded_type: bool,
}
impl Host {
    fn new(role: &str) -> Self {
        Self {
            native: native(role),
            supports: true,
            reject_received: false,
            wrong_decoded_type: false,
        }
    }
}
impl Backend for Host {
    type Value = Value;
    type Operation = <CpuBackend as Backend>::Operation;
    type Call = ();
    type Checkpoint = ();
    fn prepare_binding(&self, binding: &vm::OperationBinding) -> Option<Self::Operation> {
        self.native.prepare_binding(binding)
    }
    fn validate_value(&self, value: &Value) -> Result<(), BackendError> {
        if self.reject_received
            && matches!(
                value.physical_type().representation(),
                vm::Representation::Extension(_)
            )
        {
            return Err(BackendError::new("transient-received-value"));
        }
        self.native.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, args: &[Value]) -> Result<(), BackendError> {
        self.native.enter_frame(frame, args)
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        values: &[Value],
    ) -> Result<(), BackendError> {
        self.native.leave_frame(frame, exit, values)
    }
    fn apply(
        &mut self,
        operation: &Self::Operation,
        invocation: &Invocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        self.native.apply(operation, invocation, args)
    }
}
impl WireBackend for Host {
    fn supports_wire(&self, ty: &PhysicalType) -> bool {
        self.supports && self.native.supports_wire(ty)
    }
    fn fixed_wire_size(&self, ty: &PhysicalType) -> Option<usize> {
        self.native.fixed_wire_size(ty)
    }
    fn encoding_bound(&self, value: &Value) -> Result<usize, WireError> {
        self.native.encoding_bound(value)
    }
    fn decoding_bound(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<usize, WireError> {
        self.native.decoding_bound(ty, bytes)
    }
    fn encode_wire(&self, value: &Value) -> Result<Vec<u8>, WireError> {
        self.native.encode_wire(value)
    }
    fn decode_wire(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<Value, WireError> {
        if self.wrong_decoded_type {
            Ok(Value::Bool(true))
        } else {
            self.native.decode_wire(ty, bytes)
        }
    }
}
impl ProofBackend for Host {
    fn acceptance(&self, value: &Value) -> Option<bool> {
        self.native.acceptance(value)
    }
}
fn inputs(value: Value, receiver: Host) -> Vec<RoleInput<Host>> {
    vec![
        RoleInput {
            role: "P".into(),
            backend: Host::new("P"),
            values: vec![value],
        },
        RoleInput {
            role: "V".into(),
            backend: receiver,
            values: vec![Value::Bool(true)],
        },
    ]
}
#[derive(Default)]
struct Replace {
    second: Option<Vec<u8>>,
    sent: Vec<Vec<u8>>,
}
impl Hooks<Host> for Replace {
    fn transfer(
        &mut self,
        exchange: Exchange<'_>,
        bytes: &[u8],
        _: usize,
    ) -> Result<Option<Vec<u8>>, String> {
        self.sent.push(bytes.to_vec());
        Ok(if exchange.site == "message1" {
            self.second.take()
        } else {
            None
        })
    }
}
fn assert_closed(report: &Report<Host>) {
    assert!(
        report
            .backends
            .iter()
            .all(|(_, host)| host.native.active_frames() == 0)
    );
}

#[test]
fn all_flat_resident_layouts_transport_directly_through_joint_host() {
    let codec = native("P");
    for ark in samples() {
        let ty = selected(&ark);
        assert!(cpu_contracts().permits_wire(&ty, WireCodec::Native));
        let wire = codec.encode_wire(&ark).unwrap();
        let resident = codec.decode_wire(&ty, &wire).unwrap();
        let mut hooks = Replace::default();
        let report = run(
            &bundle(&ty, 2),
            "session",
            inputs(resident, Host::new("V")),
            RunLimits::default(),
            &mut hooks,
        )
        .unwrap();
        assert_eq!(report.outcome, Outcome::Completed, "{}", ty.spelling());
        assert_eq!(report.wire.sends, 2);
        assert_eq!(report.wire.receives, 2);
        assert_eq!(hooks.sent, [wire.clone(), wire.clone()]);
        assert_eq!(report.roles[1].outputs[0].physical_type(), ty);
        assert_eq!(
            codec.encode_wire(&report.roles[1].outputs[0]).unwrap(),
            wire
        );
        assert_closed(&report);
    }
}

#[test]
fn malformed_resident_receive_preserves_the_completed_prefix() {
    let codec = native("P");
    let ark = Value::Field(Scalar::from(7));
    let ty = selected(&ark);
    let wire = codec.encode_wire(&ark).unwrap();
    let resident = codec.decode_wire(&ty, &wire).unwrap();
    let mut scalar = wire.clone();
    scalar[6..].fill(255);
    for (replacement, reason) in [
        (wire[..wire.len() - 1].to_vec(), DecodeReason::Length),
        (
            {
                let mut b = wire.clone();
                b[0] = 0;
                b
            },
            DecodeReason::Header,
        ),
        (scalar, DecodeReason::Scalar),
    ] {
        let mut hooks = Replace {
            second: Some(replacement),
            ..Default::default()
        };
        let report = run(
            &bundle(&ty, 2),
            "session",
            inputs(resident.clone(), Host::new("V")),
            RunLimits::default(),
            &mut hooks,
        )
        .unwrap();
        assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 1 });
        let State::Stopped(stop) = &report.roles[1].before else {
            panic!("decode stop")
        };
        assert_eq!(stop.cause, StopCause::Decode(reason));
        assert_eq!(stop.site.as_deref(), Some("message1"));
        assert_eq!((report.wire.sends, report.wire.receives), (2, 2));
        assert!(report.roles[1].outputs.is_empty());
        assert!(report.pending.is_none());
        assert_eq!(
            report.reached[1].receive_completion,
            Some(vm::ReceiveCompletion::Delivered)
        );
        assert_eq!(
            report.reached[3].receive_completion,
            Some(vm::ReceiveCompletion::Stopped)
        );
        assert_closed(&report);
    }
}

#[test]
fn resident_limits_remain_capacity_failures_with_an_unconsumed_receive() {
    let codec = native("P");
    let ark = Value::Vector(vec![Scalar::from(7); 2].into());
    let ty = selected(&ark);
    let wire = codec.encode_wire(&ark).unwrap();
    let resident = codec.decode_wire(&ty, &wire).unwrap();
    let mut oversized = wire.clone();
    oversized[6..10].fill(255);
    for (replacement, limits, expected_sends, expected_receives) in [
        (
            None,
            RunLimits {
                wire_bytes: wire.len() - 1,
                ..Default::default()
            },
            0,
            0,
        ),
        (
            None,
            RunLimits {
                total_wire_bytes: 2 * wire.len() - 1,
                ..Default::default()
            },
            1,
            1,
        ),
        (Some(oversized), RunLimits::default(), 2, 1),
    ] {
        let mut hooks = Replace {
            second: replacement,
            ..Default::default()
        };
        let report = run(
            &bundle(&ty, 2),
            "session",
            inputs(resident.clone(), Host::new("V")),
            limits,
            &mut hooks,
        )
        .unwrap();
        assert!(
            matches!(&report.outcome, Outcome::DriverFailed(f) if f.kind == FailureKind::Limit)
        );
        assert_eq!(
            (report.wire.sends, report.wire.receives),
            (expected_sends, expected_receives)
        );
        assert!(report.roles[1].outputs.is_empty());
        if expected_sends == 2 {
            assert!(report.pending.is_some());
        }
        assert_closed(&report);
    }
}

#[test]
fn permission_does_not_replace_backend_support_or_transient_value_validation() {
    let codec = native("P");
    let ark = Value::Curve(G1::generator());
    let ty = selected(&ark);
    let resident = codec
        .decode_wire(&ty, &codec.encode_wire(&ark).unwrap())
        .unwrap();
    let mut receiver = Host::new("V");
    receiver.supports = false;
    let refused = run(
        &bundle(&ty, 1),
        "session",
        inputs(resident.clone(), receiver),
        RunLimits::default(),
        &mut NoHooks,
    )
    .err()
    .expect("unsupported codec refused");
    assert_eq!(refused.failure.kind, FailureKind::Setup);
    assert!(
        refused
            .inputs
            .iter()
            .all(|input| input.backend.native.active_frames() == 0)
    );
    for wrong_type in [false, true] {
        let mut receiver = Host::new("V");
        receiver.reject_received = !wrong_type;
        receiver.wrong_decoded_type = wrong_type;
        let report = run(
            &bundle(&ty, 1),
            "session",
            inputs(resident.clone(), receiver),
            RunLimits::default(),
            &mut NoHooks,
        )
        .unwrap();
        assert!(report.roles[1].outputs.is_empty());
        if wrong_type {
            assert!(
                matches!(&report.outcome, Outcome::DriverFailed(f) if f.kind == FailureKind::Contract)
            );
        } else {
            assert_eq!(report.outcome, Outcome::ParticipantStopped { role: 1 });
            let State::Stopped(stop) = &report.roles[1].before else {
                panic!("backend validation stop")
            };
            assert!(
                matches!(&stop.cause, StopCause::Backend(e) if e.text == "transient-received-value")
            );
        }
        assert_closed(&report);
    }
}

#[test]
fn proof_entry_and_proof_host_accept_only_contributed_resident_message_layouts() {
    let codec = native("P");
    for ark in samples() {
        let ty = selected(&ark);
        let admitted = Program::decode(
            &serde_json::to_vec(&carrier(&ty, 1)).unwrap(),
            cpu_contracts(),
        )
        .unwrap();
        let entry = vm::NativeProofEntry::new(
            admitted.clone(),
            "main",
            "P",
            "V",
            1,
            vm::ProofConstruction {
                suite: None,
                events: &[],
                plan: None,
                source_inputs: &Default::default(),
            },
        )
        .unwrap();
        assert_eq!(entry.admitted().bytes(), admitted.bytes());
        let resident = codec
            .decode_wire(&ty, &codec.encode_wire(&ark).unwrap())
            .unwrap();
        let mut producer = Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            native("P"),
            vec![resident],
        )
        .unwrap_or_else(|_| panic!("producer"));
        let produced = proof::produce(
            &mut producer,
            &[7; 32],
            proof::Transport::Messages(ProofFormat::Native),
            MAX_PROOF_BYTES,
            None,
        )
        .outcome
        .unwrap();
        let mut validator = Runner::new(
            &admitted,
            "main",
            "V",
            "session",
            native("V"),
            vec![Value::Bool(true)],
        )
        .unwrap_or_else(|_| panic!("validator"));
        let result = proof::validate(
            &mut validator,
            &produced.proof,
            &[7; 32],
            proof::Transport::Messages(ProofFormat::Native),
            1,
            None,
        )
        .outcome
        .unwrap();
        assert_eq!(result[0].physical_type(), ty);
        assert_eq!(
            codec.encode_wire(&result[0]).unwrap(),
            codec.encode_wire(&ark).unwrap()
        );
        assert_eq!(producer.backend().active_frames(), 0);
        assert_eq!(validator.backend().active_frames(), 0);
    }
}

#[test]
fn proof_host_checks_actual_codec_support_separately_from_permission() {
    let codec = native("P");
    let ark = Value::Field(Scalar::from(7));
    let ty = selected(&ark);
    let admitted = Program::decode(
        &serde_json::to_vec(&carrier(&ty, 1)).unwrap(),
        cpu_contracts(),
    )
    .unwrap();
    let resident = codec
        .decode_wire(&ty, &codec.encode_wire(&ark).unwrap())
        .unwrap();
    let mut unsupported = Host::new("P");
    unsupported.supports = false;
    let mut producer = Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        unsupported,
        vec![resident.clone()],
    )
    .unwrap_or_else(|_| panic!("producer"));
    let refused = proof::produce(
        &mut producer,
        &[7; 32],
        proof::Transport::Messages(ProofFormat::Native),
        MAX_PROOF_BYTES,
        None,
    );
    assert!(
        matches!(refused.outcome, Err(proof::ArtifactFailure::Wire(WireError::Backend(ref error))) if error.code == "proof-wire-type")
    );
    assert_eq!(producer.backend().native.active_frames(), 0);

    let mut producer = Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        native("P"),
        vec![resident],
    )
    .unwrap_or_else(|_| panic!("producer"));
    let produced = proof::produce(
        &mut producer,
        &[7; 32],
        proof::Transport::Messages(ProofFormat::Native),
        MAX_PROOF_BYTES,
        None,
    )
    .outcome
    .unwrap();
    let mut unsupported = Host::new("V");
    unsupported.supports = false;
    let mut validator = Runner::new(
        &admitted,
        "main",
        "V",
        "session",
        unsupported,
        vec![Value::Bool(true)],
    )
    .unwrap_or_else(|_| panic!("validator"));
    let refused = proof::validate(
        &mut validator,
        &produced.proof,
        &[7; 32],
        proof::Transport::Messages(ProofFormat::Native),
        1,
        None,
    );
    assert!(
        matches!(refused.outcome, Err(proof::ArtifactFailure::Wire(WireError::Backend(ref error))) if error.code == "proof-wire-type")
    );
    assert_eq!(validator.backend().native.active_frames(), 0);
}
