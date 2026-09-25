//! Native compiler/reference harness; the observer implements no protocol math.
//! The observer delegates all kernels to NativeBackend. Logical observations erase
//! only checked table relayouts; physical failure equivalence is separate work.

use super::origins::SourceOrigins;
use serde_json::{Value as Json, json};
use std::{cell::RefCell, path::PathBuf, process::Command, rc::Rc};
use zkc_backends::{Domain, NativeBackend, Policy, Scalar, Value};
use zkc_runtime::interactive::{
    Action, Backend, BackendError, BoundSignature, Frame, FrameExit, FrameKind, Invocation,
    OperationBinding, Origin, Packet, PathElement, PhysicalType, Runner, SourceMap, Stop, StopKind,
    Value as RuntimeValue, admit_physical,
};
use zkc_tools::protocol::{ParticipantChecker, Transport, WireBackend};

/// Somewhere for one subject to live, inside the running test's evidence. A
/// test that builds two of them would otherwise have the second's source
/// checked against the first's.
fn subject() -> zkc_test_support::Evidence {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    zkc_test_support::evidence(module_path!())
        .nested(&format!("subject-{}", NEXT.fetch_add(1, Ordering::Relaxed)))
}

/// A logical kind over a domain, as source notation writes it. The cases that
/// name a kind get its notation from one place, so that a kind added to them is
/// a compile error here rather than a parse error at the tool.
pub fn written(kind: &str, domain: &str) -> String {
    match kind {
        "field" => format!("{domain}::Element"),
        "table" => format!("Table<{domain}>"),
        "point" => format!("Point<{domain}>"),
        "round" => format!("Round<{domain}>"),
        other => panic!("no source notation recorded for the {other} kind"),
    }
}

#[path = "../common/backend.rs"]
mod fixture;
pub(super) use fixture::{backend, backend_for, backend_in};

pub(super) fn decimal(value: &Scalar) -> String {
    let result = value.to_string();
    if result.is_empty() {
        "0".into()
    } else {
        result
    }
}

pub(super) fn commitment_identity(identity: zkc_arkworks::Metadata) -> Json {
    use zkc_test_support::hex;
    json!([
        identity.arity().to_string(),
        hex(&identity.setup_id()),
        hex(&identity.key_id())
    ])
}

pub(super) fn value_json(value: &Value) -> Json {
    if let Value::Rng(token) | Value::Nonce(token) | Value::Transcript(token) = value {
        assert_eq!(
            token.issued_id(),
            0,
            "multiple resources require explicit Trace registration"
        );
    }
    let payload = match value {
        Value::Field(x) => json!(decimal(x)),
        Value::KoalaBearField(x) => json!(x.to_string()),
        Value::Bool(b) => json!(b.to_string()),
        Value::Table(t) => json!([
            t.arity().to_string(),
            t.logical_values()
                .unwrap()
                .iter()
                .map(decimal)
                .collect::<Vec<_>>()
        ]),
        Value::TableMsb(t) => json!([
            t.arity().to_string(),
            t.logical_values().iter().map(decimal).collect::<Vec<_>>()
        ]),
        Value::Rng(t) => json!(["draws", t.generation().to_string()]),
        Value::Nonce(t) => json!(["nonce", t.generation().to_string()]),
        Value::Transcript(t) => json!(["transcript", t.generation().to_string()]),
        Value::Point(p) => json!(p.iter().map(decimal).collect::<Vec<_>>()),
        Value::Round(q) => json!(q.iter().map(decimal).collect::<Vec<_>>()),
        Value::Curve(_) | Value::Groups(_) | Value::Commitment(_) | Value::Proof(_) => {
            let bytes = backend().encode_value(value).unwrap();
            json!(zkc_test_support::hex(&bytes))
        }
        Value::ProverKey(key) => commitment_identity(key.metadata()),
        Value::VerifierKey(key) => commitment_identity(key.metadata()),
        Value::OpeningState(state) => json!([
            commitment_identity(state.commitment().metadata()),
            [
                state.original().arity().to_string(),
                state
                    .original()
                    .logical_values()
                    .unwrap()
                    .iter()
                    .map(decimal)
                    .collect::<Vec<_>>()
            ],
            value_json(&Value::Commitment(std::sync::Arc::new(
                state.commitment().clone()
            )))[1]
        ]),
        _ => panic!("value outside this differential corpus"),
    };
    json!([value.physical_type().logical().spelling(), payload])
}

pub(super) fn source_path(origin: &Origin) -> Vec<Json> {
    origin
        .path
        .iter()
        .map(|p| match p {
            PathElement::Conditional { site, taken } => {
                json!(["if", site, if *taken { "then" } else { "else" }])
            }
            PathElement::Match { site, alternative } => json!(["match", site, alternative]),
            PathElement::For { site, index } => json!(["for", site, index.to_string()]),
            PathElement::Call { site, .. } => json!(["call", site]),
            PathElement::Loop { site, iteration } => {
                json!(["iteration", site, iteration.to_string()])
            }
        })
        .collect()
}

#[derive(Clone)]
pub(super) struct Trace {
    records: Rc<RefCell<Vec<Json>>>,
    origins: Rc<SourceOrigins>,
    transcript_steps: Rc<RefCell<Vec<Json>>>,
    resources: Rc<RefCell<std::collections::BTreeMap<(String, u64), String>>>,
}
impl Trace {
    pub(super) fn new(source: &[u8]) -> Self {
        Self {
            records: Rc::default(),
            origins: Rc::new(SourceOrigins::new(source)),
            transcript_steps: Rc::default(),
            resources: Rc::default(),
        }
    }
    pub(super) fn check_origin(&self, origin: &Origin) {
        self.origins.check(origin).unwrap();
    }
    pub(super) fn register_resource(
        &self,
        role: &str,
        backend: &NativeBackend,
        value: &Value,
        label: &str,
    ) {
        let (Value::Rng(token) | Value::Nonce(token) | Value::Transcript(token)) = value else {
            panic!("resource")
        };
        backend.observe(token).unwrap();
        let mut labels = self.resources.borrow_mut();
        assert!(!labels.values().any(|name| name == label));
        assert!(
            labels
                .insert((role.into(), token.issued_id()), label.into())
                .is_none()
        );
    }
    pub(super) fn value(&self, role: &str, value: &Value) -> Json {
        if let Value::Rng(token) | Value::Nonce(token) | Value::Transcript(token) = value
            && let Some(label) = self
                .resources
                .borrow()
                .get(&(role.into(), token.issued_id()))
        {
            return json!([
                value.physical_type().logical().spelling(),
                [label, token.generation().to_string()]
            ]);
        }
        value_json(value)
    }
    pub(super) fn push(&self, event: Json) {
        self.records.borrow_mut().push(event);
    }
    pub(super) fn snapshot(&self) -> Vec<Json> {
        self.records.borrow().clone()
    }
    pub(super) fn transcript_steps(&self) -> Vec<Json> {
        self.transcript_steps.borrow().clone()
    }
    pub(super) fn message(&self, packet: &Packet<Value>, received: bool) {
        let e = &packet.envelope;
        self.check_origin(&e.origin);
        let (kind, role, peer) = if received {
            ("receive", &e.receiver, &e.sender)
        } else {
            ("send", &e.sender, &e.receiver)
        };
        let location = json!([
            "source-origin/2",
            e.origin.session,
            e.origin.entry,
            e.origin.instance,
            source_path(&e.origin),
            e.site,
            role,
            []
        ]);
        assert_eq!(packet.ty, packet.payload.physical_type());
        self.push(json!([
            kind,
            location,
            e.schema,
            peer,
            value_json(&packet.payload)
        ]));
    }
}
impl Transport<Value> for Trace {
    fn transfer(&mut self, packet: &Packet<Value>, bytes: Vec<u8>) -> Result<Vec<u8>, String> {
        self.message(packet, false);
        Ok(bytes)
    }
    fn delivered(&mut self, packet: &Packet<Value>) {
        self.message(packet, true);
    }
}

pub(super) fn assert_stop_location(trace: &Trace, stop: &Stop, location: &Json, local: bool) {
    trace.check_origin(&stop.origin);
    assert_eq!(location[1], stop.origin.session);
    assert_eq!(location[2], stop.origin.entry);
    assert_eq!(location[3], stop.origin.instance);
    assert_eq!(location[6], stop.role);
    let mut path = location[4].as_array().unwrap().clone();
    let site = if local {
        let call = path.pop().unwrap();
        assert_eq!(call[0], "local");
        call[1].clone()
    } else {
        location[5].clone()
    };
    assert_eq!(path, source_path(&stop.origin));
    assert_eq!(
        site.as_str().filter(|s| !s.is_empty()),
        stop.site.as_deref()
    );
    assert!(stop.cleanup_errors.is_empty());
}

pub(super) struct Observed {
    pub(super) inner: NativeBackend,
    pub(super) source_map: SourceMap,
    pub(super) events: Trace,
    pub(super) conversions: usize,
}
impl Observed {
    fn request(&self, call: &Invocation<'_>, args: &[Value]) -> Json {
        let origin = call.frame.origin();
        self.events.check_origin(origin);
        let mut path = source_path(origin);
        let FrameKind::Local { site, .. } = call.frame.kind() else {
            panic!("local frame")
        };
        let selected = self
            .source_map
            .call(&origin.instance, call.frame.role(), site)
            .unwrap();
        path.push(json!(["local", site, selected.source_function]));
        let location = json!([
            "source-origin/2",
            origin.session,
            origin.entry,
            origin.instance,
            path,
            call.site,
            call.frame.role(),
            [
                call.logical_origin.definition,
                call.logical_origin.arguments
            ]
        ]);
        let binding = call.binding.declaration();
        json!([
            "zkc.reference-primitive/2",
            location,
            binding.contract,
            binding.arguments,
            call.attributes,
            args.iter()
                .map(|v| self.events.value(call.frame.role(), v))
                .collect::<Vec<_>>()
        ])
    }
}
impl Backend for Observed {
    type Value = Value;
    fn binding_signature(&self, binding: &OperationBinding) -> Option<BoundSignature> {
        self.inner.binding_signature(binding)
    }
    fn validate_value(&self, value: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, args: &[Value]) -> Result<(), BackendError> {
        self.inner.enter_frame(frame, args)
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        values: &[Value],
    ) -> Result<(), BackendError> {
        self.inner.leave_frame(frame, exit, values)
    }
    fn apply(&mut self, call: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>, BackendError> {
        if call.binding.declaration().contract == "table.relayout" {
            self.conversions += 1;
            return self.inner.apply(call, args);
        }
        let request = self.request(call, args);
        self.events.push(json!(["request", request]));
        let result = self.inner.apply(call, args);
        if let Ok(values) = &result {
            let contract = &call.binding.declaration().contract;
            use zkc_test_support::hex;
            let action = if contract == "transcript.challenge" {
                Some(json!([
                    "challenge",
                    hex(&zkc_runtime::logical::challenge_origin(
                        call.frame.origin(),
                        call.attributes
                    )
                    .unwrap())
                ]))
            } else if contract.starts_with("transcript.observe.") {
                Some(json!([
                    "message",
                    hex(&zkc_runtime::logical::message_origin(
                        call.frame.origin(),
                        call.attributes
                    )
                    .unwrap()),
                    hex(&self.inner.encode_value(&args[1]).unwrap())
                ]))
            } else {
                None
            };
            if let Some(action) = action {
                self.events.transcript_steps.borrow_mut().push(action);
            }
            self.events.push(json!([
                "response",
                request,
                values
                    .iter()
                    .map(|v| self.events.value(call.frame.role(), v))
                    .collect::<Vec<_>>()
            ]));
        }
        result
    }
}

impl WireBackend for Observed {
    fn encode(&self, value: &Value) -> Result<Vec<u8>, BackendError> {
        self.inner.encode_value(value)
    }
    fn decode(&self, ty: PhysicalType, bytes: &[u8]) -> Result<Value, BackendError> {
        self.inner.decode_typed_value(ty, bytes)
    }
}

pub(super) struct Fixture {
    pub(super) directory: zkc_test_support::Evidence,
    pub(super) compiler: PathBuf,
    pub(super) checker_path: PathBuf,
    pub(super) source: Vec<u8>,
    pub(super) candidate: Vec<u8>,
}
impl Fixture {
    pub(super) fn new() -> Self {
        Self::from_fixture("generic-stops.pir")
    }
    pub(super) fn from_fixture(name: &str) -> Self {
        let compiler = zkc_test_support::compiler();
        let input = zkc_test_support::source(name);
        let source = Self::compile(&compiler, "protocol-source", &input);
        let candidate = Self::compile(&compiler, "protocol-compile", &input);
        let fixture = Self {
            directory: subject(),
            compiler,
            checker_path: zkc_test_support::checker("interactive-protocol"),
            source,
            candidate,
        };
        std::fs::write(
            fixture.directory.path().join("source.json"),
            &fixture.source,
        )
        .unwrap();
        fixture
    }
    pub(super) fn from_text(source: &str) -> Self {
        let directory = subject();
        let compiler = zkc_test_support::compiler();
        let path = directory.path().join("input.pir");
        std::fs::write(&path, source).unwrap();
        let source = Self::compile(&compiler, "protocol-source", &path);
        let candidate = Self::compile(&compiler, "protocol-compile", &path);
        std::fs::write(directory.path().join("source.json"), &source).unwrap();
        Self {
            directory,
            compiler,
            source,
            candidate,
            checker_path: zkc_test_support::checker("interactive-protocol"),
        }
    }
    pub(super) fn compile(
        compiler: &std::path::Path,
        mode: &str,
        input: &std::path::Path,
    ) -> Vec<u8> {
        let result = Command::new(compiler)
            .arg(mode)
            .arg(input)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        result.stdout
    }
    pub(super) fn set_source(&mut self, source: &Json) {
        self.source = serde_json::to_vec(source).unwrap();
        let path = self.directory.path().join("source.json");
        std::fs::write(&path, &self.source).unwrap();
        self.candidate = Self::compile(&self.compiler, "protocol-compile", &path);
    }
    pub(super) fn reference(&self, inputs: &Json) -> Json {
        let (success, result) = self.reference_as(inputs, None);
        assert!(success, "{result}");
        result
    }
    pub(super) fn reference_as(&self, inputs: &Json, role: Option<&str>) -> (bool, Json) {
        let path = self.directory.path().join("inputs.json");
        std::fs::write(&path, serde_json::to_vec(inputs).unwrap()).unwrap();
        let mut command = Command::new(&self.checker_path);
        command
            .arg(if role.is_some() {
                "--generic-role"
            } else {
                "--generic-reference"
            })
            .arg(self.directory.path().join("source.json"))
            .arg(path);
        if let Some(role) = role {
            command.arg(role);
        }
        let result = command.output().unwrap();
        let value = serde_json::from_slice(&result.stdout).unwrap_or_else(|_| {
            panic!(
                "{}{}",
                String::from_utf8_lossy(&result.stdout),
                String::from_utf8_lossy(&result.stderr)
            )
        });
        (result.status.success(), value)
    }
    pub(super) fn compare(
        &self,
        cells: &[u64],
        tape: &[u64],
        budget: u64,
        allowed: bool,
        expected_conversions: usize,
    ) {
        let checker = ParticipantChecker::new(&self.checker_path).unwrap();
        let admitted = admit_physical(&self.source, &self.candidate, &backend(), &checker).unwrap();
        let mut inner = backend();
        let rng = inner
            .issue_test_tape(
                Domain::new("P", "test", "main", None),
                budget,
                tape.iter().copied().map(Scalar::from).collect(),
            )
            .unwrap();
        let Value::Rng(token) = &rng else {
            unreachable!()
        };
        let token = token.clone();
        let other = inner
            .issue_test_tape(
                Domain::new("P", "test", "main", None),
                3,
                vec![Scalar::from(7)],
            )
            .unwrap();
        let Value::Rng(other) = other else {
            unreachable!()
        };
        let table = Value::table(
            &cells.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap();
        let inputs = vec![rng, table.clone(), Value::Bool(allowed)];
        let observed = Observed {
            inner,
            source_map: admitted.source_map().unwrap().clone(),
            events: Trace::new(&self.source),
            conversions: 0,
        };
        let mut runner = Runner::new(&admitted, "main", "P", "test", observed, inputs.clone())
            .unwrap_or_else(|e| panic!("{}", e.error));
        let terminal = loop {
            match runner.poll() {
                Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
                action @ (Action::Returned(_) | Action::Stopped(_)) => break action,
                unexpected => panic!("unexpected action: {unexpected:?}"),
            }
        };
        let ports: Vec<_> = ["rng", "table", "allowed"]
            .into_iter()
            .zip(&inputs)
            .map(|(name, value)| json!([name, value_json(value)]))
            .collect();
        let reference = self.reference(&json!([
            "zkc.reference-inputs/1",
            "main",
            "test",
            [["P", ports]],
            [
                [
                    "draws",
                    "P",
                    [],
                    budget.to_string(),
                    ["rng", tape.iter().map(u64::to_string).collect::<Vec<_>>()]
                ],
                ["untouched", "P", [], "3", ["rng", ["7"]]]
            ],
            [],
            []
        ]));
        assert_eq!(reference[0], "zkc.reference-observation/1");
        assert_eq!(reference[4], json!(runner.backend().events.snapshot()));
        match terminal {
            Action::Returned(values) => assert_eq!(
                reference[3],
                json!([
                    "returned",
                    values.iter().map(value_json).collect::<Vec<_>>()
                ])
            ),
            Action::Stopped(stop) => {
                let StopKind::Backend(error) = &stop.kind else {
                    panic!("unexpected stop")
                };
                let (reason, detail) = error.code.split_once(':').unwrap();
                let reason = if reason == "rejected" {
                    "reject"
                } else {
                    reason
                };
                assert_eq!(reference[3][0], reason);
                assert_eq!(reference[3][1], detail);
                let events = runner.backend().events.snapshot();
                let last_request = events.iter().rev().find(|e| e[0] == "request").unwrap();
                assert_eq!(reference[3][2], last_request[1][1]);
                assert_stop_location(&runner.backend().events, &stop, &reference[3][2], true);
                assert!(stop.cleanup_errors.is_empty());
                assert_eq!(runner.usage().live_value_bytes, 0);
            }
            _ => unreachable!(),
        }
        let native = &runner.backend().inner;
        let observations: Vec<_> = [("draws", &token), ("untouched", &other)]
            .into_iter()
            .map(|(name, handle)| {
                let r = native.observe(handle).unwrap();
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
        assert_eq!(reference[5], json!(observations));
        assert_eq!(runner.backend().conversions, expected_conversions);
        assert_eq!(native.active_frames(), 0);
        let Value::Table(table) = table else {
            unreachable!()
        };
        assert_eq!(
            table.logical_values().unwrap(),
            cells.iter().copied().map(Scalar::from).collect::<Vec<_>>()
        );
    }
}

/// Compare the admitted source with the native runner, including terminal fields.
/// Local operation sites are finer than native Stop.site (the enclosing cut).
pub(super) fn compare_pure(fixture: &Fixture, ports: &[(&str, Value)], session: &str) -> Json {
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let admitted =
        admit_physical(&fixture.source, &fixture.candidate, &backend(), &checker).unwrap();
    let observer = Observed {
        inner: backend_in("P", session),
        source_map: admitted.source_map().unwrap().clone(),
        events: Trace::new(&fixture.source),
        conversions: 0,
    };
    let mut runner = Runner::new(
        &admitted,
        "main",
        "P",
        session,
        observer,
        ports.iter().map(|(_, v)| v.clone()).collect(),
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    let terminal = loop {
        match runner.poll() {
            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
            a @ (Action::Returned(_) | Action::Stopped(_)) => break a,
            other => panic!("unexpected {other:?}"),
        }
    };
    let inputs = json!([
        "zkc.reference-inputs/1",
        "main",
        session,
        [[
            "P",
            ports
                .iter()
                .map(|(n, v)| json!([n, value_json(v)]))
                .collect::<Vec<_>>()
        ]],
        [],
        [],
        []
    ]);
    let reference = fixture.reference(&inputs);
    let events = runner.backend().events.snapshot();
    assert_eq!(reference[4], json!(events));
    match terminal {
        Action::Returned(values) => assert_eq!(
            reference[3],
            json!([
                "returned",
                values.iter().map(value_json).collect::<Vec<_>>()
            ])
        ),
        Action::Stopped(stop) => {
            let local = match &stop.kind {
                StopKind::Backend(error) => {
                    let (reason, detail) = error.code.split_once(':').unwrap();
                    assert_eq!(
                        reference[3][0],
                        if reason == "rejected" {
                            "reject"
                        } else {
                            reason
                        }
                    );
                    assert_eq!(reference[3][1], detail);
                    let request = events.iter().rev().find(|e| e[0] == "request").unwrap();
                    assert_eq!(reference[3][2], request[1][1]);
                    true
                }
                StopKind::Explicit(reason) => {
                    assert_eq!(reference[3][0], *reason);
                    assert_eq!(reference[3][1], "source-stop");
                    false
                }
                kind => panic!("unexpected {kind:?}"),
            };
            assert_stop_location(&runner.backend().events, &stop, &reference[3][2], local);
            assert_eq!(runner.usage().live_value_bytes, 0);
        }
        _ => unreachable!(),
    }
    assert_eq!(runner.backend().inner.active_frames(), 0);
    reference
}
