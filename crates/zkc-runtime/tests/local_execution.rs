//! Public VM API controls with an independent, noncryptographic test backend.
use serde_json::{Value as Json, json};
use std::cell::Cell;
use std::sync::{Arc, Barrier, Mutex};
use zkc_runtime::{
    interpreter::{LocalRunner, Runner},
    vm::*,
};

const FIELD: &str = "field:bls12-381.fr@arkworks.fr/0";
const INDEX: &str = "index@native.index/0";
const BOOL: &str = "bool@native.bool/0";
#[derive(Clone, Debug, PartialEq)]
enum Number {
    Field(u64),
    Index(u64),
    Bool(bool),
    Shared(Arc<u64>),
    Watched(Arc<LiveDropProbe>),
    WatchedInline(Arc<LiveDropProbe>),
    WatchedIndex(Arc<LiveDropProbe>),
}
struct LiveDropProbe {
    ledger: ExecutionLedger,
    observations: Arc<Mutex<Vec<usize>>>,
}
impl std::fmt::Debug for LiveDropProbe {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("LiveDropProbe")
    }
}
impl PartialEq for LiveDropProbe {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.observations, &other.observations)
    }
}
impl Drop for LiveDropProbe {
    fn drop(&mut self) {
        self.observations
            .lock()
            .unwrap()
            .push(self.ledger.snapshot().live_reserved_bytes);
    }
}
impl Value for Number {
    fn physical_type(&self) -> PhysicalType {
        PhysicalType::parse(match self {
            Self::Index(_) | Self::WatchedIndex(_) => INDEX,
            Self::Bool(_) => BOOL,
            _ => FIELD,
        })
        .unwrap()
    }
    fn retained_bytes(&self) -> usize {
        8
    }
    fn retained_parts(&self, shared: &mut dyn FnMut(Backing) -> bool) -> usize {
        match self {
            Self::Shared(value) => {
                shared(Backing::of(value, 8));
                0
            }
            Self::Watched(value) | Self::WatchedIndex(value) => {
                shared(Backing::of(value, 8));
                0
            }
            _ => 8,
        }
    }
    fn validation_backing(&self) -> Option<Backing> {
        match self {
            Self::Shared(value) => Some(Backing::of(value, 8)),
            Self::Watched(value) | Self::WatchedIndex(value) => Some(Backing::of(value, 8)),
            _ => None,
        }
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        Ok(())
    }
    fn control_index(&self) -> Result<u64, BackendError> {
        match self {
            Self::Index(n) => Ok(*n),
            Self::WatchedIndex(_) => Ok(1),
            _ => Err(BackendError::new("index")),
        }
    }
    fn from_control_index(n: u64) -> Result<Self, BackendError> {
        Ok(Self::Index(n))
    }
    fn control_bool(&self) -> Result<bool, BackendError> {
        match self {
            Self::Bool(b) => Ok(*b),
            _ => Err(BackendError::new("bool")),
        }
    }
    fn from_control_bool(b: bool) -> Result<Self, BackendError> {
        Ok(Self::Bool(b))
    }
}
#[derive(Debug, Default)]
struct Arithmetic {
    frames: Vec<FrameId>,
    entered: Vec<FrameKind>,
    leaves: Vec<(FrameId, FrameExit)>,
    calls: usize,
    fail_leave: bool,
    fail_enter: bool,
    fail_leave_at: Option<u64>,
    wrong_signature: bool,
    reject_values: bool,
    value_validations: Cell<usize>,
    // A deliberately unavailable producer-only implementation.
    allow_multiply: bool,
    fail_apply: bool,
    allocation_gate: Option<Arc<(Barrier, Barrier)>>,
}
impl Backend for Arithmetic {
    type Value = Number;
    type Operation = BoundSignature;
    type Call = ();
    type Checkpoint = ();
    fn supports_boolean_literals(&self) -> bool {
        true
    }
    fn prepare_binding(&self, binding: &OperationBinding) -> Option<BoundSignature> {
        let field = PhysicalType::parse(FIELD).unwrap();
        let supported = binding.implementation.as_str() == "arkworks/field.add"
            || (self.allow_multiply && binding.implementation.as_str() == "arkworks/field.mul");
        supported.then(|| BoundSignature {
            inputs: vec![field.clone(), field.clone()],
            outputs: if self.wrong_signature {
                vec![]
            } else {
                vec![field]
            },
            attributes: AttributeRule::None,
        })
    }
    fn validate_value(&self, _: &Number) -> Result<(), BackendError> {
        self.value_validations.set(self.value_validations.get() + 1);
        if self.reject_values {
            Err(BackendError::new("independent-value-refusal"))
        } else {
            Ok(())
        }
    }
    fn enter_frame(&mut self, frame: &Frame, _: &[Number]) -> Result<(), BackendError> {
        assert_eq!(frame.parent(), self.frames.last().copied());
        if self.fail_enter {
            return Err(BackendError::new("entry-refused"));
        }
        self.frames.push(frame.id());
        self.entered.push(frame.kind().clone());
        Ok(())
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        _: &[Number],
    ) -> Result<(), BackendError> {
        assert_eq!(self.frames.pop(), Some(frame.id()));
        self.leaves.push((frame.id(), exit));
        if self.fail_leave || self.fail_leave_at == Some(frame.id().get()) {
            Err(BackendError::new(format!("cleanup:{}", frame.id().get())))
        } else {
            Ok(())
        }
    }
    fn apply(
        &mut self,
        _: &BoundSignature,
        invocation: &Invocation<'_>,
        args: &[Number],
    ) -> Result<Vec<Number>, BackendError> {
        // Exercise the allocation-before-effect contract, including exhaustion.
        if invocation.max_output_bytes < 8 {
            return Err(BackendError::new("allocation-refused"));
        }
        self.calls += 1;
        if let Some(gate) = &self.allocation_gate {
            gate.0.wait();
            gate.1.wait();
        }
        if self.fail_apply {
            return Err(BackendError::new("partial-operation"));
        }
        match args {
            [Number::Field(a), Number::Field(b)] => Ok(vec![Number::Field(a + b)]),
            _ => Err(BackendError::new("arithmetic-operands")),
        }
    }
    fn service_support(&self, contract: ServiceContract, method: &str) -> Option<ServiceSupport> {
        if contract != ServiceContract::RandomExtensionField {
            return None;
        }
        let signature = match method {
            "draw" => ServiceSignature {
                inputs: vec![],
                outputs: vec![
                    PhysicalType::default_for(
                        LogicalType::parse("field:koala-bear.ext8-binomial3").unwrap(),
                    )
                    .unwrap(),
                ],
            },
            "index" => ServiceSignature {
                inputs: vec![PhysicalType::parse(INDEX).unwrap()],
                outputs: vec![PhysicalType::parse(INDEX).unwrap()],
            },
            _ => return None,
        };
        Some(ServiceSupport {
            signature,
            max_retained_bytes: 8,
        })
    }
}
fn module(functions: Json, participants: Json, entries: Json) -> Json {
    json!([
        "zkc.program/0",
        [
            ["add", "field.add", ["bls12-381.fr"], "arkworks/field.add"],
            [
                "multiply",
                "field.mul",
                ["bls12-381.fr"],
                "arkworks/field.mul"
            ]
        ],
        functions,
        participants,
        entries
    ])
}
fn function(name: &str, inputs: Json, outputs: Json, body: Json) -> Json {
    json!(["function", name, inputs, outputs, body, [name, []]])
}
fn add() -> Json {
    function(
        "add_root",
        json!([["a", FIELD], ["b", FIELD]]),
        json!([FIELD]),
        json!([
            ["op", "sum", "add", [], ["a", "b"], ["c"]],
            ["return", ["c"]]
        ]),
    )
}
fn loop_function() -> Json {
    function(
        "repeat",
        json!([["lo", INDEX], ["hi", INDEX], ["x", FIELD], ["d", FIELD]]),
        json!([FIELD]),
        json!([
            [
                "for",
                "loop",
                "i",
                "lo",
                "hi",
                [["carry", "x"]],
                ["d"],
                [
                    ["op", "plus", "add", [], ["carry", "d"], ["next"]],
                    ["yield", ["next"]]
                ],
                ["result"]
            ],
            ["return", ["result"]]
        ]),
    )
}
fn decode(source: Json) -> Program {
    Program::decode(&serde_json::to_vec(&source).unwrap()).unwrap()
}
fn program() -> Program {
    decode(module(
        json!([add(), loop_function()]),
        json!([]),
        json!([]),
    ))
}
fn values(live: usize, total: usize) -> ValueBudget {
    ValueBudget {
        live_bytes: live,
        total_bytes: total,
    }
}
fn work(instructions: u64, iterations: u64, logical: u64) -> WorkBudget {
    WorkBudget {
        instructions,
        iterations,
        logical_bytes: logical,
    }
}
fn local(program: &Program, ledger: &ExecutionLedger) -> LocalRunner<Arithmetic> {
    LocalRunner::new_with_ledger(
        program,
        "add_root",
        "session",
        Arithmetic::default(),
        vec![Number::Field(2), Number::Field(5)],
        values(128, 1024),
        work(100, 100, 1024),
        Some(ledger.clone()),
    )
    .ok()
    .unwrap()
}

#[test]
fn standalone_helper_uses_entry_custody_and_local_frames_with_stable_results() {
    let program = program();
    assert_eq!(program.local_function("add_root").unwrap().inputs.len(), 2);
    assert_eq!(program.local_function_names().count(), 2);
    assert_eq!(program.entry_names().count(), 0);
    let mut runner = LocalRunner::new(
        &program,
        "add_root",
        "session",
        Arithmetic::default(),
        vec![Number::Field(3), Number::Field(4)],
    )
    .ok()
    .unwrap();
    assert_eq!(runner.backend().entered, [FrameKind::Entry]);
    assert_eq!(runner.backend().value_validations.get(), 2);
    assert!(matches!(runner.execute(),Action::Returned(values) if values == &[Number::Field(7)]));
    let usage = runner.usage();
    assert_eq!(usage.instructions, 2);
    assert!(matches!(runner.execute(), Action::Returned(_)));
    assert_eq!(runner.usage(), usage);
    assert_eq!(
        runner.backend().entered,
        [
            FrameKind::Entry,
            FrameKind::Local {
                site: "add_root".into(),
                function: "add_root".into()
            }
        ]
    );
    assert!(runner.backend().frames.is_empty());
    assert_eq!(runner.into_backend().calls, 1);
}

#[test]
fn local_loops_keep_order_usage_and_stop_coordinates() {
    let program = program();
    for iterations in [2, 3] {
        let mut runner = LocalRunner::new_with_budgets(
            &program,
            "repeat",
            "session",
            Arithmetic::default(),
            vec![
                Number::Index(0),
                Number::Index(3),
                Number::Field(1),
                Number::Field(2),
            ],
            values(1024, 4096),
            work(100, iterations, 4096),
        )
        .ok()
        .unwrap();
        if iterations == 3 {
            assert!(matches!(runner.execute(),Action::Returned(v) if v == &[Number::Field(7)]));
        } else {
            assert!(
                matches!(runner.execute(),Action::Stopped(s) if s.kind == StopKind::Limit
                && s.origin.path == [PathElement::For {site:"loop".into(),index:2}])
            );
            assert_eq!(runner.usage().live_value_bytes, 0);
        }
        assert_eq!(runner.usage().iterations, iterations);
        assert_eq!(runner.backend().calls, iterations as usize);
        assert!(runner.backend().frames.is_empty());
    }
}

#[test]
fn wrong_root_inputs_and_installation_return_backend_custody() {
    let program = program();
    for (name, inputs, backend) in [
        ("missing", vec![], Arithmetic::default()),
        ("add_root", vec![Number::Field(1)], Arithmetic::default()),
        (
            "add_root",
            vec![Number::Bool(true), Number::Field(1)],
            Arithmetic::default(),
        ),
        (
            "add_root",
            vec![Number::Field(1), Number::Field(1)],
            Arithmetic {
                wrong_signature: true,
                ..Arithmetic::default()
            },
        ),
    ] {
        let refusal = LocalRunner::new(&program, name, "session", backend, inputs)
            .err()
            .unwrap();
        assert!(refusal.backend.entered.is_empty());
        match name {
            "missing" => assert!(matches!(
                refusal.error,
                RuntimeError::Admission(AdmissionError {
                    code: ErrorCode::Symbol,
                    ..
                })
            )),
            _ => assert!(matches!(
                refusal.error,
                RuntimeError::Inputs
                    | RuntimeError::Payload
                    | RuntimeError::Admission(AdmissionError {
                        code: ErrorCode::Backend,
                        ..
                    })
            )),
        }
    }
    assert_eq!(
        Program::decode(&serde_json::to_vec(&module(json!([]), json!([]), json!([]))).unwrap())
            .unwrap_err()
            .code,
        ErrorCode::Symbol
    );
    let mut malformed = module(json!([add()]), json!([]), json!([]));
    malformed[2][0][4][0][4] = json!(["undefined", "b"]);
    assert_eq!(
        Program::decode(&serde_json::to_vec(&malformed).unwrap())
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
}

#[test]
fn explicit_stop_and_cleanup_failures_preserve_primary_and_order() {
    let source = function(
        "stopping",
        json!([["condition", BOOL]]),
        json!([]),
        json!([
            [
                "if",
                "branch",
                "condition",
                [],
                [["stop", "inner", "reject"]],
                [["yield", []]],
                []
            ],
            ["return", []]
        ]),
    );
    let program = decode(module(json!([source]), json!([]), json!([])));
    let ledger = ExecutionLedger::new(values(128, 1024), work(100, 100, 1024));
    let mut runner = LocalRunner::new_with_ledger(
        &program,
        "stopping",
        "session",
        Arithmetic {
            fail_leave: true,
            ..Arithmetic::default()
        },
        vec![Number::Bool(true)],
        values(128, 1024),
        work(100, 100, 1024),
        Some(ledger.clone()),
    )
    .ok()
    .unwrap();
    assert!(
        matches!(runner.execute(),Action::Stopped(s) if s.kind == StopKind::Explicit("reject".into())
        && s.cleanup_errors.iter().map(|e| e.code.as_str()).collect::<Vec<_>>() == ["cleanup:3","cleanup:2","cleanup:1"]
        && s.role.is_empty() && s.local.as_ref().unwrap().instruction.as_deref() == Some("inner"))
    );
    assert!(runner.backend().frames.is_empty());
    assert_eq!(runner.usage().live_value_bytes, 0);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    assert!(ledger.snapshot().instructions > 0);
}

#[test]
fn selected_verifier_does_not_install_producer_only_bindings() {
    let producer = function(
        "producer",
        json!([["x", FIELD], ["y", FIELD]]),
        json!([FIELD]),
        json!([
            ["op", "mul", "multiply", [], ["x", "y"], ["z"]],
            ["return", ["z"]]
        ]),
    );
    let participant = |symbol: &str, role: &str, function: &str| {
        json!([
            "participant",
            symbol,
            "deployment",
            role,
            [["x", FIELD], ["y", FIELD]],
            [FIELD],
            [
                ["local", "call", function, ["x", "y"], ["z"]],
                ["return", ["z"]]
            ],
            []
        ])
    };
    let program = decode(module(
        json!([add(), producer]),
        json!([
            participant("verifier", "V", "add_root"),
            participant("producer_role", "P", "producer")
        ]),
        json!([[
            "entry",
            "proof",
            [["V", "verifier"], ["P", "producer_role"]]
        ]]),
    ));
    assert_eq!(
        program
            .check_installation(&Arithmetic::default())
            .unwrap_err()
            .code,
        ErrorCode::Backend
    );
    program
        .check_role_installation("proof", "V", &Arithmetic::default())
        .unwrap();
    assert_eq!(
        program
            .check_role_installation("proof", "P", &Arithmetic::default())
            .unwrap_err()
            .code,
        ErrorCode::Backend
    );
    assert_eq!(
        program
            .check_role_installation("proof", "unknown", &Arithmetic::default())
            .unwrap_err()
            .code,
        ErrorCode::Symbol
    );
    let mut runner = Runner::new_for_role_with_ledger(
        &program,
        "proof",
        "V",
        "session",
        Arithmetic::default(),
        vec![Number::Field(4), Number::Field(5)],
        ValueBudget::default(),
        WorkBudget::default(),
        None,
    )
    .ok()
    .unwrap();
    let Action::Local(action) = runner.poll() else {
        panic!("local action")
    };
    runner.execute_local(&action.cut).unwrap();
    assert!(matches!(runner.poll(),Action::Returned(v) if v == [Number::Field(9)]));
    assert!(
        Runner::new(
            &program,
            "proof",
            "V",
            "session",
            Arithmetic::default(),
            vec![Number::Field(4), Number::Field(5)]
        )
        .is_err()
    );
}

#[test]
fn cumulative_instructions_logical_and_fresh_exhaust_across_runners() {
    let program = program();
    // First invocation costs two instructions and 24 logical bytes. Inline
    // bindings conservatively cost 48 fresh bytes including terminal retention.
    for (values_budget, work_budget) in [
        (values(128, 2048), work(3, 100, 2048)),
        (values(128, 2048), work(100, 100, 24)),
        (values(128, 48), work(100, 100, 2048)),
    ] {
        let ledger = ExecutionLedger::new(values_budget, work_budget);
        let mut first = local(&program, &ledger);
        assert!(matches!(first.execute(), Action::Returned(_)));
        let first_used = ledger.snapshot();
        drop(first);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
        let second = LocalRunner::new_with_ledger(
            &program,
            "add_root",
            "session2",
            Arithmetic::default(),
            vec![Number::Field(2), Number::Field(5)],
            values(128, 1024),
            work(100, 100, 1024),
            Some(ledger.clone()),
        );
        match second {
            Ok(mut second) => assert!(matches!(second.execute(), Action::Stopped(_))),
            Err(refusal) => assert!(matches!(refusal.error, RuntimeError::Limit)),
        }
        let used = ledger.snapshot();
        assert!(used.instructions >= first_used.instructions);
        assert!(used.total_value_bytes >= first_used.total_value_bytes);
        assert!(used.logical_bytes >= first_used.logical_bytes);
        assert_eq!(used.live_reserved_bytes, 0);
    }
}

#[test]
fn live_allowance_counts_parent_child_and_retained_outputs_until_drop() {
    let program = program();
    let ledger = ExecutionLedger::new(values(128, 4096), work(100, 100, 4096));
    let mut parent = local(&program, &ledger);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 128);
    assert!(
        LocalRunner::new_with_ledger(
            &program,
            "add_root",
            "child",
            Arithmetic::default(),
            vec![Number::Field(1), Number::Field(1)],
            values(128, 1024),
            WorkBudget::default(),
            Some(ledger.clone())
        )
        .is_err()
    );
    assert!(matches!(parent.execute(), Action::Returned(_)));
    let (backend, outputs) = parent.into_retained_outputs();
    assert!(backend.frames.is_empty());
    let outputs = outputs.unwrap();
    assert_eq!(&*outputs, [Number::Field(7)]);
    assert_eq!(outputs.reservation_bytes(), 128);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 128);
    let used = ledger.snapshot();
    drop(outputs);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    assert_eq!(ledger.snapshot().total_value_bytes, used.total_value_bytes);
    let mut child = local(&program, &ledger);
    child.cancel();
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    assert_eq!(child.backend().entered, [FrameKind::Entry]);
    assert!(child.backend().frames.is_empty());
}

#[test]
fn failed_loading_drops_inputs_before_releasing_live_allowance() {
    let program = identity_program();
    for participant in [false, true] {
        for failure in ["validation", "arity", "retention", "entry"] {
            let ledger = ExecutionLedger::new(values(128, 4096), WorkBudget::default());
            let observations = Arc::new(Mutex::new(Vec::new()));
            let mut inputs = vec![Number::Watched(Arc::new(LiveDropProbe {
                ledger: ledger.clone(),
                observations: observations.clone(),
            }))];
            if failure == "arity" {
                inputs.push(Number::Field(0));
            }
            let backend = Arithmetic {
                reject_values: failure == "validation",
                fail_enter: failure == "entry",
                ..Arithmetic::default()
            };
            let budget = values(128, if failure == "retention" { 0 } else { 1024 });
            let refusal = if participant {
                Runner::new_for_role_with_ledger(
                    &program,
                    "main",
                    "P",
                    "session",
                    backend,
                    inputs,
                    budget,
                    WorkBudget::default(),
                    Some(ledger.clone()),
                )
                .err()
                .unwrap()
            } else {
                LocalRunner::new_with_ledger(
                    &program,
                    "identity",
                    "session",
                    backend,
                    inputs,
                    budget,
                    WorkBudget::default(),
                    Some(ledger.clone()),
                )
                .err()
                .unwrap()
            };
            match failure {
                "validation" => assert!(matches!(&refusal.error, RuntimeError::Backend(e)
                    if e.code == "independent-value-refusal")),
                "arity" => assert_eq!(refusal.error, RuntimeError::Inputs),
                "retention" => assert_eq!(refusal.error, RuntimeError::Limit),
                "entry" => assert!(matches!(&refusal.error, RuntimeError::Backend(e)
                    if e.code == "entry-refused")),
                _ => unreachable!(),
            }
            assert!(refusal.backend.frames.is_empty());
            assert!(refusal.backend.entered.is_empty());
            assert_eq!(refusal.usage.live_value_bytes, 0);
            assert_eq!(
                refusal.usage.total_value_bytes,
                if failure == "entry" { 8 } else { 0 }
            );
            assert_eq!(
                *observations.lock().unwrap(),
                [128],
                "{participant} {failure}"
            );
            assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
            assert_eq!(
                ledger.snapshot().total_value_bytes,
                refusal.usage.total_value_bytes
            );
        }
    }
}

fn identity_program() -> Program {
    decode(module(
        json!([function(
            "identity",
            json!([["x", FIELD]]),
            json!([FIELD]),
            json!([["return", ["x"]]])
        )]),
        json!([[
            "participant",
            "identity_role",
            "root",
            "P",
            [["x", FIELD]],
            [FIELD],
            [["return", ["x"]]],
            []
        ]]),
        json!([["entry", "main", [["P", "identity_role"]]]]),
    ))
}

#[test]
fn pending_action_payloads_drop_before_releasing_live_allowance() {
    for query in [false, true] {
        let (ty, body, services) = if query {
            (
                INDEX,
                json!([
                    ["query", "sample", "coins", "index", ["x"], ["y"]],
                    ["return", []]
                ]),
                json!([["coins", "random.koala-bear.ext8-binomial3/0", "1"]]),
            )
        } else {
            (
                FIELD,
                json!([["send", "message", "scalar", "V", "x"], ["return", []]]),
                json!([]),
            )
        };
        let program = decode(module(
            json!([]),
            json!([
                [
                    "participant",
                    "sender",
                    "root",
                    "P",
                    [["x", ty]],
                    [],
                    body,
                    services
                ],
                [
                    "participant",
                    "receiver",
                    "root",
                    "V",
                    [],
                    [],
                    [["return", []]],
                    []
                ]
            ]),
            json!([["entry", "main", [["P", "sender"], ["V", "receiver"]]]]),
        ));
        for destination in ["cancel", "drop", "backend", "outputs"] {
            let ledger = ExecutionLedger::new(values(128, 4096), WorkBudget::default());
            let observations = Arc::new(Mutex::new(Vec::new()));
            let probe = Arc::new(LiveDropProbe {
                ledger: ledger.clone(),
                observations: observations.clone(),
            });
            let input = if query {
                Number::WatchedIndex(probe)
            } else {
                Number::Watched(probe)
            };
            let mut runner = Runner::new_for_role_with_ledger(
                &program,
                "main",
                "P",
                "session",
                Arithmetic::default(),
                vec![input],
                values(128, 1024),
                WorkBudget::default(),
                Some(ledger.clone()),
            )
            .ok()
            .unwrap();
            // Borrow the pending action: the runner owns every payload reference.
            assert!(matches!(
                (query, runner.poll_ref()),
                (true, Action::Query(_)) | (false, Action::Send(_))
            ));
            assert!(observations.lock().unwrap().is_empty());
            let used = ledger.snapshot();
            match destination {
                "cancel" => {
                    runner.cancel();
                    assert_eq!(runner.stop().unwrap().kind, StopKind::Cancelled);
                    assert!(runner.backend().frames.is_empty());
                    assert_eq!(runner.backend().leaves.len(), 1);
                    assert_eq!(runner.backend().leaves[0].0.get(), 1);
                    assert_eq!(runner.backend().leaves[0].1, FrameExit::Cancelled);
                    assert_eq!(runner.usage().live_value_bytes, 0);
                    // The last payload is gone before cancel returns, even while the runner lives.
                    assert_eq!(*observations.lock().unwrap(), [128]);
                    runner.cancel();
                }
                "drop" => drop(runner),
                "backend" => assert!(runner.into_backend().frames.is_empty()),
                "outputs" => {
                    let (backend, outputs) = runner.into_retained_outputs();
                    assert!(backend.frames.is_empty());
                    assert!(outputs.is_none());
                }
                _ => unreachable!(),
            }
            assert_eq!(
                *observations.lock().unwrap(),
                [128],
                "{query} {destination}"
            );
            let after = ledger.snapshot();
            assert_eq!(after.live_reserved_bytes, 0);
            assert_eq!(after.total_value_bytes, used.total_value_bytes);
            assert_eq!(after.instructions, used.instructions);
        }
    }
}

#[test]
fn failed_return_payloads_drop_before_releasing_live_allowance() {
    let program = identity_program();
    for participant in [false, true] {
        for shared_backing in [false, true] {
            for failure in ["cleanup", "retention"] {
                if shared_backing && failure == "retention" {
                    continue; // Shared terminal aliases do not consume fresh capacity.
                }
                let ledger = ExecutionLedger::new(values(128, 4096), WorkBudget::default());
                let observations = Arc::new(Mutex::new(Vec::new()));
                let probe = Arc::new(LiveDropProbe {
                    ledger: ledger.clone(),
                    observations: observations.clone(),
                });
                let input = if shared_backing {
                    Number::Watched(probe)
                } else {
                    Number::WatchedInline(probe)
                };
                let backend = Arithmetic {
                    fail_leave_at: (failure == "cleanup").then_some(1),
                    ..Arithmetic::default()
                };
                let budget = values(
                    128,
                    if failure == "retention" {
                        if participant { 8 } else { 16 }
                    } else {
                        1024
                    },
                );
                let (stop, usage, backend, outputs) = if participant {
                    let mut runner = Runner::new_for_role_with_ledger(
                        &program,
                        "main",
                        "P",
                        "session",
                        backend,
                        vec![input],
                        budget,
                        WorkBudget::default(),
                        Some(ledger.clone()),
                    )
                    .ok()
                    .unwrap();
                    assert!(matches!(runner.poll_ref(), Action::Stopped(_)));
                    let stop = runner.stop().unwrap().clone();
                    let usage = runner.usage();
                    let (backend, outputs) = runner.into_retained_outputs();
                    (stop, usage, backend, outputs)
                } else {
                    let mut runner = LocalRunner::new_with_ledger(
                        &program,
                        "identity",
                        "session",
                        backend,
                        vec![input],
                        budget,
                        WorkBudget::default(),
                        Some(ledger.clone()),
                    )
                    .ok()
                    .unwrap();
                    assert!(matches!(runner.execute(), Action::Stopped(_)));
                    let stop = runner.stop().unwrap().clone();
                    let usage = runner.usage();
                    let (backend, outputs) = runner.into_retained_outputs();
                    (stop, usage, backend, outputs)
                };
                if failure == "cleanup" {
                    assert!(matches!(&stop.kind, StopKind::Backend(e) if e.code == "cleanup:1"));
                } else {
                    assert_eq!(stop.kind, StopKind::Limit);
                }
                assert!(stop.cleanup_errors.is_empty());
                assert!(outputs.is_none());
                assert!(backend.frames.is_empty());
                assert_eq!((usage.live_values, usage.live_value_bytes), (0, 0));
                assert_eq!(
                    *observations.lock().unwrap(),
                    [128],
                    "{participant} {shared_backing} {failure}"
                );
                assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
                assert_eq!(ledger.snapshot().total_value_bytes, usage.total_value_bytes);
            }
        }
    }
}

#[test]
fn received_payloads_drop_before_releasing_live_allowance_on_instruction_refusal() {
    let program = decode(module(
        json!([]),
        json!([
            [
                "participant",
                "receiver",
                "root",
                "V",
                [],
                [FIELD],
                [
                    ["receive", "message", "scalar", "P", "x", FIELD],
                    ["return", ["x"]]
                ],
                []
            ],
            [
                "participant",
                "sender",
                "root",
                "P",
                [],
                [],
                [["return", []]],
                []
            ]
        ]),
        json!([["entry", "main", [["P", "sender"], ["V", "receiver"]]]]),
    ));
    for native_receive in [false, true] {
        let ledger = ExecutionLedger::new(values(128, 4096), work(0, 100, 4096));
        let observations = Arc::new(Mutex::new(Vec::new()));
        let mut runner = Runner::new_for_role_with_ledger(
            &program,
            "main",
            "V",
            "session",
            Arithmetic::default(),
            vec![],
            values(128, 1024),
            if native_receive {
                WorkBudget::default()
            } else {
                work(0, 100, 4096)
            },
            Some(ledger.clone()),
        )
        .ok()
        .unwrap();
        let input = Number::Watched(Arc::new(LiveDropProbe {
            ledger: ledger.clone(),
            observations: observations.clone(),
        }));
        if native_receive {
            let cut = runner.poll_ref().cut().unwrap();
            assert_eq!(
                runner.complete_receive(&cut, Ok(input)).unwrap(),
                ReceiveCompletion::Stopped
            );
        } else {
            let packet = Packet {
                envelope: Envelope {
                    origin: runner.root_origin().clone(),
                    site: "message".into(),
                    schema: "scalar".into(),
                    sender: "P".into(),
                    receiver: "V".into(),
                },
                ty: PhysicalType::parse(FIELD).unwrap(),
                payload: input,
            };
            assert_eq!(runner.deliver(packet), Err(RuntimeError::WrongAction));
        }
        assert_eq!(runner.stop().unwrap().kind, StopKind::Limit);
        assert!(runner.backend().frames.is_empty());
        assert_eq!(runner.usage(), Usage::default());
        assert_eq!(*observations.lock().unwrap(), [128], "{native_receive}");
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    }
}

#[test]
fn loop_arguments_drop_before_releasing_live_allowance_on_iteration_refusal() {
    let program = decode(module(
        json!([]),
        json!([[
            "participant",
            "looping",
            "root",
            "P",
            [["n", INDEX], ["x", FIELD]],
            [FIELD],
            [
                [
                    "loop",
                    "rounds",
                    ["value", "n", "4", "i"],
                    [["carry", "x"]],
                    [],
                    [["yield", ["carry"]]],
                    ["result"]
                ],
                ["return", ["result"]]
            ],
            []
        ]]),
        json!([["entry", "main", [["P", "looping"]]]]),
    ));
    let ledger = ExecutionLedger::new(values(128, 4096), work(100, 0, 4096));
    let observations = Arc::new(Mutex::new(Vec::new()));
    let mut runner = Runner::new_for_role_with_ledger(
        &program,
        "main",
        "P",
        "session",
        Arithmetic::default(),
        vec![
            Number::Index(1),
            Number::Watched(Arc::new(LiveDropProbe {
                ledger: ledger.clone(),
                observations: observations.clone(),
            })),
        ],
        values(128, 1024),
        WorkBudget::default(),
        Some(ledger.clone()),
    )
    .ok()
    .unwrap();
    assert!(runner.advance_local_control().unwrap());
    assert_eq!(runner.stop().unwrap().kind, StopKind::Limit);
    assert_eq!(runner.backend().entered, [FrameKind::Entry]);
    assert!(runner.backend().frames.is_empty());
    assert_eq!(runner.usage().live_value_bytes, 0);
    assert_eq!(runner.usage().total_value_bytes, 16);
    assert_eq!(ledger.snapshot().instructions, 1);
    assert_eq!(ledger.snapshot().iterations, 0);
    assert_eq!(*observations.lock().unwrap(), [128]);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}

#[test]
fn participant_output_guard_keeps_payloads_and_allowance_until_destruction() {
    let program = identity_program();
    for shared_backing in [false, true] {
        let ledger = ExecutionLedger::new(values(128, 4096), WorkBudget::default());
        let observations = Arc::new(Mutex::new(Vec::new()));
        let probe = Arc::new(LiveDropProbe {
            ledger: ledger.clone(),
            observations: observations.clone(),
        });
        let input = if shared_backing {
            Number::Watched(probe)
        } else {
            Number::WatchedInline(probe)
        };
        let mut runner = Runner::new_for_role_with_ledger(
            &program,
            "main",
            "P",
            "session",
            Arithmetic::default(),
            vec![input],
            values(128, 1024),
            WorkBudget::default(),
            Some(ledger.clone()),
        )
        .ok()
        .unwrap();
        assert!(matches!(runner.poll_ref(), Action::Returned(_)));
        let (backend, outputs) = runner.into_retained_outputs();
        assert!(backend.frames.is_empty());
        let outputs = outputs.unwrap();
        assert_eq!(outputs.len(), 1);
        assert_eq!(outputs.reservation_bytes(), 128);
        assert!(observations.lock().unwrap().is_empty());
        assert!(matches!(ledger.reserve_live(1), Err(RuntimeError::Limit)));
        let used = ledger.snapshot();
        drop(outputs);
        assert_eq!(*observations.lock().unwrap(), [128]);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
        assert_eq!(ledger.snapshot().total_value_bytes, used.total_value_bytes);
    }
}

#[test]
fn terminal_payloads_drop_before_releasing_live_allowance() {
    let program = decode(module(
        json!([
            function(
                "identity",
                json!([["x", FIELD]]),
                json!([FIELD]),
                json!([["return", ["x"]]])
            ),
            function(
                "stopping",
                json!([["x", FIELD]]),
                json!([FIELD]),
                json!([["stop", "halt", "reject"]])
            )
        ]),
        json!([]),
        json!([]),
    ));
    for destination in ["drop", "backend", "outputs", "cancel", "stop"] {
        let ledger = ExecutionLedger::new(values(128, 4096), WorkBudget::default());
        let observations = Arc::new(Mutex::new(Vec::new()));
        let mut runner = LocalRunner::new_with_ledger(
            &program,
            if destination == "stop" {
                "stopping"
            } else {
                "identity"
            },
            "session",
            Arithmetic::default(),
            vec![Number::Watched(Arc::new(LiveDropProbe {
                ledger: ledger.clone(),
                observations: observations.clone(),
            }))],
            values(128, 1024),
            WorkBudget::default(),
            Some(ledger.clone()),
        )
        .ok()
        .unwrap();
        if destination == "stop" {
            assert!(matches!(runner.execute(), Action::Stopped(_)));
        } else if destination != "cancel" {
            assert!(matches!(runner.execute(), Action::Returned(_)));
        }
        match destination {
            "drop" | "stop" => drop(runner),
            "backend" => drop(runner.into_backend()),
            "outputs" => {
                let (_, outputs) = runner.into_retained_outputs();
                assert!(observations.lock().unwrap().is_empty());
                drop(outputs);
            }
            "cancel" => {
                runner.cancel();
                drop(runner);
            }
            _ => unreachable!(),
        }
        assert_eq!(*observations.lock().unwrap(), [128]);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    }
}

#[test]
fn shared_backing_never_bypasses_a_second_backends_validation() {
    let program = decode(module(
        json!([function(
            "identity",
            json!([["x", FIELD]]),
            json!([FIELD]),
            json!([["return", ["x"]]])
        )]),
        json!([]),
        json!([]),
    ));
    let ledger = ExecutionLedger::new(values(256, 4096), work(100, 100, 4096));
    let value = Number::Shared(Arc::new(7));
    let mut first = LocalRunner::new_with_ledger(
        &program,
        "identity",
        "first",
        Arithmetic::default(),
        vec![value.clone()],
        values(128, 1024),
        WorkBudget::default(),
        Some(ledger.clone()),
    )
    .ok()
    .unwrap();
    assert!(matches!(first.execute(), Action::Returned(_)));
    let refusal = LocalRunner::new_with_ledger(
        &program,
        "identity",
        "second",
        Arithmetic {
            reject_values: true,
            ..Arithmetic::default()
        },
        vec![value],
        values(128, 1024),
        WorkBudget::default(),
        Some(ledger.clone()),
    )
    .err()
    .unwrap();
    assert!(
        matches!(refusal.error,RuntimeError::Backend(e) if e.code=="independent-value-refusal")
    );
    assert_eq!(ledger.snapshot().live_reserved_bytes, 128);
    drop(first);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}

#[test]
fn concurrently_live_runners_share_atomic_instruction_policy() {
    let program = program();
    let ledger = ExecutionLedger::new(values(256, 4096), work(3, 100, 4096));
    let barrier = Arc::new(Barrier::new(2));
    let terminals = Arc::new(Mutex::new(Vec::new()));
    std::thread::scope(|scope| {
        for _ in 0..2 {
            let (program, ledger, barrier, terminals) =
                (&program, &ledger, barrier.clone(), terminals.clone());
            scope.spawn(move || {
                let mut runner = local(program, ledger);
                barrier.wait();
                let returned = matches!(runner.execute(), Action::Returned(_));
                terminals.lock().unwrap().push(returned);
                // Both runner allowances remain reserved until both executions
                // reach this barrier, including a successful terminal tuple.
                barrier.wait();
            });
        }
    });
    assert!(terminals.lock().unwrap().iter().filter(|r| **r).count() <= 1);
    assert_eq!(ledger.snapshot().instructions, 3);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}

#[test]
fn shared_iterations_do_not_reset_for_a_successive_loop() {
    let program = program();
    let ledger = ExecutionLedger::new(values(2048, 32768), work(100, 3, 32768));
    for attempt in 0..2 {
        let mut runner = LocalRunner::new_with_ledger(
            &program,
            "repeat",
            "session",
            Arithmetic::default(),
            vec![
                Number::Index(0),
                Number::Index(2),
                Number::Field(1),
                Number::Field(2),
            ],
            values(2048, 8192),
            work(100, 100, 8192),
            Some(ledger.clone()),
        )
        .ok()
        .unwrap();
        if attempt == 0 {
            assert!(matches!(runner.execute(),Action::Returned(v) if v==&[Number::Field(5)]));
        } else {
            assert!(
                matches!(runner.execute(),Action::Stopped(s) if s.kind==StopKind::Limit
                && s.origin.path==[PathElement::For {site:"loop".into(),index:1}])
            );
            assert_eq!(runner.backend().calls, 1);
        }
    }
    assert_eq!(ledger.snapshot().iterations, 3);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}

#[test]
fn shared_literals_refuse_before_construction_when_the_bound_will_not_fit() {
    let program = decode(module(
        json!([function(
            "literal",
            json!([]),
            json!([BOOL]),
            json!([["bool_constant", "constant", "b", false], ["return", ["b"]]])
        )]),
        json!([]),
        json!([]),
    ));
    let ledger = ExecutionLedger::new(values(1024, 0), work(100, 100, 0));
    let mut runner = LocalRunner::new_with_ledger(
        &program,
        "literal",
        "session",
        Arithmetic::default(),
        vec![],
        values(1024, 1024),
        work(100, 100, 0),
        Some(ledger.clone()),
    )
    .ok()
    .unwrap();
    assert!(matches!(runner.execute(),Action::Stopped(s) if s.kind==StopKind::Limit));
    assert_eq!(ledger.snapshot().total_value_bytes, 0);
    assert_eq!(ledger.snapshot().pending_value_bytes, 0);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    // A false source result remains data, and literal construction uses no
    // logical operand/result charge in the existing VM contract.
    let ledger = ExecutionLedger::new(values(1024, 1024), work(100, 100, 0));
    let mut runner = LocalRunner::new_with_ledger(
        &program,
        "literal",
        "session",
        Arithmetic::default(),
        vec![],
        values(1024, 1024),
        work(100, 100, 0),
        Some(ledger.clone()),
    )
    .ok()
    .unwrap();
    assert!(matches!(runner.execute(),Action::Returned(v) if v==&[Number::Bool(false)]));
    assert_eq!(ledger.snapshot().logical_bytes, 0);
}

#[test]
fn installation_checks_every_potential_branch_of_the_selected_function() {
    let source = function(
        "branch",
        json!([["c", BOOL], ["x", FIELD], ["y", FIELD]]),
        json!([FIELD]),
        json!([
            [
                "if",
                "condition",
                "c",
                ["x", "y"],
                [["yield", ["x"]]],
                [
                    ["op", "dormant", "multiply", [], ["x", "y"], ["z"]],
                    ["yield", ["z"]]
                ],
                ["out"]
            ],
            ["return", ["out"]]
        ]),
    );
    let mut source = module(json!([source]), json!([]), json!([]));
    let program = decode(source.clone());
    assert_eq!(
        program
            .check_local_installation("branch", &Arithmetic::default())
            .unwrap_err()
            .code,
        ErrorCode::Backend
    );
    assert!(
        LocalRunner::new(
            &program,
            "branch",
            "session",
            Arithmetic::default(),
            vec![Number::Bool(true), Number::Field(1), Number::Field(2)]
        )
        .is_err()
    );
    // Dormant malformed SSA still fails eager structure admission, before any
    // root-specific installation or value-dependent branch selection.
    source[2][0][4][0][5][0][4] = json!(["undefined", "y"]);
    assert_eq!(
        Program::decode(&serde_json::to_vec(&source).unwrap())
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
}

#[test]
fn failed_allocating_hooks_keep_committed_work_and_drop_live_reservations() {
    let program = program();
    let ledger = ExecutionLedger::new(values(128, 256), work(100, 100, 256));
    let mut runner = LocalRunner::new_with_ledger(
        &program,
        "add_root",
        "session",
        Arithmetic {
            fail_apply: true,
            ..Arithmetic::default()
        },
        vec![Number::Field(1), Number::Field(2)],
        values(128, 256),
        work(100, 100, 256),
        Some(ledger.clone()),
    )
    .ok()
    .unwrap();
    assert!(
        matches!(runner.execute(),Action::Stopped(s) if matches!(&s.kind,StopKind::Backend(e) if e.code=="partial-operation"))
    );
    let used = ledger.snapshot();
    assert!(used.total_value_bytes > 32); // conservative failed-hook allocation allowance
    assert!(used.logical_bytes > 16);
    assert_eq!(used.pending_value_bytes, 0);
    assert_eq!(used.pending_logical_bytes, 0);
    assert_eq!(used.live_reserved_bytes, 0);
    drop(runner);
    assert_eq!(ledger.snapshot(), used);
}

#[test]
fn ledger_overflow_and_host_retention_are_checked_atomically() {
    let ledger = ExecutionLedger::new(
        values(usize::MAX, usize::MAX),
        work(u64::MAX, u64::MAX, u64::MAX),
    );
    let held = ledger.reserve_live(usize::MAX).unwrap();
    assert!(matches!(ledger.reserve_live(1), Err(RuntimeError::Limit)));
    ledger.charge(work(u64::MAX, 0, 0), usize::MAX).unwrap();
    let before = ledger.snapshot();
    assert!(matches!(
        ledger.charge(work(1, 1, 1), 1),
        Err(RuntimeError::Limit)
    ));
    assert_eq!(ledger.snapshot(), before);
    drop(held);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    assert_eq!(ledger.snapshot().total_value_bytes, usize::MAX);
}

#[test]
fn terminal_reservation_and_successful_body_cleanup_failures_publish_no_outputs() {
    let program = program();
    for fail_leave in [false, true] {
        let ledger = ExecutionLedger::new(values(128, 4096), work(100, 100, 4096));
        let mut runner = LocalRunner::new_with_ledger(
            &program,
            "add_root",
            "session",
            Arithmetic {
                fail_leave,
                ..Arithmetic::default()
            },
            vec![Number::Field(1), Number::Field(2)],
            values(128, if fail_leave { 4096 } else { 40 }),
            work(100, 100, 4096),
            Some(ledger.clone()),
        )
        .ok()
        .unwrap();
        match runner.execute() {
            Action::Stopped(stop) if fail_leave => {
                assert!(matches!(&stop.kind,StopKind::Backend(e) if e.code=="cleanup:2"));
                assert_eq!(
                    stop.cleanup_errors
                        .iter()
                        .map(|e| e.code.as_str())
                        .collect::<Vec<_>>(),
                    ["cleanup:1"]
                );
            }
            Action::Stopped(stop) => assert_eq!(stop.kind, StopKind::Limit),
            other => panic!("expected stop, got {other:?}"),
        }
        assert!(runner.returned_values().is_none());
        assert_eq!(runner.usage().live_value_bytes, 0);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
        assert!(runner.backend().frames.is_empty());
    }
}

#[test]
fn pending_allocation_blocks_a_live_sibling_before_custody_and_effects() {
    let program = program();
    let ledger = ExecutionLedger::new(values(256, 64), work(100, 100, 32));
    let gate = Arc::new((Barrier::new(2), Barrier::new(2)));
    let mut first = LocalRunner::new_with_ledger(
        &program,
        "add_root",
        "first",
        Arithmetic {
            allocation_gate: Some(gate.clone()),
            ..Arithmetic::default()
        },
        vec![Number::Field(1), Number::Field(2)],
        values(128, 1024),
        work(100, 100, 1024),
        Some(ledger.clone()),
    )
    .ok()
    .unwrap();
    let mut second = local(&program, &ledger);
    std::thread::scope(|scope| {
        let running = scope.spawn(|| {
            assert!(matches!(first.execute(), Action::Returned(_)));
        });
        gate.0.wait();
        let pending = ledger.snapshot();
        assert_eq!(pending.total_value_bytes, 48);
        assert_eq!(pending.pending_value_bytes, 16);
        assert_eq!(pending.logical_bytes, 16);
        assert_eq!(pending.pending_logical_bytes, 16);
        assert!(matches!(
            ledger.charge(work(0, 0, 0), 1),
            Err(RuntimeError::Limit)
        ));
        assert!(matches!(
            ledger.charge(work(0, 0, 1), 0),
            Err(RuntimeError::Limit)
        ));
        assert!(matches!(second.execute(),Action::Stopped(s) if s.kind==StopKind::Limit));
        assert_eq!(second.backend().entered, [FrameKind::Entry]);
        assert_eq!(second.backend().calls, 0);
        gate.1.wait();
        running.join().unwrap();
    });
    assert_eq!(ledger.snapshot().total_value_bytes, 64);
    assert_eq!(ledger.snapshot().logical_bytes, 24);
    assert_eq!(ledger.snapshot().pending_value_bytes, 0);
    drop(first);
    drop(second);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}

#[test]
fn participant_runners_share_policy_and_refuse_independently_retained_preparation() {
    let participant = |symbol: &str, role: &str| {
        json!([
            "participant",
            symbol,
            "deployment",
            role,
            [["x", FIELD], ["y", FIELD]],
            [FIELD],
            [
                ["local", "call", "add_root", ["x", "y"], ["z"]],
                ["return", ["z"]]
            ],
            []
        ])
    };
    let program = decode(module(
        json!([add()]),
        json!([participant("p", "P"), participant("v", "V")]),
        json!([["entry", "joint", [["P", "p"], ["V", "v"]]]]),
    ));
    let ledger = ExecutionLedger::new(values(256, 4096), work(7, 100, 4096));
    let mut first = Runner::new_for_role_with_ledger(
        &program,
        "joint",
        "P",
        "session",
        Arithmetic::default(),
        vec![Number::Field(1), Number::Field(2)],
        values(128, 1024),
        WorkBudget::default(),
        Some(ledger.clone()),
    )
    .ok()
    .unwrap();
    let mut second = Runner::new_for_role_with_ledger(
        &program,
        "joint",
        "V",
        "session",
        Arithmetic::default(),
        vec![Number::Field(1), Number::Field(2)],
        values(128, 1024),
        WorkBudget::default(),
        Some(ledger.clone()),
    )
    .ok()
    .unwrap();
    let preparation = PreparedComputations::new(&program, PreparationLimits::default());
    assert!(matches!(first.prepare_computations(preparation,&[0,1]),
        Err(RuntimeError::Backend(e)) if e.code=="computation-preparation-context"));
    assert_eq!(ledger.snapshot().live_reserved_bytes, 256);
    let Action::Local(action) = first.poll() else {
        panic!("local")
    };
    first.execute_local(&action.cut).unwrap();
    assert!(matches!(first.poll(), Action::Returned(_)));
    let Action::Local(action) = second.poll() else {
        panic!("local")
    };
    second.execute_local(&action.cut).unwrap();
    assert!(matches!(second.poll(),Action::Stopped(s) if s.kind==StopKind::Limit));
    assert_eq!(ledger.snapshot().instructions, 7);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 128);
    let (backend, outputs) = first.into_retained_outputs();
    assert!(backend.frames.is_empty());
    assert_eq!(outputs.as_deref().unwrap(), &[Number::Field(3)]);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 128);
    drop(outputs);
    assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
}
