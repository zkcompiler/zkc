//! General control and cleanup contracts, using a noncryptographic backend.
use super::*;
use serde_json::{Value as Json, json};
const BOOL: &str = "bool@native.bool/0";
const INDEX: &str = "index@native.index/0";
const RNG: &str = "rng:bls12-381.fr@host.resource/0";
#[derive(Clone, Debug)]
struct Datum {
    ty: PhysicalType,
    value: u64,
}
impl Datum {
    fn new(ty: &str, value: u64) -> Self {
        Self {
            ty: PhysicalType::parse(ty).unwrap(),
            value,
        }
    }
}
impl Value for Datum {
    fn physical_type(&self) -> PhysicalType {
        self.ty.clone()
    }
    fn retained_bytes(&self) -> usize {
        1
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        Ok(())
    }
    fn control_bool(&self) -> Result<bool, BackendError> {
        Ok(self.value != 0)
    }
    fn control_index(&self) -> Result<u64, BackendError> {
        Ok(self.value)
    }
    fn from_control_index(value: u64) -> Result<Self, BackendError> {
        Ok(Self::new(INDEX, value))
    }
    fn from_control_bool(value: bool) -> Result<Self, BackendError> {
        Ok(Self::new(BOOL, u64::from(value)))
    }
}
#[derive(Default, Debug)]
struct Store {
    frames: Vec<u64>,
    entered: Vec<Frame>,
    leaves: Vec<(u64, FrameExit, Vec<u64>)>,
    fail: Option<u64>,
    queries: Vec<(String, String, Origin)>,
}
impl Backend for Store {
    type Call = ();
    type Checkpoint = ();
    type Value = Datum;
    type Operation = crate::vm::BoundSignature;
    fn supports_boolean_literals(&self) -> bool {
        true
    }
    fn validate_value(&self, _: &Datum) -> Result<(), BackendError> {
        Ok(())
    }
    fn enter_frame(&mut self, f: &Frame, _: &[Datum]) -> Result<(), BackendError> {
        self.frames.push(f.id().get());
        self.entered.push(f.clone());
        Ok(())
    }
    fn leave_frame(
        &mut self,
        f: &Frame,
        exit: FrameExit,
        values: &[Datum],
    ) -> Result<(), BackendError> {
        assert_eq!(self.frames.pop(), Some(f.id().get()));
        self.leaves
            .push((f.id().get(), exit, values.iter().map(|v| v.value).collect()));
        if self.fail == Some(f.id().get()) {
            Err(BackendError::new("injected-leave"))
        } else {
            Ok(())
        }
    }
    fn service_support(&self, contract: ServiceContract, method: &str) -> Option<ServiceSupport> {
        if contract != ServiceContract::RandomBls12381Field || method != "draw" {
            return None;
        }
        Some(ServiceSupport {
            signature: ServiceSignature {
                inputs: vec![],
                outputs: vec![PhysicalType::parse("field:bls12-381.fr@arkworks.fr/0").unwrap()],
            },
            max_retained_bytes: 1,
        })
    }
    fn query(
        &mut self,
        invocation: &ServiceInvocation<'_>,
        _: &[Datum],
    ) -> Result<Vec<Datum>, BackendError> {
        self.queries.push((
            invocation.port.name.clone(),
            invocation.site.into(),
            invocation.frame.origin().clone(),
        ));
        Ok(vec![Datum::new("field:bls12-381.fr@arkworks.fr/0", 99)])
    }
    fn apply(
        &mut self,
        _operation: &Self::Operation,
        _: &Invocation<'_>,
        _: &[Datum],
    ) -> Result<Vec<Datum>, BackendError> {
        panic!("unreached kernel")
    }
}
fn artifact(body: Json, functions: Json) -> Json {
    json!([
        "zkc.program/0",
        [],
        functions,
        [[
            "participant",
            "p",
            "root",
            "P",
            [["c", BOOL], ["n", INDEX], ["r", RNG]],
            [BOOL, RNG],
            body,
            []
        ]],
        [["entry", "main", [["P", "p"]]]]
    ])
}
fn body(nested: bool) -> Json {
    if !nested {
        return json!([
            ["return_if", "exit", "c", ["c", "r"], ["next"]],
            ["return", ["c", "next"]]
        ]);
    }
    json!([
        [
            "loop",
            "outer",
            ["value", "n", "4", "i"],
            [["outer_r", "r"]],
            [["c", "c"], ["n", "n"]],
            [
                [
                    "loop",
                    "inner",
                    ["value", "n", "4", "j"],
                    [["inner_r", "outer_r"]],
                    [["c", "c"]],
                    [
                        ["return_if", "exit", "c", ["c", "inner_r"], ["next"]],
                        ["yield", ["next"]]
                    ],
                    ["inner_out"]
                ],
                ["yield", ["inner_out"]]
            ],
            ["out"]
        ],
        ["return", ["c", "out"]]
    ])
}
fn runner(nested: bool, taken: bool, fail: Option<u64>, total: usize) -> Runner<Store> {
    let store = Store {
        fail,
        ..Store::default()
    };
    let admitted = crate::vm::Program::decode(
        &serde_json::to_vec(&artifact(body(nested), json!([]))).unwrap(),
        &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
    )
    .and_then(|program| {
        program.check_installation(&store)?;
        Ok(program)
    })
    .unwrap();
    Runner::new_with_value_budget(
        &admitted,
        "main",
        "P",
        "test",
        store,
        vec![
            Datum::new(BOOL, u64::from(taken)),
            Datum::new(INDEX, 3),
            Datum::new(RNG, 7),
        ],
        ValueBudget {
            live_bytes: 1000,
            total_bytes: total,
        },
    )
    .unwrap()
}

#[test]
fn participant_frames_use_admitted_loop_ports_and_reject_mistyped_captures() {
    use crate::vm::{instance::Instance, retention::Retention};
    let mut source = body(true);
    source[0][4] = json!([["n", "n"], ["c", "c"]]); // preserve declared order, not lexical order
    let program = Program::decode(
        &serde_json::to_vec(&artifact(source, json!([]))).unwrap(),
        &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
    )
    .unwrap();
    let ports = |site| {
        program
            .loop_inputs("p", site)
            .iter()
            .map(|(name, ty)| (name.as_str(), ty.clone()))
            .collect::<Vec<_>>()
    };
    let typed = |name, ty| (name, PhysicalType::parse(ty).unwrap());
    assert_eq!(
        ports("outer"),
        [
            typed("i", INDEX),
            typed("outer_r", RNG),
            typed("n", INDEX),
            typed("c", BOOL)
        ]
    );
    assert_eq!(
        ports("inner"),
        [typed("j", INDEX), typed("inner_r", RNG), typed("c", BOOL)]
    );
    let mut loaded = Instance::load(
        &program,
        "main",
        "P",
        "session",
        Store::default(),
        vec![
            Datum::new(BOOL, 0),
            Datum::new(INDEX, 3),
            Datum::new(RNG, 7),
        ],
        ValueBudget::default(),
        WorkBudget::default(),
    )
    .ok()
    .unwrap();
    let mut origin = loaded.frame.origin().clone();
    origin.path.push(PathElement::Loop {
        site: "outer".into(),
        iteration: 0,
    });
    let frame = loaded.instance.loop_frame(origin, "outer", 0);
    assert_eq!(
        frame.inputs().iter().cloned().collect::<Vec<_>>(),
        program
            .loop_inputs("p", "outer")
            .iter()
            .cloned()
            .collect::<Vec<_>>()
    );
    let usage = loaded.instance.usage();
    let wrong = [
        Datum::new(INDEX, 0),
        Datum::new(RNG, 7),
        Datum::new(BOOL, 0),
        Datum::new(INDEX, 3),
    ];
    assert!(matches!(
        loaded
            .instance
            .enter_root(&frame, &wrong, Retention::Transfer),
        Err(RuntimeError::Payload)
    ));
    assert_eq!(loaded.instance.usage(), usage);
    assert_eq!(loaded.instance.backend().frames, [loaded.frame.id().get()]);
    loaded
        .instance
        .leave_frame(&loaded.frame, FrameExit::Cancelled, &[])
        .unwrap();
    loaded
        .instance
        .close_scope(loaded.scope, loaded.inputs.iter());

    // Continue through every iteration with reordered captures. All actual
    // backend entries must observe the admitted layout, including later trips.
    let mut runner = Runner::new(
        &program,
        "main",
        "P",
        "session",
        Store::default(),
        vec![
            Datum::new(BOOL, 0),
            Datum::new(INDEX, 3),
            Datum::new(RNG, 7),
        ],
    )
    .unwrap();
    while runner.advance_local_control().unwrap() {}
    assert!(matches!(runner.poll(), Action::Returned(_)));
    assert_eq!(runner.usage().iterations, 12);
    assert_eq!(runner.backend().entered.len(), 13);
    for frame in &runner.backend().entered {
        if let FrameKind::Loop { site, .. } = frame.kind() {
            assert_eq!(frame.inputs(), program.loop_inputs("p", site));
        }
    }
}

#[test]
fn distinct_loop_formals_can_capture_the_same_copy_value() {
    let source = json!([
        "zkc.program/0",
        [],
        [],
        [[
            "participant",
            "p",
            "root",
            "P",
            [["c", BOOL], ["n", INDEX]],
            [BOOL, BOOL],
            [
                [
                    "loop",
                    "repeat",
                    ["value", "n", "4", "i"],
                    [["a", "c"], ["b", "c"]],
                    [["left", "c"], ["right", "c"]],
                    [["yield", ["left", "right"]]],
                    ["first", "second"]
                ],
                ["return", ["first", "second"]]
            ],
            []
        ]],
        [["entry", "main", [["P", "p"]]]]
    ]);
    let decode = |source: &Json| {
        Program::decode(
            &serde_json::to_vec(source).unwrap(),
            &Contracts::standard(ExecutionPolicy::general_purpose()),
        )
    };
    let program = decode(&source).unwrap();
    assert_eq!(program.loop_inputs("p", "repeat").len(), 5);
    for n in [0, 3] {
        for c in [0, 1] {
            let mut runner = Runner::new(
                &program,
                "main",
                "P",
                "session",
                Store::default(),
                vec![Datum::new(BOOL, c), Datum::new(INDEX, n)],
            )
            .unwrap();
            while runner.advance_local_control().unwrap() {}
            assert!(
                matches!(runner.poll(), Action::Returned(_)),
                "n={n}, c={c}: {:?}",
                runner.stop()
            );
            assert_eq!(
                runner
                    .returned_values()
                    .unwrap()
                    .iter()
                    .map(|v| v.value)
                    .collect::<Vec<_>>(),
                [c, c]
            );
            assert_eq!(runner.usage().iterations, n);
            for frame in &runner.backend().entered {
                if let FrameKind::Loop { .. } = frame.kind() {
                    assert_eq!(frame.inputs(), program.loop_inputs("p", "repeat"));
                }
            }
        }
    }
    for captures in [
        json!(["c"]), // retired format has no fallback
        json!([["left", "c"], ["left", "c"]]),
        json!([["i", "c"]]),
        json!([["left", "missing"]]),
    ] {
        let mut invalid = source.clone();
        invalid[3][0][6][0][4] = captures;
        assert!(decode(&invalid).is_err());
    }
}

#[test]
fn conditional_return_preserves_tuple_and_unwinds_only_reached_frames() {
    for nested in [false, true] {
        let mut r = runner(nested, true, None, 1000);
        while r.advance_local_control().unwrap() {}
        assert_eq!(
            r.returned_values()
                .unwrap()
                .iter()
                .map(|v| v.value)
                .collect::<Vec<_>>(),
            [1, 7]
        );
        assert_eq!(r.usage().iterations, if nested { 2 } else { 0 });
        if let Some(counts) = r.execution_counts().json() {
            let e = &counts["events"];
            assert_eq!(e["charged_instructions"], r.usage().instructions);
            assert_eq!(e["backend_enter_calls"], if nested { 3 } else { 1 });
            assert_eq!(e["backend_leave_calls"], e["backend_enter_calls"]);
            assert_eq!(
                e["retention_commit_values"].as_u64().unwrap(),
                e["retention_release_values"].as_u64().unwrap()
                    + e["retention_unpin_values"].as_u64().unwrap()
                    + r.usage().live_values as u64
            );
        }
        let (origin, site) = r.early_return().unwrap();
        assert_eq!(site, "exit");
        assert_eq!(origin.path.len(), if nested { 2 } else { 0 });
        assert_eq!(r.backend().leaves.len(), if nested { 3 } else { 1 });
        assert!(r.backend().frames.is_empty());
        for (_, exit, values) in &r.backend().leaves {
            assert_eq!(*exit, FrameExit::Returned);
            assert_eq!(values, &[1, 7]);
        }
    }
}
#[test]
fn continuing_resources_stay_single_use_and_controls_are_explicit() {
    let mut r = runner(false, false, None, 1000);
    let usage = r.usage();
    let origin = r.root_origin().clone();
    assert!(matches!(
        r.inspect_program().unwrap(),
        ProgramState::ReturnIf { site: "exit" }
    ));
    assert_eq!(r.return_if(&origin, "wrong"), Err(RuntimeError::WrongCut));
    assert_eq!(r.usage(), usage);
    r.return_if(&origin, "exit").unwrap();
    assert!(matches!(r.poll(), Action::Returned(_)));
    assert!(r.early_return().is_none());
    let mut invalid = artifact(body(false), json!([]));
    invalid[3][0][6][1][1][1] = json!("r");
    assert!(
        crate::vm::Program::decode(
            &serde_json::to_vec(&invalid).unwrap(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
        )
        .and_then(|program| {
            program.check_installation(&Store::default())?;
            Ok(program)
        })
        .is_err()
    );
    let mut r = runner(false, true, None, 1000);
    assert!(matches!(r.poll(), Action::Stopped(_))); // poll must not silently cross control
}
#[test]
fn early_return_failures_never_publish_outputs() {
    for failure in [1, 2, 3] {
        let mut r = runner(true, true, Some(failure), 1000);
        while r.advance_local_control().unwrap() {}
        assert!(r.returned_values().is_none());
        assert!(r.early_return().is_none());
        assert!(matches!(r.stop().unwrap().kind, StopKind::Backend(_)));
        assert!(r.backend().frames.is_empty());
        assert_eq!(r.backend().leaves.len(), 3);
        assert_eq!(r.stop().unwrap().site.as_deref(), Some("exit"));
    }
    let mut r = runner(false, true, None, 3); // inputs fit, root result retention does not
    r.advance_local_control().unwrap();
    assert!(matches!(r.stop().unwrap().kind, StopKind::Limit));
    assert!(r.returned_values().is_none());
    assert!(r.backend().frames.is_empty());
    assert_eq!(r.backend().leaves[0].1, FrameExit::Stopped);
}
#[test]
fn bounded_local_condition_skips_unreached_iterations() {
    for conditional in [false, true] {
        let functions = json!([[
            "function",
            "search",
            [["lo", INDEX], ["hi", INDEX], ["state", RNG]],
            [RNG],
            [
                [
                    if conditional { "for_while" } else { "for" },
                    "search",
                    "i",
                    "lo",
                    "hi",
                    [["r", "state"]],
                    [],
                    [
                        ["bool_constant", "done", "no", false],
                        [
                            "yield",
                            if conditional {
                                vec!["no", "r"]
                            } else {
                                vec!["r"]
                            }
                        ]
                    ],
                    ["out"]
                ],
                ["return", ["out"]]
            ],
            ["search", []]
        ]]);
        let mut program = artifact(
            json!([
                ["local", "search", "search", ["n", "hi", "r"], ["out"]],
                ["return", ["c", "out"]]
            ]),
            functions,
        );
        program[3][0][4]
            .as_array_mut()
            .unwrap()
            .push(json!(["hi", INDEX]));
        let admitted = crate::vm::Program::decode(
            &serde_json::to_vec(&program).unwrap(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
        )
        .and_then(|program| {
            program.check_installation(&Store::default())?;
            Ok(program)
        })
        .unwrap();
        for upper in [0, 1, 4] {
            let mut r = Runner::new_with_budgets(
                &admitted,
                "main",
                "P",
                "test",
                Store::default(),
                vec![
                    Datum::new(BOOL, 1),
                    Datum::new(INDEX, 0),
                    Datum::new(RNG, 7),
                    Datum::new(INDEX, upper),
                ],
                ValueBudget::default(),
                WorkBudget {
                    iterations: 1,
                    ..WorkBudget::default()
                },
            )
            .unwrap();
            let Action::Local(local) = r.poll() else {
                panic!("local")
            };
            r.execute_local(&local.cut).unwrap();
            if conditional || upper <= 1 {
                let Action::Returned(values) = r.poll() else {
                    panic!("expected loop result")
                };
                assert_eq!(values[1].value, 7);
            } else {
                assert!(matches!(r.stop().unwrap().kind, StopKind::Limit));
            }
            assert_eq!(r.usage().iterations, u64::from(upper > 0));
        }
        if conditional {
            let mut changed = program.clone();
            changed[2][0][4][0][7][1][1] = json!(["r"]);
            assert!(
                crate::vm::Program::decode(
                    &serde_json::to_vec(&changed).unwrap(),
                    &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
                )
                .and_then(|program| {
                    program.check_installation(&Store::default())?;
                    Ok(program)
                })
                .is_err()
            );
            changed = program.clone();
            changed[2][0][4][0][7][1][1] = json!(["i", "r"]);
            assert!(
                crate::vm::Program::decode(
                    &serde_json::to_vec(&changed).unwrap(),
                    &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
                )
                .and_then(|program| {
                    program.check_installation(&Store::default())?;
                    Ok(program)
                })
                .is_err()
            );
            changed = program.clone();
            changed[2][0][4][0][7] = json!([["stop", "halt", "abort"]]);
            let error = crate::vm::Program::decode(
                &serde_json::to_vec(&changed).unwrap(),
                &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
            )
            .and_then(|program| {
                program.check_installation(&Store::default())?;
                Ok(program)
            })
            .unwrap_err();
            assert!(error.to_string().contains("local-control-yield"));
            changed = program.clone();
            changed[0] = json!("invalid.program");
            assert!(
                crate::vm::Program::decode(
                    &serde_json::to_vec(&changed).unwrap(),
                    &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
                )
                .and_then(|program| {
                    program.check_installation(&Store::default())?;
                    Ok(program)
                })
                .is_err()
            );
        }
    }
}

#[test]
fn false_exits_preserve_iterations_and_malformed_records_refuse() {
    let mut r = runner(true, false, None, 1000);
    while r.advance_local_control().unwrap() {}
    assert!(matches!(r.poll(), Action::Returned(_)));
    assert_eq!(r.usage().iterations, 12);
    assert!(r.early_return().is_none());
    for tag in ["invalid.program", ""] {
        let mut program = artifact(body(false), json!([]));
        program[0] = json!(tag);
        assert!(
            crate::vm::Program::decode(
                &serde_json::to_vec(&program).unwrap(),
                &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
            )
            .and_then(|program| {
                program.check_installation(&Store::default())?;
                Ok(program)
            })
            .is_err()
        );
    }
    for changed in [
        json!(["return_if", "exit", "n", ["c", "r"], ["next"]]),
        json!(["return_if", "exit", "c", ["r", "c"], ["next"]]),
        json!(["return_if", "exit", "c", ["c", "r"], []]),
        json!(["return_if", "exit", "c", ["c", "r"], ["r"]]),
    ] {
        let mut program = artifact(body(false), json!([]));
        program[3][0][6][0] = changed;
        assert!(
            crate::vm::Program::decode(
                &serde_json::to_vec(&program).unwrap(),
                &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
            )
            .and_then(|program| {
                program.check_installation(&Store::default())?;
                Ok(program)
            })
            .is_err()
        );
    }
}

#[test]
fn extra_participant_fields_and_malformed_instructions_refuse() {
    let base = artifact(body(false), json!([]));
    for parameters in [json!([["n", "2"]]), json!([["n", ["ingress", "8", []]]])] {
        let mut program = base.clone();
        program[3][0].as_array_mut().unwrap().insert(4, parameters);
        let error = crate::vm::Program::decode(
            &serde_json::to_vec(&program).unwrap(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
        )
        .and_then(|program| {
            program.check_installation(&Store::default())?;
            Ok(program)
        })
        .unwrap_err();
        assert_eq!(error.code, ErrorCode::Record);
    }
    for instruction in [
        json!(["call", "child", "other", [], []]),
        json!(["loop", "fixed", "2", [], [], [["yield", []]], []]),
        json!(["loop", "parameterized", "n", [], [], [["yield", []]], []]),
        json!(["incomplete", "end"]),
    ] {
        let mut program = base.clone();
        program[3][0][6] = json!([instruction, ["return", []]]);
        assert!(
            crate::vm::Program::decode(
                &serde_json::to_vec(&program).unwrap(),
                &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
            )
            .and_then(|program| {
                program.check_installation(&Store::default())?;
                Ok(program)
            })
            .is_err()
        );
    }
}

#[test]
fn participant_branch_transfers_exact_resources_and_cleanup_outcomes() {
    let body = json!([
        [
            "if",
            "selected",
            "c",
            [["c", "c"], ["r", "r"], ["s", "s"]],
            [["yield", ["c", "s", "r"]]],
            [["yield", ["c", "r", "s"]]],
            ["b", "first", "second"]
        ],
        ["return", ["b", "first", "second"]]
    ]);
    let artifact = json!([
        "zkc.program/0",
        [],
        [],
        [[
            "participant",
            "p",
            "root",
            "P",
            [["c", BOOL], ["r", RNG], ["s", RNG]],
            [BOOL, RNG, RNG],
            body,
            []
        ]],
        [["entry", "main", [["P", "p"]]]]
    ]);
    let program = Program::decode(
        artifact.to_string().as_bytes(),
        &Contracts::standard(ExecutionPolicy::general_purpose()),
    )
    .unwrap();
    // Capture rows transfer an affine parent at most once; only Copy parents
    // may bind several formals.
    let mut repeated = artifact.clone();
    repeated[3][0][6][0][3] = json!([["c", "c"], ["r", "r"], ["s", "r"]]);
    let refused = Program::decode(
        repeated.to_string().as_bytes(),
        &Contracts::standard(ExecutionPolicy::general_purpose()),
    )
    .unwrap_err();
    assert!(
        refused.detail.contains("interactive-resource-reuse"),
        "{refused:?}"
    );
    for selected in [false, true] {
        for cleanup_failure in [false, true] {
            let store = Store {
                fail: cleanup_failure.then_some(2),
                ..Store::default()
            };
            let mut runner = Runner::new(
                &program,
                "main",
                "P",
                "resource_branch",
                store,
                vec![
                    Datum::new(BOOL, u64::from(selected)),
                    Datum::new(RNG, 7),
                    Datum::new(RNG, 9),
                ],
            )
            .unwrap();
            assert!(runner.advance_local_control().unwrap());
            assert!(runner.advance_local_control().unwrap());
            if cleanup_failure {
                assert!(runner.stop().is_some());
                assert!(runner.returned_values().is_none());
                let leaves = runner.backend().leaves.len();
                assert!(matches!(runner.poll(), Action::Stopped(_)));
                assert_eq!(runner.backend().leaves.len(), leaves);
            } else {
                let Action::Returned(values) = runner.poll() else {
                    panic!("selected tuple")
                };
                assert_eq!(
                    values.iter().map(|v| v.value).collect::<Vec<_>>(),
                    if selected {
                        vec![1, 9, 7]
                    } else {
                        vec![0, 7, 9]
                    }
                );
            }
            assert_eq!(runner.backend().entered.len(), 2);
            assert!(
                matches!(runner.backend().entered[1].kind(),FrameKind::Branch {alternative,..} if alternative==if selected {"then"} else {"else"})
            );
        }
    }
    let mut malformed = artifact;
    malformed[3][0][6][0][5][0][1] = json!(["c", "r", "r"]);
    assert_eq!(
        Program::decode(
            malformed.to_string().as_bytes(),
            &Contracts::standard(ExecutionPolicy::general_purpose())
        )
        .unwrap_err()
        .code,
        ErrorCode::Ssa
    );
}

#[test]
fn dormant_participant_query_stop_and_allocation_are_never_reached() {
    let artifact = json!([
        "zkc.program/0",
        [],
        [[
            "function",
            "poison",
            [],
            [],
            [["stop", "reject_here", "reject"]],
            ["poison", []]
        ]],
        [[
            "participant",
            "p",
            "root",
            "P",
            [["c", BOOL]],
            [],
            [
                [
                    "if",
                    "selected",
                    "c",
                    [],
                    [
                        ["query", "draw_here", "random", "draw", [], ["drawn"]],
                        ["local", "poison_here", "poison", [], []],
                        ["yield", []]
                    ],
                    [["yield", []]],
                    []
                ],
                ["return", []]
            ],
            [["random", "random.bls12-381.fr/0", "1"]]
        ]],
        [["entry", "main", [["P", "p"]]]]
    ]);
    let program = Program::decode(
        artifact.to_string().as_bytes(),
        &Contracts::standard(ExecutionPolicy::general_purpose()),
    )
    .unwrap();
    for selected in [false, true] {
        let mut runner = Runner::new_for_role_with_ledger(
            &program,
            "main",
            "P",
            "query_branch",
            Store::default(),
            vec![Datum::new(BOOL, u64::from(selected))],
            ValueBudget::default(),
            WorkBudget::default(),
            None,
        )
        .unwrap();
        assert!(runner.advance_local_control().unwrap());
        if selected {
            let Action::Query(query) = runner.poll() else {
                panic!("selected query")
            };
            runner.execute_query(&query.cut).unwrap();
            let Action::Local(local) = runner.poll() else {
                panic!("selected local")
            };
            runner.execute_local(&local.cut).unwrap();
            assert!(matches!(runner.stop().unwrap().kind, StopKind::Explicit(_)));
            assert_eq!(runner.backend().queries.len(), 1);
            assert_eq!(runner.backend().queries[0].0, "random");
        } else {
            assert!(runner.advance_local_control().unwrap());
            assert!(matches!(runner.poll(), Action::Returned(_)));
            assert!(runner.backend().queries.is_empty());
            assert_eq!(runner.backend().entered.len(), 2); // no dormant Local frame
        }
    }
    let mut bad = artifact;
    bad[3][0][6][0][4][0][2] = json!("manufactured_root");
    assert_eq!(
        Program::decode(
            bad.to_string().as_bytes(),
            &Contracts::standard(ExecutionPolicy::general_purpose())
        )
        .unwrap_err()
        .code,
        ErrorCode::Symbol
    );
}
