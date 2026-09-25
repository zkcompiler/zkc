mod common;
use common::*;
use serde_json::{Value as Json, json};
use zkc_backends::*;
use zkc_runtime::interactive::{
    Action, Backend, BackendError, BoundSignature, ErrorCode, Frame, FrameExit, Invocation, Limits,
    OperationBinding, PathElement, Runner, StopKind, Usage, ValueBudget, admit_supplied,
};

fn candidate(ports: Json, outputs: Json, body: Json) -> Vec<u8> {
    fn physical(s: &str) -> String {
        use zkc_runtime::interactive::{LogicalType, PhysicalType};
        PhysicalType::default_for(LogicalType::parse(s).unwrap()).spelling()
    }
    let ports: Vec<_> = ports
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], physical(p[1].as_str().unwrap())]))
        .collect();
    let outputs: Vec<_> = outputs
        .as_array()
        .unwrap()
        .iter()
        .map(|t| json!(physical(t.as_str().unwrap())))
        .collect();
    let inputs: Vec<_> = ports.iter().map(|p| p[0].clone()).collect();
    let results: Vec<_> = (0..outputs.len()).map(|i| format!("result{i}")).collect();
    let mut bindings = std::collections::BTreeMap::new();
    fn gather(body: &Json, bindings: &mut std::collections::BTreeMap<String, Json>) {
        for op in body.as_array().unwrap() {
            match op[0].as_str().unwrap() {
                "op" => {
                    let name = op[2].as_str().unwrap();
                    let args = if name.starts_with("index.")
                        || name.starts_with("bool.")
                        || name.starts_with("control.")
                    {
                        json!([])
                    } else {
                        json!(["bls12-381.fr"])
                    };
                    bindings.insert(
                        name.into(),
                        json!([name, name, args, format!("arkworks/{name}")]),
                    );
                }
                "if" => {
                    gather(&op[4], bindings);
                    gather(&op[5], bindings);
                }
                "for" => gather(&op[7], bindings),
                _ => {}
            }
        }
    }
    gather(&body, &mut bindings);
    serde_json::to_vec(&json!([
        "zkc.participants/1",
        bindings.into_values().collect::<Vec<_>>(),
        "physical",
        [["function", "local", ports, outputs, body, ["local", []]]],
        [[
            "participant",
            "root",
            "instance",
            "P",
            [],
            ports,
            outputs,
            [
                ["local", "run", "local", inputs, results],
                ["return", results]
            ]
        ]],
        [["entry", "main", [["P", "root"]]]]
    ]))
    .unwrap()
}

struct Traced {
    inner: NativeBackend,
    events: Vec<Json>,
    frames: Vec<(u64, Option<u64>)>,
    blocked: Option<String>,
    fail_leave: Option<u64>,
}
impl Traced {
    fn new(inner: NativeBackend) -> Self {
        Self {
            inner,
            events: vec![],
            frames: vec![],
            blocked: None,
            fail_leave: None,
        }
    }
}
impl Backend for Traced {
    type Value = Value;
    fn binding_signature(&self, b: &OperationBinding) -> Option<BoundSignature> {
        if self.blocked.as_deref() == Some(&b.contract) {
            None
        } else {
            self.inner.binding_signature(b)
        }
    }
    fn validate_value(&self, v: &Value) -> Result<(), BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, args: &[Value]) -> Result<(), BackendError> {
        self.inner.enter_frame(f, args)?;
        self.frames
            .push((f.id().get(), f.parent().map(|id| id.get())));
        Ok(())
    }
    fn leave_frame(&mut self, f: &Frame, e: FrameExit, v: &[Value]) -> Result<(), BackendError> {
        self.inner.leave_frame(f, e, v)?;
        if self.fail_leave == Some(f.id().get()) {
            Err(BackendError::new("test:cleanup"))
        } else {
            Ok(())
        }
    }
    fn apply(&mut self, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>, BackendError> {
        self.events
            .push(json!([i.site, i.frame.origin().json(), i.domain_bytes()]));
        self.inner.apply(i, args)
    }
}
fn execute(
    mut r: Runner<Traced>,
) -> (
    Result<Vec<Value>, zkc_runtime::interactive::Stop>,
    Usage,
    Traced,
) {
    loop {
        match r.poll() {
            Action::Local(a) => r.execute_local(&a.cut).unwrap(),
            Action::Returned(v) => {
                let u = r.usage();
                return (Ok(v), u, r.into_backend());
            }
            Action::Stopped(s) => {
                let u = r.usage();
                return (Err(s), u, r.into_backend());
            }
            other => panic!("unexpected {other:?}"),
        }
    }
}
fn choose() -> Vec<u8> {
    candidate(
        json!([["cond", "bool"], ["ok", "bool"]]),
        json!(["bool"]),
        json!([
            [
                "if",
                "choose",
                "cond",
                ["ok"],
                [
                    ["op", "selected", "control.require", [], ["ok"], []],
                    ["yield", ["ok"]]
                ],
                [
                    ["op", "unselected", "bool.not", [], ["ok"], ["bad"]],
                    ["op", "dead_guard", "control.require", [], ["bad"], []],
                    ["yield", ["bad"]]
                ],
                ["answer"]
            ],
            ["return", ["answer"]]
        ]),
    )
}
#[test]
fn selected_branch_only_guards_and_exact_accounting() {
    let (out, u, b) = execute(load(
        &choose(),
        Traced::new(ark_backend(None)),
        vec![Value::Bool(true), Value::Bool(true)],
    ));
    assert!(matches!(out.unwrap()[0], Value::Bool(true)));
    assert_eq!((u.instructions, u.iterations, u.calls), (6, 0, 0)); // local, if, op, yield, function return, participant return
    assert_eq!(b.events.len(), 1);
    assert_eq!(b.events[0][0], "selected");
    assert_eq!(b.events[0][1][4], json!([["if", "choose", "then"]]));
    assert_eq!(b.frames, vec![(1, None), (2, Some(1)), (3, Some(2))]);
    assert_eq!(b.inner.active_frames(), 0);
    let (out, _, b) = execute(load(
        &choose(),
        Traced::new(ark_backend(None)),
        vec![Value::Bool(false), Value::Bool(true)],
    ));
    let stop = out.unwrap_err();
    assert_eq!(code(&stop), "rejected:require");
    assert_eq!(stop.site.as_deref(), Some("dead_guard"));
    assert_eq!(
        stop.origin.path,
        vec![PathElement::Conditional {
            site: "choose".into(),
            taken: false
        }]
    );
    assert_eq!(b.events.len(), 2);
    assert_eq!(b.inner.active_frames(), 0);
}
fn sum_loop() -> Vec<u8> {
    candidate(
        json!([
            ["lo", "index"],
            ["xs", "vector:bls12-381.fr"],
            ["zero", "field:bls12-381.fr"]
        ]),
        json!(["field:bls12-381.fr"]),
        json!([
            ["op", "length", "vector.length", [], ["xs"], ["hi"]],
            [
                "for",
                "sum",
                "i",
                "lo",
                "hi",
                [["acc", "zero"]],
                ["xs"],
                [
                    ["op", "get", "vector.get", [], ["xs", "i"], ["item"]],
                    ["op", "add", "field.add", [], ["acc", "item"], ["next"]],
                    ["yield", ["next"]]
                ],
                ["out"]
            ],
            ["return", ["out"]]
        ]),
    )
}
#[test]
fn input_length_driven_loop_zero_inverted_and_ordered_effects() {
    let bytes = sum_loop();
    for (lo, xs, total, trips) in [
        (0, vec![], 0, 0),
        (3, vec![4, 5], 0, 0),
        (1, vec![4, 5, 6], 11, 2),
    ] {
        let values = xs.into_iter().map(Scalar::from).collect::<Vec<_>>();
        let (out, u, b) = execute(load(
            &bytes,
            Traced::new(ark_backend(None)),
            vec![Value::Index(lo), Value::Vector(values.into()), f(0)],
        ));
        assert_eq!(scalar(&out.unwrap()[0]), Scalar::from(total));
        assert_eq!(u.iterations, trips);
        assert_eq!(u.instructions, 5 + 3 * trips);
        assert_eq!(b.frames.len(), 2 + trips as usize);
        for (offset, e) in b.events.iter().skip(1).enumerate() {
            assert_eq!(
                e[1][4],
                json!([["for", "sum", (lo + offset as u64 / 2).to_string()]])
            );
        }
        assert_eq!(b.inner.active_frames(), 0);
    }
}
fn random_loop() -> Vec<u8> {
    candidate(
        json!([
            ["cond", "bool"],
            ["lo", "index"],
            ["hi", "index"],
            ["r", "rng:bls12-381.fr"]
        ]),
        json!(["rng:bls12-381.fr"]),
        json!([
            [
                "for",
                "random_loop",
                "i",
                "lo",
                "hi",
                [["current", "r"]],
                ["cond"],
                [
                    [
                        "if",
                        "choose_rng",
                        "cond",
                        ["current"],
                        [
                            [
                                "op",
                                "draw",
                                "random.draw",
                                [],
                                ["current"],
                                ["value", "next"]
                            ],
                            ["yield", ["next"]]
                        ],
                        [["yield", ["current"]]],
                        ["chosen"]
                    ],
                    ["yield", ["chosen"]]
                ],
                ["final"]
            ],
            ["return", ["final"]]
        ]),
    )
}
#[test]
fn affine_rng_selected_once_each_iteration_and_exhaustion_unwinds() {
    for (condition, budget, hi, draws, success) in [
        (true, 3, 3, 3, true),
        (false, 0, 3, 0, true),
        (true, 1, 3, 2, false),
    ] {
        let mut native = ark_backend(None);
        let rng = native.issue_rng(domain(), budget).unwrap();
        let outside = native.issue_rng(domain(), 7).unwrap();
        let before = native.observe(token(&outside)).unwrap();
        let (out, u, b) = execute(load(
            &random_loop(),
            Traced::new(native),
            vec![
                Value::Bool(condition),
                Value::Index(0),
                Value::Index(hi),
                rng.clone(),
            ],
        ));
        assert_eq!(out.is_ok(), success);
        assert_eq!(b.inner.observe(token(&rng)).unwrap().draw_count, draws);
        assert_eq!(b.inner.observe(token(&outside)).unwrap(), before);
        assert_eq!(b.inner.active_frames(), 0);
        assert_eq!(b.events.len(), draws as usize);
        if success {
            assert_eq!(u.iterations, hi);
        } else {
            assert_eq!(code(&out.unwrap_err()), "exhausted:resource-budget");
        }
        for pair in b.events.windows(2) {
            assert_ne!(pair[0][2], pair[1][2]);
        }
    }
}
#[test]
fn malformed_dead_regions_and_affine_copy_are_rejected() {
    let good: Json = serde_json::from_slice(&random_loop()).unwrap();
    let backend = ark_backend(None);
    let mut cases = vec![];
    let mut v = good.clone();
    v[3][0][4][0][7][0][5] = json!([["yield", ["r"]]]);
    cases.push(v); // hidden free variable
    let mut v = good.clone();
    v[3][0][4][0][6] = json!(["cond", "r"]);
    cases.push(v); // affine invariant
    let mut v = good.clone();
    v[3][0][4][0][7][0][3] = json!(["current", "current"]);
    cases.push(v);
    let mut v = good.clone();
    v[3][0][4][0][7][0][5] = json!([["yield", []]]);
    cases.push(v);
    let mut v = good.clone();
    v[3][0][4][0][7][0][5] = json!([["return", ["current"]]]);
    cases.push(v);
    let mut v = good.clone();
    v[3][0][4][0][7][0][5] = json!([
        ["op", "draw", "random.draw", [], ["current"], ["v", "r2"]],
        ["yield", ["r2"]]
    ]);
    cases.push(v); // duplicate global site
    let mut v = good.clone();
    v[3][0][4][0][7][0][4] = json!([
        ["op", "draw", "random.draw", [], ["current"], ["v", "r2"]],
        ["yield", ["current"]]
    ]);
    cases.push(v);
    let mut v = good.clone();
    v[3][0][4][1] = json!(["return", ["r"]]);
    cases.push(v); // parent reuse after carried move
    let mut v = good.clone();
    v[3][0][4][0][7][0][5] = json!([]);
    cases.push(v);
    let mut v = good.clone();
    v[3][0][4][0][7][0][5] = json!([
        ["op", "unresolved", "missing", [], [], []],
        ["yield", ["current"]]
    ]);
    cases.push(v);
    for (i, v) in cases.iter().enumerate() {
        assert!(
            admit_supplied(&serde_json::to_vec(v).unwrap(), &backend).is_err(),
            "mutation {i}"
        );
    }
    // An unsupported implementation hidden in the else branch is still checked.
    let mut v = good;
    v[1][0][3] = json!("missing/random.draw");
    assert!(admit_supplied(&serde_json::to_vec(&v).unwrap(), &backend).is_err());
}
#[test]
fn dynamic_bound_and_iteration_exhaustion_are_finite() {
    let bytes = candidate(
        json!([["lo", "index"], ["hi", "index"]]),
        json!([]),
        json!([
            [
                "for",
                "bounded",
                "i",
                "lo",
                "hi",
                [],
                [],
                [["yield", []]],
                []
            ],
            ["return", []]
        ]),
    );
    for (lo, hi, iterations) in [
        (Limits::PARAMETER + 1, 0, 0),
        (0, Limits::PARAMETER + 1, 0),
        (0, Limits::ITERATIONS + 1, Limits::ITERATIONS),
    ] {
        let (out, u, b) = execute(load(
            &bytes,
            Traced::new(ark_backend(None)),
            vec![Value::Index(lo), Value::Index(hi)],
        ));
        let stop = out.unwrap_err();
        if lo > Limits::PARAMETER || hi > Limits::PARAMETER {
            assert_eq!(code(&stop), "exhausted:local-bound-limit");
        } else {
            assert_eq!(stop.kind, StopKind::Limit);
            assert_eq!(
                stop.origin.path.last(),
                Some(&PathElement::For {
                    site: "bounded".into(),
                    index: Limits::ITERATIONS
                })
            );
        }
        assert_eq!(u.iterations, iterations);
        assert_eq!(b.inner.active_frames(), 0);
    }
}
#[test]
fn finite_value_budget_refuses_region_entry_without_open_frame_leak() {
    let bytes = choose();
    let b = Traced::new(ark_backend(None));
    let admitted = admit_supplied(&bytes, &b).unwrap();
    let runner = Runner::new_with_value_budget(
        &admitted,
        "main",
        "P",
        "session",
        b,
        vec![Value::Bool(true), Value::Bool(true)],
        ValueBudget {
            live_bytes: 2048,
            total_bytes: 10000,
        },
    )
    .unwrap_or_else(|_| panic!("entry"));
    let (out, _, b) = execute(runner);
    assert_eq!(out.unwrap_err().kind, StopKind::Limit);
    assert_eq!(b.inner.active_frames(), 0);
    assert_eq!(b.frames.len(), 2);
}
#[test]
fn local_control_is_not_admitted_in_protocol_body() {
    let mut value: Json = serde_json::from_slice(&choose()).unwrap();
    value[4][0][7][0] = value[3][0][4][0].clone();
    assert_eq!(
        admit_supplied(&serde_json::to_vec(&value).unwrap(), &ark_backend(None))
            .unwrap_err()
            .code,
        ErrorCode::Record
    );
}

#[test]
fn region_storage_release_keeps_ghost_charge_and_final_return_charge() {
    let bytes = candidate(
        json!([["b", "bool"]]),
        json!(["bool"]),
        json!([
            [
                "if",
                "branch",
                "b",
                ["b"],
                [
                    ["op", "not1", "bool.not", [], ["b"], ["n"]],
                    ["release", ["n"]],
                    ["yield", ["b"]]
                ],
                [["yield", ["b"]]],
                ["answer"]
            ],
            ["return", ["answer"]]
        ]),
    );
    let (out, u, b) = execute(load(
        &bytes,
        Traced::new(ark_backend(None)),
        vec![Value::Bool(true)],
    ));
    assert!(out.is_ok());
    assert_eq!(u.instructions, 6); // release costs zero
    assert_eq!(
        (u.live_values, u.live_value_bytes, u.total_value_bytes),
        (1, 512, 7 * 512)
    );
    assert_eq!(b.inner.active_frames(), 0);
    // Parent + local args + capture + temporary = 2048. A second temporary
    // cannot exploit physical release to evade the conservative semantic budget.
    let mut value: Json = serde_json::from_slice(&bytes).unwrap();
    value[3][0][4][0][4]
        .as_array_mut()
        .unwrap()
        .insert(2, json!(["op", "not2", "bool.not", [], ["b"], ["m"]]));
    let bytes = serde_json::to_vec(&value).unwrap();
    let b = Traced::new(ark_backend(None));
    let admitted = admit_supplied(&bytes, &b).unwrap();
    let r = Runner::new_with_value_budget(
        &admitted,
        "main",
        "P",
        "session",
        b,
        vec![Value::Bool(true)],
        ValueBudget {
            live_bytes: 2048,
            total_bytes: 10000,
        },
    )
    .unwrap_or_else(|_| panic!());
    let (out, u, b) = execute(r);
    assert!(out.is_err());
    assert_eq!(u.live_values, 0);
    assert_eq!(u.live_value_bytes, 0);
    assert_eq!(b.inner.active_frames(), 0);
}

#[test]
fn local_region_depth_includes_participant_call_frames() {
    let mut value: Json = serde_json::from_slice(&choose()).unwrap();
    let root = value[4][0].clone();
    let count = 62;
    let mut participants = vec![];
    for i in 0..count {
        let mut p = root.clone();
        p[1] = json!(format!("p{i}"));
        p[2] = json!(format!("instance{i}"));
        if i + 1 < count {
            p[7][0] = json!([
                "call",
                "next",
                format!("p{}", i + 1),
                ["cond", "ok"],
                ["result0"]
            ]);
        }
        participants.push(p);
    }
    value[4] = json!(participants);
    value[5][0][2][0][1] = json!("p0");
    let bytes = serde_json::to_vec(&value).unwrap();
    let (out, _, b) = execute(load(
        &bytes,
        Traced::new(ark_backend(None)),
        vec![Value::Bool(true), Value::Bool(true)],
    ));
    assert!(out.is_ok()); // 62 participant + local + region = 64
    assert_eq!(b.frames.len(), Limits::STACK_DEPTH);
    let mut value: Json = serde_json::from_slice(&bytes).unwrap();
    value[3][0][4][0][4] = json!([
        [
            "if",
            "nested",
            "ok",
            ["ok"],
            [["yield", ["ok"]]],
            [["yield", ["ok"]]],
            ["result"]
        ],
        ["yield", ["result"]]
    ]);
    let (out, u, b) = execute(load(
        &serde_json::to_vec(&value).unwrap(),
        Traced::new(ark_backend(None)),
        vec![Value::Bool(true), Value::Bool(true)],
    ));
    assert_eq!(out.unwrap_err().kind, StopKind::Limit);
    assert_eq!(b.frames.len(), Limits::STACK_DEPTH);
    assert_eq!(u.live_values, 0);
    assert_eq!(b.inner.active_frames(), 0);
}

#[test]
fn instruction_exhaustion_does_not_execute_suffix_or_next_iteration() {
    let mut body = vec![];
    for i in 0..11 {
        body.push(json!([
            "op",
            format!("guard{i}"),
            "control.require",
            [],
            ["ok"],
            []
        ]));
    }
    body.push(json!(["yield", []]));
    let bytes = candidate(
        json!([["lo", "index"], ["hi", "index"], ["ok", "bool"]]),
        json!([]),
        json!([
            ["for", "bounded", "i", "lo", "hi", [], ["ok"], body, []],
            ["return", []]
        ]),
    );
    // Run directly without storing one million trace/domain byte records.
    let mut r = load(
        &bytes,
        ark_backend(None),
        vec![
            Value::Index(0),
            Value::Index(Limits::ITERATIONS),
            Value::Bool(true),
        ],
    );
    let Action::Local(a) = r.poll() else { panic!() };
    r.execute_local(&a.cut).unwrap();
    let Action::Stopped(s) = r.poll() else {
        panic!()
    };
    assert_eq!(s.kind, StopKind::Limit);
    assert_eq!(r.usage().instructions, Limits::INSTRUCTIONS);
    assert!(r.usage().iterations < Limits::ITERATIONS);
    assert_eq!(r.usage().live_values, 0);
    assert_eq!(r.into_backend().active_frames(), 0);
}

#[test]
fn recursive_installation_inventory_and_reinstallation_cover_nested_operations() {
    let bytes = random_loop();
    let admitted = admit_supplied(&bytes, &ark_backend(None)).unwrap();
    let roles = admitted.executable_implementation_roles("main").unwrap();
    assert_eq!(
        roles["arkworks/random.draw"].iter().collect::<Vec<_>>(),
        vec!["P"]
    );
    let mut backend = Traced::new(ark_backend(None));
    backend.blocked = Some("random.draw".into());
    assert_eq!(
        admit_supplied(&bytes, &backend).unwrap_err().code,
        ErrorCode::Backend
    );
    match Runner::new(&admitted, "main", "P", "session", backend, vec![]) {
        Ok(_) => panic!("reinstallation ignored nested operation"),
        Err(e) => {
            assert!(matches!(
                e.error,
                zkc_runtime::interactive::RuntimeError::Admission(_)
            ));
            assert_eq!(e.backend.inner.active_frames(), 0);
        }
    }
}

#[test]
fn nested_cleanup_failure_is_recorded_without_hiding_consumed_rng_exhaustion() {
    let mut native = ark_backend(None);
    let rng = native.issue_rng(domain(), 0).unwrap();
    let mut b = Traced::new(native);
    b.fail_leave = Some(4); // entry/local/for/if
    let (out, u, b) = execute(load(
        &random_loop(),
        b,
        vec![
            Value::Bool(true),
            Value::Index(0),
            Value::Index(1),
            rng.clone(),
        ],
    ));
    let stop = out.unwrap_err();
    assert_eq!(code(&stop), "exhausted:resource-budget");
    assert_eq!(stop.cleanup_errors, vec![BackendError::new("test:cleanup")]);
    assert_eq!(b.inner.observe(token(&rng)).unwrap().draw_count, 1);
    assert_eq!(b.inner.active_frames(), 0);
    assert_eq!(u.live_values, 0);
}
