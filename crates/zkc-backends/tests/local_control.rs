mod common;
use common::*;
use serde_json::{Value as Json, json};
use zkc_backends::*;
use zkc_runtime::interactive::Identity;
use zkc_runtime::interactive::{
    Action, Backend, BackendError, ErrorCode, Frame, FrameExit, InstalledKernel, Invocation,
    Limits, OperationBinding, PathElement, Runner, StopKind, Usage, ValueBudget, admit_supplied,
};

fn candidate(ports: Json, outputs: Json, body: Json) -> Vec<u8> {
    fn physical(s: &str) -> String {
        use zkc_runtime::interactive::{LogicalType, PhysicalType};
        PhysicalType::default_for(LogicalType::parse(s).unwrap())
            .unwrap()
            .spelling()
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
        "zkc.program/0",
        bindings.into_values().collect::<Vec<_>>(),
        [["function", "local", ports, outputs, body, ["local", []]]],
        [[
            "participant",
            "root",
            "instance",
            "P",
            ports,
            outputs,
            [
                ["local", "run", "local", inputs, results],
                ["return", results]
            ],
            []
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
    prepared: std::cell::RefCell<Vec<OperationBinding>>,
    substitute: Option<OperationBinding>,
    fail_leave: Option<u64>,
    nondeterministic: Option<&'static str>,
}
impl Traced {
    fn new(inner: NativeBackend) -> Self {
        Self {
            inner,
            events: vec![],
            frames: vec![],
            blocked: None,
            prepared: Default::default(),
            substitute: None,
            fail_leave: None,
            nondeterministic: None,
        }
    }
}
struct TracedKernel {
    inner: NativeKernel,
    deterministic: bool,
}
impl InstalledKernel for TracedKernel {
    fn signature(&self) -> &zkc_runtime::interactive::BoundSignature {
        self.inner.signature()
    }
    fn deterministic(&self) -> bool {
        self.deterministic
    }
}
impl Backend for Traced {
    type Call = ();
    type Checkpoint = ComputationCheckpoint;
    fn supports_boolean_literals(&self) -> bool {
        self.inner.supports_boolean_literals()
    }
    fn computation_checkpoint(&self) -> Option<Self::Checkpoint> {
        self.inner.computation_checkpoint()
    }
    fn replay_computation(&mut self, before: Self::Checkpoint, after: Self::Checkpoint) -> bool {
        self.inner.replay_computation(before, after)
    }
    type Value = Value;
    type Kernel = TracedKernel;
    fn prepare_binding(&self, b: &OperationBinding) -> Option<Self::Kernel> {
        self.prepared.borrow_mut().push(b.clone());
        if self.blocked.as_deref() == Some(&b.contract) {
            None
        } else {
            self.inner.prepare_binding(b).map(|inner| TracedKernel {
                deterministic: inner.deterministic()
                    && self.nondeterministic != Some(b.contract.as_str()),
                inner,
            })
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
    fn apply(
        &mut self,
        kernel: &Self::Kernel,
        i: &Invocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>, BackendError> {
        self.events
            .push(json!([i.site, i.frame.origin().json(), i.domain_bytes()]));
        if let Some(binding) = &self.substitute {
            let other = self.inner.prepare_binding(binding).unwrap();
            return self.inner.apply(&other, i, args);
        }
        self.inner.apply(&kernel.inner, i, args)
    }
}
fn execute<B: Backend<Value = Value>>(
    mut r: Runner<B>,
) -> (Result<Vec<Value>, zkc_runtime::interactive::Stop>, Usage, B) {
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
    assert_eq!((u.instructions, u.iterations), (6, 0)); // local, if, op, yield, function return, participant return
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
        let rng = native
            .issue_rng_for(Identity::Bls12381Fr, domain(), budget)
            .unwrap();
        let outside = native
            .issue_rng_for(Identity::Bls12381Fr, domain(), 7)
            .unwrap();
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
    v[2][0][4][0][7][0][5] = json!([["yield", ["r"]]]);
    cases.push(v); // hidden free variable
    let mut v = good.clone();
    v[2][0][4][0][6] = json!(["cond", "r"]);
    cases.push(v); // affine invariant
    let mut v = good.clone();
    v[2][0][4][0][7][0][3] = json!(["current", "current"]);
    cases.push(v);
    let mut v = good.clone();
    v[2][0][4][0][7][0][5] = json!([["yield", []]]);
    cases.push(v);
    let mut v = good.clone();
    v[2][0][4][0][7][0][5] = json!([["return", ["current"]]]);
    cases.push(v);
    let mut v = good.clone();
    v[2][0][4][0][7][0][5] = json!([
        ["op", "draw", "random.draw", [], ["current"], ["v", "r2"]],
        ["yield", ["r2"]]
    ]);
    cases.push(v); // duplicate global site
    let mut v = good.clone();
    v[2][0][4][0][7][0][4] = json!([
        ["op", "draw", "random.draw", [], ["current"], ["v", "r2"]],
        ["yield", ["current"]]
    ]);
    cases.push(v);
    let mut v = good.clone();
    v[2][0][4][1] = json!(["return", ["r"]]);
    cases.push(v); // parent reuse after carried move
    let mut v = good.clone();
    v[2][0][4][0][7][0][5] = json!([]);
    cases.push(v);
    let mut v = good.clone();
    v[2][0][4][0][7][0][5] = json!([
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
    value[3][0][6][0] = value[2][0][4][0].clone();
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
    value[2][0][4][0][4]
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
fn local_region_depth_counts_every_active_native_frame() {
    for (depth, succeeds) in [(20, true), (62, false)] {
        let mut body = json!([["yield", ["ok"]]]);
        for i in 0..depth {
            body = json!([
                [
                    "if",
                    format!("branch{i}"),
                    "ok",
                    ["ok"],
                    body,
                    [["yield", ["ok"]]],
                    ["out"]
                ],
                ["yield", ["out"]]
            ]);
        }
        body.as_array_mut().unwrap().last_mut().unwrap()[0] = json!("return");
        let bytes = candidate(json!([["ok", "bool"]]), json!(["bool"]), body);
        if !succeeds {
            let error = admit_supplied(&bytes, &ark_backend(None)).unwrap_err();
            assert_eq!(error.code, ErrorCode::Limit);
            continue;
        }
        let (out, usage, backend) = execute(load(
            &bytes,
            Traced::new(ark_backend(None)),
            vec![Value::Bool(true)],
        ));
        assert!(out.is_ok());
        assert_eq!(backend.frames.len(), depth + 2);
        assert_eq!(usage.live_values, 1); // The returned Boolean remains owned.
        assert_eq!(backend.inner.active_frames(), 0);
    }
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
    let rng = native
        .issue_rng_for(Identity::Bls12381Fr, domain(), 0)
        .unwrap();
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

#[test]
fn bindings_are_prepared_once_per_owned_backend_not_per_iteration() {
    let bytes = sum_loop();
    let admitting = Traced::new(ark_backend(None));
    let admitted = admit_supplied(&bytes, &admitting).unwrap();
    assert_eq!(admitting.prepared.borrow().len(), 3);
    for count in [0, 1, 64] {
        let runner = Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            Traced::new(ark_backend(None)),
            vec![
                Value::Index(0),
                Value::Vector(vec![Scalar::from(1); count].into()),
                f(0),
            ],
        )
        .unwrap_or_else(|_| panic!("entry"));
        let (out, _, backend) = execute(runner);
        assert_eq!(scalar(&out.unwrap()[0]), Scalar::from(count as u64));
        assert_eq!(*backend.prepared.borrow(), *admitting.prepared.borrow());
        assert_eq!(backend.events.len(), 1 + 2 * count);
    }
    // Admitting with one backend does not authorize another backend's installation.
    let mut different = Traced::new(ark_backend(None));
    different.blocked = Some("field.add".into());
    let failure = Runner::new(&admitted, "main", "P", "session", different, vec![])
        .err()
        .expect("uninstalled binding");
    assert!(
        matches!(failure.error, zkc_runtime::interactive::RuntimeError::Admission(ref e)
        if e.code == ErrorCode::Backend)
    );
    assert!(failure.backend.frames.is_empty());
    assert!(failure.backend.events.is_empty());
}

#[test]
fn preparation_identity_includes_static_arguments_and_coalesces_declaration_aliases() {
    use zkc_runtime::interactive::{LogicalType, PhysicalType, Value as RuntimeValue};
    let types: Vec<_> = ["sequence<index>", "sequence<bool>"]
        .into_iter()
        .map(|s| PhysicalType::default_for(LogicalType::parse(s).unwrap()).unwrap())
        .collect();
    let bytes = serde_json::to_vec(&json!([
        "zkc.program/0",
        [
            [
                "first",
                "sequence.empty",
                ["index"],
                "native/sequence.empty"
            ],
            [
                "alias",
                "sequence.empty",
                ["index"],
                "native/sequence.empty"
            ],
            ["other", "sequence.empty", ["bool"], "native/sequence.empty"]
        ],
        [[
            "function",
            "make",
            [],
            [types[0].spelling(), types[1].spelling()],
            [
                ["op", "one", "first", [], [], ["unused"]],
                ["op", "two", "alias", [], [], ["indices"]],
                ["op", "three", "other", [], [], ["bools"]],
                ["return", ["indices", "bools"]]
            ],
            ["make", []]
        ]],
        [[
            "participant",
            "root",
            "instance",
            "P",
            [],
            [types[0].spelling(), types[1].spelling()],
            [
                ["local", "run", "make", [], ["a", "b"]],
                ["return", ["a", "b"]]
            ],
            []
        ]],
        [["entry", "main", [["P", "root"]]]]
    ]))
    .unwrap();
    let admitting = Traced::new(ark_backend(None));
    let admitted = admit_supplied(&bytes, &admitting).unwrap();
    assert_eq!(admitting.prepared.borrow().len(), 2);
    let runner = Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        Traced::new(ark_backend(None)),
        vec![],
    )
    .unwrap_or_else(|_| panic!("entry"));
    let (out, _, backend) = execute(runner);
    assert_eq!(
        out.unwrap()
            .iter()
            .map(RuntimeValue::physical_type)
            .collect::<Vec<_>>(),
        types
    );
    assert_eq!(backend.prepared.borrow().len(), 2);
    assert_eq!(backend.events.len(), 3);
}

#[test]
fn native_direct_call_refuses_a_handle_for_a_different_binding() {
    let mut backend = Traced::new(ark_backend(None));
    backend.substitute = Some(OperationBinding {
        contract: "bool.not".into(),
        arguments: vec![],
        implementation: "arkworks/bool.not".into(),
    });
    let (out, _, backend) = execute(load(
        &choose(),
        backend,
        vec![Value::Bool(true), Value::Bool(true)],
    ));
    assert_eq!(code(&out.unwrap_err()), "refused:kernel-binding");
    assert_eq!(backend.inner.active_frames(), 0);
}

#[test]
fn preparation_handles_terminal_branches_and_rejects_fabricated_results() {
    let bytes = candidate(
        json!([["c", "bool"]]),
        json!([]),
        json!([
            [
                "if",
                "choose",
                "c",
                [],
                [["stop", "left", "reject"]],
                [["stop", "right", "abort"]],
                []
            ],
            ["return", []]
        ]),
    );
    for (c, site) in [(true, "left"), (false, "right")] {
        let (result, _, backend) = execute(load(
            &bytes,
            Traced::new(ark_backend(None)),
            vec![Value::Bool(c)],
        ));
        assert_eq!(result.unwrap_err().site.as_deref(), Some(site));
        assert_eq!(backend.inner.active_frames(), 0);
    }
    let mut bad: Json = serde_json::from_slice(&bytes).unwrap();
    bad[2][0][4][0][6] = json!(["fabricated"]);
    assert_eq!(
        admit_supplied(&serde_json::to_vec(&bad).unwrap(), &ark_backend(None))
            .unwrap_err()
            .code,
        ErrorCode::Signature
    );
    let mut duplicate: Json = serde_json::from_slice(&bytes).unwrap();
    duplicate[2][0][2]
        .as_array_mut()
        .unwrap()
        .push(json!(["c", "bool@native.bool/0"]));
    assert_eq!(
        admit_supplied(&serde_json::to_vec(&duplicate).unwrap(), &ark_backend(None))
            .unwrap_err()
            .code,
        ErrorCode::Ssa
    );
}

#[test]
fn prepared_code_keeps_attributes_at_each_call_site() {
    let bytes = candidate(
        json!([]),
        json!(["field:bls12-381.fr", "field:bls12-381.fr"]),
        json!([
            ["op", "first", "field.constant", ["11"], [], ["a"]],
            ["op", "second", "field.constant", ["19"], [], ["b"]],
            ["return", ["a", "b"]]
        ]),
    );
    let backend = Traced::new(ark_backend(None));
    let admitted = admit_supplied(&bytes, &backend).unwrap();
    assert_eq!(backend.prepared.borrow().len(), 1);
    let runner = Runner::new(&admitted, "main", "P", "session", backend, vec![])
        .unwrap_or_else(|_| panic!("entry"));
    let (values, _, backend) = execute(runner);
    assert_eq!(
        values.unwrap().iter().map(scalar).collect::<Vec<_>>(),
        vec![Scalar::from(11), Scalar::from(19)]
    );
    // One preparation during admission and one on the owned runner backend.
    assert_eq!(backend.prepared.borrow().len(), 2);
}

#[test]
fn prepared_calls_match_checked_calls_at_repeated_sites_and_budget_failures() {
    // The same literal site is reached repeatedly before a later out-of-bounds
    // access. The untaken arm remains unexecuted; malformed literals are already refused
    // by admission.
    let program = candidate(
        json!([
            ["lo", "index"],
            ["hi", "index"],
            ["xs", "vector:bls12-381.fr"],
            ["ok", "bool"]
        ]),
        json!([]),
        json!([
            [
                "for",
                "repeat",
                "i",
                "lo",
                "hi",
                [],
                ["xs", "ok"],
                [
                    [
                        "if",
                        "branch",
                        "ok",
                        [],
                        [
                            [
                                "op",
                                "literal",
                                "field.constant",
                                ["123456789"],
                                [],
                                ["value"]
                            ],
                            ["yield", []]
                        ],
                        [
                            [
                                "op",
                                "alternative",
                                "field.constant",
                                ["999"],
                                [],
                                ["alternative_value"]
                            ],
                            ["yield", []]
                        ],
                        []
                    ],
                    ["op", "get", "vector.get", [], ["xs", "i"], ["item"]],
                    ["yield", []]
                ],
                []
            ],
            ["return", []]
        ]),
    );
    let admitted = admit_supplied(&program, &ark_backend(None)).unwrap();
    for (length, instructions, cumulative) in [
        (8, 1000, usize::MAX),
        (2, 1000, usize::MAX),
        (8, 14, usize::MAX),
        (8, 1000, 4000),
    ] {
        let inputs = vec![
            Value::Index(0),
            Value::Index(4),
            Value::Vector(vec![Scalar::from(7u64); length].into()),
            Value::Bool(true),
        ];
        let values = ValueBudget {
            total_bytes: cumulative,
            ..Default::default()
        };
        let work = zkc_runtime::interactive::WorkBudget {
            instructions,
            ..Default::default()
        };
        let prepared = Runner::new_with_budgets(
            &admitted,
            "main",
            "P",
            "session",
            ark_backend(None),
            inputs.clone(),
            values,
            work,
        )
        .unwrap_or_else(|e| panic!("{}", e.error));
        let checked = Runner::new_with_budgets(
            &admitted,
            "main",
            "P",
            "session",
            Traced::new(ark_backend(None)),
            inputs,
            values,
            work,
        )
        .unwrap_or_else(|e| panic!("{}", e.error));
        let (actual, actual_usage, backend) = execute(prepared);
        let (expected, expected_usage, checked) = execute(checked);
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        assert_eq!(actual_usage, expected_usage);
        assert_eq!(backend.active_frames(), 0);
        assert_eq!(checked.inner.active_frames(), 0);
    }
}

#[path = "local_control/preparation.rs"]
mod preparation;
