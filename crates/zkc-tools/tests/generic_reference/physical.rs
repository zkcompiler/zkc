//! Source-checked local plan accounting against the ordinary native runner.
//! Native observations supply no reference allocation decisions or math results.
use super::*;
use std::process::Command;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, PublicInputs};
use zkc_runtime::interactive::{
    Backend, BackendError, BoundSignature, Frame, FrameExit, Invocation, OperationBinding,
    Value as RuntimeValue,
};

struct PhysicalObserved {
    inner: Observed,
    steps: Vec<Json>,
}
impl Backend for PhysicalObserved {
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
        let record = json!([
            call.site,
            call.binding.declaration().contract,
            call.max_output_bytes.to_string()
        ]);
        self.steps.push(json!([
            "attempt",
            record,
            self.inner.inner.active_frames().to_string()
        ]));
        let result = self.inner.apply(call, args);
        if let Ok(values) = &result {
            for value in values {
                match value {
                    Value::Table(t) => {
                        assert_eq!(t.storage_capacity(), t.len(), "allocation premise")
                    }
                    Value::TableMsb(t) => {
                        assert_eq!(t.storage_capacity(), t.len(), "allocation premise")
                    }
                    _ => {}
                }
            }
            self.steps.push(json!([
                "completed",
                record,
                self.inner.inner.active_frames().to_string()
            ]));
        }
        result
    }
}

fn reference(fixture: &Fixture, inputs: &Json, storage: &Json, candidate: &[u8]) -> (bool, Json) {
    let directory = fixture.directory.path();
    std::fs::write(directory.join("physical.json"), candidate).unwrap();
    std::fs::write(
        directory.join("inputs.json"),
        serde_json::to_vec(inputs).unwrap(),
    )
    .unwrap();
    std::fs::write(
        directory.join("storage.json"),
        serde_json::to_vec(storage).unwrap(),
    )
    .unwrap();
    let result = Command::new(&fixture.checker_path)
        .arg("--physical-local-reference")
        .arg(directory.join("source.json"))
        .arg(directory.join("physical.json"))
        .arg(directory.join("inputs.json"))
        .arg(directory.join("storage.json"))
        .output()
        .unwrap();
    (
        result.status.success(),
        serde_json::from_slice(&result.stdout).unwrap_or_else(|_| {
            panic!(
                "{}{}",
                String::from_utf8_lossy(&result.stdout),
                String::from_utf8_lossy(&result.stderr)
            )
        }),
    )
}

fn compare(
    fixture: &Fixture,
    rank: usize,
    capacity: usize,
    budget: u64,
    allowed: bool,
    ceiling: usize,
) -> Json {
    compare_tape(fixture, rank, capacity, budget, allowed, ceiling, &[2])
}

fn compare_tape(
    fixture: &Fixture,
    rank: usize,
    capacity: usize,
    budget: u64,
    allowed: bool,
    ceiling: usize,
    tape: &[u64],
) -> Json {
    let policy = Policy {
        max_value_bytes: ceiling,
        ..Policy::default()
    };
    let mut backend = NativeBackend::new(
        policy,
        EntryPolicy::new(
            Domain::new("P", "test", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap();
    let rng = backend
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
    let untouched = backend
        .issue_test_tape(
            Domain::new("P", "test", "main", None),
            3,
            vec![Scalar::from(7)],
        )
        .unwrap();
    let Value::Rng(untouched) = untouched else {
        unreachable!()
    };
    let mut cells = Vec::new();
    cells.try_reserve_exact(capacity).unwrap();
    cells.extend((0..1u64 << rank).map(|i| Scalar::from(i * i)));
    // Capacity is supplied by the host, not inferred from a logical table.
    assert_eq!(cells.capacity(), capacity);
    let table = zkc_arkworks::Table::from_logical_vec(cells, &policy.ark_bounds()).unwrap();
    let values = vec![rng, Value::Table(table.into()), Value::Bool(allowed)];
    assert_eq!(values[1].retained_bytes(), 256 + 32 * capacity);
    let original = value_json(&values[1]);
    let ports: Vec<_> = ["rng", "table", "allowed"]
        .into_iter()
        .zip(&values)
        .map(|(name, value)| json!([name, value_json(value)]))
        .collect();
    let inputs = json!([
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
    ]);
    let storage = json!([
        "zkc.local-resources/1",
        ceiling.to_string(),
        [["table", capacity.to_string()]]
    ]);
    // This case is 8190 draws, which is the fewest that cross the runner's
    // 16384 live values at two apiece, so its size is the limit's and not a
    // number anyone chose. Admitting a function that long takes the checker
    // longer than the default 120 seconds — the slowest call measured here was
    // 133 — and the whole case is about ten minutes across many calls. The
    // budget is a bound a healthy call cannot reach, not a target.
    let checker = ParticipantChecker::new(&fixture.checker_path)
        .unwrap()
        .with_timeout(std::time::Duration::from_secs(300));
    let admitted = admit_physical(&fixture.source, &fixture.candidate, &backend, &checker).unwrap();
    let trace = Trace::new(&fixture.source);
    let observed = PhysicalObserved {
        inner: Observed {
            inner: backend,
            source_map: admitted.source_map().unwrap().clone(),
            events: trace.clone(),
            conversions: 0,
        },
        steps: Vec::new(),
    };
    let mut runner = Runner::new(&admitted, "main", "P", "test", observed, values.clone())
        .unwrap_or_else(|e| panic!("{}", e.error));
    let terminal = loop {
        match runner.poll() {
            // A local-entry limit is also a terminal runner result.
            Action::Local(local) => {
                let _ = runner.execute_local(&local.cut);
            }
            action @ (Action::Returned(_) | Action::Stopped(_)) => break action,
            action => panic!("unexpected {action:?}"),
        }
    };
    let (success, result) = reference(fixture, &inputs, &storage, &fixture.candidate);
    assert!(success, "{result}");
    assert_eq!(result[0], "zkc.physical-reference/1");
    match terminal {
        Action::Returned(values) => assert_eq!(
            result[1],
            json!([
                "returned",
                values.iter().map(value_json).collect::<Vec<_>>()
            ])
        ),
        Action::Stopped(stop) => {
            match &stop.kind {
                StopKind::Backend(error) => {
                    let prefix = if result[1][0] == "reject" {
                        "rejected"
                    } else {
                        result[1][0].as_str().unwrap()
                    };
                    assert_eq!(
                        error.code,
                        format!("{prefix}:{}", result[1][1].as_str().unwrap())
                    );
                }
                StopKind::Limit => assert_eq!(result[1][0], "limit"),
                other => panic!("unexpected {other:?}"),
            }
            assert_eq!(stop.site.as_deref(), Some("step"));
            assert_stop_location(&trace, &stop, &result[1][2], true);
        }
        _ => unreachable!(),
    }
    assert_eq!(result[2], json!(trace.snapshot()));
    let usage = runner.usage();
    assert_eq!(
        result[4],
        json!([
            usage.instructions.to_string(),
            usage.live_values.to_string(),
            usage.live_value_bytes.to_string(),
            usage.total_value_bytes.to_string(),
            runner.backend().inner.inner.active_frames().to_string()
        ])
    );
    assert_eq!(result[5], json!(runner.backend().steps));
    assert_eq!(value_json(&values[1]), original);
    let actual = runner.backend().inner.inner.observe(&token).unwrap();
    assert_eq!(result[3][0][3], actual.generation.to_string());
    assert_eq!(result[3][0][4], actual.draw_count.to_string());
    assert_eq!(result[3][0][5], actual.budget.to_string());
    let other = runner.backend().inner.inner.observe(&untouched).unwrap();
    assert_eq!(
        (other.generation, other.draw_count, other.budget),
        (0, 0, 3)
    );
    assert_eq!(
        result[3][1],
        json!(["untouched", "P", [], "0", "0", "3", other.stage])
    );
    // Input metadata and the actual selected source relation are not optional.
    let mut wrong = storage.clone();
    wrong[2][0][1] = json!("0");
    assert_eq!(
        reference(fixture, &inputs, &wrong, &fixture.candidate),
        (false, json!(["refused", "physical-table-capacity"]))
    );
    wrong[2][0][1] = json!(((64 << 20) / 32).to_string());
    assert_eq!(
        reference(fixture, &inputs, &wrong, &fixture.candidate),
        (false, json!(["refused", "physical-table-capacity"]))
    );
    let mut changed: Json = serde_json::from_slice(&fixture.candidate).unwrap();
    let expected = if changed[3][0][4][0][0] == "op" {
        changed[3][0][4][0][3] = json!(["unexpected-attribute"]);
        // Physical formation is checked before source correspondence.
        "interactive-kernel-parameters"
    } else {
        changed[3][0][5][0] = json!("MismatchedDefinition");
        "source-local-unmatched"
    };
    assert_eq!(
        reference(
            fixture,
            &inputs,
            &storage,
            &serde_json::to_vec(&changed).unwrap()
        ),
        (false, json!(["refused", expected]))
    );
    result
}

#[test]
fn checked_local_plans_preserve_physical_failure_and_retained_state() {
    let fixture = Fixture::new();
    let ceiling = 64 << 20;
    for rank in 1..=4 {
        compare(&fixture, rank, 1 << rank, 2, true, ceiling);
        compare(&fixture, rank, (1 << rank) + 17, 2, true, ceiling);
    }
    compare(&fixture, 2, 4, 2, false, ceiling);
    compare(&fixture, 2, 4, 0, true, ceiling);
    compare(&fixture, 0, 1, 2, true, ceiling);
    // RNG output reservation fails after consumption, despite valid ingress.
    compare(&fixture, 2, 4, 2, true, 512);
    // Shared input capacity is charged at root and local entry. Leave 128 bytes
    // after the RNG result: the following real conversion fails before folding.
    let near_limit = ((64 << 20) - 2048 - 1024 - 128) / 2;
    compare(&fixture, 2, (near_limit - 256) / 32, 2, true, ceiling);
    // At the same budget, the direct LSB fold fits exactly. The MSB selection
    // needs a larger conversion first. Budget equivalence is not unconditional.
    let near_limit = ((64 << 20) - 2048 - 1024 - 320) / 2;
    let msb = compare(&fixture, 2, (near_limit - 256) / 32, 2, true, ceiling);
    assert_eq!(msb[1][0], "exhausted");
    let source = include_str!("../../../../tests/fixtures/generic-stops.pir")
        .replace("arkworks-msb/poly.fold", "arkworks/poly.fold");
    let lsb = Fixture::from_text(&source);
    let result = compare(&lsb, 2, (near_limit - 256) / 32, 2, true, ceiling);
    assert_eq!(result[1][0], "returned");
    // Root ingress fits but duplicating its args at local entry does not.
    let result = compare(&fixture, 2, (ceiling / 2 - 256) / 32, 2, true, ceiling);
    assert_eq!(result[1][0], "limit");
    compare_tape(&fixture, 2, 4, 2, true, ceiling, &[]);
    let identity = Fixture::from_text(&source.replace(
        "[draw] (r, next) = random.draw<F>(rng);\n    [guard] () = control.require<>(allowed);\n    [fold] (result) = poly.fold<F>(table, r);\n    return (result, next);",
        "return (table, rng);",
    ).replace("using (fold = \"arkworks/poly.fold\")", ""));
    let result = compare(&identity, 2, 21, 2, true, ceiling);
    assert_eq!(result[1][0], "returned");
}

/// The slowest test in this workspace, at about ten minutes, and the cost is
/// the subject rather than waste. Both implementations cap live values at
/// 16384 -- `Limits::LIVE_VALUES` in the runtime and the same number in the
/// reference's `PhysicalLocal` accounting -- so reaching the boundary means
/// each of them actually executing that many, and 8190 draws of two values is
/// the smallest source that crosses it. Shrinking the case would move the test
/// off the boundary, which is the only place the two can disagree.
#[test]
fn kernel_completion_precedes_live_value_retention() {
    // Each draw returns two values. The final backend call succeeds and consumes
    // its RNG before the runner refuses retaining values beyond its live limit.
    let count = 8190;
    let mut fixture = Fixture::new();
    let path = fixture.directory.path().join("source.json");
    let prepared = Fixture::compile(&fixture.compiler, "protocol-prepare", &path);
    let mut source: Json = serde_json::from_slice(&prepared).unwrap();
    // Explicitly bound source admits longer functions than the finite generic
    // requirement solver. This case exercises the same checked local executor.
    source[1] = json!([["draw", "random.draw", ["bls12-381.fr"], ""]]);
    let mut body = Vec::new();
    let mut input = "rng".to_string();
    for i in 0..count {
        let next = format!("n{i}");
        body.push(json!([
            "op",
            format!("d{i}"),
            "draw",
            [],
            [input],
            [format!("r{i}"), next]
        ]));
        input = next;
    }
    body.push(json!(["return", ["table", input]]));
    source[2][0][4] = json!(body);
    fixture.set_source(&source);
    let result = compare_tape(
        &fixture,
        0,
        1,
        count as u64,
        true,
        64 << 20,
        &vec![2; count],
    );
    assert_eq!(result[1][0], "limit");
    assert_eq!(result[3][0][4], count.to_string());
    assert_eq!(result[5].as_array().unwrap().len(), 2 * count);
}

#[test]
fn empty_local_uses_the_declared_participant_without_input_ports() {
    let fixture = Fixture::from_text(
        r#"module {
      fn Empty<>() -> () { return; }
      configure Run = Empty();
      protocol Main { roles(P); inputs(); outputs();
        local [step] P: Run(); return; }
      instance root: Main { roles(P=P); } entry main=root;
    }"#,
    );
    let checker = ParticipantChecker::new(&fixture.checker_path).unwrap();
    let inner = backend();
    let admitted = admit_physical(&fixture.source, &fixture.candidate, &inner, &checker).unwrap();
    let trace = Trace::new(&fixture.source);
    let observed = PhysicalObserved {
        inner: Observed {
            inner,
            source_map: admitted.source_map().unwrap().clone(),
            events: trace.clone(),
            conversions: 0,
        },
        steps: Vec::new(),
    };
    let mut runner = Runner::new(&admitted, "main", "P", "test", observed, vec![])
        .unwrap_or_else(|e| panic!("{}", e.error));
    let Action::Local(local) = runner.poll() else {
        panic!("expected local");
    };
    runner.execute_local(&local.cut).unwrap();
    let Action::Returned(values) = runner.poll() else {
        panic!("expected return");
    };
    assert!(values.is_empty());
    let (success, result) = reference(
        &fixture,
        &json!([
            "zkc.reference-inputs/1",
            "main",
            "test",
            [["P", []]],
            [],
            [],
            []
        ]),
        &json!(["zkc.local-resources/1", "67108864", []]),
        &fixture.candidate,
    );
    assert!(success, "{result}");
    assert_eq!(result[1], json!(["returned", []]));
    assert_eq!(result[2], json!(trace.snapshot()));
    assert_eq!(
        result[4],
        json!([
            runner.usage().instructions.to_string(),
            runner.usage().live_values.to_string(),
            runner.usage().live_value_bytes.to_string(),
            runner.usage().total_value_bytes.to_string(),
            runner.backend().inner.inner.active_frames().to_string()
        ])
    );
    assert_eq!(result[5], json!(runner.backend().steps));
}

#[test]
fn local_algorithm_linear_composition_matches_independent_physical_accounting() {
    let fixture = Fixture::from_fixture("local-linear.pir");
    // Two reused folds retain their actual intermediate allocation. Primitive
    // guards and failing second folds remain visible even when results die.
    for rank in 2..=5 {
        compare(&fixture, rank, 1 << rank, 2, true, 1 << 20);
    }
    compare(&fixture, 1, 2, 2, true, 1 << 20);
    compare(&fixture, 2, 4, 2, false, 1 << 20);
    compare(&fixture, 2, 4, 0, true, 1 << 20);
    compare_tape(&fixture, 2, 4, 2, true, 1 << 20, &[]);
    compare(&fixture, 2, 4, 2, true, 512);
}
