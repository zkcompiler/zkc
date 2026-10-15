use super::*;
use zkc_runtime::interactive::{Admitted, PreparationLimits, PreparedComputations, WorkBudget};

fn generated() -> Vec<u8> {
    candidate(
        json!([["n", "index"], ["x", "field:bls12-381.fr"]]),
        json!(["vector:bls12-381.fr", "vector:bls12-381.fr"]),
        json!([
            ["op", "fill", "vector.fill", [], ["x", "n"], ["xs"]],
            ["return", ["xs", "xs"]]
        ]),
    )
}
fn invoke(
    admitted: &Admitted,
    cache: &PreparedComputations<NativeBackend>,
    backend: NativeBackend,
    args: Vec<Value>,
    public: &[usize],
    values: ValueBudget,
    work: WorkBudget,
) -> (
    Result<Vec<Value>, zkc_runtime::interactive::Stop>,
    Usage,
    NativeBackend,
) {
    let mut runner = Runner::new_with_budgets(
        admitted, "main", "P", "session", backend, args, values, work,
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    runner.prepare_computations(cache.clone(), public).unwrap();
    execute(runner)
}
#[test]
fn reusable_outputs_preserve_aliases_and_every_usage_counter() {
    let admitted = admit_supplied(&generated(), &ark_backend(None)).unwrap();
    let cache = PreparedComputations::new(&admitted, PreparationLimits::default());
    for n in [0, 4, 33] {
        let run = || {
            invoke(
                &admitted,
                &cache,
                ark_backend(None),
                vec![Value::Index(n), f(7)],
                &[0, 1],
                Default::default(),
                Default::default(),
            )
        };
        let hits = cache.stats().hits;
        let (cold, cold_usage, cold_backend) = run();
        let (warm, warm_usage, warm_backend) = run();
        let cold = cold.unwrap();
        let warm = warm.unwrap();
        for (a, b) in cold.iter().zip(&warm) {
            let (Value::Vector(a), Value::Vector(b)) = (a, b) else {
                panic!("vector result")
            };
            assert_eq!(a, b);
        }
        let [Value::Vector(a), Value::Vector(b)] = warm.as_slice() else {
            panic!("two vectors")
        };
        assert!(std::sync::Arc::ptr_eq(a, b));
        assert_eq!(cold_usage, warm_usage);
        assert_eq!(cache.stats().hits, hits + 1);
        assert_eq!(cold_backend.active_frames(), 0);
        assert_eq!(warm_backend.active_frames(), 0);
    }
    assert_eq!(cache.stats().entries, 3);
}
#[test]
fn reduced_capacity_reexecutes_and_preserves_partial_failures() {
    let bytes = generated();
    let admitted = admit_supplied(&bytes, &ark_backend(None)).unwrap();
    let cache = PreparedComputations::new(&admitted, PreparationLimits::default());
    let args = || vec![Value::Index(32), f(7)];
    let (_, full, _) = invoke(
        &admitted,
        &cache,
        ark_backend(None),
        args(),
        &[0, 1],
        Default::default(),
        Default::default(),
    );
    assert_eq!(cache.stats().entries, 1);
    for (values, work) in [
        (
            ValueBudget {
                live_bytes: 1024,
                ..Default::default()
            },
            WorkBudget::default(),
        ),
        (
            ValueBudget {
                total_bytes: full.total_value_bytes - 1,
                ..Default::default()
            },
            WorkBudget::default(),
        ),
        (
            ValueBudget::default(),
            WorkBudget {
                instructions: 1,
                ..Default::default()
            },
        ),
        (
            ValueBudget::default(),
            WorkBudget {
                logical_bytes: full.logical_bytes - 1,
                ..Default::default()
            },
        ),
    ] {
        let (cached, usage, backend) = invoke(
            &admitted,
            &cache,
            ark_backend(None),
            args(),
            &[0, 1],
            values,
            work,
        );
        let empty = PreparedComputations::new(
            &admitted,
            PreparationLimits {
                entries: 0,
                bytes: 0,
            },
        );
        let (uncached, original_usage, original_backend) = invoke(
            &admitted,
            &empty,
            ark_backend(None),
            args(),
            &[0, 1],
            values,
            work,
        );
        assert!(cached.is_err());
        assert_eq!(cached.unwrap_err(), uncached.unwrap_err());
        assert_eq!(usage, original_usage);
        assert_eq!(backend.active_frames(), original_backend.active_frames());
        assert_eq!(backend.active_frames(), 0);
    }
    assert_eq!(cache.stats().hits, 0);
}
#[test]
fn private_inputs_changed_policy_and_other_programs_cannot_reuse() {
    let admitted = admit_supplied(&generated(), &ark_backend(None)).unwrap();
    let cache = PreparedComputations::new(&admitted, PreparationLimits::default());
    let args = || vec![Value::Index(8), f(3)];
    invoke(
        &admitted,
        &cache,
        ark_backend(None),
        args(),
        &[0, 1],
        Default::default(),
        Default::default(),
    )
    .0
    .unwrap();
    invoke(
        &admitted,
        &cache,
        ark_backend(None),
        args(),
        &[0],
        Default::default(),
        Default::default(),
    )
    .0
    .unwrap();
    let policy = Policy {
        max_table_elements: 4,
        ..Default::default()
    };
    assert!(
        invoke(
            &admitted,
            &cache,
            backend().policy(policy).build(),
            args(),
            &[0, 1],
            Default::default(),
            Default::default()
        )
        .0
        .is_err()
    );
    assert_eq!(cache.stats().hits, 0);
    let other = admit_supplied(&generated(), &ark_backend(None)).unwrap();
    let mut runner = Runner::new(&other, "main", "P", "session", ark_backend(None), args())
        .unwrap_or_else(|e| panic!("{}", e.error));
    assert!(
        runner
            .prepare_computations(cache, &[0, 1])
            .unwrap_err()
            .to_string()
            .contains("computation-preparation-context")
    );
    runner.cancel();
    assert_eq!(runner.into_backend().active_frames(), 0);
}
#[test]
fn bounded_storage_and_concurrent_invocations() {
    let admitted = admit_supplied(&generated(), &ark_backend(None)).unwrap();
    let disabled = PreparedComputations::new(
        &admitted,
        PreparationLimits {
            entries: 20,
            bytes: 1,
        },
    );
    invoke(
        &admitted,
        &disabled,
        ark_backend(None),
        vec![Value::Index(8), f(2)],
        &[0, 1],
        Default::default(),
        Default::default(),
    )
    .0
    .unwrap();
    assert_eq!(disabled.stats().entries, 0);
    let cache = PreparedComputations::new(
        &admitted,
        PreparationLimits {
            entries: 1,
            bytes: 8192,
        },
    );
    std::thread::scope(|scope| {
        for _ in 0..4 {
            let (admitted, cache) = (&admitted, &cache);
            scope.spawn(move || {
                for _ in 0..3 {
                    invoke(
                        admitted,
                        cache,
                        ark_backend(None),
                        vec![Value::Index(8), f(2)],
                        &[0, 1],
                        Default::default(),
                        Default::default(),
                    )
                    .0
                    .unwrap();
                }
            });
        }
    });
    assert_eq!(cache.stats().entries, 1);
    assert!(cache.stats().hits > 0);
    assert!(cache.stats().bytes <= 8192);
    invoke(
        &admitted,
        &cache,
        ark_backend(None),
        vec![Value::Index(9), f(2)],
        &[0, 1],
        Default::default(),
        Default::default(),
    )
    .0
    .unwrap();
    assert_eq!(cache.stats().entries, 1);
}
#[test]
fn skipped_nested_frames_preserve_later_frame_ids() {
    let mut program: Json = serde_json::from_slice(&choose()).unwrap();
    program[3][0][6].as_array_mut().unwrap().insert(
        1,
        json!(["local", "later", "local", ["cond", "ok"], ["later_answer"]]),
    );
    let admitted =
        admit_supplied(&serde_json::to_vec(&program).unwrap(), &ark_backend(None)).unwrap();
    let cache = PreparedComputations::new(&admitted, PreparationLimits::default());
    let run = || {
        let mut runner = Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            Traced::new(ark_backend(None)),
            vec![Value::Bool(true), Value::Bool(true)],
        )
        .unwrap_or_else(|e| panic!("{}", e.error));
        runner.prepare_computations(cache.clone(), &[0, 1]).unwrap();
        execute(runner)
    };
    let (_, usage, cold) = run();
    let (_, reused_usage, warm) = run();
    assert_eq!(usage, reused_usage);
    assert_eq!(
        cold.frames,
        vec![
            (1, None),
            (2, Some(1)),
            (3, Some(2)),
            (4, Some(1)),
            (5, Some(4))
        ]
    );
    assert_eq!(warm.frames, vec![(1, None), (2, Some(1)), (4, Some(1))]);
    assert_eq!(cache.stats().hits, 2);
}
#[test]
fn private_computation_ends_prefix_even_for_later_closed_functions() {
    let mut program: Json = serde_json::from_slice(&choose()).unwrap();
    program[2].as_array_mut().unwrap().push(json!([
        "function",
        "closed",
        [],
        ["native.bool/0"],
        [
            ["bool_constant", "literal", "result", true],
            ["return", ["result"]]
        ],
        ["closed", []]
    ]));
    // Reuse the admitted physical Boolean spelling rather than assuming a wire alias.
    program[2][1][3] = program[2][0][3].clone();
    program[3][0][6]
        .as_array_mut()
        .unwrap()
        .insert(1, json!(["local", "later", "closed", [], ["later_answer"]]));
    let admitted =
        admit_supplied(&serde_json::to_vec(&program).unwrap(), &ark_backend(None)).unwrap();
    let cache = PreparedComputations::new(&admitted, PreparationLimits::default());
    for _ in 0..2 {
        invoke(
            &admitted,
            &cache,
            ark_backend(None),
            vec![Value::Bool(true), Value::Bool(true)],
            &[],
            Default::default(),
            Default::default(),
        )
        .0
        .unwrap();
    }
    assert_eq!(cache.stats().entries, 0);
}
#[test]
fn nested_public_control_reuses_success_and_never_caches_failure() {
    let admitted = admit_supplied(&choose(), &ark_backend(None)).unwrap();
    let cache = PreparedComputations::new(&admitted, PreparationLimits::default());
    let run = |cond| {
        invoke(
            &admitted,
            &cache,
            ark_backend(None),
            vec![Value::Bool(cond), Value::Bool(true)],
            &[0, 1],
            Default::default(),
            Default::default(),
        )
    };
    let (cold, usage, _) = run(true);
    let (warm, warm_usage, backend) = run(true);
    assert!(matches!(cold.unwrap()[0], Value::Bool(true)));
    assert!(matches!(warm.unwrap()[0], Value::Bool(true)));
    assert_eq!(usage, warm_usage);
    assert_eq!(backend.active_frames(), 0);
    assert_eq!(cache.stats().hits, 1);
    let (failure, failure_usage, _) = run(false);
    let (again, again_usage, _) = run(false);
    assert_eq!(failure.as_ref().unwrap_err(), again.as_ref().unwrap_err());
    assert_eq!(failure_usage, again_usage);
    assert_eq!(failure.unwrap_err().site.as_deref(), Some("dead_guard"));
    assert_eq!(cache.stats().entries, 1);
}

#[test]
fn native_work_and_later_lower_capacity_use_the_same_accounting() {
    let bytes = candidate(
        json!([["x", "field:bls12-381.fr"]]),
        json!(["bytes"]),
        json!([
            ["op", "encode", "encoding.field_be", [], ["x"], ["encoded"]],
            ["op", "hash", "hash.keccak256", [], ["encoded"], ["out"]],
            ["return", ["out"]]
        ]),
    );
    let mut program: Json = serde_json::from_slice(&bytes).unwrap();
    for binding in program[1].as_array_mut().unwrap() {
        if binding[1] == "hash.keccak256" {
            binding[2] = json!([]);
            binding[3] = json!("native/hash.keccak256");
        }
    }
    let bytes = serde_json::to_vec(&program).unwrap();
    let admitted = admit_supplied(&bytes, &ark_backend(None)).unwrap();
    let cache = PreparedComputations::new(&admitted, PreparationLimits::default());
    let run = |instructions, external| {
        invoke(
            &admitted,
            &cache,
            ark_backend(None).with_external_work_limit(external),
            vec![f(3)],
            &[0],
            Default::default(),
            WorkBudget {
                instructions,
                ..Default::default()
            },
        )
    };
    let (cold, usage, backend) = run(100, 1000);
    let work = backend.external_work_spent();
    assert!(work > 0);
    let (warm, reused_usage, backend) = run(100, 1000);
    let (Value::Bytes(a), Value::Bytes(b)) = (&cold.unwrap()[0], &warm.unwrap()[0]) else {
        panic!("bytes")
    };
    assert_eq!(a, b);
    assert_eq!(usage, reused_usage);
    assert_eq!(work, backend.external_work_spent());
    assert_eq!(cache.stats().hits, 1);
    run(50, 500).0.unwrap(); // fallback refreshes the lower capacity context
    assert_eq!(cache.stats().hits, 1);
    run(50, 500).0.unwrap();
    assert_eq!(cache.stats().hits, 2);
    let (failure, failed_usage, backend) = run(50, work - 1);
    let empty = PreparedComputations::new(
        &admitted,
        PreparationLimits {
            entries: 0,
            bytes: 0,
        },
    );
    let (original, original_usage, original_backend) = invoke(
        &admitted,
        &empty,
        ark_backend(None).with_external_work_limit(work - 1),
        vec![f(3)],
        &[0],
        Default::default(),
        WorkBudget {
            instructions: 50,
            ..Default::default()
        },
    );
    assert_eq!(failure.unwrap_err(), original.unwrap_err());
    assert_eq!(failed_usage, original_usage);
    assert_eq!(
        backend.external_work_spent(),
        original_backend.external_work_spent()
    );
    assert_eq!(cache.stats().hits, 2);
}
