//! Reached control, frame custody, and cleanup before CFG realization.
use super::*;

/// One independently authored carrier combines the boundaries needed by the
/// compiler's explicit-outcome control profile. The dormant arm is installed,
/// but its invocation must never happen on the selected `live` alternative.
fn nested_affine_control() -> Vec<u8> {
    let state = format!(
        "{}@logical.variant/0",
        zkc_test_support::variants::logical(
            "Control.State",
            json!([["live", ["resource_unit:Control.Ticket"]], ["empty", []]])
        )
    );
    candidate(
        json!([
            ["x", "field:bls12-381.fr"],
            ["n", "index"],
            ["accept", "bool"],
            ["again", "bool"]
        ]),
        json!(["field:bls12-381.fr"]),
        json!([
            ["op", "create", "resource_unit.create", [], [], ["ticket"]],
            ["op", "zero", "index.constant", ["0"], [], ["lo"]],
            [
                "for_while",
                "loop",
                "i",
                "lo",
                "n",
                [["carry", "ticket"], ["total", "x"]],
                ["x", "accept", "again"],
                [
                    ["variant", "pack", state, "live", ["carry"], "state"],
                    [
                        "match",
                        "select",
                        "state",
                        ["accept"],
                        [
                            [
                                "live",
                                ["payload"],
                                [
                                    [
                                        "if",
                                        "guard",
                                        "accept",
                                        ["payload"],
                                        [["yield", ["payload"]]],
                                        [["stop", "reject", "reject"]],
                                        ["checked"]
                                    ],
                                    ["yield", ["checked"]]
                                ]
                            ],
                            [
                                "empty",
                                [],
                                [
                                    ["op", "dormant", "control.require", [], ["accept"], []],
                                    ["stop", "empty", "abort"]
                                ]
                            ]
                        ],
                        ["next_ticket"]
                    ],
                    ["op", "add", "field.add", [], ["total", "x"], ["sum"]],
                    ["op", "mul", "field.mul", [], ["sum", "x"], ["product"]],
                    [
                        "if",
                        "continue",
                        "again",
                        ["product"],
                        [["yield", ["product"]]],
                        [["yield", ["product"]]],
                        ["next_total"]
                    ],
                    ["yield", ["again", "next_ticket", "next_total"]]
                ],
                ["final_ticket", "answer"]
            ],
            [
                "op",
                "consume",
                "resource_unit.consume",
                [],
                ["final_ticket"],
                []
            ],
            ["return", ["answer"]]
        ]),
    )
}

fn run_nested_control(
    backend: Traced,
    n: u64,
    accept: bool,
    again: bool,
) -> (Result<Vec<Value>, zkc_runtime::vm::Stop>, Usage, Traced) {
    execute(load(
        &nested_affine_control(),
        backend,
        vec![
            f(3),
            Value::Index(n),
            Value::Bool(accept),
            Value::Bool(again),
        ],
    ))
}

fn assert_lifecycle_closed(backend: &Traced) {
    let mut entered = vec![];
    for event in &backend.lifecycle {
        if event.exit.is_none() {
            assert_eq!(event.active.0, entered.len(), "{event:?}");
            assert_eq!(event.resources.0, event.resources.1, "{event:?}");
            if event.error.is_none() {
                entered.push(event.id);
            }
        } else {
            assert_eq!(event.active.0, entered.len(), "{event:?}");
            assert_eq!(entered.pop(), Some(event.id), "{event:?}");
            assert!(event.resources.1 <= event.resources.0, "{event:?}");
        }
        assert_eq!(event.active.1, entered.len(), "{event:?}");
    }
    assert!(entered.is_empty());
    assert_eq!(backend.inner.active_frames(), 0);
    assert_eq!(backend.inner.live_resource_units(), 0);
}

#[test]
fn nested_affine_control_preserves_reached_order_and_early_completion() {
    for (n, accept, again, trips, expected) in [
        (0, false, false, 0, 3),
        (1, true, true, 1, 18),
        (3, true, true, 3, 198),
        (3, true, false, 1, 18),
    ] {
        let (out, usage, backend) =
            run_nested_control(Traced::new(ark_backend(None)), n, accept, again);
        assert_eq!(scalar(&out.unwrap()[0]), Scalar::from(expected));
        assert_eq!(
            (usage.instructions, usage.iterations),
            (7 + 10 * trips, trips)
        );
        let mut sites = vec!["create", "zero"];
        for _ in 0..trips {
            sites.extend(["add", "mul"]);
        }
        sites.push("consume");
        assert_eq!(
            backend
                .events
                .iter()
                .map(|e| e[0].as_str().unwrap())
                .collect::<Vec<_>>(),
            sites
        );
        assert!(
            backend
                .prepared
                .borrow()
                .iter()
                .any(|b| b.contract == "control.require")
        );
        assert_lifecycle_closed(&backend);
    }
}

#[test]
fn nested_affine_control_failed_entry_skips_child_exit_and_unwinds_parents() {
    // Entry=1, helper=2, iteration=3, match=4, selected if=5.
    for failed in 2..=5 {
        let mut backend = Traced::new(ark_backend(None));
        backend.fail_enter = Some(failed);
        backend.failing_exits = (1..failed).collect();
        let (out, usage, backend) = run_nested_control(backend, 3, true, true);
        let stop = out.unwrap_err();
        assert_eq!(code(&stop), "test:entry");
        assert_eq!(usage.live_values, 0);
        assert_eq!(
            stop.cleanup_errors
                .iter()
                .map(|e| e.code.clone())
                .collect::<Vec<_>>(),
            (1..failed)
                .rev()
                .map(|id| format!("test:cleanup:{id}"))
                .collect::<Vec<_>>()
        );
        let refused = backend.lifecycle.iter().find(|e| e.id == failed).unwrap();
        assert_eq!(refused.exit, None);
        assert_eq!(refused.error.as_deref(), Some("test:entry"));
        assert!(
            !backend
                .lifecycle
                .iter()
                .any(|e| e.id == failed && e.exit.is_some())
        );
        assert!(
            !backend
                .events
                .iter()
                .any(|e| e[0] == "add" || e[0] == "mul")
        );
        assert_lifecycle_closed(&backend);
    }
}

#[test]
fn nested_affine_control_bound_refusal_precedes_entry_and_keeps_cleanup_secondary() {
    let mut backend = Traced::new(ark_backend(None));
    backend.failing_exits = vec![1, 2];
    let (out, usage, backend) = run_nested_control(backend, 1_048_577, true, true);
    let stop = out.unwrap_err();
    assert_eq!(code(&stop), "exhausted:local-bound-limit");
    assert!(stop.origin.path.is_empty());
    assert_eq!(
        (usage.instructions, usage.iterations, usage.live_values),
        (4, 0, 0)
    );
    assert_eq!(
        stop.cleanup_errors,
        vec![
            BackendError::new("test:cleanup:2"),
            BackendError::new("test:cleanup:1")
        ]
    );
    assert_eq!(backend.frames, vec![(1, None), (2, Some(1))]);
    assert_lifecycle_closed(&backend);
}

#[test]
fn nested_affine_control_installs_dormant_variant_calls_before_any_frame() {
    let program =
        zkc_runtime::vm::Program::decode(&nested_affine_control(), zkc_cpu::cpu_contracts())
            .unwrap();
    let mut backend = Traced::new(ark_backend(None));
    backend.blocked = Some("control.require".into());
    let error = program.check_installation(&backend).unwrap_err();
    assert_eq!(error.code, ErrorCode::Backend);
    assert_eq!(
        error.detail,
        "installed signature mismatch: arkworks/control.require"
    );
    assert!(backend.lifecycle.is_empty());
    assert!(backend.events.is_empty());
    assert_eq!(backend.inner.active_frames(), 0);
}

#[test]
fn nested_affine_control_cleanup_failure_withholds_success_and_preserves_stop() {
    for accept in [true, false] {
        let mut backend = Traced::new(ark_backend(None));
        backend.failing_exits = vec![1, 2, 3, 4, 5];
        let (out, usage, backend) = run_nested_control(backend, 3, accept, true);
        let stop = out.unwrap_err();
        assert_eq!(usage.live_values, 0);
        let failed = backend
            .lifecycle
            .iter()
            .find(|e| e.id == 5 && e.exit.is_some())
            .unwrap();
        assert_eq!(
            failed.origin[4],
            json!([
                ["for", "loop", "0"],
                ["match", "select", "live"],
                ["if", "guard", if accept { "then" } else { "else" }]
            ])
        );
        if accept {
            assert_eq!(code(&stop), "test:cleanup:5");
            assert_eq!(failed.exit, Some(FrameExit::Returned));
            assert_eq!(failed.values, 1);
        } else {
            assert!(matches!(&stop.kind, StopKind::Explicit(reason) if reason == "reject"));
            assert_eq!(failed.exit, Some(FrameExit::Stopped));
            assert_eq!(failed.values, 0);
        }
        let first_cleanup = if accept { 4 } else { 5 };
        assert_eq!(
            stop.cleanup_errors
                .iter()
                .map(|e| e.code.clone())
                .collect::<Vec<_>>(),
            (1..=first_cleanup)
                .rev()
                .map(|id| format!("test:cleanup:{id}"))
                .collect::<Vec<_>>()
        );
        assert!(
            !backend
                .events
                .iter()
                .any(|e| e[0] == "add" || e[0] == "mul")
        );
        assert_lifecycle_closed(&backend);
    }
}

#[test]
fn nested_affine_control_each_exit_withholds_outputs_without_undoing_calls() {
    for failed in 1..=6 {
        let mut backend = Traced::new(ark_backend(None));
        backend.failing_exits = vec![failed];
        let (out, usage, backend) = run_nested_control(backend, 1, true, true);
        let stop = out.unwrap_err();
        assert_eq!(code(&stop), format!("test:cleanup:{failed}"));
        assert!(stop.cleanup_errors.is_empty());
        assert_eq!(usage.live_values, 0);
        let observed = |site: &str| backend.events.iter().any(|e| e[0] == site);
        assert_eq!(observed("add"), !matches!(failed, 4 | 5));
        assert_eq!(observed("mul"), !matches!(failed, 4 | 5));
        assert_eq!(observed("consume"), failed <= 2);
        assert_lifecycle_closed(&backend);
    }
}
