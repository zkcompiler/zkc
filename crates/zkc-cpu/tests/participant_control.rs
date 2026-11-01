//! Actual native custody and allocation through hand-authored participant arms.
mod common;
use common::*;
use serde_json::{Value as Json, json};
use zkc_cpu::Value;
use zkc_runtime::vm::{Backend, Identity, Program};

#[test]
fn selected_participant_draw_preserves_actual_roots_and_dormant_budget() {
    let bytes = program(
        &[("c", "bool"), ("x", "field"), ("r", "rng"), ("s", "rng")],
        vec![op(
            "draw",
            "arkworks/random.draw",
            &["r"],
            &["drawn", "next"],
        )],
        &["field", "rng", "rng"],
        &["drawn", "next", "s"],
    );
    let mut candidate: Json = serde_json::from_slice(&bytes).unwrap();
    candidate[3][0][6] = json!([
        [
            "if",
            "choice",
            "c",
            ["c", "x", "r", "s"],
            [
                [
                    "local",
                    "draw_selected",
                    "kernel_test",
                    ["c", "x", "r", "s"],
                    ["value", "next", "same"]
                ],
                ["yield", ["value", "next", "same"]]
            ],
            [["yield", ["x", "s", "r"]]],
            ["answer", "first", "second"]
        ],
        ["return", ["answer", "first", "second"]]
    ]);
    let bytes = candidate.to_string().into_bytes();
    for selected in [false, true] {
        for budget in [0, 2] {
            let mut backend = ark_backend(None);
            let r = backend
                .issue_rng_for(Identity::Bls12381Fr, domain(), budget)
                .unwrap();
            let s = backend
                .issue_rng_for(Identity::Bls12381Fr, domain(), 5)
                .unwrap();
            let ids = [token(&r).issued_id(), token(&s).issued_id()];
            let (out, backend) = run(
                &bytes,
                backend,
                vec![Value::Bool(selected), f(42), r.clone(), s.clone()],
            );
            assert_eq!(
                backend.observe(token(&r)).unwrap().draw_count,
                u64::from(selected)
            );
            assert_eq!(backend.observe(token(&s)).unwrap().draw_count, 0);
            if selected && budget == 0 {
                assert_eq!(code(&out.unwrap_err()), "exhausted:resource-budget");
            } else {
                let out = out.unwrap();
                assert_eq!(
                    [token(&out[1]).issued_id(), token(&out[2]).issued_id()],
                    if selected { ids } else { [ids[1], ids[0]] }
                );
                if selected {
                    assert!(backend.validate_value(&r).is_err());
                } else {
                    assert_eq!(scalar(&out[0]), zkc_cpu::Scalar::from(42u64));
                }
            }
            assert_eq!(backend.active_frames(), 0);
        }
    }
}

#[test]
fn branch_exclusive_fresh_units_need_no_fabricated_seed_or_dormant_allocation() {
    let unit = "resource_unit:Selected.Ticket@logical.resource_unit/0";
    let candidate = json!([
        "zkc.program/0",
        [[
            "create",
            "resource_unit.create",
            ["Selected.Ticket"],
            "logical/resource_unit.create",
            []
        ]],
        [[
            "function",
            "factory",
            [],
            [unit],
            [
                ["op", "create_here", "create", [], [], ["ticket"]],
                ["return", ["ticket"]]
            ],
            ["factory", []]
        ]],
        [[
            "participant",
            "p",
            "instance",
            "P",
            [["c", "bool@native.bool/0"]],
            [unit],
            [
                [
                    "if",
                    "choice",
                    "c",
                    [],
                    [
                        ["local", "then_factory", "factory", [], ["ticket"]],
                        ["yield", ["ticket"]]
                    ],
                    [
                        ["local", "else_factory", "factory", [], ["ticket"]],
                        ["yield", ["ticket"]]
                    ],
                    ["result"]
                ],
                ["return", ["result"]]
            ],
            []
        ]],
        [["entry", "main", [["P", "p"]]]]
    ]);
    // Reusing a lexical payload name in disjoint arms is legal in both readers.
    let bytes = candidate.to_string().into_bytes();
    let admitted = Program::decode(&bytes, zkc_cpu::cpu_contracts()).unwrap();
    for selected in [false, true] {
        let runner = zkc_runtime::interpreter::Runner::new_for_role_with_ledger(
            &admitted,
            "main",
            "P",
            "session",
            ark_backend(None),
            vec![Value::Bool(selected)],
            Default::default(),
            Default::default(),
            None,
        )
        .unwrap_or_else(|e| panic!("load: {}", e.error));
        let (out, backend) = finish(runner);
        let out = out.unwrap();
        assert_eq!(out.len(), 1);
        assert!(matches!(&out[0], Value::ResourceUnit(_)));
        assert_eq!(backend.live_resource_units(), 1);
        assert_eq!(backend.active_frames(), 0);
    }
}

#[test]
fn native_variant_selects_its_actual_payload_without_touching_other_arms() {
    use zkc_runtime::vm::{LogicalType, PhysicalType, Value as _};
    let nominal = zkc_format::types::variant_spelling(&json!([
        ["native_selected", "Choice"],
        [["some", ["bool"]], ["none", []]]
    ]))
    .unwrap();
    let ty = PhysicalType::default_for(LogicalType::parse(&nominal).unwrap()).unwrap();
    let candidate = json!([
        "zkc.program/0",
        [],
        [],
        [[
            "participant",
            "p",
            "instance",
            "P",
            [["c", ty.spelling()], ["fallback", "bool@native.bool/0"]],
            ["bool@native.bool/0"],
            [
                [
                    "match",
                    "choice",
                    "c",
                    ["fallback"],
                    [
                        ["some", ["payload"], [["yield", ["payload"]]]],
                        ["none", [], [["yield", ["fallback"]]]]
                    ],
                    ["result"]
                ],
                ["return", ["result"]]
            ],
            []
        ]],
        [["entry", "main", [["P", "p"]]]]
    ]);
    let bytes = candidate.to_string().into_bytes();
    for alternative in 0..2 {
        let selector = Value::pack_variant(
            ty.clone(),
            alternative,
            if alternative == 0 {
                vec![Value::Bool(true)]
            } else {
                vec![]
            },
        )
        .unwrap();
        let (out, backend) = run(
            &bytes,
            ark_backend(None),
            vec![selector, Value::Bool(false)],
        );
        assert!(matches!(out.unwrap().as_slice(),[Value::Bool(value)] if *value==(alternative==0)));
        assert_eq!(backend.active_frames(), 0);
    }
}
