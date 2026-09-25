//! Exercise the independent carrier boundary with real native values and resources.
mod common;
use common::*;
use serde_json::{Value as Json, json};
use zkc_backends::{Policy, Value};
use zkc_runtime::interactive::{
    Backend, ErrorCode, LogicalType, PhysicalType, StopKind, Value as RuntimeValue, admit_supplied,
};

use zkc_test_support::variants::logical;

fn physical(nominal: &str, arms: Json) -> String {
    format!("{}@logical.variant/1", logical(nominal, arms))
}
fn descriptor(ty: &str) -> std::sync::Arc<zkc_runtime::interactive::VariantDescriptor> {
    LogicalType::parse(ty)
        .unwrap()
        .variant_descriptor()
        .unwrap()
        .clone()
}
fn fixture(ports: Json, results: Json, body: Json) -> Json {
    let args = ports
        .as_array()
        .unwrap()
        .iter()
        .map(|p| p[0].clone())
        .collect::<Vec<_>>();
    let names = results
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
        .map(|(i, _)| format!("out{i}"))
        .collect::<Vec<_>>();
    json!([
        "zkc.participants/1",
        [
            ["add", "field.add", ["bls12-381.fr"], "arkworks/field.add"],
            [
                "draw",
                "random.draw",
                ["bls12-381.fr"],
                "arkworks/random.draw"
            ],
            [
                "make",
                "resource_unit.create",
                ["Slot.A"],
                "logical/resource_unit.create"
            ],
            [
                "pass",
                "resource_unit.pass",
                ["Slot.A"],
                "logical/resource_unit.pass"
            ],
            [
                "consume",
                "resource_unit.consume",
                ["Slot.A"],
                "logical/resource_unit.consume"
            ]
        ],
        "physical",
        [["function", "Local", ports, results, body, ["Local", []]]],
        [[
            "participant",
            "root_P",
            "root",
            "P",
            [],
            ports,
            results,
            [["local", "work", "Local", args, names], ["return", names]]
        ]],
        [["entry", "main", [["P", "root_P"]]]]
    ])
}
fn bytes(j: &Json) -> Vec<u8> {
    serde_json::to_vec(j).unwrap()
}
const FIELD: &str = "field:bls12-381.fr@arkworks.fr/1";
const RNG: &str = "rng:bls12-381.fr@host.resource/1";
const UNIT: &str = "resource_unit:Slot.A@logical.resource_unit/1";

#[test]
fn exact_canonical_descriptors_and_conservative_permissions() {
    let a = logical(
        "Lib.Result[type=F]",
        json!([["ok", ["field:bls12-381.fr"]], ["err", []]]),
    );
    let t = LogicalType::parse(&a).unwrap();
    assert_eq!(t.spelling(), a);
    assert!(t.is_duplicable() && t.is_discardable());
    assert!(t.codec().is_none());
    assert!(!PhysicalType::default_for(t.clone()).is_serializable());
    assert_ne!(
        t,
        LogicalType::parse(&logical(
            "Other",
            json!([["ok", ["field:bls12-381.fr"]], ["err", []]])
        ))
        .unwrap()
    );
    let affine = LogicalType::parse(&logical(
        "Affine",
        json!([["none", []], ["some", ["rng:bls12-381.fr"]]]),
    ))
    .unwrap();
    assert!(!affine.is_duplicable() && !affine.is_discardable());
    let unit = LogicalType::parse(&logical(
        "Guard",
        json!([["none", []], ["some", ["resource_unit:Slot.A"]]]),
    ))
    .unwrap();
    assert!(!unit.is_duplicable() && unit.is_discardable());
    let inner = logical("Inner", json!([["unit", ["resource_unit:Slot.A"]]]));
    let nested = LogicalType::parse(&logical(
        "Outer",
        json!([["nested", [inner]], ["none", []]]),
    ))
    .unwrap();
    assert!(!nested.is_duplicable() && nested.is_discardable());
    assert!(LogicalType::parse(&logical("X".repeat(1536).as_str(), json!([["z", []]]))).is_ok());
}

/// The refusal a spelling meets, as the code and detail the reader emits.
fn refusal(spelling: &str) -> (ErrorCode, String) {
    let error = LogicalType::parse(spelling).unwrap_err();
    (error.code, error.detail)
}
fn refused_as(spelling: &str, detail: &str) {
    assert_eq!(
        refusal(spelling),
        (ErrorCode::Type, detail.to_owned()),
        "{}",
        &spelling[..spelling.len().min(96)]
    );
}
/// A spelling of arbitrary descriptor JSON, including shapes the fixture
/// encoder would never produce.
fn raw(descriptor: Json) -> String {
    format!(
        "variant:{}",
        zkc_test_support::hex(&serde_json::to_vec(&descriptor).unwrap())
    )
}

#[test]
fn malformed_descriptors_fail_closed() {
    for (arms, detail) in [
        (json!([]), "variant:alternatives"),
        (json!([["a", []], ["a", []]]), "variant:duplicate-label"),
        (json!([["bad!", []]]), "variant:label"),
        (json!([["ok", ["bool@native.bool/1"]]]), "variant:payload"),
        (
            json!([["ok", ["unknown"]]]),
            "explicit nominal identity required",
        ),
        (json!([["ok", vec!["bool"; 129]]]), "variant:payload-limit"),
        (
            json!(
                (0..33)
                    .map(|i| json!([format!("a{i}"), []]))
                    .collect::<Vec<_>>()
            ),
            "variant:alternatives",
        ),
    ] {
        refused_as(&logical("X", arms), detail);
    }
    for (nominal, detail) in [
        ("", "variant:nominal"),
        // The reader keeps the string; the canonical re-encoding refuses it.
        ("é", "variant:graph-node"),
        ("bad\n", "variant:graph-node"),
        (&"X".repeat(262145), "variant:limit"),
    ] {
        refused_as(&logical(nominal, json!([["ok", []]])), detail);
    }
    let valid = logical("X", json!([["ok", []]]));
    for (bad, detail) in [
        (format!("{valid}00"), "variant:json"),
        // Uppercase digits after an intact prefix: only the hexadecimal
        // alphabet is wrong.
        (
            format!("variant:{}", valid[8..].to_uppercase()),
            "variant:hex",
        ),
        (format!("{valid}f"), "variant:hex"),
        (format!("{valid}@logical.variant/1"), "variant:hex"),
        ("variant:".to_owned(), "variant:hex"),
    ] {
        refused_as(&bad, detail);
    }
    // An uppercase prefix is not a variant spelling at all.
    assert_eq!(
        refusal(&valid.to_uppercase()),
        (
            ErrorCode::Type,
            "unknown or opaque executable type".to_owned()
        )
    );
    assert!(LogicalType::parse(&valid).is_ok());
    let mut bytes = zkc_test_support::unhex(&valid[8..]);
    bytes.insert(1, b' ');
    let noncanonical = format!("variant:{}", zkc_test_support::hex(&bytes));
    refused_as(&noncanonical, "variant:canonical");
    let mut deep = "bool".to_owned();
    for i in 0..9 {
        deep = logical(&format!("N{i}"), json!([["ok", [deep]]]));
    }
    refused_as(&deep, "variant:limit");
    let error = PhysicalType::parse(&format!("{valid}@host.resource/1")).unwrap_err();
    assert_eq!(
        (error.code, error.detail.as_str()),
        (
            ErrorCode::Type,
            "representation does not implement logical type"
        )
    );
}

#[test]
fn malformed_descriptor_graphs_name_the_failed_check() {
    for (descriptor, detail) in [
        (json!([]), "variant:descriptor"),
        (json!(["zkc.variant/1"]), "variant:descriptor"),
        // A canonical graph whose root is a lone string, not a variant tree.
        (json!(["zkc.variant/1", ["x"]]), "variant:descriptor"),
        (json!(["zkc.variant/2", ["x"]]), "variant:version"),
        (json!(["zkc.variant/1", []]), "variant:descriptor"),
        (json!(["zkc.variant/1", [1]]), "variant:graph-node"),
        (
            json!(["zkc.variant/1", ["x", ["01"]]]),
            "variant:graph-reference",
        ),
        (
            json!(["zkc.variant/1", ["x", ["99999999999999999999"]]]),
            "variant:graph-reference",
        ),
        (json!(["zkc.variant/1", [["0"]]]), "variant:graph-reference"),
    ] {
        refused_as(&raw(descriptor), detail);
    }
    // Forty nodes that each reference their predecessor twice: a small
    // spelling whose expansion doubles per node.
    let mut nodes = vec![json!("x")];
    for i in 0..40 {
        nodes.push(json!([i.to_string(), i.to_string()]));
    }
    refused_as(&raw(json!(["zkc.variant/1", nodes])), "variant:graph-limit");
    // One node past the graph's node budget, however small each node is.
    let wide: Vec<Json> = (0..=16384).map(|_| json!("x")).collect();
    refused_as(&raw(json!(["zkc.variant/1", wide])), "variant:graph-limit");
    let valid = logical("X", json!([["ok", []]]));
    for (tree, detail) in [
        (json!(["X", [["ok"]]]), "variant:alternative"),
        (json!(["X", [[["ok"], []]]]), "variant:label"),
        (json!(["X", [["ok", "bool"]]]), "variant:payload-limit"),
        (json!(["X", [["ok", [valid]]]]), "variant:payload"),
    ] {
        refused_as(&zkc_test_support::variants::encode_tree(tree), detail);
    }
}

#[test]
fn native_active_payload_has_unequal_layouts_and_no_wire_codec() {
    let ty = logical(
        "Unequal",
        json!([
            ["scalar", ["field:bls12-381.fr"]],
            ["wide", ["bool", "index", "indices"]],
            ["empty", []]
        ]),
    );
    let d = descriptor(&ty);
    let empty = Value::pack_variant(d.clone(), 2, vec![]).unwrap();
    let scalar = Value::pack_variant(d.clone(), 0, vec![f(9)]).unwrap();
    let wide = Value::pack_variant(
        d.clone(),
        1,
        vec![
            Value::Bool(true),
            Value::Index(4),
            Value::Indices(vec![1, 2, 3].into()),
        ],
    )
    .unwrap();
    assert_eq!(empty.unpack_variant().unwrap().2.len(), 0);
    assert_eq!(wide.unpack_variant().unwrap().2.len(), 3);
    assert!(empty.retained_bytes() < scalar.retained_bytes());
    assert!(scalar.retained_bytes() < wide.retained_bytes());
    let backend = ark_backend(None);
    for value in [&empty, &scalar, &wide] {
        backend.validate_value(value).unwrap();
        assert_eq!(
            backend.encode_value(value).unwrap_err().code,
            "refused:nonserializable"
        );
    }
    assert_eq!(
        Value::pack_variant(d.clone(), 3, vec![]).unwrap_err().code,
        "refused:variant-alternative"
    );
    assert_eq!(
        Value::pack_variant(d.clone(), 0, vec![]).unwrap_err().code,
        "refused:variant-payload"
    );
    assert_eq!(
        Value::pack_variant(d, 0, vec![Value::Bool(false)])
            .unwrap_err()
            .code,
        "refused:variant-payload"
    );
    assert_eq!(
        backend
            .decode_typed_value(empty.physical_type(), b"")
            .unwrap_err()
            .code,
        "refused:nonserializable"
    );
    // A value that is not a variant has no alternative to unpack.
    assert_eq!(
        Value::Bool(true).unpack_variant().unwrap_err().code,
        "refused:variant-type"
    );
}

#[test]
fn selected_arm_and_capture_execute_on_native_backend() {
    let ty = physical(
        "Unequal",
        json!([
            ["one", ["field:bls12-381.fr"]],
            ["empty", []],
            ["two", ["field:bls12-381.fr", "bool"]]
        ]),
    );
    for (arm, payload, expected) in [
        ("one", json!(["x"]), 14),
        ("empty", json!([]), 5),
        ("two", json!(["x", "flag"]), 14),
    ] {
        let j = fixture(
            json!([["x", FIELD], ["cap", FIELD], ["flag", "bool@native.bool/1"]]),
            json!([FIELD]),
            json!([
                ["variant", "pack", ty, arm, payload, "v"],
                [
                    "match",
                    "case",
                    "v",
                    ["cap"],
                    [
                        [
                            "one",
                            ["p"],
                            [
                                ["op", "add-one", "add", [], ["p", "cap"], ["sum"]],
                                ["yield", ["sum"]]
                            ]
                        ],
                        ["empty", [], [["yield", ["cap"]]]],
                        [
                            "two",
                            ["p", "b"],
                            [
                                ["op", "add-two", "add", [], ["p", "cap"], ["sum"]],
                                ["yield", ["sum"]]
                            ]
                        ]
                    ],
                    ["answer"]
                ],
                ["return", ["answer"]]
            ]),
        );
        let (out, backend) = run(
            &bytes(&j),
            ark_backend(None),
            vec![f(9), f(5), Value::Bool(true)],
        );
        assert_eq!(
            scalar(&out.unwrap()[0]),
            zkc_backends::Scalar::from(expected)
        );
        assert_eq!(backend.active_frames(), 0);
    }
}

#[test]
fn nested_affine_rng_crosses_only_selected_frames_and_keeps_authority() {
    let inner = logical(
        "Inner",
        json!([["rng", ["rng:bls12-381.fr"]], ["zero", []]]),
    );
    let outer = physical("Outer", json!([["nested", [inner]], ["unused", []]]));
    let inner_physical = format!("{inner}@logical.variant/1");
    let j = fixture(
        json!([["r", RNG]]),
        json!([FIELD, RNG]),
        json!([
            ["variant", "inner", inner_physical, "rng", ["r"], "v"],
            ["variant", "outer", outer, "nested", ["v"], "w"],
            [
                "match",
                "outer-case",
                "w",
                [],
                [
                    [
                        "nested",
                        ["inside"],
                        [
                            [
                                "match",
                                "inner-case",
                                "inside",
                                [],
                                [
                                    [
                                        "rng",
                                        ["active"],
                                        [
                                            [
                                                "op",
                                                "draw-active",
                                                "draw",
                                                [],
                                                ["active"],
                                                ["x", "next"]
                                            ],
                                            ["yield", ["x", "next"]]
                                        ]
                                    ],
                                    ["zero", [], [["stop", "empty-stop", "refused"]]]
                                ],
                                ["x", "next"]
                            ],
                            ["yield", ["x", "next"]]
                        ]
                    ],
                    ["unused", [], [["stop", "unused-stop", "reject"]]]
                ],
                ["x", "next"]
            ],
            ["return", ["x", "next"]]
        ]),
    );
    let mut backend = ark_backend(None);
    let rng = backend.issue_rng(domain(), 2).unwrap();
    let old = rng.clone();
    let outside = backend.issue_rng(domain(), 7).unwrap();
    let before = backend.observe(token(&outside)).unwrap();
    let (out, backend) = run(&bytes(&j), backend, vec![rng]);
    let out = out.unwrap();
    assert_eq!(backend.observe(token(&out[1])).unwrap().generation, 1);
    assert_eq!(backend.observe(token(&out[1])).unwrap().budget, 1);
    assert_eq!(
        backend.validate_value(&old).unwrap_err().code,
        "refused:capability-stale"
    );
    assert_eq!(backend.observe(token(&outside)).unwrap(), before);
    assert_eq!(backend.active_frames(), 0);
}

#[test]
fn terminal_stops_bypass_other_arms_and_preserve_categories() {
    let ty = physical(
        "Stop",
        json!([["stop", []], ["continue", ["field:bls12-381.fr"]]]),
    );
    for reason in ["reject", "abort", "exhausted", "incomplete", "refused"] {
        let j = fixture(
            json!([["r", RNG]]),
            json!([FIELD]),
            json!([
                ["variant", "pack", ty, "stop", [], "v"],
                [
                    "match",
                    "case",
                    "v",
                    ["r"],
                    [
                        [
                            "stop",
                            [],
                            [
                                ["op", "draw-before-stop", "draw", [], ["r"], ["x", "next"]],
                                ["stop", "terminal", reason]
                            ]
                        ],
                        ["continue", ["x"], [["yield", ["x"]]]]
                    ],
                    ["answer"]
                ],
                ["return", ["answer"]]
            ]),
        );
        let mut backend = ark_backend(None);
        let rng = backend.issue_rng(domain(), 2).unwrap();
        let old = rng.clone();
        let (out, backend) = run(&bytes(&j), backend, vec![rng]);
        let stop = out.unwrap_err();
        assert_eq!(stop.kind, StopKind::Explicit(reason.into()));
        assert_eq!(backend.observe(token(&old)).unwrap().generation, 1);
        assert_eq!(backend.active_frames(), 0);
        assert!(stop.cleanup_errors.is_empty());
    }
}

#[test]
fn resource_unit_in_active_payload_survives_join_and_is_consumed_once() {
    let ty = physical(
        "Guard",
        json!([["guard", ["resource_unit:Slot.A"]], ["zero", []]]),
    );
    let j = fixture(
        json!([]),
        json!([]),
        json!([
            ["op", "make", "make", [], [], ["g"]],
            ["variant", "pack", ty, "guard", ["g"], "v"],
            [
                "match",
                "case",
                "v",
                [],
                [
                    [
                        "guard",
                        ["g"],
                        [
                            ["op", "pass", "pass", [], ["g"], ["next"]],
                            ["yield", ["next"]]
                        ]
                    ],
                    ["zero", [], [["stop", "zero-stop", "reject"]]]
                ],
                ["next"]
            ],
            ["op", "consume", "consume", [], ["next"], []],
            ["return", []]
        ]),
    );
    let (out, backend) = run(&bytes(&j), ark_backend(None), vec![]);
    assert!(out.unwrap().is_empty());
    assert_eq!(backend.active_frames(), 0);
    let mut duplicate = j.clone();
    duplicate[3][0][4]
        .as_array_mut()
        .unwrap()
        .insert(4, json!(["op", "again", "consume", [], ["next"], []]));
    let error = admit_supplied(&bytes(&duplicate), &ark_backend(None)).unwrap_err();
    assert_eq!(
        (error.code, error.detail.as_str()),
        (
            ErrorCode::Ssa,
            "interactive-resource-reuse: consumed operand next"
        )
    );
}

#[test]
fn malformed_matches_and_boundary_escapes_refuse_independently() {
    let ty = physical("X", json!([["a", ["field:bls12-381.fr"]], ["b", []]]));
    let base = fixture(
        json!([["x", FIELD]]),
        json!([FIELD]),
        json!([
            ["variant", "pack", ty, "a", ["x"], "v"],
            [
                "match",
                "case",
                "v",
                ["x"],
                [
                    ["a", ["p"], [["yield", ["p"]]]],
                    ["b", [], [["yield", ["x"]]]]
                ],
                ["out"]
            ],
            ["return", ["out"]]
        ]),
    );
    let backend = ark_backend(None);
    admit_supplied(&bytes(&base), &backend).unwrap();
    for mutation in 0..10 {
        let mut j = base.clone();
        match mutation {
            0 => j[3][0][4][1][4]
                .as_array_mut()
                .unwrap()
                .pop()
                .map(|_| ())
                .unwrap(),
            1 => j[3][0][4][1][4][1][0] = json!("a"),
            2 => j[3][0][4][1][4][1][0] = json!("extra"),
            3 => j[3][0][4][1][4][0][1] = json!([]),
            4 => j[3][0][4][1][3] = json!([]), // arm cannot reach outside capture environment
            5 => j[3][0][4][0][3] = json!("missing"),
            6 => j[3][0][4][0][4] = json!([]),
            8 => j[3][0][4][1][2] = json!("x"), // a field is not a variant to match on
            9 => j[3][0][4][0][2] = json!(FIELD), // nor a type to construct
            _ => {
                j[3][0][4][1][4][0][2] =
                    json!([["send", "leak", "tag", "V", "p"], ["yield", ["p"]]])
            }
        }
        let error = admit_supplied(&bytes(&j), &backend).unwrap_err();
        let expected = [
            (ErrorCode::Signature, "match-exhaustive"),
            (ErrorCode::Signature, "match-alternative"),
            (ErrorCode::Signature, "match-alternative"),
            (ErrorCode::Signature, "match-alternative"),
            (ErrorCode::Ssa, "unavailable operand x"),
            (ErrorCode::Signature, "variant-alternative"),
            (ErrorCode::Signature, "operand arity"),
            (ErrorCode::Record, "unknown local instruction"),
            (ErrorCode::Type, "match-scrutinee"),
            (ErrorCode::Type, "variant-constructor-type"),
        ];
        assert_eq!(
            (error.code, error.detail.as_str()),
            expected[mutation],
            "mutation {mutation}"
        );
    }
    let mut entry = base.clone();
    entry[4][0][5][0][1] = json!(ty);
    let error = admit_supplied(&bytes(&entry), &backend).unwrap_err();
    assert_eq!(
        (error.code, error.detail.as_str()),
        (ErrorCode::Type, "variant-participant-boundary")
    );
    let mut send = base.clone();
    send[3][0][3] = json!([ty]);
    send[3][0][4] = json!([["variant", "pack", ty, "a", ["x"], "v"], ["return", ["v"]]]);
    send[4][0][7] = json!([
        ["local", "work", "Local", ["x"], ["v"]],
        ["send", "leak", "tag", "V", "v"],
        ["return", []]
    ]);
    send[4][0][6] = json!([]);
    let error = admit_supplied(&bytes(&send), &backend).unwrap_err();
    assert_eq!(
        (error.code, error.detail.as_str()),
        (ErrorCode::Type, "nonserializable message type")
    );
}

#[test]
fn inactive_resource_arm_still_controls_copy_and_drop() {
    let ty = physical(
        "Affine",
        json!([["none", []], ["rng", ["rng:bls12-381.fr"]]]),
    );
    let make = json!(["variant", "pack", ty, "none", [], "v"]);
    let match_v = |site: &str| {
        json!([
            "match",
            site,
            "v",
            [],
            [
                ["none", [], [["yield", []]]],
                ["rng", ["r"], [["yield", []]]]
            ],
            []
        ])
    };
    let duplicate = fixture(
        json!([]),
        json!([]),
        json!([make, match_v("first"), match_v("second"), ["return", []]]),
    );
    let error = admit_supplied(&bytes(&duplicate), &ark_backend(None)).unwrap_err();
    assert_eq!(
        (error.code, error.detail.as_str()),
        (
            ErrorCode::Ssa,
            "interactive-resource-reuse: consumed operand v"
        )
    );
    let drop = fixture(
        json!([]),
        json!([]),
        json!([make, ["release", ["v"]], ["return", []]]),
    );
    let error = admit_supplied(&bytes(&drop), &ark_backend(None)).unwrap_err();
    assert_eq!(
        (error.code, error.detail.as_str()),
        (ErrorCode::Type, "release-resource")
    );
    let zero = fixture(
        json!([]),
        json!([]),
        json!([make, match_v("once"), ["return", []]]),
    );
    let (out, backend) = run(&bytes(&zero), ark_backend(None), vec![]);
    assert!(out.unwrap().is_empty());
    assert_eq!(backend.active_frames(), 0);
}

#[test]
fn active_retained_bytes_and_resource_exhaustion_stay_terminal() {
    let ty = physical(
        "Large",
        json!([["empty", []], ["payload", ["field:bls12-381.fr"]]]),
    );
    let j = fixture(
        json!([]),
        json!([]),
        json!([["variant", "pack", ty, "empty", [], "v"], ["return", []]]),
    );
    let (out, backend) = run(
        &bytes(&j),
        backend()
            .policy(Policy {
                max_value_bytes: 512,
                ..Policy::default()
            })
            .build(),
        vec![],
    );
    assert!(
        matches!(out.unwrap_err().kind,StopKind::Backend(e) if e.code=="exhausted:output-bytes")
    );
    assert_eq!(backend.active_frames(), 0);
    let ty = physical("R", json!([["r", ["rng:bls12-381.fr"]]]));
    let j = fixture(
        json!([["r", RNG]]),
        json!([]),
        json!([
            ["variant", "pack", ty, "r", ["r"], "v"],
            [
                "match",
                "case",
                "v",
                [],
                [[
                    "r",
                    ["r"],
                    [
                        ["op", "draw", "draw", [], ["r"], ["x", "next"]],
                        ["yield", []]
                    ]
                ]],
                []
            ],
            ["return", []]
        ]),
    );
    let mut backend = ark_backend(None);
    let r = backend.issue_rng(domain(), 0).unwrap();
    let old = r.clone();
    let (out, backend) = run(&bytes(&j), backend, vec![r]);
    assert!(
        matches!(out.unwrap_err().kind,StopKind::Backend(e) if e.code=="exhausted:resource-budget")
    );
    assert_eq!(backend.observe(token(&old)).unwrap().generation, 1);
    assert_eq!(backend.active_frames(), 0);
}

#[test]
fn resource_variant_transfers_through_local_function_ports() {
    let ty = physical(
        "Guard",
        json!([["guard", ["resource_unit:Slot.A"]], ["zero", []]]),
    );
    let mut j = fixture(json!([]), json!([UNIT]), json!([["return", []]]));
    j[3] = json!([
        [
            "function",
            "Make",
            [],
            [ty],
            [
                ["op", "issue", "make", [], [], ["g"]],
                ["variant", "pack", ty, "guard", ["g"], "v"],
                ["return", ["v"]]
            ],
            ["Make", []]
        ],
        [
            "function",
            "Use",
            [["v", ty]],
            [UNIT],
            [
                [
                    "match",
                    "case",
                    "v",
                    [],
                    [
                        ["guard", ["g"], [["yield", ["g"]]]],
                        ["zero", [], [["stop", "none", "refused"]]]
                    ],
                    ["out"]
                ],
                ["return", ["out"]]
            ],
            ["Use", []]
        ]
    ]);
    j[4][0][7] = json!([
        ["local", "make", "Make", [], ["v"]],
        ["local", "use", "Use", ["v"], ["g"]],
        ["return", ["g"]]
    ]);
    let (out, backend) = run(&bytes(&j), ark_backend(None), vec![]);
    let guard = out.unwrap().remove(0);
    backend.validate_value(&guard).unwrap();
    assert_eq!(backend.active_frames(), 0);
    let consume = fixture(
        json!([["g", UNIT]]),
        json!([]),
        json!([["op", "consume", "consume", [], ["g"], []], ["return", []]]),
    );
    let old = guard.clone();
    let (out, backend) = run(&bytes(&consume), backend, vec![guard]);
    assert!(out.unwrap().is_empty());
    assert_eq!(
        backend.validate_value(&old).unwrap_err().code,
        "refused:capability-unissued"
    );
}

#[test]
fn zero_trip_variant_carry_preserves_incoming_resource() {
    let ty = physical("Carry", json!([["rng", ["rng:bls12-381.fr"]]]));
    let j = fixture(
        json!([
            ["r", RNG],
            ["lo", "index@native.index/1"],
            ["hi", "index@native.index/1"]
        ]),
        json!([RNG]),
        json!([
            ["variant", "pack", ty, "rng", ["r"], "v"],
            [
                "for",
                "loop",
                "i",
                "lo",
                "hi",
                [["state", "v"]],
                [],
                [["stop", "loop-stop", "abort"]],
                ["next"]
            ],
            [
                "match",
                "case",
                "next",
                [],
                [["rng", ["r"], [["yield", ["r"]]]]],
                ["r1"]
            ],
            ["return", ["r1"]]
        ]),
    );
    for upper in [0, 1] {
        let mut backend = ark_backend(None);
        let rng = backend.issue_rng(domain(), 4).unwrap();
        let old = rng.clone();
        let (out, backend) = run(
            &bytes(&j),
            backend,
            vec![rng, Value::Index(0), Value::Index(upper)],
        );
        if upper == 0 {
            backend.validate_value(&out.unwrap()[0]).unwrap();
        } else {
            assert_eq!(out.unwrap_err().kind, StopKind::Explicit("abort".into()));
        }
        assert_eq!(backend.observe(token(&old)).unwrap().generation, 0);
        assert_eq!(backend.active_frames(), 0);
    }
    let mut capture = j.clone();
    capture[3][0][4][1][5] = json!([]);
    capture[3][0][4][1][6] = json!(["v"]);
    capture[3][0][4][1][8] = json!([]);
    let error = admit_supplied(&bytes(&capture), &ark_backend(None)).unwrap_err();
    assert_eq!(
        (error.code, error.detail.as_str()),
        (ErrorCode::Capture, "affine local loop capture")
    );
}

#[test]
fn wrong_nominal_same_layout_refuses() {
    let a = physical("A", json!([["ok", ["field:bls12-381.fr"]]]));
    let b = physical("B", json!([["ok", ["field:bls12-381.fr"]]]));
    let mut j = fixture(
        json!([["x", FIELD]]),
        json!([]),
        json!([["variant", "pack", a, "ok", ["x"], "v"], ["return", []]]),
    );
    j[3][0][3] = json!([a]);
    j[3][0][4][1] = json!(["return", ["v"]]);
    // Retain the variant only as a local intermediate, with matching call
    // arity. The participant must not expose a variant at its output boundary.
    j[4][0][7][0][4] = json!(["discarded"]);
    admit_supplied(&bytes(&j), &ark_backend(None)).unwrap();

    j[3][0][3] = json!([b]);
    let error = admit_supplied(&bytes(&j), &ark_backend(None)).unwrap_err();
    assert_eq!(error.code, ErrorCode::Signature);
    assert_eq!(error.detail, "function-return-types: operand type v");
}

#[test]
fn duplicate_affine_captures_refuse() {
    let ty = physical("Z", json!([["z", []]]));
    let mut j = fixture(
        json!([["r", RNG]]),
        json!([]),
        json!([
            ["variant", "pack", ty, "z", [], "v"],
            [
                "match",
                "case",
                "v",
                ["r"],
                [["z", [], [["yield", []]]]],
                []
            ],
            ["return", []]
        ]),
    );
    admit_supplied(&bytes(&j), &ark_backend(None)).unwrap();
    j[3][0][4][1][3] = json!(["r", "r"]);
    let error = admit_supplied(&bytes(&j), &ark_backend(None)).unwrap_err();
    assert_eq!(error.code, ErrorCode::Ssa);
    assert_eq!(
        error.detail,
        "interactive-resource-reuse: consumed operand r"
    );
}

#[test]
fn private_match_cannot_schedule_transcript_challenges() {
    let ty = physical("Private", json!([["a", []], ["b", []]]));
    let transcript = "transcript:merlin3.bls12-381.fr64be/1@host.resource/1";
    let mut j = fixture(
        json!([["t", transcript]]),
        json!([]),
        json!([
            ["variant", "pack", ty, "a", [], "v"],
            [
                "match",
                "case",
                "v",
                ["t"],
                [
                    [
                        "a",
                        [],
                        [
                            [
                                "op",
                                "challenge",
                                "challenge",
                                ["Protocol", "instance", "P", "V", "site"],
                                ["t"],
                                ["x", "next"]
                            ],
                            ["yield", []]
                        ]
                    ],
                    ["b", [], [["yield", []]]]
                ],
                []
            ],
            ["return", []]
        ]),
    );
    j[1].as_array_mut().unwrap().push(json!([
        "challenge",
        "transcript.challenge",
        ["merlin3.bls12-381.fr64be/1"],
        "arkworks/transcript.challenge"
    ]));
    let mut outside_match = j.clone();
    outside_match[3][0][4] = json!([j[3][0][4][1][4][0][2][0], ["return", []]]);
    admit_supplied(&bytes(&outside_match), &ark_backend(None)).unwrap();
    let error = admit_supplied(&bytes(&j), &ark_backend(None)).unwrap_err();
    assert_eq!(error.detail, "match-protocol-effect");
}

#[test]
fn shared_descriptor_graph_refusal_corpus() {
    let cases: Json = serde_json::from_str(include_str!(
        "../../../tests/fixtures/variants/descriptors.json"
    ))
    .unwrap();
    for row in cases.as_array().unwrap() {
        let bytes = serde_json::to_vec(&row[2]).unwrap();
        let spelling = format!("variant:{}", zkc_test_support::hex(&bytes));
        let parsed = LogicalType::parse(&spelling);
        assert_eq!(
            parsed.is_ok(),
            row[1].as_bool().unwrap(),
            "{}: {parsed:?}",
            row[0]
        );
        // The corpus is shared with the compiler and the formal reader, which
        // name their refusals differently, so the native identifier for each
        // row is kept here rather than in the fixture.
        let expected = match row[0].as_str().unwrap() {
            "canonical" => continue,
            "raised-version" => "variant:version",
            "forward-reference" | "leading-zero" | "negative-reference" | "missing-reference"
            | "self-reference" => "variant:graph-reference",
            "duplicate-root" | "unused-entry" | "alternate-order" => "variant:canonical",
            "number-node" | "object-node" | "non-ascii" => "variant:graph-node",
            "empty-nominal" => "variant:nominal",
            "physical-payload" => "variant:payload",
            "noncanonical-leaf" => "noncanonical nominal spelling",
            "unknown-leaf" => "explicit nominal identity required",
            "exponential-expansion" | "expanded-depth" | "expansion-ratio" => "variant:graph-limit",
            other => panic!("corpus row {other} has no expected refusal here"),
        };
        let error = parsed.unwrap_err();
        assert_eq!(
            (error.code, error.detail.as_str()),
            (ErrorCode::Type, expected),
            "{}",
            row[0]
        );
    }
}
