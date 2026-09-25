use super::*;

#[test]
fn exact_seven_field_vector_preserves_origin_and_public_ports() {
    let s = source();
    let i = identity(&s);
    assert_eq!(
        i.normalized,
        json!([
            "zkc.protocol-identity/1",
            ["entry", "main", "root"],
            [["instance", "root", "Root", [], [], [["P", "P"], ["V", "V"]]]],
            [[
                "protocol",
                "Root",
                ["P", "V"],
                [],
                s[3][0][4],
                s[3][0][5],
                [],
                [
                    ["message", "site0", "bool-wire", "P", "V", "v0", "v3"],
                    ["local", "site1", "V", "Check", ["v3"], ["v4"]],
                    ["local", "site2", "V", "Draw", ["v2"], ["v5", "v6"]],
                    ["return", ["v4", "v6"]]
                ]
            ]],
            [
                [
                    "function",
                    "Check",
                    [["v0", "bool"]],
                    ["bool"],
                    [
                        [
                            "op",
                            "site0",
                            ["operation", "control.require", []],
                            [],
                            ["v0"],
                            []
                        ],
                        ["return", ["v0"]]
                    ],
                    ["Check", []]
                ],
                [
                    "function",
                    "Draw",
                    [["v0", "rng:bls12-381.fr"]],
                    ["field:bls12-381.fr", "rng:bls12-381.fr"],
                    [
                        [
                            "op",
                            "site0",
                            ["operation", "random.draw", ["bls12-381.fr"]],
                            [],
                            ["v0"],
                            ["v1", "v2"]
                        ],
                        ["return", ["v1", "v2"]]
                    ],
                    ["Draw", []]
                ]
            ],
            [],
            []
        ])
    );
    assert_eq!(
        i.source[2][0][4][0],
        json!(["op", "site0", "rng_binding", [], ["rng"], ["c", "next"]])
    );
    assert_eq!(i.descriptor[5][1], json!([["Draw", "site0"]]));
    let tree = zkc_runtime::logical::decode_tree(&root(&i)).unwrap();
    assert_eq!(tree[0], "zkc.artifact-binding/1");
    assert_eq!(tree[1], i.normalized);
    assert_eq!(tree[2], i.descriptor);
}

#[test]
fn simultaneous_label_renaming_resolves_draws_and_receive_selectors() {
    let s = source();
    let base = identity(&s);
    let mut changed = s.clone();
    changed[2][0][4][0][1] = json!("site2");
    changed[2][1][4][0][1] = json!("site0");
    for (op, site) in ["site2", "site0", "site1"].into_iter().enumerate() {
        changed[3][0][7][op][1] = json!(site);
    }
    let mut d = descriptor();
    d[5][1][0][1] = json!("site2");
    let other = Identity::derive(&changed, &d).unwrap();
    let mut c = configuration();
    c[3][0][2] = json!("site2");
    assert_eq!(
        base.configuration(&configuration()).unwrap(),
        other.configuration(&c).unwrap()
    );
    assert_eq!(base.normalized, other.normalized);
    assert_eq!(base.descriptor, other.descriptor);
    assert_eq!(root(&base), root(&other));
    assert!(Identity::derive(&changed, &descriptor()).is_err());
    assert!(other.configuration(&configuration()).is_err());
    // Names equal to canonical coordinates still resolve by ORIGINAL occurrence.
    assert_eq!(other.source[3][0][7][0][1], "site0");
}

#[test]
fn local_ssa_and_binding_aliases_and_physical_choices_are_ignored() {
    let s = source();
    let mut changed = s.clone();
    changed[1][0][0] = json!("renamed_binding");
    changed[1][0][3] = json!("");
    changed[2][0][2][0][0] = json!("fresh");
    changed[2][0][4][0][2] = json!("renamed_binding");
    changed[2][0][4][0][4] = json!(["fresh"]);
    changed[2][0][4][0][5] = json!(["one", "two"]);
    changed[2][0][4][1][1] = json!(["one", "two"]);
    changed[3][0][7][0][6] = json!("new_received");
    changed[3][0][7][1][4] = json!(["new_received"]);
    assert_eq!(root(&identity(&s)), root(&identity(&changed)));
    assert_ne!(identity(&s).source, identity(&changed).source);
    // The function-origin slot is authority, even if it resembles debug data.
    changed[2][0][5][0] = json!("AnotherOrigin");
    assert_ne!(root(&identity(&s)), root(&identity(&changed)));
}

#[test]
fn complete_behavior_and_public_interface_remain_bound() {
    let original = source();
    let expected = root(&identity(&original));
    for mutate in [
        |s: &mut Json| {
            s[2][1][4].as_array_mut().unwrap().remove(0);
        }, // guard removed
        |s: &mut Json| {
            s[2][0][4][0][3] = json!(["different-attribute"]);
        },
        |s: &mut Json| {
            s[1][0][2] = json!(["different-wire-contract"]);
        },
        |s: &mut Json| {
            s[3][0][7][0][2] = json!("different-schema");
        },
        |s: &mut Json| {
            s[3][0][4][0][0] = json!("renamed_public_port");
            s[3][0][7][0][5] = json!("renamed_public_port");
        },
        |s: &mut Json| {
            s[3][0][7].as_array_mut().unwrap().swap(1, 2);
        },
    ] {
        let mut changed = original.clone();
        mutate(&mut changed);
        assert_ne!(expected, root(&identity(&changed)));
    }
}

#[test]
fn public_context_and_all_configuration_bytes_and_order_are_bound() {
    let i = identity(&source());
    let c = json!([
        "zkc.public-configuration/1",
        [
            ["vk", "verifier_key:C", "aa"],
            ["vk2", "verifier_key:C", "bb"]
        ],
        [["P", "cm", "vk"], ["V", "expected", "vk2"]],
        [["root", "V", "msg", "vk"]]
    ]);
    let resolved = i.configuration(&c).unwrap();
    assert_eq!(resolved[3][0][2], "site0");
    for n in 0..3 {
        assert_eq!(resolved[n], c[n]);
    }
    let baseline = i
        .binding(&json!("00"), &json!([["ok", "bool", "aa"]]), &resolved)
        .unwrap();
    assert_ne!(
        baseline,
        i.binding(&json!("01"), &json!([["ok", "bool", "aa"]]), &resolved)
            .unwrap()
    );
    assert_ne!(
        baseline,
        i.binding(&json!("00"), &json!([["ok", "bool", "bb"]]), &resolved)
            .unwrap()
    );
    for group in 1..3 {
        let mut changed = c.clone();
        changed[group].as_array_mut().unwrap().reverse();
        assert_ne!(
            baseline,
            i.binding(
                &json!("00"),
                &json!([["ok", "bool", "aa"]]),
                &i.configuration(&changed).unwrap()
            )
            .unwrap()
        );
    }
    for (path, value) in [("/1/0/2", "cc"), ("/2/0/2", "vk2"), ("/3/0/3", "vk2")] {
        let mut changed = c.clone();
        *changed.pointer_mut(path).unwrap() = json!(value);
        assert_ne!(
            baseline,
            i.binding(
                &json!("00"),
                &json!([["ok", "bool", "aa"]]),
                &i.configuration(&changed).unwrap()
            )
            .unwrap()
        );
    }
}

#[test]
fn unused_valid_declarations_and_top_level_order_do_not_change_identity() {
    let s = source();
    let mut changed = s.clone();
    changed[1].as_array_mut().unwrap().push(json!([
        "unused_binding",
        "field.constant",
        ["bls12-381.fr"],
        ""
    ]));
    changed[2].as_array_mut().unwrap().push(json!([
        "function",
        "Unused",
        [],
        [],
        [["return", []]],
        ["Unused", []]
    ]));
    changed[3].as_array_mut().unwrap().push(json!([
        "protocol",
        "UnusedProtocol",
        ["P", "V"],
        [],
        [],
        [],
        [],
        [["return", []]]
    ]));
    changed[4].as_array_mut().unwrap().push(json!([
        "instance",
        "unused_instance",
        "UnusedProtocol",
        [],
        [],
        [["P", "P"], ["V", "V"]]
    ]));
    changed[5]
        .as_array_mut()
        .unwrap()
        .push(json!(["entry", "unused_entry", "unused_instance"]));
    for group in 1..6 {
        changed[group].as_array_mut().unwrap().reverse();
    }
    assert_eq!(root(&identity(&s)), root(&identity(&changed)));
    // Shape errors cannot hide in an excluded declaration.
    changed[2][0][4] = json!([["unknown", "site"]]);
    assert_eq!(
        Identity::derive(&changed, &descriptor()).err().unwrap(),
        "identity-instruction"
    );
}

#[test]
fn generic_original_body_and_final_definition_order_without_specialization() {
    let s = library();
    let i = Identity::derive(&s, &generic_descriptor()).unwrap();
    assert_eq!(i.normalized[4].as_array().unwrap().len(), 1); // Only ordinary Check.
    assert_eq!(
        i.normalized[5],
        json!([[
            "generic_function",
            "GenericDraw",
            [["G", "Group"], ["F", "Field"]],
            [["Field", ["F"]]],
            [["v0", "rng:F"]],
            ["field:F", "rng:F"],
            [
                [
                    "op",
                    "site0",
                    "random.draw",
                    ["F"],
                    [],
                    ["v0"],
                    ["v1", "v2"]
                ],
                ["return", ["v1", "v2"]]
            ]
        ]])
    );
    assert_eq!(
        i.normalized[6],
        json!([[
            "configure",
            "Configured",
            "GenericDraw",
            [["G", "bls12-381.g1"], ["F", "bls12-381.fr"]],
            []
        ]])
    );
    assert_eq!(
        i.source[2][1][4],
        json!([["site0", "arkworks/random.draw"]])
    );
    assert_eq!(i.descriptor[5][1], json!([["Configured", "site0"]]));
    let mut flattened = s.clone();
    flattened[2][1] = json!([
        "configure",
        "Configured",
        "GenericDraw",
        [["F", "bls12-381.fr"], ["G", "bls12-381.g1"]],
        []
    ]);
    flattened[2].as_array_mut().unwrap().reverse();
    assert_eq!(
        root(&i),
        root(&Identity::derive(&flattened, &generic_descriptor()).unwrap())
    );
    // Static terms/literals/parameter names remain original, with no algebraic reduction.
    flattened[1][0][6][0][4] = json!(["12345678901234567890"]);
    assert_ne!(
        root(&i),
        root(&Identity::derive(&flattened, &generic_descriptor()).unwrap())
    );
}
