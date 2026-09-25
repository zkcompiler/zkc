use super::*;

#[test]
fn configuration_using_and_draws_follow_final_definition_across_partial_chain() {
    let s = library();
    let i = Identity::derive(&s, &generic_descriptor()).unwrap();
    let mut other = s.clone();
    other[1][0][6][0][1] = json!("site7");
    other[2][1][4][0][0] = json!("site7");
    let mut d = generic_descriptor();
    d[5][1][0][1] = json!("site7");
    assert_eq!(root(&i), root(&Identity::derive(&other, &d).unwrap()));
    other[2][1][4][0][0] = json!("generic_draw");
    assert_eq!(
        Identity::derive(&other, &d).err().unwrap(),
        "identity-using-site"
    );
    let mut other = s.clone();
    other[2][0][2] = json!("Configured");
    assert_eq!(
        Identity::derive(&other, &generic_descriptor())
            .err()
            .unwrap(),
        "identity-configuration-cycle"
    );
    let mut other = s.clone();
    other[2][1][3] = json!([]);
    assert_eq!(
        Identity::derive(&other, &generic_descriptor())
            .err()
            .unwrap(),
        "identity-open-configuration"
    );
    let mut other = s.clone();
    other[2][1][3] = json!([["F", "bls12-381.fr"]]);
    assert_eq!(
        Identity::derive(&other, &generic_descriptor())
            .err()
            .unwrap(),
        "identity-configuration-rebinding"
    );
}

#[test]
fn nested_zero_loops_bind_fresh_scopes_before_outer_results_and_count_sites_preorder() {
    let mut s = source();
    s[3][0][7] = json!([
        [
            "loop",
            "outer",
            ["constant", "0"],
            [["acc", "ok"]],
            ["payload"],
            [
                [
                    "message",
                    "inner_msg",
                    "bool-wire",
                    "P",
                    "V",
                    "payload",
                    "received"
                ],
                [
                    "loop",
                    "inner",
                    ["constant", "0"],
                    [["inside", "acc"]],
                    ["received"],
                    [
                        ["local", "guard", "V", "Check", ["received"], ["checked"]],
                        ["yield", ["inside"]]
                    ],
                    ["nested_result"]
                ],
                ["yield", ["nested_result"]]
            ],
            ["result"]
        ],
        ["local", "draw", "V", "Draw", ["coins"], ["c", "next"]],
        ["return", ["result", "next"]]
    ]);
    let i = identity(&s);
    assert_eq!(
        i.normalized[3][0][7],
        json!([
            [
                "loop",
                "site0",
                ["constant", "0"],
                [["v0", "v1"]],
                [["v1", "v0"]],
                [
                    ["message", "site1", "bool-wire", "P", "V", "v1", "v2"],
                    [
                        "loop",
                        "site2",
                        ["constant", "0"],
                        [["v0", "v0"]],
                        [["v1", "v2"]],
                        [
                            ["local", "site3", "V", "Check", ["v1"], ["v2"]],
                            ["yield", ["v0"]]
                        ],
                        ["v3"]
                    ],
                    ["yield", ["v3"]]
                ],
                ["v3"]
            ],
            ["local", "site4", "V", "Draw", ["v2"], ["v4", "v5"]],
            ["return", ["v3", "v5"]]
        ])
    );
    assert_eq!(i.source[3][0][7][0][4], json!(["payload"]));
    assert_eq!(i.normalized[4].as_array().unwrap().len(), 2); // zero loop's callee remains.
    let mut changed = s.clone();
    changed[3][0][7][0][5][1][5][0][4] = json!(["nested_result"]);
    assert_eq!(
        Identity::derive(&changed, &descriptor()).err().unwrap(),
        "identity-ssa-reference"
    );
    let mut changed = s.clone();
    changed[3][0][7][0][2][1] = json!("1");
    assert_ne!(root(&i), root(&identity(&changed)));
}

#[test]
fn closure_retains_complete_declared_dependencies_and_repeated_shared_instances() {
    let mut s = source();
    let child = json!([
        "protocol",
        "Child",
        ["P", "V"],
        [],
        [],
        [],
        [],
        [["return", []]]
    ]);
    s[3].as_array_mut().unwrap().push(child);
    s[3][0][6] = json!([["left", "Child", []], ["right", "Child", []]]);
    s[4][0][4] = json!([["left", "shared"], ["right", "shared"]]);
    s[4].as_array_mut().unwrap().push(json!([
        "instance",
        "shared",
        "Child",
        [],
        [],
        [["P", "P"], ["V", "V"]]
    ]));
    let i = identity(&s);
    assert_eq!(i.normalized[2].as_array().unwrap().len(), 2);
    assert_eq!(i.normalized[3].as_array().unwrap().len(), 2);
    assert_eq!(i.normalized[3][0][1], "Child");
    let mut changed = s.clone();
    changed[3][1][7] = json!([["stop", "halt", "V", "reject"]]);
    assert_ne!(root(&i), root(&identity(&changed))); // no call is needed to retain dependency behavior.
    changed[4][0][4].as_array_mut().unwrap().reverse();
    assert_ne!(identity(&changed).normalized[2], i.normalized[2]); // map order retained.
}

#[test]
fn demanded_parent_configuration_is_retained_only_when_it_is_itself_a_callee() {
    let mut s = library();
    s[2][0][3] = json!([["F", "bls12-381.fr"], ["G", "bls12-381.g1"]]);
    s[2][1][3] = json!([]);
    let d = generic_descriptor();
    let base = Identity::derive(&s, &d).unwrap();
    assert_eq!(base.normalized[6].as_array().unwrap().len(), 1);
    s[3][3][0][7].as_array_mut().unwrap().insert(
        3,
        json!([
            "local",
            "parent_call",
            "V",
            "Partial",
            ["next"],
            ["second", "last"]
        ]),
    );
    s[3][3][0][7][4][1] = json!(["checked", "last"]);
    let selected = Identity::derive(&s, &d).unwrap();
    assert_eq!(selected.normalized[6].as_array().unwrap().len(), 2);
    assert_eq!(selected.normalized[6][1][1], "Partial");
    assert_eq!(selected.normalized[6][1][2], "GenericDraw");
}
