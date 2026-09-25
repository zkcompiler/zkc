use super::*;

fn controlled_source() -> Json {
    let mut s = source();
    s[1].as_array_mut().unwrap().push(json!([
        "index_binding",
        "index.constant",
        [],
        "arkworks/index.constant"
    ]));
    s[2].as_array_mut().unwrap().push(json!([
        "function",
        "Helper",
        [["x", "bool"]],
        ["bool"],
        [
            ["op", "guard", "require_binding", [], ["x"], []],
            ["return", ["x"]]
        ],
        ["Helper", []]
    ]));
    s[2][1][4] = json!([
        ["op", "zero", "index_binding", ["0"], [], ["lo"]],
        ["op", "one", "index_binding", ["1"], [], ["hi"]],
        [
            "for",
            "repeat",
            "i",
            "lo",
            "hi",
            [["state", "arg"]],
            [],
            [
                [
                    "if",
                    "choose",
                    "state",
                    ["state"],
                    [["yield", ["state"]]],
                    [
                        ["apply", "helper_call", "Helper", [], ["state"], ["checked"]],
                        ["yield", ["checked"]]
                    ],
                    ["selected"]
                ],
                ["yield", ["selected"]]
            ],
            ["answer"]
        ],
        ["return", ["answer"]]
    ]);
    s
}
#[test]
fn identity_covers_nested_helpers_and_dead_branch_bodies() {
    let s = controlled_source();
    let base = Identity::derive(&s, &descriptor()).unwrap();
    let mut changed = s.clone();
    // This helper is reachable only inside the loop's else region.
    changed[2][2][4]
        .as_array_mut()
        .unwrap()
        .insert(1, json!(["op", "second", "require_binding", [], ["x"], []]));
    assert_ne!(
        root(&base),
        root(&Identity::derive(&changed, &descriptor()).unwrap())
    );
    let mut changed = s;
    changed[2][1][4][2][7][0][5] = json!([["yield", ["state"]]]);
    assert_ne!(
        root(&base),
        root(&Identity::derive(&changed, &descriptor()).unwrap())
    );
}
#[test]
fn identity_region_alpha_normalization_and_capture_scope() {
    let s = controlled_source();
    let base = Identity::derive(&s, &descriptor()).unwrap();
    fn rename(v: &mut Json) {
        match v {
            Json::String(s)
                if matches!(
                    s.as_str(),
                    "arg" | "state" | "i" | "lo" | "hi" | "checked" | "selected" | "answer"
                ) =>
            {
                *s = format!("renamed_{s}")
            }
            Json::Array(a) => a.iter_mut().for_each(rename),
            _ => {}
        }
    }
    let mut other = s.clone();
    rename(&mut other[2][1]);
    assert_eq!(
        root(&base),
        root(&Identity::derive(&other, &descriptor()).unwrap())
    );
    let mut other = s.clone();
    other[2][1][4][2][7][0][3] = json!([]);
    assert_eq!(
        Identity::derive(&other, &descriptor()).err().unwrap(),
        "identity-ssa-reference"
    );
    let mut other = s;
    other[2][1][4][2][7][0][1] = json!("repeat");
    assert_eq!(
        Identity::derive(&other, &descriptor()).err().unwrap(),
        "identity-duplicate-site"
    );
}
