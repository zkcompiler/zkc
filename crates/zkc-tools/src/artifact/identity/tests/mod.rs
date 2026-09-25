use super::*;

mod malformed;
mod normalization;
mod scopes;

fn descriptor() -> Json {
    json!([
        "zkc.construction/1",
        "main",
        "P",
        "V",
        [["ok", [["V", "ok"]]]],
        ["coins", [["Draw", "draw"]]],
        "0",
        "merlin3.bls12-381.fr64be/1",
        "normalized"
    ])
}

fn source() -> Json {
    json!([
        "zkc.protocol/1",
        [
            [
                "rng_binding",
                "random.draw",
                ["bls12-381.fr"],
                "arkworks/random.draw"
            ],
            ["require_binding", "control.require", [], ""]
        ],
        [
            [
                "function",
                "Draw",
                [["rng", "rng:bls12-381.fr"]],
                ["field:bls12-381.fr", "rng:bls12-381.fr"],
                [
                    ["op", "draw", "rng_binding", [], ["rng"], ["c", "next"]],
                    ["return", ["c", "next"]]
                ],
                ["Draw", []]
            ],
            [
                "function",
                "Check",
                [["arg", "bool"]],
                ["bool"],
                [
                    ["op", "require", "require_binding", [], ["arg"], []],
                    ["return", ["arg"]]
                ],
                ["Check", []]
            ]
        ],
        [[
            "protocol",
            "Root",
            ["P", "V"],
            [],
            [
                ["payload", "P", "bool"],
                ["ok", "V", "bool"],
                ["coins", "V", "rng:bls12-381.fr"]
            ],
            [["V", "bool"], ["V", "rng:bls12-381.fr"]],
            [],
            [
                [
                    "message",
                    "msg",
                    "bool-wire",
                    "P",
                    "V",
                    "payload",
                    "received"
                ],
                ["local", "check", "V", "Check", ["received"], ["checked"]],
                [
                    "local",
                    "sample",
                    "V",
                    "Draw",
                    ["coins"],
                    ["challenge", "next"]
                ],
                ["return", ["checked", "next"]]
            ]
        ]],
        [["instance", "root", "Root", [], [], [["P", "P"], ["V", "V"]]]],
        [["entry", "main", "root"]]
    ])
}

fn configuration() -> Json {
    json!([
        "zkc.public-configuration/1",
        [],
        [],
        [["root", "V", "msg", "vk"]]
    ])
}

fn identity(s: &Json) -> Identity {
    Identity::derive(s, &descriptor()).unwrap()
}

fn root(i: &Identity) -> Vec<u8> {
    i.binding(
        &json!(""),
        &json!([]),
        &json!(["zkc.public-configuration/1", [], [], []]),
    )
    .unwrap()
}

fn library() -> Json {
    let mut s = source();
    s[3][0][7][2][3] = json!("Configured");
    json!([
        "zkc.library/1",
        [[
            "generic_function",
            "GenericDraw",
            [["G", "Group"], ["F", "Field"]],
            [["Field", ["F"]]],
            [["rng", "rng:F"]],
            ["field:F", "rng:F"],
            [
                [
                    "op",
                    "generic_draw",
                    "random.draw",
                    ["F"],
                    [],
                    ["rng"],
                    ["c", "next"]
                ],
                ["return", ["c", "next"]]
            ]
        ]],
        [
            [
                "configure",
                "Partial",
                "GenericDraw",
                [["F", "bls12-381.fr"]],
                []
            ],
            [
                "configure",
                "Configured",
                "Partial",
                [["G", "bls12-381.g1"]],
                [["generic_draw", "arkworks/random.draw"]]
            ],
            ["configure", "UnusedOpen", "GenericDraw", [], []]
        ],
        s
    ])
}

fn generic_descriptor() -> Json {
    let mut d = descriptor();
    d[5][1] = json!([["Configured", "generic_draw"]]);
    d
}

#[test]
fn same_field_suites_have_distinct_descriptor_and_binding_identity() {
    let src = source();
    let a = Identity::derive(&src, &descriptor()).unwrap();
    let mut d = descriptor();
    d[7] = json!("spongefish0.7.4.keccak.bls12-381.fr64be/1");
    let b = Identity::derive(&src, &d).unwrap();
    assert_eq!(a.normalized, b.normalized);
    assert_ne!(a.descriptor, b.descriptor);
    let context = json!("context");
    let public = json!([]);
    let configuration = json!([]);
    assert_ne!(
        a.binding(&context, &public, &configuration).unwrap(),
        b.binding(&context, &public, &configuration).unwrap()
    );
}

mod local_control;
