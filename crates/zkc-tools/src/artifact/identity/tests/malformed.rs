use super::*;

#[test]
fn substantive_reference_and_shape_errors_fail_closed() {
    for (mutate, code) in [
        (
            |s: &mut Json| {
                s[2][1][1] = json!("Draw");
            },
            "identity-duplicate-symbol",
        ),
        (
            |s: &mut Json| {
                s[3][0][7][1][1] = json!("msg");
            },
            "identity-duplicate-site",
        ),
        (
            |s: &mut Json| {
                s[3][0][7][1][3] = json!("missing");
            },
            "identity-callee-reference",
        ),
        (
            |s: &mut Json| {
                s[2][1][4][0][2] = json!("missing");
            },
            "identity-binding-reference",
        ),
        (
            |s: &mut Json| {
                s[3][0][7][0][6] = json!("ok");
            },
            "identity-ssa-binding",
        ),
        (
            |s: &mut Json| {
                s[2][1][4].as_array_mut().unwrap().reverse();
            },
            "identity-terminator",
        ),
    ] as [(fn(&mut Json), &str); 6]
    {
        let mut s = source();
        mutate(&mut s);
        assert_eq!(Identity::derive(&s, &descriptor()).err().unwrap(), code);
    }
    let mut d = descriptor();
    d[5][1][0][0] = json!("GenericDraw");
    assert_eq!(
        Identity::derive(&source(), &d).err().unwrap(),
        "identity-draw-target"
    );
    let i = identity(&source());
    let mut c = configuration();
    c[3][0][0] = json!("missing");
    assert_eq!(
        i.configuration(&c).unwrap_err(),
        "identity-receive-instance"
    );
    c[3][0][0] = json!("root");
    c[3][0][2] = json!("check");
    assert_eq!(i.configuration(&c).unwrap_err(), "identity-receive-site");
    // Identity derivation is the normalized policy's; an exact descriptor
    // and a descriptor under another tag are both refused.
    for (index, value) in [(8, "exact"), (0, "zkc.construction/2")] {
        let mut d = descriptor();
        d[index] = json!(value);
        assert_eq!(
            Identity::derive(&source(), &d).err().unwrap(),
            "identity-descriptor"
        );
    }
    assert_eq!(
        Identity::derive(
            &json!(["zkc.protocol/2", "p", [], [], [], []]),
            &descriptor()
        )
        .err()
        .unwrap(),
        "identity-source-version"
    );
}

#[test]
fn malicious_shapes_are_bounded_before_clones_and_recursion() {
    let mut s = source();
    s[1][0][1] = json!("x".repeat(4097));
    assert_eq!(
        Identity::derive(&s, &descriptor()).err().unwrap(),
        "identity-string-limit"
    );
    let mut deep = json!("");
    for _ in 0..66 {
        deep = json!([deep]);
    }
    assert_eq!(
        Identity::derive(&deep, &descriptor()).err().unwrap(),
        "identity-tree-limit"
    );
    let wide = Json::Array(vec![json!([]); 32_769]);
    assert_eq!(
        Identity::derive(&wide, &descriptor()).err().unwrap(),
        "identity-tree-limit"
    );
    assert_eq!(
        Identity::derive(&json!({"source": []}), &descriptor())
            .err()
            .unwrap(),
        "identity-tree-kind"
    );
    let i = identity(&source());
    let oversized = json!([
        "zkc.public-configuration/1",
        [["vk", "t", "a".repeat(io::INPUT_LIMIT)]],
        [],
        []
    ]);
    assert_eq!(
        i.configuration(&oversized).unwrap_err(),
        "identity-tree-limit"
    );
    assert_eq!(
        bounds::serialize(&source(), 10).unwrap_err(),
        "identity-byte-limit"
    );
}

#[test]
fn repeated_binding_expansion_obeys_aggregate_output_limit() {
    let mut s = source();
    // Compact source, massive if every occurrence copied the large binding
    // arguments without a running output budget. No semantic admission claim.
    s[1][1][2] = json!(["x".repeat(4000)]);
    let mut ops = Vec::new();
    for n in 0..5000 {
        ops.push(json!([
            "op",
            format!("guard{n}"),
            "require_binding",
            [],
            ["arg"],
            []
        ]));
    }
    ops.push(json!(["return", ["arg"]]));
    s[2][1][4] = Json::Array(ops);
    assert!(serde_json::to_vec(&s).unwrap().len() < 1 << 20);
    assert_eq!(
        Identity::derive(&s, &descriptor()).err().unwrap(),
        "identity-tree-limit"
    );
}

#[test]
fn arbitrary_truncations_and_wrong_kinds_never_panic() {
    fn locations(value: &Json, path: String, out: &mut Vec<String>) {
        out.push(path.clone());
        if let Json::Array(a) = value {
            for (i, v) in a.iter().enumerate() {
                locations(v, format!("{path}/{i}"), out);
            }
        }
    }
    let source = library();
    let descriptor = generic_descriptor();
    let mut paths = Vec::new();
    locations(&source, String::new(), &mut paths);
    for path in paths {
        for bad in [json!(null), json!([]), json!(["malformed"])] {
            let mut changed = source.clone();
            *changed.pointer_mut(&path).unwrap() = bad;
            let result = std::panic::catch_unwind(|| Identity::derive(&changed, &descriptor));
            assert!(result.is_ok(), "panic at {path}");
        }
    }
}
