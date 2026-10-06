use serde_json::json;
use zkc_runtime::{
    interactive::{Limits, Origin, PathElement},
    logical::*,
};

fn origin() -> Origin {
    Origin {
        format: zkc_runtime::interactive::ArtifactFormat::ExplicitBindings,
        session: "workerA".into(),
        entry: "main".into(),
        instance: "child".into(),
        path: vec![
            PathElement::Call {
                site: "opening".into(),
                instance: "child".into(),
            },
            PathElement::Loop {
                site: "rounds".into(),
                iteration: 12,
            },
        ],
    }
}
fn attrs() -> Vec<String> {
    ["Protocol", "call", "Draw", "draw", "V"]
        .map(Into::into)
        .to_vec()
}

#[test]
fn independent_known_answers_and_no_json_spelling_dependence() {
    assert_eq!(
        zkc_test_support::hex(&encode_tree(&json!("é")).unwrap()),
        "000200000000000000c3a9"
    );
    assert_eq!(
        zkc_test_support::hex(&encode_tree(&json!(["a", []])).unwrap()),
        "01020000000000000000010000000000000061010000000000000000"
    );
    assert_eq!(
        encode_tree(&serde_json::from_str::<serde_json::Value>(r#"["\u00e9"]"#).unwrap()).unwrap(),
        encode_tree(&json!(["é"])).unwrap()
    );
    assert_ne!(
        encode_tree(&json!("é")).unwrap(),
        encode_tree(&json!("e\u{301}")).unwrap()
    );
    for tree in [
        json!(""),
        json!([]),
        json!(["ab", "c"]),
        json!(["a", "bc"]),
        json!([["a"], "bc"]),
        json!(["a", ["bc"]]),
    ] {
        let b = encode_tree(&tree).unwrap();
        assert_eq!(decode_tree(&b).unwrap(), tree);
        for n in 0..b.len() {
            assert!(decode_tree(&b[..n]).is_err());
        }
        let mut extra = b;
        extra.push(0);
        assert_eq!(decode_tree(&extra).unwrap_err().0, "tree-trailing");
    }
    let trees = [
        json!(""),
        json!([]),
        json!(["ab", "c"]),
        json!(["a", "bc"]),
        json!([["a"], "bc"]),
        json!(["a", ["bc"]]),
    ];
    let bytes = trees
        .iter()
        .map(|t| encode_tree(t).unwrap())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(bytes.len(), trees.len());
}

#[test]
fn hostile_kinds_counts_utf8_depth_and_lengths() {
    for t in [
        json!(null),
        json!(true),
        json!(1),
        json!({"a": "b"}),
        json!([[], 2]),
    ] {
        assert_eq!(encode_tree(&t).unwrap_err().0, "tree-kind");
    }
    for tag in [0, 1, 2, 255] {
        let mut b = vec![tag];
        b.extend(u64::MAX.to_le_bytes());
        assert!(decode_tree(&b).is_err());
    }
    let mut utf8 = vec![0];
    utf8.extend(1u64.to_le_bytes());
    utf8.push(255);
    assert_eq!(decode_tree(&utf8).unwrap_err().0, "tree-utf8");
    assert!(encode_tree(&json!("x".repeat(TreeLimits::STRING_BYTES + 1))).is_err());
    assert!(encode_tree(&json!(vec![""; TreeLimits::ARRAY_LENGTH + 1])).is_err());
    let mut nested = json!("");
    for _ in 0..TreeLimits::DEPTH + 1 {
        nested = json!([nested]);
    }
    assert!(encode_tree(&nested).is_err());
    let mut deep = Vec::new();
    for _ in 0..TreeLimits::DEPTH + 1 {
        deep.push(1);
        deep.extend(1u64.to_le_bytes());
    }
    deep.push(0);
    deep.extend(0u64.to_le_bytes());
    assert!(decode_tree(&deep).is_err());
    assert!(decode_tree(&vec![0; TreeLimits::BYTES + 1]).is_err());
    for s in [
        "",
        "01",
        "-1",
        "+1",
        " 1",
        "1 ",
        "18446744073709551616",
        "١",
    ] {
        assert!(natural_index(s).is_err());
    }
    assert_eq!(natural_index("18446744073709551615").unwrap(), u64::MAX);
}

#[test]
fn origin_exact_tree_session_invariance_and_component_controls() {
    let o = origin();
    let a = attrs();
    let expected = json!([
        "zkc.logical-origin/1",
        "main",
        "child",
        [["call", "opening", "child"], ["loop", "rounds", "12"]],
        ["challenge", "Protocol", "call", "Draw", "draw", "V"]
    ]);
    let bytes = challenge_origin(&o, &a).unwrap();
    assert_eq!(decode_tree(&bytes).unwrap(), expected);
    let mut changed = o.clone();
    changed.session = "different_process".into();
    assert_eq!(bytes, challenge_origin(&changed, &a).unwrap());
    for i in 0..5 {
        let mut b = a.clone();
        b[i].push('x');
        assert_ne!(bytes, challenge_origin(&o, &b).unwrap());
    }
    changed = o.clone();
    changed.entry.push('x');
    assert_ne!(bytes, challenge_origin(&changed, &a).unwrap());
    changed = o.clone();
    changed.instance.push('x');
    assert_ne!(bytes, challenge_origin(&changed, &a).unwrap());
    changed = o.clone();
    changed.path.reverse();
    assert_ne!(bytes, challenge_origin(&changed, &a).unwrap());
    changed = o.clone();
    changed.path.push(PathElement::Loop {
        site: "rounds".into(),
        iteration: 1,
    });
    assert_ne!(bytes, challenge_origin(&changed, &a).unwrap());
    assert_ne!(bytes, message_origin(&o, &a).unwrap());
    assert!(challenge_origin(&o, &a[..4]).is_err());
}

#[test]
fn public_origin_preflight_bounds_all_strings() {
    let a = attrs();
    for slot in 0..7 {
        let mut o = origin();
        let huge = "x".repeat(Limits::STRING_BYTES + 1);
        match slot {
            0 => o.entry = huge,
            1 => o.instance = huge,
            2 => {
                o.path[0] = PathElement::Call {
                    site: huge,
                    instance: "child".into(),
                }
            }
            3 => {
                o.path[0] = PathElement::Call {
                    site: "call".into(),
                    instance: huge,
                }
            }
            4 => {
                o.path[1] = PathElement::Loop {
                    site: huge,
                    iteration: 0,
                }
            }
            5 => {
                o.path[1] = PathElement::Conditional {
                    site: huge,
                    taken: true,
                }
            }
            _ => {
                o.path[1] = PathElement::For {
                    site: huge,
                    index: 0,
                }
            }
        }
        assert_eq!(challenge_origin(&o, &a).unwrap_err().0, "tree-limit");
    }
}

#[test]
fn public_root_strings_have_separate_tree_ceiling() {
    let public_hex = "ab".repeat(8192);
    let root = json!([
        "zkc.artifact-binding/1",
        [],
        [],
        "",
        [["table", "table:bls12-381.fr", public_hex]],
        ["zkc.public-configuration/1", [], [], []]
    ]);
    let bytes = encode_tree(&root).unwrap();
    assert_eq!(decode_tree(&bytes).unwrap(), root);
    assert_eq!(Limits::STRING_BYTES, 4096);
    assert_eq!(Limits::ARTIFACT_BYTES, 1024 * 1024);
    // An individual string may approach the whole 16 MiB budget, but its
    // nine-byte tag/length header is included in the total ceiling.
    let largest = json!("x".repeat(TreeLimits::BYTES - 9));
    let bytes = encode_tree(&largest).unwrap();
    assert_eq!(bytes.len(), TreeLimits::BYTES);
    assert_eq!(decode_tree(&bytes).unwrap(), largest);
    assert!(encode_tree(&json!("x".repeat(TreeLimits::BYTES - 8))).is_err());
}

#[test]
fn native_origins_have_exact_shapes_and_distinct_event_kinds() {
    use zkc_runtime::logical::native_origin;
    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
    let query = json!([
        "zkc.native-origin/1",
        "main",
        ["subprotocol"],
        [],
        [
            "query",
            "Round",
            "draw",
            "input_2",
            "random.bls12-381.fr/1",
            "draw",
            "V"
        ]
    ]);
    let bytes = encode_tree(&query).unwrap();
    let encoded = hex(&bytes);
    assert_eq!(
        native_origin(std::slice::from_ref(&encoded), "query").unwrap(),
        bytes
    );
    for port in [
        "service_2",
        "input_",
        "input_01",
        "input_+1",
        "input_18446744073709551616",
    ] {
        let mut wrong_port = zkc_runtime::logical::decode_tree(&bytes).unwrap();
        wrong_port[4][3] = json!(port);
        let encoded = encode_tree(&wrong_port)
            .unwrap()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        assert!(native_origin(&[encoded], "query").is_err());
    }
    assert!(native_origin(std::slice::from_ref(&encoded), "message").is_err());
    assert!(native_origin(std::slice::from_ref(&encoded), "unknown").is_err());
    assert!(native_origin(&[], "query").is_err());
    assert!(native_origin(&[encoded.clone(), encoded.clone()], "query").is_err());
    for end in 0..encoded.len() {
        assert!(native_origin(&[encoded[..end].into()], "query").is_err());
    }
    for text in [
        format!("{encoded}00"),
        encoded.to_uppercase(),
        "ff".repeat(2049),
    ] {
        assert!(native_origin(&[text], "query").is_err());
    }
    for slot in 0..5 {
        let mut bad = query.clone();
        bad[slot] = match slot {
            0 => json!("zkc.logical-origin/1"),
            1 => json!(""),
            2 => json!(["contains space"]),
            3 => json!(["0"]),
            _ => json!(["query", "Round", "draw", "input_2", "random", "draw"]),
        };
        assert!(native_origin(&[hex(&encode_tree(&bad).unwrap())], "query").is_err());
    }
    let message = json!([
        "zkc.native-origin/1",
        "main",
        [],
        [],
        ["message", "Round", "response", "response", "P", "V"]
    ]);
    let bytes = encode_tree(&message).unwrap();
    assert_eq!(native_origin(&[hex(&bytes)], "message").unwrap(), bytes);
    // Hostile array counts cannot cause a large allocation through this reader.
    let mut bad = bytes;
    bad[1..9].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(native_origin(&[hex(&bad)], "message").is_err());
}

#[test]
fn indexed_native_origins_require_explicit_coordinates_and_separate_versions() {
    use zkc_runtime::logical::{indexed_native_origin, native_origin, native_origin_template};
    let encoded = |v: &serde_json::Value| {
        encode_tree(v)
            .unwrap()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    };
    let template = json!([
        "zkc.native-origin-template/1",
        "main",
        [
            ["repeat", "main", "outer"],
            ["apply", "main", "call"],
            ["repeat", "step", "inner"]
        ],
        [],
        [
            "query",
            "step",
            "draw",
            "input_4",
            "random.bls12-381.fr/1",
            "draw",
            "V"
        ]
    ]);
    let attrs = [encoded(&template)];
    assert!(native_origin(&attrs, "query").is_err());
    native_origin_template(&attrs, "query").unwrap();
    for coordinates in [vec![0, 0], vec![2, 7], vec![u64::MAX, u64::MAX]] {
        let mut expected = template.clone();
        expected[0] = json!("zkc.native-origin/2");
        expected[3] = json!(coordinates.iter().map(u64::to_string).collect::<Vec<_>>());
        assert_eq!(
            indexed_native_origin(&attrs, "query", &coordinates).unwrap(),
            encode_tree(&expected).unwrap()
        );
    }
    for coordinates in [vec![], vec![0], vec![0, 1, 2], vec![0; 65]] {
        assert!(indexed_native_origin(&attrs, "query", &coordinates).is_err());
    }
    for slot in [0, 2, 3, 4] {
        let mut changed = template.clone();
        changed[slot] = match slot {
            0 => json!("zkc.native-origin/1"),
            2 => json!([["loop", "main", "outer"]]),
            3 => json!(["0"]),
            _ => json!(["repeat", "main", "outer"]),
        };
        assert!(native_origin_template(&[encoded(&changed)], "query").is_err());
    }
    for text in [
        attrs[0].clone() + "00",
        attrs[0].to_uppercase(),
        "00".repeat(2049),
    ] {
        assert!(native_origin_template(&[text], "query").is_err());
    }
}
