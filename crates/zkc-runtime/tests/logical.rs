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
