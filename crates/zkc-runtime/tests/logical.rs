use serde_json::json;
use zkc_runtime::{interactive::Limits, logical::*};

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
fn public_root_strings_have_separate_tree_ceiling() {
    let public_hex = "ab".repeat(8192);
    let root = json!([
        "zkc.artifact-binding",
        [],
        [],
        "",
        [["table", "table:bls12-381.fr", public_hex]],
        ["zkc.public-configuration", [], [], []]
    ]);
    let bytes = encode_tree(&root).unwrap();
    assert_eq!(decode_tree(&bytes).unwrap(), root);
    assert_eq!(Limits::STRING_BYTES, 4096);
    assert_eq!(Limits::ARTIFACT_BYTES, 4 * 1024 * 1024);
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
    use zkc_runtime::logical::native_origin_template;
    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
    let query = json!([
        "zkc.native-origin-template/0",
        "main",
        [["apply", "main", "subprotocol"]],
        [],
        [
            "query",
            "Round",
            "draw",
            "input_2",
            "random.bls12-381.fr/0",
            "draw",
            "V"
        ]
    ]);
    let bytes = encode_tree(&query).unwrap();
    let encoded = hex(&bytes);
    assert_eq!(
        native_origin_template(std::slice::from_ref(&encoded), "query").unwrap(),
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
        assert!(native_origin_template(&[encoded], "query").is_err());
    }
    assert!(native_origin_template(std::slice::from_ref(&encoded), "message").is_err());
    assert!(native_origin_template(std::slice::from_ref(&encoded), "unknown").is_err());
    assert!(native_origin_template(&[], "query").is_err());
    assert!(native_origin_template(&[encoded.clone(), encoded.clone()], "query").is_err());
    for end in 0..encoded.len() {
        assert!(native_origin_template(&[encoded[..end].into()], "query").is_err());
    }
    for text in [
        format!("{encoded}00"),
        encoded.to_uppercase(),
        "ff".repeat(2049),
    ] {
        assert!(native_origin_template(&[text], "query").is_err());
    }
    for slot in 0..5 {
        let mut bad = query.clone();
        bad[slot] = match slot {
            0 => json!("invalid.native-origin-template"),
            1 => json!(""),
            2 => json!(["contains space"]),
            3 => json!(["0"]),
            _ => json!(["query", "Round", "draw", "input_2", "random", "draw"]),
        };
        assert!(native_origin_template(&[hex(&encode_tree(&bad).unwrap())], "query").is_err());
    }
    let message = json!([
        "zkc.native-origin-template/0",
        "main",
        [],
        [],
        ["message", "Round", "response", "response", "P", "V"]
    ]);
    let bytes = encode_tree(&message).unwrap();
    assert_eq!(
        native_origin_template(&[hex(&bytes)], "message").unwrap(),
        bytes
    );
    // Hostile array counts cannot cause a large allocation through this reader.
    let mut bad = bytes;
    bad[1..9].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(native_origin_template(&[hex(&bad)], "message").is_err());
}

#[test]
fn indexed_native_origins_require_explicit_coordinates_and_template_format() {
    use zkc_runtime::logical::{indexed_native_origin, native_origin_template};
    let encoded = |v: &serde_json::Value| {
        encode_tree(v)
            .unwrap()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    };
    let template = json!([
        "zkc.native-origin-template/0",
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
            "random.bls12-381.fr/0",
            "draw",
            "V"
        ]
    ]);
    let attrs = [encoded(&template)];

    native_origin_template(&attrs, "query").unwrap();
    for coordinates in [vec![0, 0], vec![2, 7], vec![u64::MAX, u64::MAX]] {
        let mut expected = template.clone();
        expected[0] = json!("zkc.native-origin/0");
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
            0 => json!("zkc.native-origin/0"),
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

#[test]
fn query_templates_name_their_method_and_index_bounds_are_canonical() {
    use zkc_runtime::interactive::{LogicalType, PhysicalType, ServiceContract};
    use zkc_runtime::logical::{native_query_template, uniform_index_bound};
    let template = |method: &str| {
        let bytes = encode_tree(&json!([
            "zkc.native-origin-template/0",
            "main",
            [],
            [],
            [
                "query",
                "Round",
                "sample",
                "input_0",
                "random.koala-bear.ext8-binomial3/0",
                method,
                "V"
            ]
        ]))
        .unwrap();
        (
            bytes.iter().map(|b| format!("{b:02x}")).collect::<String>(),
            bytes,
        )
    };
    let (draw, draw_bytes) = template("draw");
    let (index, index_bytes) = template("index");
    assert_eq!(
        native_query_template(std::slice::from_ref(&draw), "draw").unwrap(),
        draw_bytes
    );
    assert_eq!(
        native_query_template(std::slice::from_ref(&index), "index").unwrap(),
        index_bytes
    );
    assert!(native_query_template(std::slice::from_ref(&draw), "index").is_err());
    assert!(native_query_template(std::slice::from_ref(&index), "draw").is_err());

    for (text, bound) in [
        ("1", 1),
        ("2", 2),
        ("32", 32),
        ("9223372036854775808", 1 << 63),
    ] {
        assert_eq!(uniform_index_bound(text).unwrap(), bound);
    }
    for text in [
        "",
        "0",
        "3",
        "032",
        "+8",
        "8 ",
        "9223372036854775809",
        "18446744073709551615",
        "18446744073709551616",
    ] {
        assert!(uniform_index_bound(text).is_err(), "{text:?}");
    }

    let index_type = PhysicalType::default_for(LogicalType::parse("index").unwrap()).unwrap();
    let signature = ServiceContract::RandomExtensionField
        .signature("index")
        .unwrap();
    assert_eq!(signature.inputs, vec![index_type.clone()]);
    assert_eq!(signature.outputs, vec![index_type]);
    for contract in [
        ServiceContract::RandomBls12381Field,
        ServiceContract::RandomBn254Field,
        ServiceContract::RandomRistrettoField,
    ] {
        assert!(contract.signature("index").is_none());
        assert!(contract.signature("draw").is_some());
    }
}
