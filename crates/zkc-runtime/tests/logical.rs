use serde_json::json;
use zkc_runtime::{logical::*, vm::Limits};

// Independent grammar, deliberately not encode_tree as the oracle.
fn reference(value: &serde_json::Value, out: &mut Vec<u8>) {
    if let Some(text) = value.as_str() {
        out.push(0);
        out.extend_from_slice(&(text.len() as u64).to_le_bytes());
        out.extend_from_slice(text.as_bytes());
    } else {
        let array = value.as_array().unwrap();
        out.push(1);
        out.extend_from_slice(&(array.len() as u64).to_le_bytes());
        for value in array {
            reference(value, out);
        }
    }
}

#[test]
fn borrowed_stream_matches_independent_grammar_and_short_writes() {
    use std::io::{self, Write};
    struct Short(Vec<u8>);
    impl Write for Short {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            let n = bytes.len().min(3);
            self.0.extend_from_slice(&bytes[..n]);
            Ok(n)
        }
        fn flush(&mut self) -> io::Result<()> {
            panic!("caller owns flush")
        }
    }
    for n in [0, 1, 255, 511, 512, 513, 8192] {
        let bytes: Vec<_> = (0..n).map(|i| i as u8).collect();
        let nested = json!(["é", ["", "end"]]);
        let nodes = [
            Tree::Text("binding"),
            Tree::Json(&nested),
            Tree::Hex(&bytes),
        ];
        let encoding = Tree::Array(&nodes).prepare().unwrap();
        let expected = json!(["binding", nested, zkc_test_support::hex(&bytes)]);
        let mut reference_bytes = Vec::new();
        reference(&expected, &mut reference_bytes);
        assert_eq!(encoding.size(), reference_bytes.len());
        assert_eq!(encoding.to_vec().unwrap(), reference_bytes);
        let mut sink = Short(Vec::new());
        encoding.write(&mut sink).unwrap();
        assert_eq!(sink.0, reference_bytes);
    }
    // The complete preflight refuses a late malformed child before any writes.
    let invalid = json!(["valid", false]);
    assert_eq!(Tree::Json(&invalid).prepare().unwrap_err().0, "tree-kind");
    let bytes = vec![0; (TreeLimits::BYTES - 9) / 2];
    assert!(Tree::Hex(&bytes).prepare().is_ok());
    assert!(Tree::Hex(&vec![0; bytes.len() + 1]).prepare().is_err());
    let encoding = Tree::Text("abc").prepare().unwrap();
    let mut sink = &mut [0u8; 10][..];
    assert_eq!(
        encoding.write(&mut sink).unwrap_err().kind(),
        io::ErrorKind::WriteZero
    );
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
        assert_eq!(
            native_origin_template(&[encoded], "query").unwrap_err().0,
            "native-origin"
        );
    }
    for kind in ["message", "unknown"] {
        assert_eq!(
            native_origin_template(std::slice::from_ref(&encoded), kind)
                .unwrap_err()
                .0,
            "native-origin"
        );
    }
    for attrs in [vec![], vec![encoded.clone(), encoded.clone()]] {
        assert_eq!(
            native_origin_template(&attrs, "query").unwrap_err().0,
            "native-origin"
        );
    }
    for end in 0..encoded.len() {
        assert_eq!(
            native_origin_template(&[encoded[..end].into()], "query")
                .unwrap_err()
                .0,
            if end == 0 || end % 2 != 0 {
                "native-origin"
            } else {
                "tree-truncated"
            },
            "hex prefix {end}"
        );
    }
    for (text, code) in [
        (format!("{encoded}00"), "tree-trailing"),
        (encoded.to_uppercase(), "native-origin"),
        ("ff".repeat(2049), "native-origin"),
    ] {
        assert_eq!(
            native_origin_template(&[text], "query").unwrap_err().0,
            code
        );
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
        assert_eq!(
            native_origin_template(&[hex(&encode_tree(&bad).unwrap())], "query")
                .unwrap_err()
                .0,
            "native-origin"
        );
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
    assert_eq!(
        native_origin_template(&[hex(&bad)], "message")
            .unwrap_err()
            .0,
        "tree-limit"
    );
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
    for event in [
        json!(["start", "main", "call"]),
        json!(["message", "step", "reply", "Schema", "P", "V"]),
        json!([
            "query",
            "step",
            "draw",
            "input_4",
            "random.bls12-381.fr/0",
            "draw",
            "V"
        ]),
        json!([
            "query",
            "step",
            "sample",
            "input_18446744073709551615",
            "random.koala-bear.ext8-binomial3/0",
            "index",
            "V"
        ]),
    ] {
        let kind = event[0].as_str().unwrap();
        let template = json!([
            "zkc.native-origin-template/0",
            "main",
            [
                ["repeat", "main", "outer"],
                ["apply", "main", "call"],
                ["repeat", "step", "inner"]
            ],
            [],
            event
        ]);
        let attrs = [encoded(&template)];

        let mut template_bytes = Vec::new();
        reference(&template, &mut template_bytes);
        assert_eq!(
            native_origin_template(&attrs, kind).unwrap(),
            template_bytes
        );
        if kind == "query" {
            assert_eq!(
                native_query_template(&attrs, event[5].as_str().unwrap()).unwrap(),
                template_bytes
            );
        }
        for coordinates in [
            [0, 0],
            [2, 7],
            [u64::MAX, 0],
            [0, u64::MAX],
            [u64::MAX, u64::MAX],
            [0, 0],
        ] {
            let mut expected = template.clone();
            expected[0] = json!("zkc.native-origin/0");
            expected[3] = json!(coordinates.iter().map(u64::to_string).collect::<Vec<_>>());
            let mut expected_bytes = Vec::new();
            reference(&expected, &mut expected_bytes);
            assert_eq!(
                indexed_native_origin(&attrs, kind, &coordinates).unwrap(),
                expected_bytes
            );
        }
        for coordinates in [vec![], vec![0], vec![0, 1, 2], vec![0; 65]] {
            assert_eq!(
                indexed_native_origin(&attrs, kind, &coordinates)
                    .unwrap_err()
                    .0,
                "native-origin-coordinates"
            );
        }
        for slot in [0, 2, 3, 4] {
            let mut changed = template.clone();
            changed[slot] = match slot {
                0 => json!("zkc.native-origin/0"),
                2 => json!([["loop", "main", "outer"]]),
                3 => json!(["0"]),
                _ => json!(["repeat", "main", "outer"]),
            };
            assert_eq!(
                native_origin_template(&[encoded(&changed)], kind)
                    .unwrap_err()
                    .0,
                "native-origin"
            );
        }
        for (text, code) in [
            (attrs[0].clone() + "00", "tree-trailing"),
            (attrs[0].to_uppercase(), "native-origin"),
            ("00".repeat(2049), "native-origin"),
        ] {
            assert_eq!(native_origin_template(&[text], kind).unwrap_err().0, code);
        }
    }
}

#[test]
fn native_origin_validation_precedes_method_and_coordinate_checks() {
    // Later faults must not hide decoding failures, even when the decoded
    // tree would also fail the origin grammar or the coordinate count is wrong.
    for (bytes, code) in [
        (vec![2; 9], "tree-tag"),
        (vec![0], "tree-truncated"),
        (
            [vec![0], 1u64.to_le_bytes().to_vec(), vec![255]].concat(),
            "tree-utf8",
        ),
        (
            [vec![1], u64::MAX.to_le_bytes().to_vec()].concat(),
            "tree-limit",
        ),
        (
            [encode_tree(&json!(["wrong-shape"])).unwrap(), vec![0]].concat(),
            "tree-trailing",
        ),
    ] {
        let attrs = [zkc_test_support::hex(&bytes)];
        assert_eq!(
            indexed_native_origin(&attrs, "unknown", &[0; 65])
                .unwrap_err()
                .0,
            code
        );
        assert_eq!(
            native_query_template(&attrs, "wrong-method").unwrap_err().0,
            code
        );
        // Hex and attribute cardinality checks precede even malformed trees.
        assert_eq!(
            indexed_native_origin(&[attrs[0].clone() + "g0"], "query", &[])
                .unwrap_err()
                .0,
            "native-origin"
        );
        assert_eq!(
            native_query_template(&[attrs[0].clone(), attrs[0].clone()], "draw")
                .unwrap_err()
                .0,
            "native-origin"
        );
    }
}

#[test]
fn native_origins_complete_a_maximum_size_template() {
    let path: Vec<_> = (0..40)
        .map(|i| json!([if i % 2 == 0 { "apply" } else { "repeat" }, "P", "s"]))
        .collect();
    let mut template = json!([
        "zkc.native-origin-template/0",
        "e".repeat(128),
        path,
        [],
        ["start", "P", "s"]
    ]);
    let mut bytes = Vec::new();
    reference(&template, &mut bytes);
    template[4][2] = json!("s".repeat(1 + 2048 - bytes.len()));
    bytes.clear();
    reference(&template, &mut bytes);
    assert_eq!(bytes.len(), 2048);
    let attrs = [zkc_test_support::hex(&bytes)];
    assert_eq!(native_origin_template(&attrs, "start").unwrap(), bytes);
    let coordinates: Vec<_> = (0..20)
        .map(|i| if i % 2 == 0 { 0 } else { u64::MAX })
        .collect();
    let mut completed = template.clone();
    completed[0] = json!("zkc.native-origin/0");
    completed[3] = json!(coordinates.iter().map(u64::to_string).collect::<Vec<_>>());
    let mut expected = Vec::new();
    reference(&completed, &mut expected);
    assert!(expected.len() > 2048 && expected.len() < 4096);
    assert_eq!(
        indexed_native_origin(&attrs, "start", &coordinates).unwrap(),
        expected
    );

    // One more name byte remains legal grammar but exceeds the template ceiling.
    template[4][2] = json!(template[4][2].as_str().unwrap().to_owned() + "s");
    bytes.clear();
    reference(&template, &mut bytes);
    assert_eq!(bytes.len(), 2049);
    assert_eq!(
        indexed_native_origin(&[zkc_test_support::hex(&bytes)], "start", &coordinates)
            .unwrap_err()
            .0,
        "native-origin"
    );
}

#[test]
fn query_templates_name_their_method_and_index_bounds_are_canonical() {
    use zkc_runtime::logical::{native_query_template, uniform_index_bound};
    use zkc_runtime::vm::{LogicalType, PhysicalType, ServiceContract};
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
    assert_eq!(
        native_query_template(std::slice::from_ref(&draw), "index")
            .unwrap_err()
            .0,
        "native-origin"
    );
    assert_eq!(
        native_query_template(std::slice::from_ref(&index), "draw")
            .unwrap_err()
            .0,
        "native-origin"
    );

    for (text, bound) in [
        ("1", 1),
        ("2", 2),
        ("32", 32),
        ("9223372036854775808", 1 << 63),
        ("3", 3),
        ("9223372036854775809", (1 << 63) + 1),
        ("18446744073709551615", u64::MAX),
    ] {
        assert_eq!(uniform_index_bound(text).unwrap(), bound);
    }
    for text in ["", "0", "032", "+8", "8 ", "18446744073709551616"] {
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
