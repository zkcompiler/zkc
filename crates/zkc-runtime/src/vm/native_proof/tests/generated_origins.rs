use super::*;

fn encode(tree: &Json) -> String {
    zkc_format::logical::encode_tree(tree)
        .unwrap()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

fn encode_origin(protocol: &str, query: bool) -> String {
    let event = if query {
        json!([
            "query",
            protocol,
            "draw",
            "input_0",
            "random.bls12-381.fr/0",
            "draw",
            "V"
        ])
    } else {
        json!([
            "message",
            protocol,
            "oracle_0_7_opening_request",
            "oracle_0_7_opening_request",
            "V",
            "P"
        ])
    };
    let value = json!([
        "zkc.native-origin-template/0",
        "main",
        [["apply", "Root", "call"], ["repeat", "Leaf", "round"]],
        [],
        event
    ]);
    encode(&value)
}

#[test]
fn generated_origin_keeps_loop_lineage_without_reapplying_site_prefix() {
    let protocol = format!("zkc.oracle.{}", "a".repeat(64));
    let origin = encode_origin(&protocol, false);
    assert_eq!(
        native_origin_site(&origin, "message").unwrap(),
        "oracle_0_7_opening_request"
    );
    let decoded = zkc_format::logical::decode_tree(
        &zkc_format::logical::native_origin_template(&[origin], "message").unwrap(),
    )
    .unwrap();
    assert_eq!(
        decoded[2],
        json!([["apply", "Root", "call"], ["repeat", "Leaf", "round"]])
    );
    assert_eq!(
        native_origin_site(&encode_origin("Leaf", false), "message").unwrap(),
        "apply_4_call_oracle_0_7_opening_request"
    );
}

#[test]
fn generated_namespace_refuses_noncanonical_identity_or_query() {
    for suffix in [
        String::new(),
        "a".repeat(63),
        "a".repeat(65),
        "A".repeat(64),
        "g".repeat(64),
        format!("{}-", "a".repeat(63)),
    ] {
        assert!(
            native_origin_site(
                &encode_origin(&format!("zkc.oracle.{suffix}"), false),
                "message"
            )
            .is_err()
        );
    }
    assert!(
        native_origin_site(
            &encode_origin(&format!("zkc.oracle.{}", "a".repeat(64)), true),
            "query"
        )
        .is_err()
    );
}

fn mixed_origin(protocol: &str) -> Json {
    json!([
        "zkc.native-origin-template/0",
        "main",
        [
            ["apply", "Root", "a"],
            ["repeat", "Middle", "rounds"],
            ["apply", "Middle", "b"],
            ["repeat", protocol, "oracle_0_7_round"],
            ["apply", "Leaf", "c"],
            ["branch", "Tail", "choice", "Accepted"],
            ["repeat", "Tail", "tail"]
        ],
        [],
        ["message", protocol, "message", "message", "V", "P"]
    ])
}

fn read_frames(tree: &Json, work: &mut ProofWork) -> Result<Vec<ControlFrame>> {
    // Exercise the frame reader only after the existing template grammar check.
    let bytes = zkc_format::logical::native_origin_template(&[encode(tree)], "message").unwrap();
    let checked = zkc_format::logical::decode_tree(&bytes).unwrap();
    control_frames(&checked, work)
}

#[test]
fn generated_repeat_keeps_actual_site_and_authored_prefix_progression() {
    let protocol = format!("zkc.oracle.{}", "0123456789abcdef".repeat(4));
    let tree = mixed_origin(&protocol);
    let frames = read_frames(&tree, &mut ProofWork(PROOF_WORK)).unwrap();
    assert_eq!(
        frames,
        vec![
            ControlFrame::Repeat {
                protocol: "Middle".into(),
                site: "apply_1_a_rounds".into(),
            },
            ControlFrame::Repeat {
                protocol,
                site: "oracle_0_7_round".into(),
            },
            ControlFrame::Branch {
                protocol: "Tail".into(),
                site: "apply_22_apply_11_apply_1_a_b_c_choice".into(),
                alternative: "Accepted".into(),
            },
            ControlFrame::Repeat {
                protocol: "Tail".into(),
                site: "apply_22_apply_11_apply_1_a_b_c_tail".into(),
            },
        ]
    );
    assert_eq!(repeat_count(&frames), 3);
    assert_eq!(
        native_origin_site(&encode(&tree), "message").unwrap(),
        "message"
    );

    let bytes = zkc_format::logical::indexed_native_origin(&[encode(&tree)], "message", &[2, 3, 5])
        .unwrap();
    assert!(
        zkc_format::logical::indexed_native_origin(&[encode(&tree)], "message", &[2, 3]).is_err()
    );
    let mut dynamic = tree;
    dynamic[0] = json!("zkc.native-origin/0");
    dynamic[3] = json!(["2", "3", "5"]);
    assert_eq!(bytes, zkc_format::logical::encode_tree(&dynamic).unwrap());
}

#[test]
fn ordinary_control_and_event_still_expand_nested_applications() {
    let tree = mixed_origin("Leaf");
    let frames = read_frames(&tree, &mut ProofWork(PROOF_WORK)).unwrap();
    assert_eq!(
        frames[1],
        ControlFrame::Repeat {
            protocol: "Leaf".into(),
            site: "apply_11_apply_1_a_b_oracle_0_7_round".into(),
        }
    );
    assert_eq!(
        native_origin_site(&encode(&tree), "message").unwrap(),
        "apply_22_apply_11_apply_1_a_b_c_message"
    );
}

#[test]
fn generated_repeat_matches_only_exact_actual_control_and_bijective_lineage() {
    let protocol = format!("zkc.oracle.{}", "a".repeat(64));
    let frames = read_frames(&mixed_origin(&protocol), &mut ProofWork(PROOF_WORK)).unwrap();
    let repeat = |site: &str, maximum| ControlPosition::Repeat {
        site: site.into(),
        maximum,
    };
    let branch = |site: &str, alternative: &str| ControlPosition::Branch {
        site: site.into(),
        alternative: alternative.into(),
    };
    let positions = vec![
        repeat("apply_1_a_rounds", 4),
        repeat("oracle_0_7_round", 8),
        branch("apply_22_apply_11_apply_1_a_b_c_choice", "Accepted"),
        repeat("apply_22_apply_11_apply_1_a_b_c_tail", 16),
    ];
    let fixture = Fixture::authored();
    let program = Program::decode(
        fixture.program.to_string().as_bytes(),
        &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
    )
    .unwrap();
    let helpers = BTreeMap::new();
    let mut work = ProofWork(PROOF_WORK);
    let mut walk = ProofWalk {
        admitted: &program,
        helpers: &helpers,
        producer: "P",
        validator: "V",
        validating: true,
        transcript: false,
        affine_state: false,
        calls: BTreeSet::new(),
        verified: BTreeSet::new(),
        states: BTreeSet::new(),
        reached: vec![],
        frames: BTreeMap::new(),
        positions: BTreeMap::new(),
        work: &mut work,
        witness_slots: BTreeSet::new(),
        delivered_witnesses: BTreeSet::new(),
        witness_values: BTreeSet::new(),
    };
    walk.match_frames(&frames, &positions).unwrap();
    walk.match_frames(&frames, &positions).unwrap();
    for (index, wrong) in [
        (0, repeat("rounds", 4)),
        (1, repeat("renamed", 8)),
        (1, repeat("apply_11_apply_1_a_b_oracle_0_7_round", 8)),
        (2, branch("choice", "Accepted")),
        (
            2,
            branch("apply_22_apply_11_apply_1_a_b_c_choice", "Rejected"),
        ),
        (3, repeat("tail", 16)),
        (1, branch("oracle_0_7_round", "Accepted")),
        // Same sites, but the registered source path cannot acquire a new bound.
        (1, repeat("oracle_0_7_round", 9)),
    ] {
        let mut actual = positions.clone();
        actual[index] = wrong;
        assert_eq!(
            walk.match_frames(&frames, &actual).unwrap_err().0,
            "native-proof-control-origin"
        );
    }
    assert_eq!(
        walk.match_frames(&frames, &positions[..3]).unwrap_err().0,
        "native-proof-coordinate-operand"
    );
    // A second canonical protocol cannot alias the registered actual path.
    let other = format!("zkc.oracle.{}", "b".repeat(64));
    let renamed = read_frames(&mixed_origin(&other), &mut ProofWork(PROOF_WORK)).unwrap();
    assert_eq!(
        walk.match_frames(&renamed, &positions).unwrap_err().0,
        "native-proof-control-origin"
    );
}

#[test]
fn malformed_reserved_frame_protocols_are_not_treated_as_authored() {
    for suffix in [
        String::new(),
        "a".repeat(63),
        "a".repeat(65),
        "A".repeat(64),
        "g".repeat(64),
        format!("{}-", "a".repeat(63)),
    ] {
        // All accepted step tags must reject malformed reserved identities.
        // This does not assert producer support for generated Apply or Branch.
        for index in [0, 3, 5] {
            let mut tree = mixed_origin("Leaf");
            tree[2][index][1] = json!(format!("zkc.oracle.{suffix}"));
            assert_eq!(
                read_frames(&tree, &mut ProofWork(PROOF_WORK))
                    .unwrap_err()
                    .0,
                "native-proof-origin"
            );
        }
    }
}

#[test]
fn generated_frame_validation_keeps_cumulative_charge_before_work() {
    let mut tree = mixed_origin(&format!("zkc.oracle.{}", "a".repeat(64)));
    let mut prefix = tree.clone();
    prefix[2].as_array_mut().unwrap().truncate(3);
    let mut work = ProofWork(PROOF_WORK);
    read_frames(&prefix, &mut work).unwrap();
    let prefix_cost = PROOF_WORK - work.0;
    for protocol in [
        format!("zkc.oracle.{}", "a".repeat(64)),
        format!("zkc.oracle.{}", "g".repeat(64)),
    ] {
        tree[2][3][1] = json!(protocol);
        let mut exhausted = ProofWork(prefix_cost);
        assert_eq!(
            read_frames(&tree, &mut exhausted).unwrap_err().0,
            "native-proof-control-limit"
        );
        assert_eq!(exhausted.0, 0);
    }
    assert_eq!(
        read_frames(&tree, &mut ProofWork(PROOF_WORK))
            .unwrap_err()
            .0,
        "native-proof-origin"
    );
}
