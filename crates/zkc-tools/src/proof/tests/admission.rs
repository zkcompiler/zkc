//! Independently authored Program and deployment: the verifier returns the
//! second received Boolean. Public input binding is a separate Host property.
use super::*;

fn deployment() -> Json {
    let boolean = "bool@native.bool/1";
    let candidate = json!([
        "zkc.program/1",
        [],
        "physical",
        [],
        [
            [
                "participant",
                "p",
                "root",
                "P",
                [],
                [["a", boolean], ["b", boolean], ["public", boolean]],
                [],
                [
                    ["send", "first", "first", "V", "a"],
                    ["send", "second", "second", "V", "b"],
                    ["return", []]
                ],
                []
            ],
            [
                "participant",
                "v",
                "root",
                "V",
                [],
                [["public", boolean]],
                [boolean],
                [
                    ["receive", "first", "first", "P", "a", boolean],
                    ["receive", "second", "second", "P", "b", boolean],
                    ["return", ["b"]]
                ],
                []
            ]
        ],
        [["entry", "main", [["P", "p"], ["V", "v"]]]]
    ]);
    let origin = |site| {
        hex(&logical::encode_tree(&json!([
            "zkc.native-origin-template/1",
            "main",
            [],
            [],
            ["message", "protocol", site, site, "P", "V"]
        ]))
        .unwrap())
    };
    let first = origin("first");
    let second = origin("second");
    let descriptor = json!([
        "zkc.native-proof-descriptor/4",
        [
            "zkc.native-proof-policy/4",
            "main",
            "P",
            "V",
            "3",
            "",
            "",
            ["2"],
            []
        ],
        "zkc.native-origin/2",
        [["message", first], ["message", second]],
        [["V", "2", "bool", "zkcv.bool/1"]],
        [
            [first, "bool", "zkcv.bool/1"],
            [second, "bool", "zkcv.bool/1"]
        ]
    ]);
    let mut result = json!([
        "zkc.native-proof/4",
        "0".repeat(64),
        descriptor,
        "",
        candidate.to_string(),
        "",
        [
            [
                "P",
                "p",
                [["0", "bool"], ["1", "bool"], ["2", "bool"]],
                [],
                [],
                ""
            ],
            ["V", "v", [["2", "bool"]], [["3", "bool"]], [], "0"]
        ],
        ["true", "false"],
        [[first, "first"], [second, "second"]]
    ]);
    seal(&mut result);
    result
}

fn seal(value: &mut Json) {
    value[3] = json!(hash(&logical::encode_tree(&value[2]).unwrap()));
    value[5] = json!(hash(value[4].as_str().unwrap().as_bytes()));
}

fn admit(value: &Json) -> Result<NativeDeployment> {
    let bytes = serde_json::to_vec(value).unwrap();
    NativeDeployment::admit(&bytes, &hash(&bytes), Default::default())
}

fn request(producer: bool, decision: bool, public: bool) -> ProofInputs {
    let value = |v| InputValue::Native(Box::new(Value::Bool(v)));
    ProofInputs {
        public: vec![value(public)],
        inputs: if producer {
            vec![value(!decision), value(decision), value(public)]
        } else {
            vec![value(public)]
        },
        context: b"independent host case".to_vec(),
        services: vec![],
        transcript_budget: 0,
    }
}

#[test]
fn actual_received_decision_and_public_context_govern_verification() {
    let deployment = admit(&deployment()).unwrap();
    for decision in [false, true] {
        let produced = deployment
            .execute_typed(&request(true, decision, true), None)
            .unwrap();
        assert!(produced.cleanup_errors.is_empty());
        assert_eq!(produced.messages, 2);
        let proof = produced.outcome.unwrap();
        // Two canonical Boolean frames, in the actual send order.
        assert_eq!(proof.len(), 70);
        let mut expected = Vec::new();
        for value in [!decision, decision] {
            expected.extend([7, 0, 0, 0, 0, 0, 0, 0]);
            expected.extend(b"ZKCV\x01\x05");
            expected.push(u8::from(value));
        }
        assert_eq!(&proof[40..], expected);
        let verified = deployment
            .execute_typed(&request(false, true, true), Some(&proof))
            .unwrap();
        assert_eq!(verified.messages, 2);
        assert!(verified.cleanup_errors.is_empty());
        if decision {
            assert!(verified.outcome.is_ok());
            assert!(matches!(verified.outputs.unwrap()[&3], Value::Bool(true)));
            let changed = deployment
                .execute_typed(&request(false, true, false), Some(&proof))
                .unwrap();
            assert_eq!(changed.outcome.unwrap_err(), "proof-header");
            assert!(changed.outputs.is_none());
        } else {
            assert_eq!(verified.outcome.unwrap_err(), "artifact-rejected");
            assert!(verified.outputs.is_none());
        }
    }
}

#[test]
fn wire_role_public_and_authority_checks_keep_their_refusal_order() {
    let valid = deployment();
    let mut bad = valid.clone();
    bad[8][0][1] = json!("second");
    bad[8][1][1] = json!("first");
    bad[6][0][1] = json!("wrong-participant");
    bad[2][4][0][1] = json!("1");
    seal(&mut bad);
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-wire-map");
    bad[8] = valid[8].clone();
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-role-map");
    bad[6] = valid[6].clone();
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-public-map");
    bad[2][4] = valid[2][4].clone();
    seal(&mut bad);
    let bytes = serde_json::to_vec(&bad).unwrap();
    let extra_authority = SetupAuthority {
        keys: [(2, [0; 32])].into(),
        inputs: BTreeMap::new(),
    };
    assert_eq!(
        NativeDeployment::admit(&bytes, &hash(&bytes), extra_authority).unwrap_err(),
        "native-proof-key-authority"
    );
    assert!(admit(&bad).is_ok());
}

#[test]
fn authentication_and_inner_bindings_precede_candidate_and_interface_checks() {
    assert_eq!(
        NativeDeployment::admit(b"not json", &"0".repeat(64), Default::default()).unwrap_err(),
        "native-proof-deployment-binding"
    );
    let mut bad = deployment();
    bad[3] = json!("0".repeat(64));
    bad[4] = json!("invalid candidate");
    bad[6] = json!([]);
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-descriptor-binding");
    bad[3] = json!(hash(&logical::encode_tree(&bad[2]).unwrap()));
    assert_eq!(admit(&bad).unwrap_err(), "native-proof-candidate-binding");
    seal(&mut bad);
    // Compare with independent ordinary Program admission of the same bad bytes.
    let backend = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "native-proof", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let expected = admit_supplied(b"invalid candidate", &backend)
        .unwrap_err()
        .to_string();
    assert_eq!(admit(&bad).unwrap_err(), expected);
}

#[test]
fn message_origins_are_unique_complete_and_match_both_participants() {
    let valid = deployment();
    let mut duplicate = valid.clone();
    duplicate[2][3][1] = duplicate[2][3][0].clone();
    seal(&mut duplicate);
    assert_eq!(admit(&duplicate).unwrap_err(), "native-proof-origin-map");
    let mut missing = valid.clone();
    missing[2][5].as_array_mut().unwrap().pop();
    seal(&mut missing);
    assert_eq!(admit(&missing).unwrap_err(), "native-proof-message-map");
    let mut drift = valid;
    let mut candidate: Json = serde_json::from_str(drift[4].as_str().unwrap()).unwrap();
    candidate[4][1][7][0][2] = json!("other-schema");
    drift[4] = json!(candidate.to_string());
    seal(&mut drift);
    assert_eq!(admit(&drift).unwrap_err(), "native-proof-wire-map");
}
