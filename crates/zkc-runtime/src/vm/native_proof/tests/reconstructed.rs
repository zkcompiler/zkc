//! Endpoint checks deliberately do not claim equality with absent source.
use super::*;

fn append_request(f: &mut Fixture) {
    let mut request = event(false);
    request.reconstructed = true;
    request.origin = zkc_format::logical::encode_tree(&json!([
        "zkc.native-origin-template/0",
        "main",
        [],
        [],
        ["message", "Round", "request", "request", "V", "P"]
    ]))
    .unwrap()
    .iter()
    .map(|b| format!("{b:02x}"))
    .collect();
    let mut helper = f.program[2][0].clone();
    helper[1] = json!("request");
    helper[4][1][3] = json!([request.origin]);
    helper[5][0] = json!("request");
    f.program[2].as_array_mut().unwrap().push(helper);
    for participant in f.program[3].as_array_mut().unwrap() {
        let body = participant[6].as_array_mut().unwrap();
        let mut returned = body.pop().unwrap();
        let values = returned[1].as_array_mut().unwrap();
        let previous = values.last().unwrap().clone();
        *values.last_mut().unwrap() = json!("request_state");
        body.push(json!([
            "local",
            "request",
            "request",
            [previous, "candidate"],
            ["request_state"]
        ]));
        body.push(returned);
    }
    f.events.push(request);
}
fn fixture() -> Fixture {
    let mut f = Fixture::native();
    append_request(&mut f);
    f
}
fn decode_error(f: &Fixture) {
    assert!(
        Program::decode(
            f.program.to_string().as_bytes(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
        )
        .is_err()
    );
}

#[test]
fn request_after_final_challenge_admits_combined_and_each_endpoint() {
    fixture().admit(None).unwrap();
    for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
        fixture()
            .selected(operation)
            .admit(Some(operation))
            .unwrap();
    }
}

#[test]
fn reconstructed_class_cannot_replace_a_selected_delivery() {
    for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
        let mut f = fixture().selected(operation);
        f.events[2].reconstructed = true;
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-observation-order"
        );
        let mut f = fixture().selected(operation);
        f.events[3].reconstructed = false;
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-observation-payload"
        );
    }
}

#[test]
fn request_requires_native_profile_and_message_metadata() {
    let mut f = fixture();
    f.suite = None;
    assert_eq!(f.admit(None).unwrap_err().0, "native-proof-events");
    let mut f = Fixture::custom();
    f.events[0].reconstructed = true;
    assert_eq!(
        f.admit(None).unwrap_err().0,
        "native-proof-reconstructed-profile"
    );
    for field in 0..7 {
        let mut f = fixture();
        let request = &mut f.events[3];
        match field {
            0 => request.payload = None,
            1 => request.bound = Some(8),
            2 => request.count = Some(1),
            3 => request.difficulty = Some(0),
            4 => request.start_inputs = Some(vec![]),
            5 => request.contract = "transcript.native.indexed.challenge".into(),
            _ => {
                f.events[0].reconstructed = true;
            }
        }
        assert_eq!(
            f.admit(None).unwrap_err().0,
            "native-proof-reconstructed-message",
            "mutation {field}"
        );
    }
}

#[test]
fn helper_classification_requires_actual_origin_payload_and_full_metadata() {
    let mut f = fixture();
    f.events[3].payload = Some(super::super::super::LogicalType::parse("index").unwrap());
    assert_eq!(f.admit(None).unwrap_err().0, "native-proof-state-chain");
    let mut f = fixture();
    f.events.swap(2, 3);
    assert_eq!(f.admit(None).unwrap_err().0, "native-proof-state-chain");
    let mut f = fixture();
    // A valid helper for a different ordinary origin does not acquire the class.
    f.program[2][3][4][1][3] = json!([f.events[0].origin]);
    assert!(f.admit(None).is_err());
    let mut f = fixture();
    f.events[1].reconstructed = true;
    assert_eq!(
        f.admit(None).unwrap_err().0,
        "native-proof-reconstructed-message"
    );
}

#[test]
fn surviving_request_transport_and_unobserved_messages_refuse() {
    for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
        let mut f = fixture().selected(operation);
        let transport = if operation == NativeProofOperation::Prove {
            json!([
                "receive",
                "request_wire",
                "request_wire",
                "V",
                "extra",
                BOOL
            ])
        } else {
            json!(["send", "request_wire", "request_wire", "P", "candidate"])
        };
        f.program[3][0][6]
            .as_array_mut()
            .unwrap()
            .insert(4, transport);
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-state-chain"
        );
        let mut f = fixture().selected(operation);
        let transport = if operation == NativeProofOperation::Prove {
            json!(["send", "extra", "extra", "V", "candidate"])
        } else {
            json!(["receive", "extra", "extra", "P", "extra", BOOL])
        };
        f.program[3][0][6]
            .as_array_mut()
            .unwrap()
            .insert(4, transport);
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-observation-order"
        );
    }
}

#[test]
fn unsent_private_request_payload_refuses() {
    let mut f = fixture().selected(NativeProofOperation::Prove);
    f.program[3][0][4]
        .as_array_mut()
        .unwrap()
        .insert(2, json!(["secret", BOOL]));
    f.program[3][0][6][4][3][1] = json!("secret");
    let maps = BTreeMap::from([("P".into(), vec![0, 1, 2])]);
    assert_eq!(
        f.admit_with(Some(NativeProofOperation::Prove), &maps, &[0], 0)
            .unwrap_err()
            .0,
        "native-proof-private-dependency"
    );
}

#[test]
fn helper_payload_cannot_hide_computation_or_state() {
    let mut f = fixture();
    f.program[2][3][4][1][4][1] = json!("t");
    decode_error(&f);
    let mut f = fixture();
    f.program[2][3][4].as_array_mut().unwrap().insert(
        1,
        json!(["bool_constant", "fabricated", "fabricated", true]),
    );
    f.program[2][3][4][2][4][1] = json!("fabricated");
    assert_eq!(
        f.admit(None).unwrap_err().0,
        "native-proof-helper-signature"
    );
    let mut f = fixture();
    f.program[3][0][6][4][3][1] = json!("t3");
    decode_error(&f);
}

#[test]
fn reconstructed_requests_keep_gated_witness_rules() {
    for difficulty in [Some(0), Some(3)] {
        let mut f = block_fixture(difficulty);
        append_request(&mut f);
        f.admit(None).unwrap();
        for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
            let mut selected = Fixture {
                program: f.program.clone(),
                events: f.events.clone(),
                plan: None,
                suite: f.suite,
            }
            .selected(operation);
            selected.remove_functions(&[if operation == NativeProofOperation::Prove {
                "challenge"
            } else {
                "search"
            }]);
            selected.admit(Some(operation)).unwrap();
            selected.program[3][0][6][5][3][1] = json!("w");
            // Ordinary data positions cannot accept the witness type.
            decode_error(&selected);
        }
    }
}

#[test]
fn witness_cannot_leak_into_a_request_with_the_same_payload_type() {
    for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
        let mut f = block_fixture(Some(0));
        append_request(&mut f);
        let state = f.program[2][4][2][0][1].clone();
        let index = "index@native.index/0";
        f.events[3].payload = Some(super::super::super::LogicalType::parse("index").unwrap());
        f.program[1].as_array_mut().unwrap().push(json!([
            "op_request",
            "transcript.native.indexed.observe.data",
            [BLOCK_SUITE, "index"],
            "plonky3/transcript.native.indexed.observe.data",
            []
        ]));
        f.program[2][4][2] = json!([["t", state], ["v", index]]);
        f.program[2][4][4][1][2] = json!("op_request");
        for participant in f.program[3].as_array_mut().unwrap() {
            participant[6][5][3][1] = json!("w");
        }
        let mut f = f.selected(operation);
        f.remove_functions(&[if operation == NativeProofOperation::Prove {
            "challenge"
        } else {
            "search"
        }]);
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-state-escape"
        );
    }
}

fn repeated_fixture() -> Fixture {
    let mut f = fixture();
    let bytes = zkc_format::logical::native_origin_template(
        std::slice::from_ref(&f.events[3].origin),
        "message",
    )
    .unwrap();
    let mut origin = zkc_format::logical::decode_tree(&bytes).unwrap();
    origin[2] = json!([["repeat", "Round", "requests"]]);
    f.events[3].origin = zkc_format::logical::encode_tree(&origin)
        .unwrap()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    let index = "index@native.index/0";
    f.program[1].as_array_mut().unwrap().extend([
        json!(["append", "indices.append", [], "native/indices.append", []]),
        json!([
            "constant",
            "index.constant",
            [],
            "native/index.constant",
            []
        ]),
    ]);
    let helper = &mut f.program[2][3];
    helper[2].as_array_mut().unwrap().push(json!(["i", index]));
    helper[4][1][3] = json!([f.events[3].origin]);
    helper[4][1][4][2] = json!("coords1");
    helper[4].as_array_mut().unwrap().insert(
        1,
        json!([
            "op",
            "coordinate",
            "append",
            [],
            ["coords", "i"],
            ["coords1"]
        ]),
    );
    f.program[2].as_array_mut().unwrap().push(json!([
        "function",
        "request_count",
        [],
        [index],
        [
            ["op", "count", "constant", ["2"], [], ["n"]],
            ["return", ["n"]]
        ],
        ["request_count", []]
    ]));
    for (endpoint, participant) in f.program[3].as_array_mut().unwrap().iter_mut().enumerate() {
        let body = participant[6].as_array_mut().unwrap();
        body.truncate(4);
        body.extend([
            json!(["local", "count", "request_count", [], ["n"]]),
            json!([
                "loop",
                "requests",
                ["value", "n", "2", "i"],
                [["loop_state", "t3"]],
                [["candidate", "candidate"], ["n", "n"]],
                [
                    [
                        "local",
                        "request",
                        "request",
                        ["loop_state", "candidate", "i"],
                        ["request_state"]
                    ],
                    ["yield", ["request_state"]]
                ],
                ["final_state"]
            ]),
            json!([
                "return",
                if endpoint == 0 {
                    vec!["final_state"]
                } else {
                    vec!["candidate", "final_state"]
                }
            ]),
        ]);
    }
    f
}

#[test]
fn reconstructed_repeat_requires_the_actual_induction_operand() {
    repeated_fixture().admit(None).unwrap();
    for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
        let mut f = repeated_fixture().selected(operation);
        f.admit(Some(operation)).unwrap();
        // Same index type, but not the induction SSA.
        f.program[3][0][6][5][5][0][3][2] = json!("n");
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-coordinate-operand"
        );
    }
    let mut f = repeated_fixture();
    f.program[2][3][4].as_array_mut().unwrap().insert(
        1,
        json!(["op", "fabricated", "constant", ["0"], [], ["fabricated"]]),
    );
    f.program[2][3][4][2][4][1] = json!("fabricated");
    assert_eq!(
        f.admit(None).unwrap_err().0,
        "native-proof-helper-coordinates"
    );
}

#[test]
fn nested_requests_transport_coordinates_through_renamed_capture_formals() {
    fn nested() -> Fixture {
        let mut f = repeated_fixture();
        let bytes = zkc_format::logical::native_origin_template(
            std::slice::from_ref(&f.events[3].origin),
            "message",
        )
        .unwrap();
        let mut origin = zkc_format::logical::decode_tree(&bytes).unwrap();
        origin[2] = json!([
            ["repeat", "Outer", "rounds"],
            ["repeat", "Round", "requests"]
        ]);
        f.events[3].origin = zkc_format::logical::encode_tree(&origin)
            .unwrap()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let helper = &mut f.program[2][3];
        helper[2]
            .as_array_mut()
            .unwrap()
            .insert(2, json!(["outer", "index@native.index/0"]));
        helper[4][2][3] = json!([f.events[3].origin]);
        helper[4][1][4][0] = json!("outer_coords");
        helper[4].as_array_mut().unwrap().insert(
            1,
            json!([
                "op",
                "outer_coordinate",
                "append",
                [],
                ["coords", "outer"],
                ["outer_coords"]
            ]),
        );
        for participant in f.program[3].as_array_mut().unwrap() {
            let mut inner = participant[6][5].clone();
            inner[3][0][1] = json!("outer_state");
            inner[4] = json!([
                ["inner_candidate", "candidate"],
                ["inner_n", "n"],
                ["outer_coordinate", "outer_i"]
            ]);
            inner[5][0][3] = json!(["loop_state", "inner_candidate", "outer_coordinate", "i"]);
            inner[6] = json!(["inner_result"]);
            participant[6][5] = json!([
                "loop",
                "rounds",
                ["value", "n", "2", "outer_i"],
                [["outer_state", "t3"]],
                [["candidate", "candidate"], ["n", "n"]],
                [inner, ["yield", ["inner_result"]]],
                ["final_state"]
            ]);
        }
        f
    }
    nested().admit(None).unwrap();
    for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
        let mut f = nested().selected(operation);
        f.admit(Some(operation)).unwrap();
        // A count has the right type, but cannot replace the captured outer
        // induction value passed to the actual request helper.
        f.program[3][0][6][5][5][0][5][0][3][2] = json!("inner_n");
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-coordinate-operand"
        );
        let mut f = nested().selected(operation);
        f.program[3][0][6][5][5][0][4][2][1] = json!("n");
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-loop-state"
        );
    }
}

#[test]
fn observation_after_final_challenge_cannot_be_omitted() {
    for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
        let mut f = fixture().selected(operation);
        f.remove_functions(&["request"]);
        let body = f.program[3][0][6].as_array_mut().unwrap();
        body.remove(4);
        let values = body[4][1].as_array_mut().unwrap();
        *values.last_mut().unwrap() = json!("t3");
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-state-chain"
        );
    }
}
