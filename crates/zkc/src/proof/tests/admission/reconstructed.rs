use super::*;

const SUITE: &str = "merlin3.bls12-381.fr64be/0";
const STATE: &str = "transcript:merlin3.bls12-381.fr64be/0@host.resource/0";
const BOOL: &str = "bool@native.bool/0";
const FIELD: &str = "field:bls12-381.fr@arkworks.fr/0";

fn native() -> Json {
    let mut value = deployment();
    let origin = |tail: Json| {
        hex(&logical::encode_tree(&json!([
            "zkc.native-origin-template/0",
            "main",
            [],
            [],
            tail
        ]))
        .unwrap())
    };
    let query = origin(json!([
        "query",
        "protocol",
        "draw",
        "input_3",
        "random.bls12-381.fr/0",
        "draw",
        "V"
    ]));
    let delivery = origin(json!([
        "message", "protocol", "delivery", "delivery", "V", "P"
    ]));
    let request = origin(json!([
        "message", "protocol", "request", "request", "V", "P"
    ]));
    let first = value[2][3][0][1].clone();
    let second = value[2][3][1][1].clone();
    value[2][1][5] = json!(SUITE);
    value[2][1][6] = json!(["3"]);
    value[2][1][8] = json!([["draw", "delivery"]]);
    value[2][3] = json!([
        ["message", first],
        ["message", second],
        ["query", query],
        ["message", delivery],
        ["reconstructed-message", request]
    ]);
    value[2][5].as_array_mut().unwrap().extend([
        json!([delivery, "field:bls12-381.fr", "zkcv.field.bls12-381.fr/0"]),
        json!([request, "bool", "zkcv.bool/0"]),
    ]);
    let mut program: Json = serde_json::from_str(value[4].as_str().unwrap()).unwrap();
    program[1] = json!([
        ["empty", "indices.empty", [], "native/indices.empty", []],
        [
            "op_observe",
            "transcript.native.indexed.observe.data",
            [SUITE, "bool"],
            "arkworks/transcript.native.indexed.observe.data",
            []
        ],
        [
            "op_delivery",
            "transcript.native.indexed.observe.data",
            [SUITE, "field:bls12-381.fr"],
            "arkworks/transcript.native.indexed.observe.data",
            []
        ],
        [
            "op_query",
            "transcript.native.indexed.challenge",
            [SUITE],
            "arkworks/transcript.native.indexed.challenge",
            []
        ]
    ]);
    let observer = |name: &str, origin: &Json, ty: &str, operation: &str| {
        json!([
            "function",
            name,
            [["t", STATE], ["payload", ty]],
            [STATE],
            [
                ["op", "coords", "empty", [], [], ["coords"]],
                [
                    "op",
                    "observe",
                    operation,
                    [origin],
                    ["t", "payload", "coords"],
                    ["next"]
                ],
                ["return", ["next"]]
            ],
            [name, []]
        ])
    };
    program[2] = json!([
        observer("first", &first, BOOL, "op_observe"),
        observer("second", &second, BOOL, "op_observe"),
        observer("delivery", &json!(delivery), FIELD, "op_delivery"),
        observer("request", &json!(request), BOOL, "op_observe"),
        [
            "function",
            "query",
            [["t", STATE]],
            [FIELD, STATE],
            [
                ["op", "coords", "empty", [], [], ["coords"]],
                [
                    "op",
                    "draw",
                    "op_query",
                    [query],
                    ["t", "coords"],
                    ["c", "next"]
                ],
                ["return", ["c", "next"]]
            ],
            ["query", []]
        ]
    ]);
    for i in 0..2 {
        program[3][i][4]
            .as_array_mut()
            .unwrap()
            .push(json!(["t", STATE]));
        program[3][i][5].as_array_mut().unwrap().push(json!(STATE));
        let first = program[3][i][6][0].clone();
        let second = program[3][i][6][1].clone();
        program[3][i][6] = json!([
            first,
            ["local", "observe.first", "first", ["t", "a"], ["t1"]],
            second,
            ["local", "observe.second", "second", ["t1", "b"], ["t2"]],
            ["local", "query", "query", ["t2"], ["c", "t3"]],
            ["local", "delivery", "delivery", ["t3", "c"], ["t4"]],
            ["local", "request", "request", ["t4", "b"], ["t5"]],
            ["return", if i == 0 { vec!["t5"] } else { vec!["b", "t5"] }]
        ]);
    }
    value[4] = json!(program.to_string());
    seal(&mut value);
    value
}

#[test]
fn request_after_final_message_executes_without_a_proof_frame() {
    let host = admit(&native()).unwrap();
    let mut producer = request(true, true, true);
    let mut verifier = request(false, true, true);
    producer.transcript_budget = 1_000_000;
    verifier.transcript_budget = 1_000_000;
    let produced = host.execute(&producer, Invocation::Prove).unwrap();
    assert_eq!(produced.messages, 2);
    let proof = produced.outcome.unwrap();
    assert_eq!(proof.len(), 70); // Two canonical Boolean frames.
    let verified = host.execute(&verifier, Invocation::Verify(&proof)).unwrap();
    assert_eq!(verified.verification_result(), Some(true));
    assert_eq!(verified.messages, 2);
    let missing = host
        .execute(&verifier, Invocation::Verify(&proof[..55]))
        .unwrap();
    assert!(missing.outcome.is_err());
    let mut extra = proof.clone();
    extra.extend_from_slice(&proof[40..55]);
    let extra = host.execute(&verifier, Invocation::Verify(&extra)).unwrap();
    assert!(extra.outcome.is_err());
}

#[test]
fn reconstructed_rows_cannot_consume_selected_delivery_or_own_transport() {
    let mut value = native();
    value[2][3][3][0] = json!("reconstructed-message");
    seal(&mut value);
    assert_eq!(
        admit(&value).unwrap_err(),
        "native-proof-reconstructed-message"
    );
    let mut value = native();
    value[2][3][4][0] = json!("message");
    seal(&mut value);
    assert_eq!(admit(&value).unwrap_err(), "native-proof-event-map");
    let mut value = native();
    let request_origin = value[2][3][4][1].clone();
    value[8]
        .as_array_mut()
        .unwrap()
        .push(json!([request_origin, "request"]));
    seal(&mut value);
    assert_eq!(admit(&value).unwrap_err(), "native-proof-wire-map");
    let mut value = native();
    value[2][5].as_array_mut().unwrap().pop();
    seal(&mut value);
    assert_eq!(admit(&value).unwrap_err(), "native-proof-message-map");
}

#[test]
fn reconstructed_rows_require_installed_profile_direction_and_exact_codec() {
    let mut value = native();
    value[2][1][5] = json!("");
    value[2][1][6] = json!([]);
    value[2][1][8] = json!([]);
    value[2][3].as_array_mut().unwrap().drain(2..4);
    seal(&mut value);
    assert_eq!(
        admit(&value).unwrap_err(),
        "native-proof-reconstructed-profile"
    );
    let mut value = native();
    value[2][3][0][0] = json!("reconstructed-message");
    seal(&mut value);
    assert_eq!(
        admit(&value).unwrap_err(),
        "native-proof-reconstructed-message"
    );
    let mut value = native();
    value[2][5][3][2] = json!("zkc.native-data/0");
    seal(&mut value);
    assert_eq!(admit(&value).unwrap_err(), "native-proof-message-map");
}
