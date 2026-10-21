//! Independent carriers exercise admission without a compiler or opposite role.
use super::*;
use serde_json::{Value as Json, json};

const BOOL: &str = "bool@native.bool/0";
const SUITE: &str = "merlin3.bls12-381.fr64be/0";
const STATE: &str = "transcript:merlin3.bls12-381.fr64be/0@host.resource/0";
const FIELD: &str = "field:bls12-381.fr@arkworks.fr/0";

struct Fixture {
    program: Json,
    events: Vec<NativeTranscriptEvent>,
    plan: Option<ConstructionPlan>,
    suite: Option<&'static str>,
}
impl Fixture {
    fn authored() -> Self {
        Self {
            program: json!([
                "zkc.program/0",
                [],
                [],
                [
                    [
                        "participant",
                        "p",
                        "root",
                        "P",
                        [["public", BOOL], ["candidate", BOOL]],
                        [],
                        [
                            ["send", "message", "message", "V", "candidate"],
                            ["return", []]
                        ],
                        []
                    ],
                    [
                        "participant",
                        "v",
                        "root",
                        "V",
                        [["public", BOOL]],
                        [BOOL],
                        [
                            ["receive", "message", "message", "P", "candidate", BOOL],
                            ["return", ["candidate"]]
                        ],
                        []
                    ]
                ],
                [["entry", "main", [["P", "p"], ["V", "v"]]]]
            ]),
            events: vec![],
            plan: None,
            suite: None,
        }
    }
    fn selected(mut self, operation: NativeProofOperation) -> Self {
        let index = usize::from(operation == NativeProofOperation::Verify);
        self.program[3] = json!([self.program[3][index].clone()]);
        self.program[4][0][2] = json!([self.program[4][0][2][index].clone()]);
        self
    }
    fn maps(&self) -> BTreeMap<String, Vec<usize>> {
        self.program[4][0][2]
            .as_array()
            .unwrap()
            .iter()
            .map(|r| {
                let role = r[0].as_str().unwrap();
                (role.into(), if role == "P" { vec![0, 1] } else { vec![0] })
            })
            .collect()
    }
    fn admit(&self, operation: Option<NativeProofOperation>) -> Result<NativeProofEntry> {
        self.admit_with(operation, &self.maps(), &[0], 0)
    }
    fn admit_with(
        &self,
        operation: Option<NativeProofOperation>,
        maps: &BTreeMap<String, Vec<usize>>,
        public: &[usize],
        acceptance: usize,
    ) -> Result<NativeProofEntry> {
        let program = Program::decode(self.program.to_string().as_bytes()).unwrap();
        let construction = ProofConstruction {
            suite: self.suite,
            events: &self.events,
            plan: self.plan.as_ref(),
            source_inputs: maps,
        };
        match operation {
            None => NativeProofEntry::new(program, "main", "P", "V", acceptance, construction),
            Some(operation) => NativeProofEntry::new_for_operation(
                program,
                "main",
                "P",
                "V",
                acceptance,
                construction,
                operation,
                public,
            ),
        }
    }
    fn native() -> Self {
        let mut f = Self::authored();
        let observe = event(false);
        let query = event(true);
        let mut delivery = event(false);
        delivery.origin = crate::logical::encode_tree(&json!([
            "zkc.native-origin-template/0",
            "main",
            [],
            [],
            ["message", "Round", "delivery", "delivery", "V", "P"]
        ]))
        .unwrap()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
        delivery.payload = Some(super::super::LogicalType::parse("field:bls12-381.fr").unwrap());
        f.events = vec![observe.clone(), query.clone(), delivery.clone()];
        f.suite = Some(SUITE);
        f.program[1] = json!([
            ["empty", "indices.empty", [], "native/indices.empty"],
            [
                "op_observe",
                observe.contract,
                [SUITE, "bool"],
                "arkworks/transcript.native.indexed.observe.data"
            ],
            [
                "op_challenge",
                query.contract,
                [SUITE],
                "arkworks/transcript.native.indexed.challenge"
            ],
            [
                "op_delivery",
                delivery.contract,
                [SUITE, "field:bls12-381.fr"],
                "arkworks/transcript.native.indexed.observe.data"
            ]
        ]);
        f.program[2] = json!([
            [
                "function",
                "observe",
                [["t", STATE], ["v", BOOL]],
                [STATE],
                [
                    ["op", "coordinates", "empty", [], [], ["coords"]],
                    [
                        "op",
                        "observe",
                        "op_observe",
                        [observe.origin],
                        ["t", "v", "coords"],
                        ["next"]
                    ],
                    ["return", ["next"]]
                ],
                ["observe", []]
            ],
            [
                "function",
                "challenge",
                [["t", STATE]],
                [FIELD, STATE],
                [
                    ["op", "coordinates", "empty", [], [], ["coords"]],
                    [
                        "op",
                        "challenge",
                        "op_challenge",
                        [query.origin],
                        ["t", "coords"],
                        ["c", "next"]
                    ],
                    ["return", ["c", "next"]]
                ],
                ["challenge", []]
            ],
            [
                "function",
                "delivery",
                [["t", STATE], ["c", FIELD]],
                [STATE],
                [
                    ["op", "coordinates", "empty", [], [], ["coords"]],
                    [
                        "op",
                        "delivery",
                        "op_delivery",
                        [delivery.origin],
                        ["t", "c", "coords"],
                        ["next"]
                    ],
                    ["return", ["next"]]
                ],
                ["delivery", []]
            ]
        ]);
        for i in 0..2 {
            f.program[3][i][4]
                .as_array_mut()
                .unwrap()
                .push(json!(["t", STATE]));
            f.program[3][i][5]
                .as_array_mut()
                .unwrap()
                .push(json!(STATE));
            let body = f.program[3][i][6].as_array_mut().unwrap();
            body.insert(
                1,
                json!(["local", "observe", "observe", ["t", "candidate"], ["t1"]]),
            );
            body.insert(
                2,
                json!(["local", "challenge", "challenge", ["t1"], ["c", "t2"]]),
            );
            body.insert(
                3,
                json!(["local", "delivery", "delivery", ["t2", "c"], ["t3"]]),
            );
            body[4] = json!([
                "return",
                if i == 0 {
                    vec!["t3"]
                } else {
                    vec!["candidate", "t3"]
                }
            ]);
        }
        f
    }
    fn custom() -> Self {
        let mut f = Self::authored();
        let observe = event(false);
        f.events = vec![observe.clone()];
        f.program[2] = json!([
            [
                "function",
                "initialize",
                [],
                [BOOL],
                [
                    ["bool_constant", "initial", "state", true],
                    ["return", ["state"]]
                ],
                ["initialize", []]
            ],
            [
                "function",
                "observe",
                [["t", BOOL], ["value", BOOL]],
                [BOOL],
                [["return", ["t"]]],
                ["observe", []]
            ],
            [
                "function",
                "start",
                [["t", BOOL]],
                [BOOL],
                [["return", ["t"]]],
                ["start", []]
            ]
        ]);
        f.plan = ConstructionPlan::read(&json!([
            "zkc.construction-plan/0",
            "custom",
            "local",
            ["bool"],
            "initialize",
            ["start", []],
            [["observe", "local", [observe.origin]]],
            []
        ]))
        .unwrap();
        for i in 0..2 {
            f.program[3][i][5].as_array_mut().unwrap().push(json!(BOOL));
            let body = f.program[3][i][6].as_array_mut().unwrap();
            body.insert(0, json!(["local", "initialize", "initialize", [], ["t"]]));
            body.insert(1, json!(["local", "start", "start", ["t"], ["started"]]));
            body.insert(
                3,
                json!([
                    "local",
                    "observe",
                    "observe",
                    ["started", "candidate"],
                    ["next"]
                ]),
            );
            body[4] = json!([
                "return",
                if i == 0 {
                    vec!["next"]
                } else {
                    vec!["candidate", "next"]
                }
            ]);
        }
        f
    }
    fn codec() -> Self {
        let mut f = Self::custom();
        let bytes = "bytes@native.bytes/0";
        let index = "index@native.index/0";
        f.program[1] = json!([
            ["empty", "bytes.empty", [], "native/bytes.empty"],
            ["slice_bytes", "bytes.slice", [], "native/bytes.slice"],
            ["zero", "index.constant", [], "native/index.constant"]
        ]);
        let functions = f.program[2].as_array_mut().unwrap();
        functions.extend([
            json!([
                "function",
                "record_init",
                [],
                [index],
                [["op", "zero", "zero", ["0"], [], ["r"]], ["return", ["r"]]],
                ["record_init", []]
            ]),
            json!([
                "function",
                "encode",
                [["r", index], ["v", BOOL]],
                [index, bytes],
                [
                    ["op", "empty", "empty", [], [], ["chunk"]],
                    ["return", ["r", "chunk"]]
                ],
                ["encode", []]
            ]),
            json!([
                "function",
                "receive",
                [["r", index], ["proof", bytes]],
                [index, index, index],
                [
                    ["op", "zero", "zero", ["0"], [], ["z"]],
                    ["return", ["r", "z", "z"]]
                ],
                ["receive", []]
            ]),
            json!([
                "function",
                "slice",
                [["proof", bytes], ["lo", index], ["hi", index]],
                [bytes],
                [
                    [
                        "op",
                        "slice",
                        "slice_bytes",
                        [],
                        ["proof", "lo", "hi"],
                        ["chunk"]
                    ],
                    ["return", ["chunk"]]
                ],
                ["slice", []]
            ]),
            json!([
                "function",
                "decode",
                [["chunk", bytes]],
                [BOOL],
                [
                    ["bool_constant", "decoded", "value", true],
                    ["return", ["value"]]
                ],
                ["decode", []]
            ]),
            json!([
                "function",
                "wire",
                [["t", BOOL], ["chunk", bytes]],
                [BOOL],
                [["return", ["t"]]],
                ["wire", []]
            ]),
            json!([
                "function",
                "write",
                [["r", index]],
                [bytes],
                [
                    ["op", "empty", "empty", [], [], ["proof"]],
                    ["return", ["proof"]]
                ],
                ["write", []]
            ]),
            json!([
                "function",
                "finish",
                [["r", index], ["proof", bytes]],
                [],
                [["return", []]],
                ["finish", []]
            ]),
        ]);
        f.plan.as_mut().unwrap().codec = Some(construction::RecordCodec {
            record: vec![PhysicalType::parse(index).unwrap()],
            initialize: "record_init".into(),
            write: "write".into(),
            finish: "finish".into(),
            inputs: vec![],
            conditional_write: String::new(),
            conditional_finish: String::new(),
            messages: vec![construction::CodecMessage {
                encode: "encode".into(),
                receive: "receive".into(),
                decode: "decode".into(),
                wire: "wire".into(),
                slice: "slice".into(),
                origins: vec![f.events[0].origin.clone()],
            }],
        });
        f.program[3][0][5]
            .as_array_mut()
            .unwrap()
            .push(json!(bytes));
        f.program[3][0][6] = json!([
            ["local", "initialize", "initialize", [], ["initial"]],
            ["local", "start", "start", ["initial"], ["t"]],
            ["local", "record_init", "record_init", [], ["r"]],
            [
                "local",
                "encode",
                "encode",
                ["r", "candidate"],
                ["r1", "chunk"]
            ],
            ["local", "wire", "wire", ["t", "chunk"], ["wire_state"]],
            [
                "local",
                "observe",
                "observe",
                ["wire_state", "candidate"],
                ["next"]
            ],
            ["local", "write", "write", ["r1"], ["proof"]],
            ["return", ["next", "proof"]]
        ]);
        f.program[3][1][4]
            .as_array_mut()
            .unwrap()
            .push(json!(["proof", bytes]));
        f.program[3][1][6] = json!([
            ["local", "initialize", "initialize", [], ["initial"]],
            ["local", "start", "start", ["initial"], ["t"]],
            ["local", "record_init", "record_init", [], ["r"]],
            [
                "local",
                "receive",
                "receive",
                ["r", "proof"],
                ["r1", "lo", "hi"]
            ],
            ["local", "slice", "slice", ["proof", "lo", "hi"], ["chunk"]],
            ["local", "wire", "wire", ["t", "chunk"], ["wire_state"]],
            ["local", "decode", "decode", ["chunk"], ["candidate"]],
            [
                "local",
                "observe",
                "observe",
                ["wire_state", "candidate"],
                ["next"]
            ],
            ["local", "finish", "finish", ["r1", "proof"], []],
            ["return", ["candidate", "next"]]
        ]);
        f
    }
    fn remove_functions(&mut self, names: &[&str]) {
        self.program[2]
            .as_array_mut()
            .unwrap()
            .retain(|f| !names.contains(&f[1].as_str().unwrap()));
    }
}
fn event(query: bool) -> NativeTranscriptEvent {
    let tail = if query {
        json!([
            "query",
            "Round",
            "draw",
            "input_2",
            "random.bls12-381.fr/0",
            "draw",
            "V"
        ])
    } else {
        json!(["message", "Round", "message", "message", "P", "V"])
    };
    let bytes = crate::logical::encode_tree(&json!([
        "zkc.native-origin-template/0",
        "main",
        [],
        [],
        tail
    ]))
    .unwrap();
    NativeTranscriptEvent {
        contract: format!(
            "transcript.native.indexed.{}",
            if query { "challenge" } else { "observe.data" }
        ),
        origin: bytes.iter().map(|b| format!("{b:02x}")).collect(),
        payload: (!query).then(|| super::super::LogicalType::parse("bool").unwrap()),
        bound: None,
        start_inputs: None,
    }
}

#[test]
fn combined_and_selected_admission_share_authored_native_and_custom_rules() {
    for fixture in [
        Fixture::authored,
        Fixture::native,
        Fixture::custom,
        Fixture::codec,
    ] {
        let combined = fixture().admit(None).unwrap();
        assert!(combined.producer().is_some() && combined.validator().is_some());
        for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
            let f = fixture().selected(operation);
            let selected = f.admit(Some(operation)).unwrap();
            assert_eq!(
                selected.producer().is_some(),
                operation == NativeProofOperation::Prove
            );
            assert_eq!(
                selected.validator().is_some(),
                operation == NativeProofOperation::Verify
            );
            assert_eq!(selected.producer_role(), "P");
            assert_eq!(selected.validator_role(), "V");
            assert_eq!(
                selected.admitted().bytes(),
                f.program.to_string().as_bytes()
            );
            assert_eq!(selected.binds_invocation(), combined.binds_invocation());
            assert_eq!(selected.transcript(), combined.transcript());
            assert_eq!(f.admit(None).unwrap_err().0, "native-proof-entry");
        }
    }
}

#[test]
fn selected_codec_needs_only_its_own_transport_helpers() {
    use NativeProofOperation::{Prove, Verify};
    for operation in [Prove, Verify] {
        let mut f = Fixture::codec().selected(operation);
        let absent = if operation == Prove {
            vec!["receive", "decode", "slice", "finish"]
        } else {
            vec!["encode", "write"]
        };
        f.remove_functions(&absent);
        let admitted = f.admit(Some(operation)).unwrap();
        assert!(admitted.has_record_codec());
        for name in absent {
            assert!(admitted.admitted().local_function(name).is_none());
        }
        assert_eq!(f.admit(None).unwrap_err().0, "native-proof-codec-function");
    }
}

#[test]
fn conditional_codec_finalizers_are_selected_but_retained_opposite_bodies_still_check() {
    use NativeProofOperation::{Prove, Verify};
    let conditional = || {
        let mut f = Fixture::codec();
        let bytes = "bytes@native.bytes/0";
        let index = "index@native.index/0";
        f.program[2].as_array_mut().unwrap().extend([
            json!([
                "function",
                "conditional_write",
                [["condition", BOOL], ["r", index]],
                [bytes],
                [
                    [
                        "if",
                        "branch",
                        "condition",
                        ["r"],
                        [["op", "yes", "empty", [], [], ["a"]], ["yield", ["a"]]],
                        [["op", "no", "empty", [], [], ["b"]], ["yield", ["b"]]],
                        ["proof"]
                    ],
                    ["return", ["proof"]]
                ],
                ["conditional_write", []]
            ]),
            json!([
                "function",
                "conditional_finish",
                [["condition", BOOL], ["r", index], ["proof", bytes]],
                [],
                [
                    [
                        "if",
                        "branch",
                        "condition",
                        ["r", "proof"],
                        [["yield", []]],
                        [["yield", []]],
                        []
                    ],
                    ["return", []]
                ],
                ["conditional_finish", []]
            ]),
        ]);
        let plan = f.plan.as_mut().unwrap().codec.as_mut().unwrap();
        plan.conditional_write = "conditional_write".into();
        plan.conditional_finish = "conditional_finish".into();
        f
    };
    assert!(conditional().admit(None).is_ok());
    for operation in [Prove, Verify] {
        let mut f = conditional().selected(operation);
        if operation == Prove {
            f.remove_functions(&["receive", "decode", "slice", "finish", "conditional_finish"]);
        } else {
            f.remove_functions(&["encode", "write", "conditional_write"]);
        }
        assert!(f.admit(Some(operation)).is_ok());
        let mut f = conditional().selected(operation);
        // A retained opposite-direction declaration cannot bypass correspondence.
        let name = if operation == Prove {
            "conditional_finish"
        } else {
            "conditional_write"
        };
        let function = f.program[2]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|f| f[1] == name)
            .unwrap();
        if operation == Prove {
            function[4] = json!([["return", []]]);
        } else {
            // Keep the carrier well typed but change its prescribed body.
            function[4][0][4]
                .as_array_mut()
                .unwrap()
                .insert(0, json!(["bool_constant", "extra", "unused", true]));
        }
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            if operation == Prove {
                "native-proof-codec-finalizer"
            } else {
                "native-proof-codec-finalizer-body"
            }
        );
    }
}

#[test]
fn codec_checks_retained_opposite_helpers_and_selected_wire_order() {
    use NativeProofOperation::{Prove, Verify};
    for operation in [Prove, Verify] {
        let mut f = Fixture::codec().selected(operation);
        let name = if operation == Prove {
            "decode"
        } else {
            "encode"
        };
        let function = f.program[2]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|f| f[1] == name)
            .unwrap();
        // Structurally valid, but an invalid retained codec signature.
        function[3].as_array_mut().unwrap().clear();
        *function[4].as_array_mut().unwrap().last_mut().unwrap() = json!(["return", []]);
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-codec-signature"
        );

        let mut f = Fixture::codec().selected(operation);
        let body = f.program[3][0][6].as_array_mut().unwrap();
        if operation == Prove {
            // Copyable state makes this SSA-valid but breaks ordered wire observation.
            body[5][3] = json!(["t", "candidate"]);
        } else {
            body[7][3] = json!(["t", "candidate"]);
        }
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-codec-payload"
        );
    }
}

#[test]
fn selected_codec_requires_each_helper_used_by_its_direction() {
    use NativeProofOperation::{Prove, Verify};
    for (operation, names) in [
        (Prove, vec!["record_init", "encode", "wire", "write"]),
        (
            Verify,
            vec![
                "record_init",
                "receive",
                "slice",
                "wire",
                "decode",
                "finish",
            ],
        ),
    ] {
        for name in names {
            let mut f = Fixture::codec().selected(operation);
            let plan = f.plan.as_mut().unwrap().codec.as_mut().unwrap();
            // The retained executable remains well formed; the plan's required
            // helper reference no longer names its checked implementation.
            match name {
                "record_init" => plan.initialize = "absent".into(),
                "encode" => plan.messages[0].encode = "absent".into(),
                "wire" => plan.messages[0].wire = "absent".into(),
                "write" => plan.write = "absent".into(),
                "receive" => plan.messages[0].receive = "absent".into(),
                "slice" => plan.messages[0].slice = "absent".into(),
                "decode" => plan.messages[0].decode = "absent".into(),
                "finish" => plan.finish = "absent".into(),
                _ => unreachable!(),
            }
            assert_eq!(
                f.admit(Some(operation)).unwrap_err().0,
                "native-proof-codec-function",
                "{name}"
            );
        }
    }
}

#[test]
fn producer_shared_roots_cannot_acquire_witness_dependencies() {
    for codec in [false, true] {
        let mut f = if codec {
            Fixture::codec()
        } else {
            Fixture::custom()
        }
        .selected(NativeProofOperation::Prove);
        if codec {
            f.plan
                .as_mut()
                .unwrap()
                .codec
                .as_mut()
                .unwrap()
                .inputs
                .push(1);
        } else {
            f.plan.as_mut().unwrap().inputs.push(1);
        }
        assert_eq!(
            f.admit(Some(NativeProofOperation::Prove)).unwrap_err().0,
            "native-proof-private-dependency"
        );
    }
}

#[test]
fn wrong_operation_endpoint_inventory_and_acceptance_refuse() {
    use NativeProofOperation::{Prove, Verify};
    assert_eq!(
        Fixture::authored().admit(Some(Prove)).unwrap_err().0,
        "native-proof-entry"
    );
    for (actual, requested) in [(Prove, Verify), (Verify, Prove)] {
        assert_eq!(
            Fixture::authored()
                .selected(actual)
                .admit(Some(requested))
                .unwrap_err()
                .0,
            "native-proof-role"
        );
    }
    let f = Fixture::authored().selected(Verify);
    assert_eq!(
        f.admit_with(Some(Verify), &f.maps(), &[0], 1)
            .unwrap_err()
            .0,
        "native-proof-validator"
    );
    let f = Fixture::authored().selected(Prove);
    // The descriptor's output selector is not an output of the absent verifier.
    assert!(f.admit_with(Some(Prove), &f.maps(), &[0], 999).is_ok());
    let mut f = Fixture::authored().selected(Verify);
    f.program[3][0][3] = json!("Other");
    f.program[4][0][2][0][0] = json!("Other");
    assert_eq!(f.admit(Some(Verify)).unwrap_err().0, "native-proof-role");
    for (operation, producer, validator) in [
        (Prove, "P", ""),
        (Verify, "bad role", "V"),
        (Verify, "V", "V"),
    ] {
        let f = Fixture::authored().selected(operation);
        let maps = f.maps();
        let program = Program::decode(f.program.to_string().as_bytes()).unwrap();
        assert_eq!(
            NativeProofEntry::new_for_operation(
                program,
                "main",
                producer,
                validator,
                0,
                ProofConstruction {
                    suite: None,
                    events: &[],
                    plan: None,
                    source_inputs: &maps
                },
                operation,
                &[0],
            )
            .unwrap_err()
            .0,
            "native-proof-profile"
        );
    }
}

#[test]
fn selected_source_maps_are_exact_and_public_indices_are_independent() {
    use NativeProofOperation::{Prove, Verify};
    for operation in [Prove, Verify] {
        let f = Fixture::authored().selected(operation);
        let role = if operation == Prove { "P" } else { "V" };
        for maps in [
            BTreeMap::new(),
            BTreeMap::from([(role.into(), vec![])]),
            BTreeMap::from([(role.into(), vec![0, 0])]),
            BTreeMap::from([(role.into(), vec![1024])]),
            BTreeMap::from([("Other".into(), vec![0])]),
        ] {
            assert_eq!(
                f.admit_with(Some(operation), &maps, &[0], 0).unwrap_err().0,
                "native-proof-source-map"
            );
        }
        let mut maps = f.maps();
        maps.insert(if operation == Prove { "V" } else { "P" }.into(), vec![]);
        assert_eq!(
            f.admit_with(Some(operation), &maps, &[0], 0).unwrap_err().0,
            "native-proof-source-map"
        );
        for public in [&[0, 0][..], &[1024][..], &[1, 0][..]] {
            assert_eq!(
                f.admit_with(Some(operation), &f.maps(), public, 0)
                    .unwrap_err()
                    .0,
                "native-proof-source-map"
            );
        }
    }
    let f = Fixture::native().selected(Prove);
    assert!(f.admit(Some(Prove)).is_ok()); // Only the producer map exists.
    let f = Fixture::authored().selected(Verify);
    assert_eq!(
        f.admit_with(Some(Verify), &f.maps(), &[], 0).unwrap_err().0,
        "native-proof-source-map"
    );
}

#[test]
fn selected_event_order_origin_state_and_wire_correspondence_refuse() {
    for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
        let mut f = Fixture::native().selected(operation);
        f.events.swap(0, 1);
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-state-chain"
        );
        let mut f = Fixture::native().selected(operation);
        f.events[0].origin = event(true).origin;
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-duplicate-origin"
        );
        let mut f = Fixture::native().selected(operation);
        f.events[0].payload = Some(super::super::LogicalType::parse("index").unwrap());
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-state-chain"
        );
        let mut f = Fixture::native().selected(operation);
        f.program[3][0][6][2][3] = json!(["t"]);
        // General SSA admission refuses the consumed affine predecessor.
        assert!(Program::decode(f.program.to_string().as_bytes()).is_err());
        let mut f = Fixture::authored().selected(operation);
        f.program[3][0][6][0][3] = json!("Other");
        assert_eq!(
            f.admit(Some(operation)).unwrap_err().0,
            "native-proof-state-chain"
        );
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Boolean(bool);
impl super::super::Value for Boolean {
    fn physical_type(&self) -> PhysicalType {
        PhysicalType::parse(BOOL).unwrap()
    }
    fn validate_serializable(&self) -> std::result::Result<(), super::super::BackendError> {
        Ok(())
    }
    fn retained_bytes(&self) -> usize {
        1
    }
    fn control_bool(&self) -> std::result::Result<bool, super::super::BackendError> {
        Ok(self.0)
    }
}
// No installed numerical kernels, services, entropy, capabilities or keys.
#[derive(Debug, Default)]
struct EndpointBackend {
    frames: usize,
}
impl super::super::Backend for EndpointBackend {
    type Value = Boolean;
    type Operation = super::super::BoundSignature;
    type Call = ();
    type Checkpoint = ();
    fn validate_value(&self, _: &Boolean) -> std::result::Result<(), super::super::BackendError> {
        Ok(())
    }
    fn enter_frame(
        &mut self,
        _: &super::super::Frame,
        _: &[Boolean],
    ) -> std::result::Result<(), super::super::BackendError> {
        self.frames += 1;
        Ok(())
    }
    fn leave_frame(
        &mut self,
        _: &super::super::Frame,
        _: super::super::FrameExit,
        _: &[Boolean],
    ) -> std::result::Result<(), super::super::BackendError> {
        self.frames -= 1;
        Ok(())
    }
    fn apply(
        &mut self,
        _: &Self::Operation,
        _: &super::super::Invocation<'_>,
        _: &[Boolean],
    ) -> std::result::Result<Vec<Boolean>, super::super::BackendError> {
        panic!("unavailable operation must never execute")
    }
}

#[test]
fn verifier_executes_without_opposite_runtime_dependencies_and_checks_all_reached_regions() {
    use super::super::{Action, ValueBudget, WorkBudget};
    use crate::interpreter::Runner;
    let mut f = Fixture::authored().selected(NativeProofOperation::Verify);
    f.program[1] = json!([[
        "constant",
        "field.constant",
        ["bls12-381.fr"],
        "arkworks/field.constant"
    ]]);
    f.program[2] = json!([
        [
            "function",
            "decision",
            [["value", BOOL]],
            [BOOL],
            [["return", ["value"]]],
            ["decision", []]
        ],
        [
            "function",
            "producer_helper",
            [["value", BOOL]],
            [BOOL],
            [
                [
                    "if",
                    "branch",
                    "value",
                    ["value"],
                    [
                        ["op", "unavailable", "constant", ["1"], [], ["unused"]],
                        ["yield", ["value"]]
                    ],
                    [["yield", ["value"]]],
                    ["result"]
                ],
                ["return", ["result"]]
            ],
            ["producer_helper", []]
        ]
    ]);
    f.program[3][0][6] = json!([
        ["local", "decide", "decision", ["public"], ["accepted"]],
        ["return", ["accepted"]]
    ]);
    let entry = f.admit(Some(NativeProofOperation::Verify)).unwrap();
    let program = entry.admitted();
    assert!(
        program
            .check_installation(&EndpointBackend::default())
            .is_err()
    );
    assert!(
        program
            .check_role_installation("main", "V", &EndpointBackend::default())
            .is_ok()
    );
    assert!(
        program
            .check_role_installation("main", "P", &EndpointBackend::default())
            .is_err()
    );
    for value in [false, true] {
        let mut runner = Runner::new_for_role_with_ledger(
            program,
            "main",
            "V",
            "invocation",
            EndpointBackend::default(),
            vec![Boolean(value)],
            ValueBudget::default(),
            WorkBudget::default(),
            None,
        )
        .unwrap();
        let Action::Local(action) = runner.poll() else {
            panic!("selected local action")
        };
        runner.execute_local(&action.cut).unwrap();
        assert!(
            matches!(runner.poll(), Action::Returned(values) if values == vec![Boolean(value)])
        );
        assert_eq!(runner.into_backend().frames, 0);
    }
    f.program[3][0][6][0][2] = json!("producer_helper");
    let entry = f.admit(Some(NativeProofOperation::Verify)).unwrap();
    // The unavailable kernel is in a potential region, even with false input.
    let failure = Runner::new_for_role_with_ledger(
        entry.admitted(),
        "main",
        "V",
        "invocation",
        EndpointBackend::default(),
        vec![Boolean(false)],
        ValueBudget::default(),
        WorkBudget::default(),
        None,
    )
    .err()
    .unwrap();
    assert_eq!(failure.backend.frames, 0);
}
