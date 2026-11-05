//! Independent carriers exercise admission without a compiler or opposite role.
use super::*;
use serde_json::{Value as Json, json};
mod generated_origins;
mod reconstructed;

const BOOL: &str = "bool@native.bool/0";
const SUITE: &str = "merlin3.bls12-381.fr64be/0";
const STATE: &str = "transcript:merlin3.bls12-381.fr64be/0@host.resource/0";
const FIELD: &str = "field:bls12-381.fr@arkworks.fr/0";

#[test]
fn local_verifier_custody_does_not_grant_wire_or_provider_permissions() {
    let unit = "resource_unit:Slot.A@logical.resource_unit/0";
    let rng = "rng:bls12-381.fr@host.resource/0";
    let mut fixture = Fixture::authored();
    fixture.program[2] = json!([
        [
            "function",
            "unit",
            [["x", unit]],
            [unit],
            [["return", ["x"]]],
            ["unit", []]
        ],
        [
            "function",
            "rng",
            [["x", rng]],
            [rng],
            [["return", ["x"]]],
            ["rng", []]
        ]
    ]);
    let contracts = crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose());
    let program = Program::decode(fixture.program.to_string().as_bytes(), &contracts).unwrap();
    verifier_function(
        &program.program.functions["unit"],
        &contracts,
        &mut ProofWork(PROOF_WORK),
    )
    .unwrap();
    assert!(
        !verifier_data(
            &PhysicalType::parse(unit).unwrap(),
            &contracts,
            &mut ProofWork(PROOF_WORK),
        )
        .unwrap()
    );
    assert_eq!(
        verifier_function(
            &program.program.functions["rng"],
            &contracts,
            &mut ProofWork(PROOF_WORK)
        )
        .unwrap_err()
        .0,
        "native-proof-verifier-resource"
    );
}

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
        let program = Program::decode(
            self.program.to_string().as_bytes(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
        )
        .unwrap();
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
        delivery.origin = zkc_format::logical::encode_tree(&json!([
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
            ["empty", "indices.empty", [], "native/indices.empty", []],
            [
                "op_observe",
                observe.contract,
                [SUITE, "bool"],
                "arkworks/transcript.native.indexed.observe.data",
                []
            ],
            [
                "op_challenge",
                query.contract,
                [SUITE],
                "arkworks/transcript.native.indexed.challenge",
                []
            ],
            [
                "op_delivery",
                delivery.contract,
                [SUITE, "field:bls12-381.fr"],
                "arkworks/transcript.native.indexed.observe.data",
                []
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
            ["empty", "bytes.empty", [], "native/bytes.empty", []],
            ["slice_bytes", "bytes.slice", [], "native/bytes.slice", []],
            ["zero", "index.constant", [], "native/index.constant", []]
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
    let bytes = zkc_format::logical::encode_tree(&json!([
        "zkc.native-origin-template/0",
        "main",
        [],
        [],
        tail
    ]))
    .unwrap();
    NativeTranscriptEvent {
        reconstructed: false,
        contract: format!(
            "transcript.native.indexed.{}",
            if query { "challenge" } else { "observe.data" }
        ),
        origin: bytes.iter().map(|b| format!("{b:02x}")).collect(),
        payload: (!query).then(|| super::super::LogicalType::parse("bool").unwrap()),
        bound: None,
        count: None,
        difficulty: None,
        start_inputs: None,
    }
}

fn selected_payload_fixture(codec: bool, payload: &PhysicalType) -> Fixture {
    let mut f = if codec {
        Fixture::codec()
    } else {
        Fixture::custom()
    };
    let spelling = payload.spelling();
    f.events[0].payload = Some(payload.logical().clone());
    f.program[3][0][4][1][1] = json!(spelling);
    let observer = f.program[2]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|f| f[1] == "observe")
        .unwrap();
    observer[2][1][1] = json!(spelling);
    if codec {
        if payload.kind() != Type::Variant {
            f.program[1].as_array_mut().unwrap().push(json!([
                "constant",
                "field.constant",
                ["bls12-381.fr"],
                "test/field.constant",
                []
            ]));
        }
        let functions = f.program[2].as_array_mut().unwrap();
        let encode = functions.iter_mut().find(|f| f[1] == "encode").unwrap();
        encode[2][1][1] = json!(spelling);
        let decode = functions.iter_mut().find(|f| f[1] == "decode").unwrap();
        decode[3] = json!([spelling]);
        decode[4] = if payload.kind() == Type::Variant {
            json!([
                ["variant", "decoded", spelling, "empty", [], "value"],
                ["return", ["value"]]
            ])
        } else {
            json!([
                ["op", "decoded", "constant", ["1"], [], ["value"]],
                ["return", ["value"]]
            ])
        };
    } else {
        f.program[3][1][6][2][5] = json!(spelling);
    }
    *f.program[3][1][6]
        .as_array_mut()
        .unwrap()
        .last_mut()
        .unwrap() = json!(["return", ["public", "next"]]);
    f
}
fn selected_payload_context(
    permission: bool,
) -> (crate::vm::Contracts, PhysicalType, PhysicalType) {
    use crate::vm::*;
    let mut builder = ContractsBuilder::standard();
    let field = builder
        .add_representation(
            "test/proof-scalar",
            LogicalType::parse("field:bls12-381.fr").unwrap(),
        )
        .unwrap();
    if permission {
        builder
            .add_wire_permission(field.clone(), WireCodec::Native)
            .unwrap();
    }
    builder
        .add_implementation(
            OperationBinding {
                contract: "field.constant".into(),
                arguments: vec!["bls12-381.fr".into()],
                implementation: "test/field.constant".into(),
                physical_arguments: vec![],
            },
            BoundSignature {
                inputs: vec![],
                outputs: vec![field.clone()],
                attributes: AttributeRule::FieldDecimal,
            },
            ImplementationRequirements {
                timing: TimingRequirement::OperandIndependent,
                timing_operands: &[],
            },
        )
        .unwrap();
    let logical = LogicalType::parse(&zkc_test_support::variants::logical(
        "SelectedProof",
        json!([["empty", []], ["value", ["field:bls12-381.fr"]]]),
    ))
    .unwrap();
    let variant = builder
        .aggregate_type(logical, Representation::Variant, vec![field.clone()])
        .unwrap();
    (
        builder.finish(ExecutionPolicy::general_purpose()),
        field,
        variant,
    )
}
fn admit_selected_payload(
    f: &Fixture,
    contracts: &crate::vm::Contracts,
    operation: Option<NativeProofOperation>,
) -> Result<NativeProofEntry> {
    let program = Program::decode(f.program.to_string().as_bytes(), contracts).unwrap();
    let maps = f.maps();
    let construction = ProofConstruction {
        suite: f.suite,
        events: &f.events,
        plan: f.plan.as_ref(),
        source_inputs: &maps,
    };
    match operation {
        None => NativeProofEntry::new(program, "main", "P", "V", 0, construction),
        Some(operation) => NativeProofEntry::new_for_operation(
            program,
            "main",
            "P",
            "V",
            0,
            construction,
            operation,
            &[0],
        ),
    }
}
#[test]
fn custom_constructions_and_record_codecs_preserve_selected_payloads() {
    let (contracts, field, variant) = selected_payload_context(true);
    for payload in [field, variant] {
        for codec in [false, true] {
            let f = selected_payload_fixture(codec, &payload);
            admit_selected_payload(&f, &contracts, None).unwrap();
            for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
                let selected = selected_payload_fixture(codec, &payload).selected(operation);
                admit_selected_payload(&selected, &contracts, Some(operation)).unwrap();
            }
            let mut wrong = selected_payload_fixture(codec, &payload);
            wrong.events[0].payload = Some(crate::vm::LogicalType::parse("index").unwrap());
            assert_eq!(
                admit_selected_payload(&wrong, &contracts, None)
                    .unwrap_err()
                    .0,
                "native-proof-helper-signature"
            );
        }
    }
}
#[test]
fn custom_child_starts_and_queries_retain_selected_ports() {
    let (contracts, field, _) = selected_payload_context(true);
    let spelling = field.spelling();
    let carrier = json!([
        "zkc.program/0",
        [[
            "constant",
            "field.constant",
            ["bls12-381.fr"],
            "test/field.constant",
            []
        ]],
        [
            [
                "function",
                "selected_query",
                [["t", BOOL]],
                [spelling, BOOL],
                [
                    ["op", "query", "constant", ["1"], [], ["c"]],
                    ["return", ["c", "t"]]
                ],
                ["query", []]
            ],
            [
                "function",
                "selected_start",
                [["t", BOOL], ["shared", spelling]],
                [BOOL],
                [["return", ["t"]]],
                ["start", []]
            ]
        ],
        [],
        []
    ]);
    let program = Program::decode(carrier.to_string().as_bytes(), &contracts).unwrap();
    let query = &program.program.functions["selected_query"];
    let state = [PhysicalType::parse(BOOL).unwrap()];
    custom_helper(
        query,
        &state,
        &[event(true)],
        "main",
        "V",
        &mut ProofWork(PROOF_WORK),
    )
    .unwrap();
    let mut wrong_query = event(true);
    let origin = zkc_format::logical::encode_tree(&json!([
        "zkc.native-origin-template/0",
        "main",
        [],
        [],
        [
            "query",
            "Round",
            "draw",
            "input_2",
            "random.koala-bear/0",
            "draw",
            "V"
        ]
    ]))
    .unwrap();
    wrong_query.origin = origin.iter().map(|b| format!("{b:02x}")).collect();
    assert!(
        custom_helper(
            query,
            &state,
            &[wrong_query],
            "main",
            "V",
            &mut ProofWork(PROOF_WORK)
        )
        .is_err()
    );
    let origin = zkc_format::logical::encode_tree(&json!([
        "zkc.native-origin-template/0",
        "main",
        [],
        [],
        ["start", "Round", "child"]
    ]))
    .unwrap();
    let mut start = NativeTranscriptEvent {
        reconstructed: false,
        contract: "construction.start".into(),
        origin: origin.iter().map(|b| format!("{b:02x}")).collect(),
        payload: None,
        bound: None,
        count: None,
        difficulty: None,
        start_inputs: Some(vec![field.logical().clone()]),
    };
    let function = &program.program.functions["selected_start"];
    custom_helper(
        function,
        &state,
        std::slice::from_ref(&start),
        "main",
        "V",
        &mut ProofWork(PROOF_WORK),
    )
    .unwrap();
    start.start_inputs = Some(vec![crate::vm::LogicalType::parse("index").unwrap()]);
    assert!(
        custom_helper(
            function,
            &state,
            &[start],
            "main",
            "V",
            &mut ProofWork(PROOF_WORK)
        )
        .is_err()
    );
}

#[test]
fn selected_record_codec_requires_permission_for_inactive_payload_children() {
    let (contracts, field, variant) = selected_payload_context(false);
    for payload in [field, variant] {
        let f = selected_payload_fixture(true, &payload);
        assert_eq!(
            admit_selected_payload(&f, &contracts, None).unwrap_err().0,
            "native-proof-verifier-resource"
        );
    }
}

#[test]
fn record_codec_checks_wire_permission_at_its_own_boundary() {
    for permission in [false, true] {
        let (contracts, _, variant) = selected_payload_context(permission);
        let f = selected_payload_fixture(true, &variant);
        let program = Program::decode(f.program.to_string().as_bytes(), &contracts).unwrap();
        let plan = f.plan.as_ref().unwrap();
        let helper = custom_helper(
            &program.program.functions["observe"],
            &plan.state,
            &f.events,
            "main",
            "V",
            &mut ProofWork(PROOF_WORK),
        )
        .unwrap();
        let helpers = BTreeMap::from([("observe".into(), helper)]);
        let checked = codec::CheckedCodec::new(
            &program,
            plan.codec.as_ref().unwrap(),
            &plan.state,
            &helpers,
            "P",
            "V",
            None,
            &mut ProofWork(PROOF_WORK),
        );
        if permission {
            assert!(checked.is_ok());
        } else {
            assert_eq!(checked.err().unwrap().0, "native-proof-wire-type");
        }
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
        let program = Program::decode(
            f.program.to_string().as_bytes(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
        )
        .unwrap();
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
        assert!(
            Program::decode(
                f.program.to_string().as_bytes(),
                &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
            )
            .is_err()
        );
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
    fn from_control_bool(value: bool) -> std::result::Result<Self, super::super::BackendError> {
        Ok(Self(value))
    }

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
    fn supports_boolean_literals(&self) -> bool {
        true
    }

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
        "arkworks/field.constant",
        []
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

const BLOCK_SUITE: &str = "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0";

// Closed independently authored carriers test Rust admission. The compiler's
// actual source producer is exercised separately by the integration owner.
fn block_fixture(difficulty: Option<u8>) -> Fixture {
    fn replace(value: &mut Json, from: &str, to: &str) {
        match value {
            Json::String(text) if text == from => *text = to.into(),
            Json::Array(values) => values.iter_mut().for_each(|v| replace(v, from, to)),
            _ => (),
        }
    }
    let mut f = Fixture::native();
    let state = format!("transcript:{BLOCK_SUITE}@host.resource/0");
    replace(&mut f.program, STATE, &state);
    replace(&mut f.program, SUITE, BLOCK_SUITE);
    replace(&mut f.program, FIELD, "indices@native.indices/0");
    replace(
        &mut f.program,
        "arkworks/transcript.native.indexed.observe.data",
        "plonky3/transcript.native.indexed.observe.data",
    );
    let old_origin = f.events[1].origin.clone();
    let bytes =
        zkc_format::logical::native_query_template(std::slice::from_ref(&old_origin), "draw")
            .unwrap();
    let mut tree = zkc_format::logical::decode_tree(&bytes).unwrap();
    tree[4][4] = json!("random.koala-bear.ext4-binomial3/0");
    tree[4][5] = json!("indices");
    let origin: String = zkc_format::logical::encode_tree(&tree)
        .unwrap()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    replace(&mut f.program, &old_origin, &origin);
    f.events[1].origin = origin;
    f.events[1].contract = if difficulty.is_some() {
        "transcript.native.indexed.indices.gated"
    } else {
        "transcript.native.indexed.indices"
    }
    .into();
    f.events[1].bound = Some(1 << 63);
    f.events[1].count = Some(3);
    f.events[1].difficulty = difficulty;
    f.events[2].payload = Some(super::super::LogicalType::parse("indices").unwrap());
    f.suite = Some(BLOCK_SUITE);
    f.program[1][2][1] = json!(f.events[1].contract);
    f.program[1][2][3] = json!(format!("plonky3/{}", f.events[1].contract));
    f.program[1][3][2][1] = json!("indices");
    let mut attributes = vec![
        json!(f.events[1].origin),
        json!((1u64 << 63).to_string()),
        json!("3"),
    ];
    if let Some(bits) = difficulty {
        attributes.push(json!(bits.to_string()));
    }
    f.program[2][1][4][1][3] = json!(attributes);
    if difficulty.is_some() {
        f.program[2][1][2]
            .as_array_mut()
            .unwrap()
            .push(json!(["w", "index@native.index/0"]));
        f.program[2][1][4][1][4] = json!(["t", "w", "coords"]);
        let mut search = f.program[2][1].clone();
        search[1] = json!("search");
        search[2] = json!([["t", state]]);
        search[3] = json!(["indices@native.indices/0", "index@native.index/0", state]);
        search[4][1][2] = json!("op_search");
        search[4][1][4] = json!(["t", "coords"]);
        search[4][1][5] = json!(["c", "w", "next"]);
        search[4][2][1] = json!(["c", "w", "next"]);
        f.program[2].as_array_mut().unwrap().push(search);
        f.program[1].as_array_mut().unwrap().push(json!([
            "op_search",
            "transcript.native.indexed.indices.search",
            [BLOCK_SUITE],
            "plonky3/transcript.native.indexed.indices.search",
            []
        ]));
        f.program[3][0][6][2][2] = json!("search");
        f.program[3][0][6][2][4] = json!(["c", "w", "t2"]);
        f.program[3][0][6]
            .as_array_mut()
            .unwrap()
            .insert(3, json!(["send", "gate.draw", "gate.draw", "V", "w"]));
        f.program[3][1][6][2][3] = json!(["t1", "w"]);
        f.program[3][1][6].as_array_mut().unwrap().insert(
            2,
            json!([
                "receive",
                "gate.draw",
                "gate.draw",
                "P",
                "w",
                "index@native.index/0"
            ]),
        );
    }
    f
}

#[test]
fn independent_block_carriers_admit_each_endpoint_and_zero_difficulty() {
    for bits in [None, Some(0), Some(4), Some(64)] {
        block_fixture(bits).admit(None).unwrap();
        for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
            let mut f = block_fixture(bits).selected(operation);
            // The ordinary carrier retains the other endpoint's helper. Prune
            // its dormant definition; endpoint artifacts contain only their own.
            if bits.is_some() {
                if operation == NativeProofOperation::Prove {
                    f.program[2].as_array_mut().unwrap().remove(1);
                } else {
                    f.program[2].as_array_mut().unwrap().pop();
                }
            }
            f.admit(Some(operation)).unwrap();
        }
    }
}

#[test]
fn custom_plans_cannot_claim_native_index_block_adapters() {
    for bits in [None, Some(0), Some(4)] {
        let mut f = block_fixture(bits);
        let adapters: Vec<_> = ["observe", "challenge", "delivery"]
            .into_iter()
            .zip(&f.events)
            .map(|(name, event)| json!([name, "native", [event.origin]]))
            .collect();
        f.plan = ConstructionPlan::read(&json!([
            "zkc.construction-plan/0",
            "Custom",
            "host",
            [format!("transcript:{BLOCK_SUITE}")],
            "",
            ["", []],
            adapters,
            []
        ]))
        .unwrap();
        assert_eq!(f.admit(None).unwrap_err().0, "native-proof-index-block");
        for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
            let mut selected = block_fixture(bits).selected(operation);
            selected.plan = f.plan.clone();
            if bits.is_some() {
                if operation == NativeProofOperation::Prove {
                    selected.program[2].as_array_mut().unwrap().remove(1);
                } else {
                    selected.program[2].as_array_mut().unwrap().pop();
                }
            }
            assert_eq!(
                selected.admit(Some(operation)).unwrap_err().0,
                "native-proof-index-block"
            );
        }
    }
}

#[test]
fn block_parameter_carriers_refuse_malformed_and_out_of_domain_values() {
    let valid = block_fixture(Some(4));
    let contracts = crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose());
    for (position, values) in [
        (
            1,
            vec![
                "0",
                "3",
                "9223372036854775809",
                "18446744073709551616",
                "01",
                "-1",
            ],
        ),
        (2, vec!["0", "1048577", "01", "1.0"]),
        (3, vec!["65", "00", "-1"]),
    ] {
        for value in values {
            let mut f = valid.program.clone();
            f[2][1][4][1][3][position] = json!(value);
            assert_eq!(
                Program::decode(f.to_string().as_bytes(), &contracts)
                    .unwrap_err()
                    .code,
                crate::vm::ErrorCode::Attributes,
                "{position}: {value}"
            );
        }
    }
    for change in [0, 1] {
        let mut f = valid.program.clone();
        let attrs = f[2][1][4][1][3].as_array_mut().unwrap();
        if change == 0 {
            attrs.pop();
        } else {
            attrs.push(json!("0"));
        }
        assert_eq!(
            Program::decode(f.to_string().as_bytes(), &contracts)
                .unwrap_err()
                .code,
            crate::vm::ErrorCode::Attributes
        );
    }
}

#[test]
fn block_admission_binds_count_bound_difficulty_and_witness_placement() {
    for parameter in 1..=3 {
        let mut f = block_fixture(Some(4));
        f.program[2][1][4][1][3][parameter] = json!(match parameter {
            1 => "8",
            2 => "2",
            _ => "3",
        });
        assert!(f.admit(None).is_err(), "parameter {parameter}");
    }
    let mut f = block_fixture(Some(4));
    f.program[3][0][6].as_array_mut().unwrap().swap(3, 4);
    assert_eq!(f.admit(None).unwrap_err().0, "native-proof-witness-order");
    let mut f = block_fixture(Some(4));
    f.program[3][1][6].as_array_mut().unwrap().swap(1, 2);
    assert_eq!(f.admit(None).unwrap_err().0, "native-proof-witness-input");
    let mut f = block_fixture(Some(4));
    for endpoint in 0..2 {
        f.program[3][endpoint][6][if endpoint == 0 { 3 } else { 2 }][2] = json!("wrong-schema");
    }
    assert!(f.admit(None).is_err());
    let mut f = block_fixture(Some(4));
    f.events[1].difficulty = Some(3);
    assert!(f.admit(None).is_err());
}

#[test]
fn block_origin_roles_suite_and_repeat_coordinates_are_independent_checks() {
    fn replace(value: &mut Json, from: &str, to: &str) {
        match value {
            Json::String(text) if text == from => *text = to.into(),
            Json::Array(values) => values.iter_mut().for_each(|v| replace(v, from, to)),
            _ => (),
        }
    }
    for mutation in 0..3 {
        let mut f = block_fixture(Some(4));
        let old = f.events[1].origin.clone();
        let mut origin = zkc_format::logical::decode_tree(
            &zkc_format::logical::native_query_template(std::slice::from_ref(&old), "indices")
                .unwrap(),
        )
        .unwrap();
        match mutation {
            0 => origin[1] = json!("another-entry"),
            1 => origin[4][6] = json!("P"),
            _ => origin[4][4] = json!("random.koala-bear.ext8-binomial3/0"),
        }
        let new: String = zkc_format::logical::encode_tree(&origin)
            .unwrap()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        replace(&mut f.program, &old, &new);
        f.events[1].origin = new;
        assert!(f.admit(None).is_err(), "origin mutation {mutation}");
    }
    let mut f = block_fixture(Some(4));
    for event in &mut f.events {
        let old = event.origin.clone();
        let mut origin = zkc_format::logical::decode_tree(
            &zkc_format::logical::native_origin_template(
                std::slice::from_ref(&old),
                if event.payload.is_some() {
                    "message"
                } else {
                    "query"
                },
            )
            .unwrap(),
        )
        .unwrap();
        origin[2] = json!([["repeat", "Round", "rounds"]]);
        event.origin = zkc_format::logical::encode_tree(&origin)
            .unwrap()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        replace(&mut f.program, &old, &event.origin);
    }
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
    for function in f.program[2].as_array_mut().unwrap().iter_mut() {
        function[2]
            .as_array_mut()
            .unwrap()
            .push(json!(["i", "index@native.index/0"]));
        *function[4][1][4]
            .as_array_mut()
            .unwrap()
            .last_mut()
            .unwrap() = json!("coords1");
        function[4].as_array_mut().unwrap().insert(
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
    }
    f.program[2].as_array_mut().unwrap().push(json!([
        "function",
        "round_count",
        [],
        ["index@native.index/0"],
        [
            ["op", "count", "constant", ["2"], [], ["n"]],
            ["return", ["n"]]
        ],
        ["round_count", []]
    ]));
    for endpoint in 0..2 {
        let body = f.program[3][endpoint][6].as_array_mut().unwrap();
        let mut inner = std::mem::take(body);
        inner.pop();
        // Each event helper receives the current repeat induction operand.
        for action in &mut inner {
            if action[0] == "local" {
                action[3].as_array_mut().unwrap().push(json!("i"));
            }
        }
        inner.push(json!(["yield", ["t3"]]));
        *body = vec![
            json!(["local", "round_count", "round_count", [], ["n"]]),
            json!([
                "loop",
                "rounds",
                ["value", "n", "2", "i"],
                [["t", "root_t"]],
                if endpoint == 0 {
                    vec![("candidate", "candidate")]
                } else {
                    vec![]
                },
                inner,
                ["final_t"]
            ]),
            json!([
                "return",
                if endpoint == 0 {
                    vec!["final_t"]
                } else {
                    vec!["public", "final_t"]
                }
            ]),
        ];
        f.program[3][endpoint][4][2 - endpoint][0] = json!("root_t");
    }
    f.admit(None).unwrap();
    // Both the actual helper's coordinates and the invocation's induction
    // operand are checked, independently of equal index types.
    f.program[2][1][4][1][4][1] = json!("w");
    assert_eq!(
        f.admit(None).unwrap_err().0,
        "native-proof-helper-coordinates"
    );
}

#[test]
fn block_witness_slots_follow_nested_source_applications() {
    fn replace(value: &mut Json, from: &str, to: &str) {
        match value {
            Json::String(text) if text == from => *text = to.into(),
            Json::Array(values) => values.iter_mut().for_each(|v| replace(v, from, to)),
            _ => (),
        }
    }
    let mut f = block_fixture(Some(0));
    for event in &mut f.events {
        let old = event.origin.clone();
        let kind = if event.payload.is_some() {
            "message"
        } else {
            "query"
        };
        let mut origin = zkc_format::logical::decode_tree(
            &zkc_format::logical::native_origin_template(std::slice::from_ref(&old), kind).unwrap(),
        )
        .unwrap();
        origin[2] = json!([["apply", "Root", "a"], ["apply", "Middle", "b"]]);
        event.origin = zkc_format::logical::encode_tree(&origin)
            .unwrap()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        replace(&mut f.program, &old, &event.origin);
    }
    assert_eq!(
        native_origin_site(&f.events[1].origin, "query").unwrap(),
        "apply_11_apply_1_a_b_draw"
    );
    assert!(f.admit(None).is_err()); // The raw local gate slot cannot alias the application.
    replace(
        &mut f.program,
        "gate.draw",
        "gate.apply_11_apply_1_a_b_draw",
    );
    f.admit(None).unwrap();
}

#[test]
fn authored_selected_participant_requests_admit_without_transcript_state() {
    for nested in [false, true] {
        let mut fixture = Fixture::authored();
        for role in 0..2 {
            let message = fixture.program[3][role][6][0].clone();
            let branch = json!([
                "if",
                "choice",
                "public",
                if role == 0 {
                    vec![("candidate", "candidate")]
                } else {
                    vec![("public", "public")]
                },
                [
                    message,
                    ["yield", if role == 0 { vec![] } else { vec!["candidate"] }]
                ],
                [["yield", if role == 0 { vec![] } else { vec!["public"] }]],
                if role == 0 { vec![] } else { vec!["chosen"] }
            ]);
            fixture.program[3][role][6] = if nested {
                fixture.program[3][role][4]
                    .as_array_mut()
                    .unwrap()
                    .push(json!(["count", "index@native.index/0"]));
                json!([
                    [
                        "loop",
                        "rounds",
                        ["value", "count", "2", "i"],
                        if role == 0 {
                            vec![]
                        } else {
                            vec![("previous", "public")]
                        },
                        if role == 0 {
                            vec![("public", "public"), ("candidate", "candidate")]
                        } else {
                            vec![("public", "public")]
                        },
                        [
                            branch,
                            ["yield", if role == 0 { vec![] } else { vec!["chosen"] }]
                        ],
                        if role == 0 { vec![] } else { vec!["accepted"] }
                    ],
                    ["return", if role == 0 { vec![] } else { vec!["accepted"] }]
                ])
            } else {
                json!([
                    branch,
                    ["return", if role == 0 { vec![] } else { vec!["chosen"] }]
                ])
            };
        }
        fixture.admit(None).unwrap();
    }
}

// These checks target the transcript reader independently of the separately
// owned dependency and record-codec readers. Public-entry tests below retain
// the complete integration gate; no blanket refusal is an expected success.
mod selected_control {
    use super::*;

    fn replace(value: &mut Json, from: &str, to: &str) {
        match value {
            Json::String(text) if text == from => *text = to.into(),
            Json::Array(items) => items.iter_mut().for_each(|v| replace(v, from, to)),
            _ => {}
        }
    }
    fn encode(tree: &Json) -> String {
        zkc_format::logical::encode_tree(tree)
            .unwrap()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }
    fn origin(event: &NativeTranscriptEvent) -> Json {
        zkc_format::logical::decode_tree(
            &zkc_format::logical::native_origin_template(
                std::slice::from_ref(&event.origin),
                if event.payload.is_some() {
                    "message"
                } else {
                    "query"
                },
            )
            .unwrap(),
        )
        .unwrap()
    }

    fn fixture(custom: bool, both: bool) -> Fixture {
        let mut f = if custom {
            Fixture::custom()
        } else {
            Fixture::native()
        };
        let base_events = f.events.clone();
        let base_functions = f.program[2].as_array().unwrap().clone();
        let symbols: Vec<&str> = if custom {
            vec!["observe"]
        } else {
            vec!["observe", "challenge", "delivery"]
        };
        let base_bodies = [f.program[3][0][6].clone(), f.program[3][1][6].clone()];
        f.remove_functions(&symbols);
        f.events.clear();
        if let Some(plan) = &mut f.plan {
            plan.adapters.clear();
        }
        for label in if both {
            vec!["then", "else"]
        } else {
            vec!["then"]
        } {
            for (symbol, event) in symbols.iter().zip(&base_events) {
                let mut event = event.clone();
                let mut tree = origin(&event);
                tree[2] = json!([["branch", "Round", "choice", label]]);
                tree[4][2] = json!(format!("{}_{}", tree[4][2].as_str().unwrap(), label));
                let old = event.origin.clone();
                event.origin = encode(&tree);
                let name = format!("{symbol}_{label}");
                let mut function = base_functions
                    .iter()
                    .find(|f| f[1] == *symbol)
                    .unwrap()
                    .clone();
                function[1] = json!(name);
                replace(&mut function, &old, &event.origin);
                f.program[2].as_array_mut().unwrap().push(function);
                if let Some(plan) = &mut f.plan {
                    plan.adapters.push(construction::Adapter {
                        symbol: name,
                        native: false,
                        origins: vec![event.origin.clone()],
                    });
                }
                f.events.push(event);
            }
        }
        for (role, base_body) in base_bodies.iter().enumerate() {
            let mut arms = Vec::new();
            for label in ["then", "else"] {
                let active = label == "then" || both;
                let body = base_body.as_array().unwrap();
                let mut arm = if active {
                    Json::Array(body[if custom { 2 } else { 0 }..body.len() - 1].to_vec())
                } else {
                    json!([])
                };
                for symbol in &symbols {
                    replace(&mut arm, symbol, &format!("{symbol}_{label}"));
                }
                replace(&mut arm, if custom { "started" } else { "t" }, "arm_state");
                replace(&mut arm, "candidate", "arm_candidate");
                // Sites are globally unique even when their bodies are dormant.
                replace(&mut arm, "message", &format!("message_{label}"));
                arm.as_array_mut().unwrap().push(json!([
                    "yield",
                    if role == 0 {
                        vec![if active {
                            if custom { "next" } else { "t3" }
                        } else {
                            "arm_state"
                        }]
                    } else {
                        vec![
                            "arm_public",
                            if active {
                                if custom { "next" } else { "t3" }
                            } else {
                                "arm_state"
                            },
                        ]
                    }
                ]));
                arms.push(arm);
            }
            let mut captures = vec![json!(["arm_public", "public"])];
            if role == 0 {
                captures.push(json!(["arm_candidate", "candidate"]));
            }
            captures.push(json!(["arm_state", if custom { "started" } else { "t" }]));
            let mut body = if custom {
                base_body.as_array().unwrap()[..2].to_vec()
            } else {
                vec![]
            };
            body.push(json!([
                "if",
                "choice",
                "public",
                captures,
                arms[0],
                arms[1],
                if role == 0 {
                    vec!["joined"]
                } else {
                    vec!["accepted", "joined"]
                }
            ]));
            body.push(json!([
                "return",
                if role == 0 {
                    vec!["joined"]
                } else {
                    vec!["accepted", "joined"]
                }
            ]));
            f.program[3][role][6] = json!(body);
        }
        f
    }

    fn walk(f: &Fixture, allowance: usize) -> Result<Vec<NativeTranscriptEvent>> {
        let program = Program::decode(
            f.program.to_string().as_bytes(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
        )
        .unwrap();
        let transcript = f
            .suite
            .map(|s| PhysicalType::parse(&format!("transcript:{s}@host.resource/0")).unwrap());
        let mut work = ProofWork(allowance);
        let mut helpers = BTreeMap::new();
        if let Some(plan) = &f.plan {
            for adapter in &plan.adapters {
                let events: Vec<_> = f
                    .events
                    .iter()
                    .filter(|e| adapter.origins.contains(&e.origin))
                    .cloned()
                    .collect();
                let function = &program.program.functions[&adapter.symbol];
                helpers.insert(
                    adapter.symbol.clone(),
                    custom_helper(function, &plan.state, &events, "main", "V", &mut work)?,
                );
            }
        } else {
            for (name, function) in &program.program.functions {
                if let Some(helper) = helper(function, transcript.as_ref(), "main", "V", &mut work)?
                {
                    helpers.insert(name.clone(), helper);
                }
            }
        }
        let mut previous = None;
        let mut used = BTreeSet::new();
        let witness_slots: BTreeSet<_> = f
            .events
            .iter()
            .filter(|e| e.difficulty.is_some())
            .map(witness_slot)
            .collect::<Result<_>>()?;
        for (name, participant) in &program.program.participants {
            let custom = f.plan.is_some();
            let body = &participant.body[if custom { 2 } else { 0 }..];
            let current = if custom {
                f.plan
                    .as_ref()
                    .unwrap()
                    .state
                    .iter()
                    .map(|_| "started".to_owned())
                    .collect()
            } else {
                vec![participant.inputs.last().unwrap().0.clone()]
            };
            let mut walk = ProofWalk {
                admitted: &program,
                helpers: &helpers,
                producer: "P",
                validator: "V",
                validating: name == "v",
                transcript: true,
                affine_state: !custom,
                calls: BTreeSet::new(),
                verified: BTreeSet::new(),
                states: BTreeSet::new(),
                reached: Vec::new(),
                frames: BTreeMap::new(),
                positions: BTreeMap::new(),
                work: &mut work,
                witness_slots: witness_slots.clone(),
                delivered_witnesses: BTreeSet::new(),
                witness_values: BTreeSet::new(),
            };
            walk.block(body, Some(current), &[], &[], 0)?;
            if walk.reached != f.events || walk.delivered_witnesses != witness_slots {
                return Err(refuse("native-proof-state-chain"));
            }
            if previous.as_ref().is_some_and(|p| p != &walk.frames) {
                return Err(refuse("native-proof-loop-layout"));
            }
            previous = Some(walk.frames);
            used.extend(walk.calls);
        }
        if used.len() != helpers.len() {
            return Err(refuse("native-proof-state-chain"));
        }
        Ok(f.events.clone())
    }

    #[test]
    fn native_and_copy_state_thread_all_arms_with_role_specific_results() {
        for custom in [false, true] {
            for both in [false, true] {
                let f = fixture(custom, both);
                assert_eq!(walk(&f, PROOF_WORK).unwrap(), f.events);
            }
        }
    }

    #[test]
    fn complete_entry_admits_selected_native_and_custom_profiles() {
        for custom in [false, true] {
            let f = fixture(custom, true);
            f.admit(None).unwrap();
        }
    }

    #[test]
    fn copy_state_cannot_be_duplicated_omitted_substituted_or_reused() {
        for mutation in 0..5 {
            let mut f = fixture(true, true);
            let branch = &mut f.program[3][0][6][2];
            match mutation {
                0 => {
                    branch[3]
                        .as_array_mut()
                        .unwrap()
                        .push(json!(["duplicate", "started"]));
                }
                1 => branch[3][2][1] = json!("public"),
                2 => {
                    branch[3][0][1] = json!("started");
                    branch[3][2][1] = json!("public");
                }
                3 => branch[4][2][1] = json!(["arm_state"]),
                4 => branch[2] = json!("started"),
                _ => unreachable!(),
            }
            assert!(walk(&f, PROOF_WORK).is_err(), "mutation {mutation}");
        }
    }

    #[test]
    fn dormant_inventory_and_exact_origin_alternatives_are_checked() {
        let mut f = fixture(false, true);
        f.events.pop();
        assert_eq!(
            walk(&f, PROOF_WORK).unwrap_err().0,
            "native-proof-state-chain"
        );
        for mutation in 0..4 {
            let mut f = fixture(false, true);
            let old = f.events[0].origin.clone();
            let mut tree = origin(&f.events[0]);
            match mutation {
                0 => tree[2][0][3] = json!("else"),
                1 => tree[2][0][2] = json!("moved"),
                2 => tree[2] = json!([]),
                3 => tree[2][0][1] = json!("OtherProtocol"),
                _ => unreachable!(),
            }
            let new = encode(&tree);
            replace(&mut f.program, &old, &new);
            f.events[0].origin = new;
            assert!(walk(&f, PROOF_WORK).is_err(), "origin mutation {mutation}");
        }
        let mut f = fixture(false, true);
        // Move the call and its descriptor together; the actual arm still wins.
        f.program[3][0][6][0][4][1][2] = json!("observe_else");
        assert!(walk(&f, PROOF_WORK).is_err());
    }

    #[test]
    fn pending_messages_and_challenges_cannot_cross_branch_boundaries() {
        let mut f = fixture(false, true);
        let send = f.program[3][0][6][0][4].as_array_mut().unwrap().remove(0);
        let mut send = send;
        replace(&mut send, "arm_candidate", "candidate");
        f.program[3][0][6].as_array_mut().unwrap().insert(0, send);
        assert_eq!(
            walk(&f, PROOF_WORK).unwrap_err().0,
            "native-proof-observation-order"
        );

        let mut f = fixture(false, true);
        let branch = &mut f.program[3][0][6][0];
        branch[4].as_array_mut().unwrap().remove(3); // No delivery after the draw.
        branch[4][3][1] = json!(["t2"]);
        assert_eq!(
            walk(&f, PROOF_WORK).unwrap_err().0,
            "native-proof-state-chain"
        );
    }

    #[test]
    fn arm_environments_do_not_leak_state_names() {
        let mut f = fixture(true, true);
        // An ordinary sibling result may reuse an earlier arm's successor name.
        f.program[2].as_array_mut().unwrap().push(json!([
            "function",
            "identity",
            [["value", BOOL]],
            [BOOL],
            [["return", ["value"]]],
            ["identity", []]
        ]));
        for role in 0..2 {
            let arm = &mut f.program[3][role][6][2][5];
            replace(arm, "next", "other_next");
            arm.as_array_mut().unwrap().insert(
                0,
                json!(["local", "ordinary", "identity", ["arm_public"], ["next"]]),
            );
            arm.as_array_mut().unwrap().insert(
                1,
                json!(["local", "ordinary_again", "identity", ["next"], ["unused"]]),
            );
        }
        walk(&f, PROOF_WORK).unwrap();
    }

    #[test]
    fn event_free_branch_keeps_state_outside_and_zero_state_still_observes() {
        let mut f = fixture(true, true);
        for role in 0..2 {
            f.program[3][role][6].as_array_mut().unwrap().insert(
                2,
                json!([
                    "if",
                    "empty",
                    "public",
                    [["value", "public"]],
                    [["yield", []]],
                    [["yield", []]],
                    []
                ]),
            );
        }
        walk(&f, PROOF_WORK).unwrap();
        // A local construction may have no state ports at all.
        let mut f = fixture(true, true);
        f.plan.as_mut().unwrap().state.clear();
        for function in f.program[2].as_array_mut().unwrap() {
            if function[1].as_str().unwrap().starts_with("observe_") {
                function[2] = json!([["value", BOOL]]);
            } else {
                function[2] = json!([]);
            }
            function[3] = json!([]);
            function[4] = json!([["return", []]]);
        }
        for role in 0..2 {
            f.program[3][role][5] = if role == 0 { json!([]) } else { json!([BOOL]) };
            f.program[3][role][6][0][4] = json!([]);
            f.program[3][role][6][1][3] = json!([]);
            f.program[3][role][6][1][4] = json!([]);
            let branch = &mut f.program[3][role][6][2];
            branch[3].as_array_mut().unwrap().pop();
            branch[6].as_array_mut().unwrap().pop();
            for arm in [4, 5] {
                branch[arm][1][3] = json!(["arm_candidate"]);
                branch[arm][1][4] = json!([]);
                branch[arm][2][1].as_array_mut().unwrap().pop();
            }
            f.program[3][role][6][3][1].as_array_mut().unwrap().pop();
        }
        walk(&f, PROOF_WORK).unwrap();
    }

    #[test]
    fn return_if_uses_actual_arm_successor_and_static_suffix() {
        for custom in [false, true] {
            let mut f = fixture(custom, true);
            for role in 0..2 {
                let branch = &mut f.program[3][role][6][if custom { 2 } else { 0 }];
                let arm = branch[4].as_array_mut().unwrap();
                let state = if custom { "next" } else { "t3" };
                arm.insert(
                    arm.len() - 1,
                    json!([
                        "return_if",
                        "complete",
                        "arm_public",
                        if role == 0 {
                            vec![state]
                        } else {
                            vec!["arm_public", state]
                        },
                        if custom { vec![] } else { vec!["continued"] }
                    ]),
                );
                if !custom {
                    let last = arm.len() - 1;
                    replace(&mut arm[last], "t3", "continued");
                }
            }
            walk(&f, PROOF_WORK).unwrap();
            f.events.pop(); // Completion does not excuse a missing dormant event.
            assert!(walk(&f, PROOF_WORK).is_err());
        }
    }

    #[test]
    fn control_work_charges_dormant_arms_captures_and_origin_maps() {
        let f = fixture(false, true);
        assert_eq!(walk(&f, 0).unwrap_err().0, "native-proof-control-limit");
        assert_eq!(walk(&f, 20).unwrap_err().0, "native-proof-control-limit");
        walk(&f, PROOF_WORK).unwrap();
        let program = Program::decode(
            f.program.to_string().as_bytes(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
        )
        .unwrap();
        let mut work = ProofWork(1);
        assert_eq!(
            local_setup(
                &program.program.functions["observe_then"].body,
                &mut work,
                0
            )
            .unwrap_err()
            .0,
            "native-proof-control-limit"
        );
    }
    fn looped(mut f: Fixture, inside: bool, count: u64) -> Fixture {
        let index = "index@native.index/0";
        for event in &mut f.events {
            let old = event.origin.clone();
            let mut tree = origin(event);
            let label = tree[2][0][3].as_str().unwrap().to_owned();
            let step = json!([
                "repeat",
                "Round",
                if inside {
                    format!("rounds_{label}")
                } else {
                    "rounds".into()
                }
            ]);
            if inside {
                tree[2].as_array_mut().unwrap().push(step);
            } else {
                tree[2].as_array_mut().unwrap().insert(0, step);
            }
            event.origin = encode(&tree);
            replace(&mut f.program, &old, &event.origin);
        }
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
        for function in f.program[2].as_array_mut().unwrap() {
            function[2]
                .as_array_mut()
                .unwrap()
                .push(json!(["i", index]));
            let transition_inputs = function[4][1][4].as_array_mut().unwrap();
            *transition_inputs.last_mut().unwrap() = json!("indexed");
            function[4].as_array_mut().unwrap().insert(
                1,
                json!([
                    "op",
                    "coordinate",
                    "append",
                    [],
                    ["coords", "i"],
                    ["indexed"]
                ]),
            );
        }
        f.program[2].as_array_mut().unwrap().push(json!([
            "function",
            "count",
            [],
            [index],
            [
                ["op", "constant", "constant", [count.to_string()], [], ["n"]],
                ["return", ["n"]]
            ],
            ["count", []]
        ]));
        for role in 0..2 {
            let mut branch = f.program[3][role][6][0].clone();
            for (arm_index, label) in [(4, "then"), (5, "else")] {
                let arm = branch[arm_index].as_array_mut().unwrap();
                for op in arm.iter_mut() {
                    if op[0] == "local" {
                        op[3].as_array_mut().unwrap().push(json!("coordinate"));
                    }
                }
                if inside {
                    let mut inner = arm[..arm.len() - 1].to_vec();
                    inner.push(json!(["yield", ["t3"]]));
                    let mut captures = vec![json!(["arm_public", "arm_public"])];
                    if role == 0 {
                        captures.push(json!(["arm_candidate", "arm_candidate"]));
                    }
                    *arm = vec![
                        json!(["local", format!("count_{label}"), "count", [], ["n"]]),
                        json!([
                            "loop",
                            format!("rounds_{label}"),
                            ["value", "n", "3", "coordinate"],
                            [["arm_state", "arm_state"]],
                            captures,
                            inner,
                            ["loop_state"]
                        ]),
                        json!([
                            "yield",
                            if role == 0 {
                                vec!["loop_state"]
                            } else {
                                vec!["arm_public", "loop_state"]
                            }
                        ]),
                    ];
                }
            }
            if inside {
                f.program[3][role][6][0] = branch;
            } else {
                branch[3]
                    .as_array_mut()
                    .unwrap()
                    .push(json!(["coordinate", "iteration"]));
                let mut captures = vec![json!(["public", "public"])];
                if role == 0 {
                    captures.push(json!(["candidate", "candidate"]));
                }
                // The caller's root state and loop formal intentionally differ.
                f.program[3][role][4][2 - role][0] = json!("root_state");
                f.program[3][role][6] = json!([
                    ["local", "count", "count", [], ["n"]],
                    [
                        "loop",
                        "rounds",
                        ["value", "n", "3", "iteration"],
                        [["t", "root_state"]],
                        captures,
                        [branch, ["yield", ["joined"]]],
                        ["final_state"]
                    ],
                    [
                        "return",
                        if role == 0 {
                            vec!["final_state"]
                        } else {
                            vec!["public", "final_state"]
                        }
                    ]
                ]);
            }
        }
        f
    }

    #[test]
    fn branch_in_loop_and_loop_in_branch_admit_zero_one_and_three_trips() {
        for inside in [false, true] {
            for count in [0, 1, 3] {
                let f = looped(fixture(false, true), inside, count);
                // Root formal spelling is part of the actual program, not the
                // origin. The reader derives it from the admitted input port.
                walk(&f, PROOF_WORK).unwrap();
            }
        }
        let mut f = looped(fixture(false, true), false, 1);
        f.program[3][1][6][1][2][2] = json!("2");
        assert_eq!(
            walk(&f, PROOF_WORK).unwrap_err().0,
            "native-proof-loop-layout"
        );
        let mut f = looped(fixture(false, true), false, 1);
        f.program[3][0][6][1][5][0][3].as_array_mut().unwrap().pop();
        // Preserve structural scope while substituting an ordinary index for
        // the induction capture; equal types cannot establish a coordinate.
        f.program[3][0][6][1][4]
            .as_array_mut()
            .unwrap()
            .push(json!(["n", "n"]));
        f.program[3][0][6][1][5][0][3]
            .as_array_mut()
            .unwrap()
            .push(json!(["coordinate", "n"]));
        assert_eq!(
            walk(&f, PROOF_WORK).unwrap_err().0,
            "native-proof-coordinate-operand"
        );
    }

    #[test]
    fn match_payloads_captures_and_labels_remain_distinct() {
        let mut f = fixture(true, true);
        let variant = format!(
            "{}@logical.variant/0",
            zkc_test_support::variants::encode_tree(json!([
                "Choice",
                [["left", ["bool"]], ["right", ["bool"]]]
            ]))
        );
        for event in &mut f.events {
            let old = event.origin.clone();
            let mut tree = origin(event);
            tree[2][0][3] = json!(if tree[2][0][3] == "then" {
                "left"
            } else {
                "right"
            });
            event.origin = encode(&tree);
            replace(&mut f.program, &old, &event.origin);
            for adapter in &mut f.plan.as_mut().unwrap().adapters {
                for value in &mut adapter.origins {
                    if value == &old {
                        *value = event.origin.clone();
                    }
                }
            }
        }
        f.program[2].as_array_mut().unwrap().push(json!([
            "function",
            "choose",
            [["value", BOOL]],
            [&variant],
            [
                ["variant", "pack", &variant, "left", ["value"], "choice"],
                ["return", ["choice"]]
            ],
            ["choose", []]
        ]));
        for role in 0..2 {
            let branch = f.program[3][role][6][2].clone();
            let mut left = branch[4].clone();
            let mut right = branch[5].clone();
            // Use the actual variant payload as the producer's message. It is
            // neither a tag nor an extra capture row nor a transcript slot.
            if role == 0 {
                replace(&mut left, "arm_candidate", "payload");
                replace(&mut right, "arm_candidate", "payload");
            }
            f.program[3][role][6][2] = json!([
                "match",
                "choice",
                "selector",
                branch[3],
                [["left", ["payload"], left], ["right", ["payload"], right]],
                branch[6]
            ]);
            f.program[3][role][6].as_array_mut().unwrap().insert(
                2,
                json!(["local", "choose", "choose", ["public"], ["selector"]]),
            );
        }
        walk(&f, PROOF_WORK).unwrap();
        let mut wrong = f.program.clone();
        wrong[3][0][6][3][4][1][0] = json!("left");
        assert!(
            Program::decode(
                wrong.to_string().as_bytes(),
                &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
            )
            .is_err()
        );
        // A same-typed payload cannot replace the captured current state.
        f.program[3][0][6][3][4][0][2][1][3][0] = json!("payload");
        assert_eq!(
            walk(&f, PROOF_WORK).unwrap_err().0,
            "native-proof-state-chain"
        );
    }

    #[test]
    fn witness_groups_cannot_cross_an_arm_or_branch_entry() {
        let mut f = block_fixture(Some(0));
        for event in &mut f.events {
            let old = event.origin.clone();
            let mut tree = origin(event);
            tree[2] = json!([["branch", "Round", "choice", "then"]]);
            event.origin = encode(&tree);
            replace(&mut f.program, &old, &event.origin);
        }
        for role in 0..2 {
            let body = f.program[3][role][6].as_array().unwrap();
            let mut arm = json!(body[..body.len() - 1].to_vec());
            replace(&mut arm, "t", "arm_state");
            replace(&mut arm, "candidate", "arm_candidate");
            let mut captures = vec![json!(["arm_public", "public"])];
            if role == 0 {
                captures.push(json!(["arm_candidate", "candidate"]));
            }
            captures.push(json!(["arm_state", "t"]));
            arm.as_array_mut().unwrap().push(json!([
                "yield",
                if role == 0 {
                    vec!["t3"]
                } else {
                    vec!["arm_public", "t3"]
                }
            ]));
            f.program[3][role][6] = json!([
                [
                    "if",
                    "choice",
                    "public",
                    captures,
                    arm,
                    [[
                        "yield",
                        if role == 0 {
                            vec!["arm_state"]
                        } else {
                            vec!["arm_public", "arm_state"]
                        }
                    ]],
                    if role == 0 {
                        vec!["joined"]
                    } else {
                        vec!["accepted", "joined"]
                    }
                ],
                [
                    "return",
                    if role == 0 {
                        vec!["joined"]
                    } else {
                        vec!["accepted", "joined"]
                    }
                ]
            ]);
        }
        walk(&f, PROOF_WORK).unwrap();
        for role in 0..2 {
            let saved = f.program.clone();
            f.program[3][role][6][0][4].as_array_mut().unwrap().insert(
                3,
                json!([
                    "if",
                    "split_witness",
                    "arm_public",
                    [],
                    [["yield", []]],
                    [["yield", []]],
                    []
                ]),
            );
            assert_eq!(
                walk(&f, PROOF_WORK).unwrap_err().0,
                "native-proof-witness-order"
            );
            f.program = saved;
        }
    }

    #[test]
    fn runner_executes_only_the_selected_arm_of_the_original_program() {
        use crate::interpreter::Runner;
        use crate::vm::{Action, CutKind};
        let f = fixture(true, true);
        let entry = f.admit(None).unwrap();
        for selected in [false, true] {
            let mut runner = Runner::new(
                entry.admitted(),
                "main",
                "P",
                "selected",
                EndpointBackend::default(),
                vec![Boolean(selected), Boolean(true)],
            )
            .unwrap();
            let mut messages = Vec::new();
            let mut calls = Vec::new();
            loop {
                if runner.advance_local_control().unwrap() {
                    continue;
                }
                match runner.poll() {
                    Action::Local(action) => {
                        calls.push(action.cut.site.clone());
                        runner.execute_local(&action.cut).unwrap();
                    }
                    Action::Send(packet) => {
                        messages.push(packet.envelope.site.clone());
                        runner
                            .take_send(&packet.envelope.cut(CutKind::Send))
                            .unwrap();
                    }
                    Action::Returned(values) => {
                        assert_eq!(values, vec![Boolean(true)]);
                        break;
                    }
                    action => panic!("unexpected action: {action:?}"),
                }
            }
            let label = if selected { "then" } else { "else" };
            assert_eq!(messages, [format!("message_{label}")]);
            assert_eq!(
                calls,
                [
                    "initialize".to_owned(),
                    "start".to_owned(),
                    format!("observe_{label}")
                ]
            );
            assert_eq!(runner.into_backend().frames, 0);
        }
    }
    #[test]
    fn typed_frames_preserve_apply_expansion_generated_sites_and_exact_origin_bytes() {
        let mut tree = json!([
            "zkc.native-origin-template/0",
            "main",
            [
                ["apply", "Root", "a"],
                ["repeat", "Middle", "rounds"],
                ["apply", "Middle", "b"],
                ["branch", "Leaf", "choice", "else"]
            ],
            [],
            ["message", "Leaf", "message", "message", "P", "V"]
        ]);
        let original = encode(&tree);
        let frames = control_frames(&tree, &mut ProofWork(PROOF_WORK)).unwrap();
        assert_eq!(
            frames,
            vec![
                ControlFrame::Repeat {
                    protocol: "Middle".into(),
                    site: "apply_1_a_rounds".into()
                },
                ControlFrame::Branch {
                    protocol: "Leaf".into(),
                    site: "apply_11_apply_1_a_b_choice".into(),
                    alternative: "else".into()
                },
            ]
        );
        assert_eq!(repeat_count(&frames), 1);
        assert_eq!(
            native_origin_site(&original, "message").unwrap(),
            "apply_11_apply_1_a_b_message"
        );
        let bytes = zkc_format::logical::indexed_native_origin(
            std::slice::from_ref(&original),
            "message",
            &[3],
        )
        .unwrap();
        let mut dynamic = tree.clone();
        dynamic[0] = json!("zkc.native-origin/0");
        dynamic[3] = json!(["3"]);
        assert_eq!(bytes, zkc_format::logical::encode_tree(&dynamic).unwrap());
        assert_eq!(encode(&tree), original);
        assert!(
            zkc_format::logical::indexed_native_origin(
                std::slice::from_ref(&original),
                "message",
                &[3, 1]
            )
            .is_err()
        );
        tree[4][1] = json!(format!("zkc.oracle.{}", "a".repeat(64)));
        tree[4][2] = json!("already_expanded");
        assert_eq!(
            native_origin_site(&encode(&tree), "message").unwrap(),
            "already_expanded"
        );
        assert_eq!(
            control_frames(&tree, &mut ProofWork(PROOF_WORK)).unwrap(),
            frames
        );
    }

    #[test]
    fn independent_arm_loop_counts_are_not_flattened_into_one_count() {
        let mut f = looped(fixture(false, true), true, 0);
        let mut count = f.program[2].as_array().unwrap().last().unwrap().clone();
        count[1] = json!("else_count");
        count[4][0][3] = json!(["3"]);
        f.program[2].as_array_mut().unwrap().push(count);
        for role in 0..2 {
            f.program[3][role][6][0][5][0][2] = json!("else_count");
        }
        walk(&f, PROOF_WORK).unwrap();
    }

    #[test]
    fn setup_depth_is_bounded_independently_of_work() {
        let f = fixture(false, true);
        let program = Program::decode(
            f.program.to_string().as_bytes(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
        )
        .unwrap();
        assert_eq!(
            participant_setup(
                &program.program.participants["p"].body,
                &mut ProofWork(PROOF_WORK),
                65
            )
            .unwrap_err()
            .0,
            "native-proof-loop-limit"
        );
    }
    #[test]
    fn nested_branches_keep_every_actual_position_in_the_origin() {
        let mut f = fixture(false, true);
        for event in &mut f.events {
            let old = event.origin.clone();
            let mut tree = origin(event);
            tree[2]
                .as_array_mut()
                .unwrap()
                .insert(0, json!(["branch", "Round", "outer", "then"]));
            event.origin = encode(&tree);
            replace(&mut f.program, &old, &event.origin);
        }
        for role in 0..2 {
            let inner = f.program[3][role][6][0].clone();
            let mut captures = vec![json!(["public", "public"])];
            if role == 0 {
                captures.push(json!(["candidate", "candidate"]));
            }
            captures.push(json!(["t", "t"]));
            f.program[3][role][6] = json!([
                [
                    "if",
                    "outer",
                    "public",
                    captures,
                    [
                        inner,
                        [
                            "yield",
                            if role == 0 {
                                vec!["joined"]
                            } else {
                                vec!["accepted", "joined"]
                            }
                        ]
                    ],
                    [[
                        "yield",
                        if role == 0 {
                            vec!["t"]
                        } else {
                            vec!["public", "t"]
                        }
                    ]],
                    if role == 0 {
                        vec!["outer_state"]
                    } else {
                        vec!["outer_result", "outer_state"]
                    }
                ],
                [
                    "return",
                    if role == 0 {
                        vec!["outer_state"]
                    } else {
                        vec!["outer_result", "outer_state"]
                    }
                ]
            ]);
        }
        walk(&f, PROOF_WORK).unwrap();
        let old = f.events[0].origin.clone();
        let mut tree = origin(&f.events[0]);
        tree[2][0][3] = json!("else");
        f.events[0].origin = encode(&tree);
        replace(&mut f.program, &old, &f.events[0].origin);
        assert_eq!(
            walk(&f, PROOF_WORK).unwrap_err().0,
            "native-proof-control-origin"
        );
    }

    #[test]
    fn private_entry_selector_needs_dependency_admission() {
        let mut f = fixture(false, true);
        f.program[3][0][6][0][2] = json!("candidate");
        assert_eq!(
            f.admit(None).unwrap_err().0,
            "native-proof-private-dependency"
        );
    }

    #[test]
    fn dynamic_local_stop_does_not_skip_static_arm_inventory() {
        use crate::interpreter::Runner;
        use crate::vm::{Action, CutKind, StopKind};
        let mut f = fixture(true, true);
        f.program[2].as_array_mut().unwrap().push(json!([
            "function",
            "poison",
            [],
            [],
            [["stop", "reject", "reject"]],
            ["poison", []]
        ]));
        for role in 0..2 {
            f.program[3][role][6][2][4]
                .as_array_mut()
                .unwrap()
                .insert(0, json!(["local", "poison", "poison", [], []]));
        }
        walk(&f, PROOF_WORK).unwrap();
        let entry = f.admit(None).unwrap();
        for selected in [false, true] {
            let mut runner = Runner::new(
                entry.admitted(),
                "main",
                "P",
                "stop",
                EndpointBackend::default(),
                vec![Boolean(selected), Boolean(true)],
            )
            .unwrap();
            let mut sent = 0;
            loop {
                if runner.advance_local_control().unwrap() {
                    continue;
                }
                match runner.poll() {
                    Action::Local(action) => {
                        runner.execute_local(&action.cut).unwrap();
                    }
                    Action::Send(packet) => {
                        sent += 1;
                        runner
                            .take_send(&packet.envelope.cut(CutKind::Send))
                            .unwrap();
                    }
                    Action::Returned(_) => {
                        assert!(!selected);
                        assert_eq!(sent, 1);
                        break;
                    }
                    Action::Stopped(stop) => {
                        assert!(selected);
                        assert_eq!(stop.kind, StopKind::Explicit("reject".into()));
                        assert_eq!(sent, 0);
                        break;
                    }
                    action => panic!("unexpected action: {action:?}"),
                }
            }
            assert_eq!(runner.into_backend().frames, 0);
        }
        f.events.pop();
        assert!(walk(&f, PROOF_WORK).is_err());
    }
    #[test]
    fn unequal_message_counts_keep_complete_arm_inventory() {
        let mut f = fixture(true, true);
        let mut extra = f.events[0].clone();
        let mut tree = origin(&extra);
        tree[4][2] = json!("extra_then");
        tree[4][3] = json!("extra_then");
        extra.origin = encode(&tree);
        f.events.insert(1, extra.clone());
        let mut function = f.program[2]
            .as_array()
            .unwrap()
            .iter()
            .find(|function| function[1] == "observe_then")
            .unwrap()
            .clone();
        function[1] = json!("observe_extra");
        f.program[2].as_array_mut().unwrap().push(function);
        f.plan.as_mut().unwrap().adapters.insert(
            1,
            construction::Adapter {
                symbol: "observe_extra".into(),
                native: false,
                origins: vec![extra.origin],
            },
        );
        for role in 0..2 {
            let arm = f.program[3][role][6][2][4].as_array_mut().unwrap();
            let yield_at = arm.len() - 1;
            arm.insert(
                yield_at,
                if role == 0 {
                    json!(["send", "extra_then", "extra_then", "V", "arm_candidate"])
                } else {
                    json!([
                        "receive",
                        "extra_then",
                        "extra_then",
                        "P",
                        "extra_payload",
                        BOOL
                    ])
                },
            );
            arm.insert(
                yield_at + 1,
                json!([
                    "local",
                    "observe_extra",
                    "observe_extra",
                    [
                        "next",
                        if role == 0 {
                            "arm_candidate"
                        } else {
                            "extra_payload"
                        }
                    ],
                    ["extra_state"]
                ]),
            );
            let last = arm.len() - 1;
            replace(&mut arm[last], "next", "extra_state");
        }
        assert_eq!(walk(&f, PROOF_WORK).unwrap().len(), 3);
    }

    #[test]
    fn coordinate_capture_reuse_keeps_the_actual_first_row() {
        let mut f = looped(fixture(false, true), false, 1);
        for role in 0..2 {
            f.program[3][role][6][1][5][0][3]
                .as_array_mut()
                .unwrap()
                .push(json!(["duplicate_coordinate", "iteration"]));
        }
        walk(&f, PROOF_WORK).unwrap();
        f.program[3][0][6][1][5][0][4][1][3][2] = json!("duplicate_coordinate");
        assert_eq!(
            walk(&f, PROOF_WORK).unwrap_err().0,
            "native-proof-coordinate-operand"
        );
    }
    #[test]
    fn record_codec_normalization_preserves_observed_and_event_free_branches() {
        for observed in [false, true] {
            let mut f = Fixture::codec();
            if observed {
                let mut tree = origin(&f.events[0]);
                tree[2] = json!([["branch", "Round", "choice", "then"]]);
                f.events[0].origin = encode(&tree);
                let plan = f.plan.as_mut().unwrap();
                plan.adapters[0].origins = vec![f.events[0].origin.clone()];
                plan.codec.as_mut().unwrap().messages[0].origins = vec![f.events[0].origin.clone()];
            }
            for role in 0..2 {
                let mut body = f.program[3][role][6].as_array().unwrap().clone();
                if observed {
                    let mut arm = body[3..body.len() - 2].to_vec();
                    arm.push(json!([
                        "yield",
                        if role == 0 {
                            vec!["next", "r1"]
                        } else {
                            vec!["public", "next", "r1"]
                        }
                    ]));
                    let mut captures = vec![json!(["public", "public"])];
                    if role == 0 {
                        captures.push(json!(["candidate", "candidate"]));
                    }
                    captures.extend([json!(["t", "t"]), json!(["r", "r"])]);
                    if role == 1 {
                        captures.push(json!(["proof", "proof"]));
                    }
                    body.truncate(3);
                    body.push(json!([
                        "if",
                        "choice",
                        "public",
                        captures,
                        arm,
                        [[
                            "yield",
                            if role == 0 {
                                vec!["t", "r"]
                            } else {
                                vec!["public", "t", "r"]
                            }
                        ]],
                        if role == 0 {
                            vec!["joined", "record"]
                        } else {
                            vec!["accepted", "joined", "record"]
                        }
                    ]));
                    if role == 0 {
                        body.extend([
                            json!(["local", "write", "write", ["record"], ["proof"]]),
                            json!(["return", ["joined", "proof"]]),
                        ]);
                    } else {
                        body.extend([
                            json!(["local", "finish", "finish", ["record", "proof"], []]),
                            json!(["return", ["accepted", "joined"]]),
                        ]);
                    }
                } else {
                    body[3][3][0] = json!("record");
                    body.insert(
                        3,
                        json!([
                            "if",
                            "choice",
                            "public",
                            if role == 0 {
                                vec![("r", "r")]
                            } else {
                                vec![("r", "r"), ("proof", "proof")]
                            },
                            [["yield", ["r"]]],
                            [["yield", ["r"]]],
                            ["record"]
                        ]),
                    );
                }
                f.program[3][role][6] = json!(body);
            }
            let entry = f.admit(None).unwrap();
            assert!(entry.has_record_codec());
            // Normalization is evidence: the original Runner body still owns
            // the record and proof captures and its actual output layout.
            assert!(
                matches!(&entry.admitted().program.participants["v"].body[3],
                Instruction::Conditional { captures, .. } if captures.last().unwrap().1 == "proof")
            );
            f.program[3][1][6][3][3]
                .as_array_mut()
                .unwrap()
                .push(json!(["duplicate_proof", "proof"]));
            assert!(f.admit(None).is_err());
        }
    }
    #[test]
    fn an_event_free_branch_does_not_make_its_enclosing_loop_observed() {
        let mut f = fixture(false, true);
        let index = "index@native.index/0";
        f.program[1].as_array_mut().unwrap().push(json!([
            "count_binding",
            "index.constant",
            [],
            "native/index.constant",
            []
        ]));
        f.program[2].as_array_mut().unwrap().push(json!([
            "function",
            "count",
            [],
            [index],
            [
                ["op", "count", "count_binding", ["3"], [], ["n"]],
                ["return", ["n"]]
            ],
            ["count", []]
        ]));
        for role in 0..2 {
            f.program[3][role][6].as_array_mut().unwrap().insert(
                0,
                json!([
                    "loop",
                    "empty_loop",
                    ["value", "n", "3", "i"],
                    [],
                    [["public", "public"]],
                    [
                        [
                            "if",
                            "empty_branch",
                            "public",
                            [],
                            [["yield", []]],
                            [["yield", []]],
                            []
                        ],
                        ["yield", []]
                    ],
                    []
                ]),
            );
            f.program[3][role][6]
                .as_array_mut()
                .unwrap()
                .insert(0, json!(["local", "count", "count", [], ["n"]]));
        }
        walk(&f, PROOF_WORK).unwrap();
    }
}

mod physical_accounting {
    use super::*;

    fn repeated(calls: usize, aggregate: bool) -> Fixture {
        let physical = if aggregate {
            let arms: Vec<_> = (0..8)
                .map(|i| json!([format!("a{i}"), vec!["bool"; 8]]))
                .collect();
            format!(
                "{}@logical.variant/0",
                zkc_test_support::variants::logical("AccountingPayload", json!(arms))
            )
        } else {
            BOOL.into()
        };
        let arm = |prefix: &str| {
            let mut body: Vec<_> = (0..calls)
                .map(|i| {
                    json!([
                        "local",
                        format!("{prefix}.{i}"),
                        "id",
                        ["data"],
                        [format!("unused.{i}")]
                    ])
                })
                .collect();
            body.push(json!(["yield", []]));
            body
        };
        Fixture {
            program: json!([
                "zkc.program/0",
                [],
                [[
                    "function",
                    "id",
                    [["x", physical]],
                    [physical],
                    [["return", ["x"]]],
                    ["id", []]
                ]],
                [[
                    "participant",
                    "v",
                    "root",
                    "V",
                    [["choose", BOOL], ["payload", physical]],
                    [BOOL],
                    [
                        [
                            "if",
                            "choice",
                            "choose",
                            [["data", "payload"]],
                            arm("left"),
                            arm("right"),
                            []
                        ],
                        ["return", ["choose"]]
                    ],
                    []
                ]],
                [["entry", "main", [["V", "v"]]]]
            ]),
            events: vec![],
            plan: None,
            suite: None,
        }
    }
    fn decode(f: &Fixture) -> Program {
        Program::decode(
            f.program.to_string().as_bytes(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
        )
        .unwrap()
    }
    fn walk(program: &Program, allowance: usize) -> Result<(usize, usize)> {
        let helpers = BTreeMap::new();
        let mut work = ProofWork(allowance);
        let mut walk = ProofWalk {
            admitted: program,
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
        walk.block(&program.program.participants["v"].body, None, &[], &[], 0)?;
        Ok((allowance - walk.work.0, walk.verified.len()))
    }

    #[test]
    fn repeated_aggregate_all_arm_calls_have_charged_cold_and_cached_judgments() {
        let one = decode(&repeated(1, true));
        let two = decode(&repeated(2, true));
        let scalar = decode(&repeated(1, false));
        let (cold, cached) = walk(&one, PROOF_WORK).unwrap();
        assert_eq!(cached, 1); // The second arm reuses a completed function judgment.
        let (warm, cached) = walk(&two, PROOF_WORK).unwrap();
        assert_eq!(cached, 1);
        assert!(cold > walk(&scalar, PROOF_WORK).unwrap().0);
        assert!(warm > cold); // Every hit, including the dormant arm, still costs work.
        assert!(warm - cold < cold);
        let scalar_one = walk(&scalar, PROOF_WORK).unwrap().0;
        let scalar_two = walk(&decode(&repeated(2, false)), PROOF_WORK).unwrap().0;
        assert_eq!(
            warm - cold,
            scalar_two - scalar_one,
            "warm aggregate hits must not repeat the cold recursive judgment"
        );
        let mut cold_fixture = repeated(1, true);
        let mut second = cold_fixture.program[2][0].clone();
        second[1] = json!("id2");
        second[5][0] = json!("id2");
        cold_fixture.program[2].as_array_mut().unwrap().push(second);
        cold_fixture.program[3][0][6][0][5][0][2] = json!("id2");
        let (two_cold, cached) = walk(&decode(&cold_fixture), PROOF_WORK).unwrap();
        assert_eq!(cached, 2);
        assert!(two_cold > cold);
        assert_eq!(walk(&two, warm).unwrap(), (warm, 1));
        assert_eq!(
            walk(&two, warm - 1).unwrap_err().0,
            "native-proof-control-limit"
        );
        // A distinct decoded Program cannot inherit the previous walk's cache.
        assert_eq!(
            walk(&decode(&repeated(2, true)), PROOF_WORK).unwrap().0,
            warm
        );
        repeated(100, true)
            .admit_with(
                Some(NativeProofOperation::Verify),
                &BTreeMap::from([("V".into(), vec![0, 1])]),
                &[0, 1],
                0,
            )
            .unwrap();
        // The independently reviewed 20,000-call carrier used 420,069 old work
        // units while rebuilding at least 2,600,000 default-layout nodes.
        assert_eq!(
            repeated(10_000, true)
                .admit_with(
                    Some(NativeProofOperation::Verify),
                    &BTreeMap::from([("V".into(), vec![0, 1])]),
                    &[0, 1],
                    0
                )
                .unwrap_err()
                .0,
            "native-proof-control-limit"
        );
    }

    #[test]
    fn type_judgments_charge_before_work_and_keep_exhaustion_sticky() {
        let program = decode(&repeated(1, true));
        let function = &program.program.functions["id"];
        let mut full = ProofWork(PROOF_WORK);
        verifier_function(function, program.contracts(), &mut full).unwrap();
        let exact = PROOF_WORK - full.0;
        let mut work = ProofWork(exact);
        verifier_function(function, program.contracts(), &mut work).unwrap();
        assert_eq!(work.0, 0);
        let mut short = ProofWork(exact - 1);
        assert_eq!(
            verifier_function(function, program.contracts(), &mut short)
                .unwrap_err()
                .0,
            "native-proof-control-limit"
        );
        assert_eq!(short.0, 0);
        assert!(short.charge(1).is_err());
        let mut failed = ProofWork(7);
        assert!(failed.charge(8).is_err());
        assert_eq!(failed.0, 0);
        assert!(failed.charge(1).is_err());
        // Codec uses its own remaining counter and diagnostic, never a new
        // ProofWork(PROOF_WORK) hidden inside the shared judgment.
        let mut codec_work = exact;
        construction_function(function, &[], program.contracts(), &mut codec_work).unwrap();
        assert_eq!(codec_work, 0);
        let mut codec_short = exact - 1;
        assert_eq!(
            construction_function(function, &[], program.contracts(), &mut codec_short)
                .unwrap_err()
                .0,
            "native-proof-codec-limit"
        );
        assert_eq!(codec_short, 0);
        assert!(AdmissionWork::charge(&mut codec_short, 1).is_err());
    }

    #[test]
    fn nested_default_and_selected_children_retain_their_exact_permissions() {
        for permission in [false, true] {
            let (contracts, _, selected) = selected_payload_context(permission);
            let mut work = ProofWork(PROOF_WORK);
            assert_eq!(
                verifier_data(&selected, &contracts, &mut work).unwrap(),
                permission
            );
            let sequence = PhysicalType::parse("sequence<bool>@logical.sequence/0").unwrap();
            assert!(verifier_data(&sequence, &contracts, &mut work).unwrap());
        }
    }
    #[test]
    fn wire_precharge_exhaustion_does_not_enter_contract_lookup() {
        use std::sync::{
            Arc,
            atomic::{AtomicUsize, Ordering},
        };
        #[derive(Debug)]
        struct Count(Arc<AtomicUsize>);
        impl crate::vm::ContractSupport for Count {
            fn permits_type(&self, _: &PhysicalType) -> bool {
                self.0.fetch_add(1, Ordering::Relaxed);
                true
            }
            fn permits_binding(&self, _: &crate::vm::OperationBinding) -> bool {
                true
            }
        }
        let (contracts, _, payload) = selected_payload_context(true);
        let calls = Arc::new(AtomicUsize::new(0));
        let contracts = contracts.restricted(Count(calls.clone()));
        let mut full = ProofWork(PROOF_WORK);
        assert!(type_work::wire_data(&payload, &contracts, &mut full).unwrap());
        assert!(calls.load(Ordering::Relaxed) > 0);
        let exact = PROOF_WORK - full.0;
        for allowance in [0, exact - 1] {
            calls.store(0, Ordering::Relaxed);
            let mut short = ProofWork(allowance);
            assert_eq!(
                type_work::wire_data(&payload, &contracts, &mut short)
                    .unwrap_err()
                    .0,
                "native-proof-control-limit"
            );
            assert_eq!(short.0, 0);
            assert_eq!(
                calls.load(Ordering::Relaxed),
                0,
                "no recursive contract validation after reservation failure"
            );
        }
        let mut work = ProofWork(exact);
        assert!(type_work::wire_data(&payload, &contracts, &mut work).unwrap());
        assert_eq!(work.0, 0);
    }

    fn codec_constructor_work(rows: usize, allowance: usize, aggregate: bool) -> Result<usize> {
        let (contracts, field, variant) = selected_payload_context(true);
        let payload = if aggregate { variant } else { field };
        let mut f = selected_payload_fixture(true, &payload);
        for row in 1..rows {
            let mut event = f.events[0].clone();
            let mut tree = zkc_format::logical::decode_tree(
                &zkc_format::logical::native_origin_template(&[event.origin.clone()], "message")
                    .unwrap(),
            )
            .unwrap();
            tree[4][2] = json!(format!("message{row}"));
            tree[4][3] = json!(format!("message{row}"));
            event.origin = zkc_format::logical::encode_tree(&tree)
                .unwrap()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            let symbol = format!("observe{row}");
            let mut function = f.program[2]
                .as_array()
                .unwrap()
                .iter()
                .find(|function| function[1] == "observe")
                .unwrap()
                .clone();
            function[1] = json!(symbol);
            function[5][0] = json!(symbol);
            f.program[2].as_array_mut().unwrap().push(function);
            let plan = f.plan.as_mut().unwrap();
            let mut adapter = plan.adapters[0].clone();
            adapter.symbol = symbol;
            adapter.origins = vec![event.origin.clone()];
            plan.adapters.push(adapter);
            let codec = plan.codec.as_mut().unwrap();
            let mut selection = codec.messages[0].clone();
            selection.origins = vec![event.origin.clone()];
            codec.messages.push(selection); // Reuse encode/receive/decode/wire/slice.
            f.events.push(event);
        }
        let program = Program::decode(f.program.to_string().as_bytes(), &contracts).unwrap();
        let plan = f.plan.as_ref().unwrap();
        let mut helpers = BTreeMap::new();
        for (adapter, event) in plan.adapters.iter().zip(&f.events) {
            let helper = custom_helper(
                &program.program.functions[&adapter.symbol],
                &plan.state,
                std::slice::from_ref(event),
                "main",
                "V",
                &mut ProofWork(PROOF_WORK),
            )
            .unwrap();
            helpers.insert(adapter.symbol.clone(), helper);
        }
        let mut work = ProofWork(allowance);
        codec::CheckedCodec::new(
            &program,
            plan.codec.as_ref().unwrap(),
            &plan.state,
            &helpers,
            "P",
            "V",
            None,
            &mut work,
        )?;
        Ok(allowance - work.0)
    }

    #[test]
    fn codec_constructor_repeated_aggregate_rows_charge_wire_comparisons_and_copies() {
        let one = codec_constructor_work(1, PROOF_WORK, true).unwrap();
        let two = codec_constructor_work(2, PROOF_WORK, true).unwrap();
        assert!(
            two > one,
            "reused helper judgments cannot skip per-message physical work"
        );
        let scalar_one = codec_constructor_work(1, PROOF_WORK, false).unwrap();
        let scalar_two = codec_constructor_work(2, PROOF_WORK, false).unwrap();
        assert!(
            two - one > scalar_two - scalar_one,
            "each repeated row must charge complete aggregate layout work"
        );
        assert_eq!(codec_constructor_work(2, two, true).unwrap(), two);
        assert_eq!(
            codec_constructor_work(2, two - 1, true).unwrap_err().0,
            "native-proof-control-limit"
        );
        assert_eq!(
            codec_constructor_work(2, 0, true).unwrap_err().0,
            "native-proof-control-limit"
        );
        assert_eq!(
            codec_constructor_work(2, one, true).unwrap_err().0,
            "native-proof-control-limit"
        );
    }
}

mod complete_state_vectors {
    use super::*;

    fn fixture(early: bool) -> Fixture {
        let mut f = Fixture::codec();
        let index = "index@native.index/0";
        let bytes = "bytes@native.bytes/0";
        let mut origin = zkc_format::logical::decode_tree(
            &zkc_format::logical::native_origin_template(&[f.events[0].origin.clone()], "message")
                .unwrap(),
        )
        .unwrap();
        origin[2] = json!([
            ["repeat", "Round", "rounds"],
            ["branch", "Round", "choice", "then"],
            ["branch", "Round", "detail", "then"]
        ]);
        f.events[0].origin = zkc_format::logical::encode_tree(&origin)
            .unwrap()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let plan = f.plan.as_mut().unwrap();
        plan.state = vec![PhysicalType::parse(BOOL).unwrap(); 2];
        plan.adapters[0].origins = vec![f.events[0].origin.clone()];
        plan.codec.as_mut().unwrap().messages[0].origins = vec![f.events[0].origin.clone()];
        for function in f.program[2].as_array_mut().unwrap() {
            match function[1].as_str().unwrap() {
                "initialize" => {
                    function[3] = json!([BOOL, BOOL]);
                    function[4] = json!([
                        ["bool_constant", "left", "left", true],
                        ["bool_constant", "right", "right", false],
                        ["return", ["left", "right"]]
                    ]);
                }
                "start" | "observe" | "wire" => {
                    let name = function[1].as_str().unwrap().to_owned();
                    let mut inputs = vec![json!(["left", BOOL]), json!(["right", BOOL])];
                    if name == "observe" {
                        inputs.extend([json!(["value", BOOL]), json!(["i", index])]);
                    }
                    if name == "wire" {
                        inputs.push(json!(["chunk", bytes]));
                    }
                    function[2] = json!(inputs);
                    function[3] = json!([BOOL, BOOL]);
                    function[4] = json!([["return", ["left", "right"]]]);
                }
                _ => {}
            }
        }
        f.program[2].as_array_mut().unwrap().push(json!([
            "function",
            "count",
            [],
            [index],
            [["op", "count", "zero", ["1"], [], ["n"]], ["return", ["n"]]],
            ["count", []]
        ]));
        if early {
            f.program[2].as_array_mut().unwrap().extend([
                json!([
                    "function",
                    "write_if",
                    [["condition", BOOL], ["r", index]],
                    [bytes],
                    [
                        [
                            "if",
                            "choose",
                            "condition",
                            ["r"],
                            [["op", "yes", "empty", [], [], ["p"]], ["yield", ["p"]]],
                            [["op", "no", "empty", [], [], ["p"]], ["yield", ["p"]]],
                            ["proof"]
                        ],
                        ["return", ["proof"]]
                    ],
                    ["write_if", []]
                ]),
                json!([
                    "function",
                    "finish_if",
                    [["condition", BOOL], ["r", index], ["proof", bytes]],
                    [],
                    [
                        [
                            "if",
                            "choose",
                            "condition",
                            ["r", "proof"],
                            [["yield", []]],
                            [["yield", []]],
                            []
                        ],
                        ["return", []]
                    ],
                    ["finish_if", []]
                ]),
            ]);
            let codec = f.plan.as_mut().unwrap().codec.as_mut().unwrap();
            codec.conditional_write = "write_if".into();
            codec.conditional_finish = "finish_if".into();
        }
        for role in 0..2 {
            if early {
                f.program[3][role][4]
                    .as_array_mut()
                    .unwrap()
                    .insert(1, json!(["complete", BOOL]));
            }
            f.program[3][role][5] = if role == 0 {
                json!([BOOL, BOOL, bytes])
            } else {
                json!([BOOL, BOOL, BOOL])
            };
            let mut observed = if role == 0 {
                vec![
                    json!([
                        "local",
                        "encode",
                        "encode",
                        ["r", "candidate"],
                        ["r1", "chunk"]
                    ]),
                    json!([
                        "local",
                        "wire",
                        "wire",
                        ["left", "right", "chunk"],
                        ["w0", "w1"]
                    ]),
                    json!([
                        "local",
                        "observe",
                        "observe",
                        ["w0", "w1", "candidate", "coordinate"],
                        ["n0", "n1"]
                    ]),
                ]
            } else {
                vec![
                    json!([
                        "local",
                        "receive",
                        "receive",
                        ["r", "proof"],
                        ["r1", "lo", "hi"]
                    ]),
                    json!(["local", "slice", "slice", ["proof", "lo", "hi"], ["chunk"]]),
                    json!([
                        "local",
                        "wire",
                        "wire",
                        ["left", "right", "chunk"],
                        ["w0", "w1"]
                    ]),
                    json!(["local", "decode", "decode", ["chunk"], ["candidate"]]),
                    json!([
                        "local",
                        "observe",
                        "observe",
                        ["w0", "w1", "candidate", "coordinate"],
                        ["n0", "n1"]
                    ]),
                ]
            };
            if early {
                observed.push(if role == 0 {
                    json!([
                        "local",
                        "conditional_finish",
                        "write_if",
                        ["complete", "r1"],
                        ["partial"]
                    ])
                } else {
                    json!([
                        "local",
                        "conditional_finish",
                        "finish_if",
                        ["complete", "r1", "proof"],
                        []
                    ])
                });
                observed.push(json!([
                    "return_if",
                    "finalize",
                    "complete",
                    if role == 0 {
                        vec!["n0", "n1", "partial"]
                    } else {
                        vec!["public", "n0", "n1"]
                    },
                    []
                ]));
            }
            observed.push(json!(["yield", ["n0", "n1", "r1"]]));
            let captures = |first: &str, second: &str, record: &str| {
                let mut result = vec![json!(["public", "public"])];
                if early {
                    result.push(json!(["complete", "complete"]));
                }
                if role == 0 {
                    result.push(json!(["candidate", "candidate"]));
                }
                result.extend([
                    json!(["coordinate", "coordinate"]),
                    json!(["left", first]),
                    json!(["right", second]),
                    json!(["r", record]),
                ]);
                if role == 1 {
                    result.push(json!(["proof", "proof"]));
                }
                result
            };
            let inner = json!([
                "if",
                "detail",
                "public",
                captures("left", "right", "r"),
                observed,
                [["yield", ["left", "right", "r"]]],
                ["inner0", "inner1", "inner_record"]
            ]);
            let outer = json!([
                "if",
                "choice",
                "public",
                captures("left", "right", "r"),
                [inner, ["yield", ["inner0", "inner1", "inner_record"]]],
                [["yield", ["left", "right", "r"]]],
                ["outer0", "outer1", "outer_record"]
            ]);
            let mut loop_captures = vec![json!(["public", "public"])];
            if early {
                loop_captures.push(json!(["complete", "complete"]));
            }
            if role == 0 {
                loop_captures.push(json!(["candidate", "candidate"]));
            }
            if role == 1 {
                loop_captures.push(json!(["proof", "proof"]));
            }
            let mut body = vec![
                json!([
                    "local",
                    "initialize",
                    "initialize",
                    [],
                    ["initial0", "initial1"]
                ]),
                json!([
                    "local",
                    "start",
                    "start",
                    ["initial0", "initial1"],
                    ["started0", "started1"]
                ]),
                json!(["local", "record_init", "record_init", [], ["record"]]),
                json!(["local", "count", "count", [], ["n"]]),
                json!([
                    "loop",
                    "rounds",
                    ["value", "n", "2", "coordinate"],
                    [["left", "started0"], ["right", "started1"], ["r", "record"]],
                    loop_captures,
                    [outer, ["yield", ["outer0", "outer1", "outer_record"]]],
                    ["joined0", "joined1", "joined_record"]
                ]),
            ];
            if role == 0 {
                body.extend([
                    json!(["local", "write", "write", ["joined_record"], ["proof"]]),
                    json!(["return", ["joined0", "joined1", "proof"]]),
                ]);
            } else {
                body.extend([
                    json!(["local", "finish", "finish", ["joined_record", "proof"], []]),
                    json!(["return", ["public", "joined0", "joined1"]]),
                ]);
            }
            f.program[3][role][6] = json!(body);
        }
        f
    }

    fn admit(
        f: &Fixture,
        operation: Option<NativeProofOperation>,
        early: bool,
    ) -> Result<NativeProofEntry> {
        if !early {
            return f.admit(operation);
        }
        let maps = f
            .maps()
            .into_keys()
            .map(|role| {
                let indices = if role == "P" {
                    vec![0, 1, 2]
                } else {
                    vec![0, 1]
                };
                (role, indices)
            })
            .collect();
        f.admit_with(operation, &maps, &[0, 1], 0)
    }

    #[test]
    fn actual_complete_entry_threads_distinct_same_typed_slots_through_codec_and_control() {
        for early in [false, true] {
            let f = fixture(early);
            assert!(admit(&f, None, early).unwrap().has_record_codec());
            for operation in [NativeProofOperation::Prove, NativeProofOperation::Verify] {
                assert!(
                    admit(&fixture(early).selected(operation), Some(operation), early)
                        .unwrap()
                        .has_record_codec()
                );
            }
            for mutation in ["swap", "stale", "mixed"] {
                let mut bad = fixture(early);
                // Change just the event-bearing inner arm in the actual validator.
                let arm = bad.program[3][1][6][4][5][0][4][0][4]
                    .as_array_mut()
                    .unwrap();
                let returned = arm.last_mut().unwrap();
                returned[1] = match mutation {
                    "swap" => json!(["n1", "n0", "r1"]),
                    "stale" => json!(["left", "right", "r1"]),
                    _ => json!(["n0", "right", "r1"]),
                };
                assert_eq!(
                    admit(&bad, None, early).unwrap_err().0,
                    "native-proof-state-chain",
                    "{early}/{mutation}"
                );
            }
            if early {
                let mut bad = fixture(true);
                let arm = bad.program[3][1][6][4][5][0][4][0][4]
                    .as_array_mut()
                    .unwrap();
                let returned = arm.iter_mut().find(|op| op[0] == "return_if").unwrap();
                returned[3] = json!(["public", "n1", "n0"]);
                assert_eq!(
                    admit(&bad, None, early).unwrap_err().0,
                    "native-proof-state-chain"
                );
            }
        }
    }
}

mod signature_accounting {
    use super::*;

    fn physical(aggregate: bool) -> String {
        if !aggregate {
            return BOOL.into();
        }
        let arms: Vec<_> = (0..8)
            .map(|i| json!([format!("a{i}"), vec!["bool"; 8]]))
            .collect();
        format!(
            "{}@logical.variant/0",
            zkc_test_support::variants::logical("AccountingPayload", json!(arms))
        )
    }

    fn decode(carrier: Json) -> Program {
        Program::decode(
            carrier.to_string().as_bytes(),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose()),
        )
        .unwrap()
    }

    fn adapters(aggregate: bool, rows: usize) -> (Program, Vec<PhysicalType>) {
        let spelling = physical(aggregate);
        let functions: Vec<_> = (0..rows)
            .map(|i| {
                let name = format!("observe{i}");
                json!([
                    "function",
                    name,
                    [["s", spelling], ["v", BOOL]],
                    [spelling],
                    [["return", ["s"]]],
                    [name, []]
                ])
            })
            .collect();
        let program = decode(json!(["zkc.program/0", [], functions, [], []]));
        // Form the plan state independently, without cloning Program's layout.
        let state = vec![PhysicalType::parse(&spelling).unwrap()];
        let actual = &program.program.functions["observe0"].inputs[0].1;
        assert_eq!(actual, &state[0]);
        if aggregate {
            assert!(!std::ptr::eq(
                actual.children().unwrap().as_ptr(),
                state[0].children().unwrap().as_ptr()
            ));
            fn nodes(ty: &PhysicalType) -> usize {
                1 + ty
                    .children()
                    .unwrap_or_default()
                    .iter()
                    .map(nodes)
                    .sum::<usize>()
            }
            assert_eq!(nodes(&state[0]), 65);
        }
        (program, state)
    }

    fn measured(mut run: impl FnMut(&mut ProofWork) -> Result<()>) -> usize {
        let mut work = ProofWork(PROOF_WORK);
        run(&mut work).unwrap();
        let cost = PROOF_WORK - work.0;
        assert!(cost > 0);
        let mut exact = ProofWork(cost);
        run(&mut exact).unwrap();
        assert_eq!(exact.0, 0);
        for allowance in [0, cost - 1] {
            let mut short = ProofWork(allowance);
            assert_eq!(run(&mut short).unwrap_err().0, "native-proof-control-limit");
            assert_eq!(short.0, 0);
            assert_eq!(run(&mut short).unwrap_err().0, "native-proof-control-limit");
            assert_eq!(short.charge(1).unwrap_err().0, "native-proof-control-limit");
        }
        cost
    }

    fn helper_work(aggregate: bool, rows: usize) -> usize {
        let (program, state) = adapters(aggregate, rows);
        let events = vec![event(false)];
        measured(|work| {
            for function in program.program.functions.values() {
                let helper = custom_helper(function, &state, &events, "main", "V", work)?;
                assert!(helper.frames.is_empty());
                assert_eq!(helper.events, events);
                assert_eq!(helper.message, Some(("P".into(), "V".into())));
            }
            Ok(())
        })
    }

    #[test]
    fn frameless_custom_helper_reserves_aggregate_signature_before_later_function_judgment() {
        let scalar = helper_work(false, 1);
        let aggregate = helper_work(true, 1);
        assert!(aggregate > scalar);
        let (program, state) = adapters(true, 1);
        let function = &program.program.functions["observe0"];
        let mut exact = ProofWork(aggregate);
        custom_helper(function, &state, &[event(false)], "main", "V", &mut exact).unwrap();
        assert_eq!(exact.0, 0);
        assert_eq!(
            construction_function(function, &state, program.contracts(), &mut exact)
                .unwrap_err()
                .0,
            "native-proof-control-limit"
        );
        eprintln!("signature helper local logical work: scalar={scalar}, aggregate65={aggregate}");
    }

    #[test]
    fn each_actual_adapter_row_pays_its_own_state_comparisons() {
        let scalar = helper_work(false, 1);
        let scalar_two = helper_work(false, 2);
        let aggregate = helper_work(true, 1);
        let aggregate_two = helper_work(true, 2);
        assert_eq!(scalar_two - scalar, scalar);
        assert_eq!(aggregate_two - aggregate, aggregate);
        assert!(aggregate_two - aggregate > scalar_two - scalar);
        eprintln!(
            "adapter rows logical work: scalar1={scalar}, scalar2={scalar_two}, aggregate1={aggregate}, aggregate2={aggregate_two}"
        );
    }

    #[test]
    fn custom_signature_failures_keep_their_typed_refusals() {
        let (program, state) = adapters(true, 1);
        let function = &program.program.functions["observe0"];
        let mut mismatch = event(false);
        mismatch.payload = Some(super::super::super::LogicalType::parse("index").unwrap());
        for (slots, events) in [
            (vec![PhysicalType::parse(BOOL).unwrap()], vec![event(false)]),
            (state.clone(), vec![mismatch]),
        ] {
            let mut work = ProofWork(PROOF_WORK);
            assert_eq!(
                custom_helper(function, &slots, &events, "main", "V", &mut work)
                    .err()
                    .unwrap()
                    .0,
                "native-proof-helper-signature"
            );
            assert!(work.0 < PROOF_WORK);
        }
        let mut malformed = event(false);
        malformed.origin = "00".into();
        let mut work = ProofWork(PROOF_WORK);
        assert_eq!(
            custom_helper(function, &state, &[malformed], "main", "V", &mut work)
                .err()
                .unwrap()
                .0,
            "native-proof-origin"
        );
        assert!(work.0 < PROOF_WORK);
    }

    #[test]
    fn selected_port_precharges_recursive_logical_mismatches() {
        let (_, state) = adapters(true, 1);
        let selected = PhysicalType::parse(&physical(true)).unwrap();
        let cost = measured(|work| {
            assert_eq!(
                selected_port(Some(&selected), state[0].logical(), work)?,
                state[0]
            );
            Ok(())
        });
        let scalar = PhysicalType::parse(BOOL).unwrap();
        let mut work = ProofWork(PROOF_WORK);
        assert_eq!(
            selected_port(Some(&selected), scalar.logical(), &mut work)
                .unwrap_err()
                .0,
            "native-proof-helper-signature"
        );
        assert!(PROOF_WORK - work.0 > 2);
        eprintln!("selected aggregate port logical work={cost}");
    }

    #[test]
    fn participant_and_root_signatures_reserve_both_independent_layouts() {
        let mut costs = Vec::new();
        for aggregate in [false, true] {
            let (program, state) = adapters(aggregate, 1);
            let function = &program.program.functions["observe0"];
            let participant = measured(|work| {
                participant_state_ports(&function.inputs[..1], &function.outputs, &state, 1, work)
            });
            let root = measured(|work| root_output_signature(function, &state, work));
            costs.push((participant, root));
            let wrong = vec![PhysicalType::parse("index@native.index/0").unwrap()];
            assert_eq!(
                participant_state_ports(
                    &function.inputs[..1],
                    &function.outputs,
                    &wrong,
                    1,
                    &mut ProofWork(PROOF_WORK)
                )
                .unwrap_err()
                .0,
                "native-proof-state-ports"
            );
            assert_eq!(
                root_output_signature(function, &wrong, &mut ProofWork(PROOF_WORK))
                    .unwrap_err()
                    .0,
                "native-proof-construction-root"
            );
        }
        assert!(costs[1].0 > costs[0].0);
        assert!(costs[1].1 > costs[0].1);
        eprintln!(
            "participant/root signature logical work: scalar={:?}, aggregate65={:?}",
            costs[0], costs[1]
        );
    }

    #[test]
    fn grouped_events_and_frames_pay_copy_and_comparison_work() {
        let (_, state) = adapters(false, 1);
        let mut first = event(false);
        let bytes = zkc_format::logical::native_origin_template(&[first.origin.clone()], "message")
            .unwrap();
        let mut origin = zkc_format::logical::decode_tree(&bytes).unwrap();
        origin[2] = json!([
            ["repeat", "Round", "rounds"],
            ["branch", "Round", "choose", "then"]
        ]);
        let encode = |origin: &Json| {
            zkc_format::logical::encode_tree(origin)
                .unwrap()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        };
        first.origin = encode(&origin);
        let mut second = first.clone();
        origin[4][2] = json!("second");
        second.origin = encode(&origin);
        let program = decode(json!([
            "zkc.program/0",
            [],
            [[
                "function",
                "observe",
                [
                    ["s", BOOL],
                    ["a", BOOL],
                    ["b", BOOL],
                    ["i", "index@native.index/0"]
                ],
                [BOOL],
                [["return", ["s"]]],
                ["observe", []]
            ]],
            [],
            []
        ]));
        let events = vec![first, second];
        let cost = measured(|work| {
            let helper = custom_helper(
                &program.program.functions["observe"],
                &state,
                &events,
                "main",
                "V",
                work,
            )?;
            assert_eq!(helper.events, events);
            assert_eq!(helper.frames.len(), 2);
            Ok(())
        });
        eprintln!("grouped events and repeat/branch frames logical work={cost}");
    }

    fn index_helper(then_ops: usize, else_ops: usize) -> (Program, NativeTranscriptEvent) {
        let mut event = event(true);
        event.contract = "transcript.native.indexed.index".into();
        event.bound = Some(7);
        let bytes =
            zkc_format::logical::native_origin_template(&[event.origin.clone()], "query").unwrap();
        let mut origin = zkc_format::logical::decode_tree(&bytes).unwrap();
        origin[4][5] = json!("index");
        event.origin = zkc_format::logical::encode_tree(&origin)
            .unwrap()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let arm = |prefix: &str, count: usize| {
            let mut ops: Vec<_> = (0..count)
                .map(|i| {
                    json!([
                        "bool_constant",
                        format!("{prefix}{i}"),
                        format!("unused{i}"),
                        true
                    ])
                })
                .collect();
            ops.push(json!(["yield", ["s"]]));
            ops
        };
        let program = decode(json!([
            "zkc.program/0",
            [],
            [[
                "function",
                "sample",
                [["s", BOOL]],
                ["index@native.index/0", BOOL],
                [
                    [
                        "if",
                        "choice",
                        "s",
                        ["s"],
                        arm("left", then_ops),
                        arm("right", else_ops),
                        ["next"]
                    ],
                    ["stop", "reject", "reject"]
                ],
                ["sample", []]
            ]],
            [],
            []
        ]));
        (program, event)
    }

    #[test]
    fn custom_index_range_reserves_complete_dormant_child_traversal_at_callpoint() {
        let state = vec![PhysicalType::parse(BOOL).unwrap()];
        let cost = |left, right| {
            let (program, event) = index_helper(left, right);
            measured(|work| {
                custom_helper(
                    &program.program.functions["sample"],
                    &state,
                    std::slice::from_ref(&event),
                    "main",
                    "V",
                    work,
                )
                .map(|_| ())
            })
        };
        let empty = cost(0, 0);
        let left = cost(3, 0);
        let right = cost(0, 3);
        let both = cost(3, 3);
        assert!(left > empty);
        assert_eq!(left, right);
        assert_eq!(both - empty, 2 * (left - empty));
        eprintln!(
            "index helper child traversal logical work: empty={empty}, left={left}, right={right}, both={both}"
        );
    }
}
