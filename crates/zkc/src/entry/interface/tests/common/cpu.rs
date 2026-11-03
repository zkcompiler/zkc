//! CPU contexts and source subjects authored independently of inventory conversion.
use super::*;
use crate::entry::{self, BindingError, RoleInputs, RunEntry, RunRequest};
use std::collections::BTreeMap;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, SetupRegistry, Value as Native};
use zkc_runtime::{
    host::wire::WireBackend,
    vm::{LogicalType, PhysicalType},
};

fn physical(logical: &str) -> String {
    PhysicalType::default_for(LogicalType::parse(logical).unwrap())
        .unwrap()
        .spelling()
}
fn backend() -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("role00000000", "session", "sample_Protocol", None),
            None,
        ),
        SetupRegistry::default(),
    )
    .unwrap()
}
fn package(d: &Value, inputs: &[Vec<String>]) -> (Package, String) {
    let participants: Vec<_> = inputs
        .iter()
        .enumerate()
        .map(|(i, types)| {
            json!([
                "participant",
                format!("participant{i}"),
                "root",
                format!("role{i:08}"),
                types
                    .iter()
                    .enumerate()
                    .map(|(n, t)| json!([format!("x{n}"), t]))
                    .collect::<Vec<_>>(),
                [],
                [["return", []]],
                []
            ])
        })
        .collect();
    let program = json!([
        "zkc.program/0",
        [],
        [],
        participants,
        [[
            "entry",
            "sample_Protocol",
            [
                ["role00000000", "participant0"],
                ["role00000001", "participant1"]
            ]
        ]]
    ])
    .to_string();
    let artifact=json!({"format":"zkc.run/0","candidate":program,"entry":"sample_Protocol","roles":["role00000000","role00000001"],"steps":[{"role":0,"instruction":0,"anchor":null},{"role":1,"instruction":0,"anchor":null}]}).to_string();
    let bytes=json!({"format":"zkc.entry/0","original":"original","interface":d.to_string(),"artifact":artifact,"assets":[],"options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization":entry::OracleSelection::default()}}).to_string();
    (
        Package::capture(
            bytes.as_bytes(),
            &Sha256::digest(bytes.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap(),
        program,
    )
}
/// The context the SDK produces from a named request, checked against its
/// canonical rows for this program. A test pin identifies fixture bytes only,
/// not external application trust.
fn produced(
    run: &RunEntry,
    request: RunRequest,
    program: &str,
    rows: Value,
) -> (Vec<u8>, [u8; 32]) {
    let bytes = run.common_input_context(request).unwrap();
    assert_eq!(
        zkc_format::logical::decode_tree(&bytes).unwrap(),
        json!([
            "zkc.input-bindings/0",
            digest(program),
            "sample_Protocol",
            rows
        ])
    );
    let pin = Sha256::digest(&bytes).into();
    (bytes, pin)
}
/// A produced context with edited rows, for reader refusals.
fn edited(bytes: &[u8], change: impl FnOnce(&mut Value)) -> (Vec<u8>, [u8; 32]) {
    let mut tree = zkc_format::logical::decode_tree(bytes).unwrap();
    change(&mut tree);
    let bytes = zkc_format::logical::encode_tree(&tree).unwrap();
    let pin = Sha256::digest(&bytes).into();
    (bytes, pin)
}
fn row(input: usize, path: Value, logical: &str, facet: Value, expected: Value) -> Value {
    json!([
        [
            ["role00000000", input.to_string(), path.clone()],
            ["role00000001", input.to_string(), path]
        ],
        physical(logical),
        facet,
        expected
    ])
}
fn native_hex(value: &Native) -> String {
    crate::io::bytes::hex(&backend().encode_wire(value).unwrap())
}
fn request(p: entry::Value, v: entry::Value) -> RunRequest {
    RunRequest {
        session: "common-inputs".into(),
        setups: BTreeMap::new(),
        roles: [("P".into(), p), ("V".into(), v)]
            .into_iter()
            .map(|(role, value)| {
                (
                    role,
                    RoleInputs {
                        inputs: [("subject".into(), value)].into(),
                        ..Default::default()
                    },
                )
            })
            .collect(),
    }
}
fn admitted(d: &Value, types: &[Vec<String>]) -> (RunEntry, String) {
    let (package, program) = package(d, types);
    (
        RunEntry::admit(package, Default::default(), Default::default()).unwrap(),
        program,
    )
}

#[test]
fn named_bool_value_and_enum_tag_contexts_execute_and_refuse_before_execution() {
    for tag_only in [false, true] {
        let boolean = schema("boolean", "bool", json!(["bool"]));
        let s = if tag_only {
            variant("example::NamedChoice", vec![field("flag", 0, boolean)])
        } else {
            boolean
        };
        let logical = s["leaves"][0].as_str().unwrap();
        let d = shared(
            s.clone(),
            json!({"kind":if tag_only {"tag"} else {"value"}}),
        );
        let (run, program) = admitted(&d, &[vec![physical(logical)], vec![physical(logical)]]);
        let make = |flag| {
            if tag_only {
                entry::Value::Variant {
                    alternative: "Payload".into(),
                    fields: [("flag".into(), Native::Bool(flag).into())].into(),
                }
            } else {
                Native::Bool(flag).into()
            }
        };
        let expected = if tag_only {
            "31".into()
        } else {
            native_hex(&Native::Bool(true))
        };
        // Tags agree although the payloads differ.
        let (bytes, pin) = produced(
            &run,
            request(make(true), make(!tag_only)),
            &program,
            json!([row(
                0,
                json!([]),
                logical,
                json!(if tag_only { "tag" } else { "value" }),
                json!(["active", expected])
            )]),
        );
        let bound = run.bind_common_inputs(&bytes, &pin).unwrap();
        if !tag_only {
            let error = bound
                .prepare(request(make(true), make(false)))
                .err()
                .unwrap();
            assert_eq!(error.phase, entry::EntryPhase::Preparation);
            assert_eq!(error.code(), "input-binding-Value");
        }
        let plan = bound.prepare(request(make(true), make(true))).unwrap();
        assert!(plan.execute().is_success());
        // Tag equality permits deliberately unequal active payloads.
        if tag_only {
            assert!(
                bound
                    .prepare(request(make(false), make(true)))
                    .unwrap()
                    .execute()
                    .is_success()
            );
        }
    }
}

#[test]
fn named_extents_preserve_zero_contents_and_both_matrix_axes() {
    for (axis, rows, cols) in [(0, 0, 3), (0, 2, 3), (1, 2, 3)] {
        let logical = "matrix:bls12-381.fr";
        let d = shared(
            schema("builtin", "Matrix", json!([logical])),
            json!({"kind":"extent","axis":axis}),
        );
        let (run, program) = admitted(&d, &[vec![physical(logical)], vec![physical(logical)]]);
        let expected = if axis == 0 { rows } else { cols };
        let shape = || Native::matrix(rows, cols, &[], &Policy::default()).unwrap();
        let (bytes, pin) = produced(
            &run,
            request(shape().into(), shape().into()),
            &program,
            json!([row(
                0,
                json!([]),
                logical,
                json!(["extent", axis.to_string()]),
                json!([
                    "active",
                    crate::io::bytes::hex(expected.to_string().as_bytes())
                ])
            )]),
        );
        let bound = run.bind_common_inputs(&bytes, &pin).unwrap();
        let left = Native::matrix(rows, cols, &[], &Policy::default()).unwrap();
        let right = Native::matrix(
            rows,
            cols,
            &if rows > 0 {
                vec![(1, 2, zkc_cpu::Scalar::from(9u64))]
            } else {
                vec![]
            },
            &Policy::default(),
        )
        .unwrap();
        assert!(
            bound
                .prepare(request(left.into(), right.into()))
                .unwrap()
                .execute()
                .is_success()
        );
        let wrong = Native::matrix(cols, rows, &[], &Policy::default()).unwrap();
        assert_eq!(
            bound
                .prepare(request(
                    Native::matrix(rows, cols, &[], &Policy::default())
                        .unwrap()
                        .into(),
                    wrong.into()
                ))
                .err()
                .unwrap()
                .code(),
            "input-binding-Value"
        );
    }
}

#[test]
fn pinned_inventory_rejects_omission_extra_observation_axis_slot_entry_and_program() {
    let logical = "bytes";
    let s = schema("builtin", "Bytes", json!([logical]));
    let d = run_document(
        json!([
            port("subject", 0, json!([0]), json!([0, 1]), s.clone()),
            port("other", 1, json!([1]), json!([0, 1]), s)
        ]),
        json!([obligation(0, json!([]), json!({"kind":"extent","axis":0}))]),
    );
    let (run, program) = admitted(
        &d,
        &[vec![physical(logical); 2], vec![physical(logical); 2]],
    );
    let empty = || entry::Value::from(Native::Bytes(vec![].into()));
    let both = |role: &str| {
        (
            role.to_owned(),
            RoleInputs {
                inputs: [("subject".into(), empty()), ("other".into(), empty())].into(),
                ..Default::default()
            },
        )
    };
    let (original, _) = produced(
        &run,
        RunRequest {
            session: "common-inputs".into(),
            setups: BTreeMap::new(),
            roles: [both("P"), both("V")].into(),
        },
        &program,
        json!([row(
            0,
            json!([]),
            logical,
            json!(["extent", "0"]),
            json!(["active", "30"])
        )]),
    );
    for attack in [
        "omit", "extra", "value", "axis", "slot", "role", "path", "entry", "program", "pin",
    ] {
        let (run, _) = admitted(
            &d,
            &[vec![physical(logical); 2], vec![physical(logical); 2]],
        );
        let (bytes, mut pin) = edited(&original, |tree| {
            let rows = &mut tree[3];
            match attack {
                "omit" => *rows = json!([]),
                "extra" => {
                    let extra = rows[0].clone();
                    rows.as_array_mut().unwrap().push(extra);
                }
                "value" => rows[0][2] = json!("value"),
                "axis" => rows[0][2] = json!(["extent", "1"]),
                "slot" => {
                    rows[0][0][0][1] = json!("1");
                    rows[0][0][1][1] = json!("1");
                }
                "role" => rows[0][0][0][0] = json!("P"),
                "path" => rows[0][0][0][2] = json!(["0", "0"]),
                "entry" => tree[2] = json!("stale"),
                "program" => tree[1] = json!("stale"),
                _ => (),
            }
        });
        if attack == "pin" {
            pin = [0; 32];
        }
        let error = run.bind_common_inputs(&bytes, &pin).err().unwrap();
        assert_eq!(
            error,
            match attack {
                "entry" | "program" => BindingError::Subject,
                "pin" => BindingError::Identity,
                _ => BindingError::Requirements,
            },
            "{attack}"
        );
    }
    // Authenticating a newly edited package plus a new context is not coverage.
    let mut reduced = d;
    reduced["protocols"][0]["common_input_requirements"] = json!([]);
    let (run, program) = admitted(
        &reduced,
        &[vec![physical(logical); 2], vec![physical(logical); 2]],
    );
    let (bytes, pin) = produced(
        &run,
        RunRequest {
            session: "common-inputs".into(),
            setups: BTreeMap::new(),
            roles: [both("P"), both("V")].into(),
        },
        &program,
        json!([]),
    );
    assert!(run.bind_common_inputs(&bytes, &pin).is_ok());
}

#[test]
fn nested_payload_inventory_uses_actual_program_types_and_conditional_paths() {
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let mut tuple = schema("tuple", "(bool,bool)", json!(["bool", "bool"]));
    tuple["fields"] = json!([
        field("0", 0, boolean.clone()),
        field("1", 1, boolean.clone())
    ]);
    let inner = variant(
        "example::Inner",
        vec![field("prefix", 0, tuple.clone()), field("flag", 2, boolean)],
    );
    let outer = variant(
        "example::Outer",
        vec![field("prefix", 0, tuple), field("nested", 2, inner)],
    );
    let logical = outer["leaves"][0].as_str().unwrap().to_owned();
    let path = json!([{"kind":"alternative","index":1},{"kind":"payload","index":1},{"kind":"alternative","index":1},{"kind":"payload","index":1}]);
    let mut d = shared(outer, json!({"kind":"value"}));
    for c in d["protocols"][0]["common_input_requirements"][0]["components"]
        .as_array_mut()
        .unwrap()
    {
        c["path"] = path.clone();
    }
    let (run, program) = admitted(&d, &[vec![physical(&logical)], vec![physical(&logical)]]);
    assert_eq!(
        run.common_input_requirements().unwrap()[0].components[0].path,
        [(1, 2), (1, 2)]
    );
    let make = |active, flag| entry::Value::Variant {
        alternative: if active { "Payload" } else { "Empty" }.into(),
        fields: if active {
            [
                (
                    "prefix".into(),
                    entry::Value::Tuple(vec![
                        Native::Bool(false).into(),
                        Native::Bool(true).into(),
                    ]),
                ),
                (
                    "nested".into(),
                    entry::Value::Variant {
                        alternative: "Payload".into(),
                        fields: [
                            (
                                "prefix".into(),
                                entry::Value::Tuple(vec![
                                    Native::Bool(true).into(),
                                    Native::Bool(false).into(),
                                ]),
                            ),
                            ("flag".into(), Native::Bool(flag).into()),
                        ]
                        .into(),
                    },
                ),
            ]
            .into()
        } else {
            BTreeMap::new()
        },
    };
    let (bytes, pin) = produced(
        &run,
        request(make(true, true), make(true, true)),
        &program,
        json!([row(
            0,
            json!(["1", "2", "1", "2"]),
            "bool",
            json!("value"),
            json!(["active", native_hex(&Native::Bool(true))])
        )]),
    );
    let bound = run.bind_common_inputs(&bytes, &pin).unwrap();
    assert!(
        bound
            .prepare(request(make(true, true), make(true, true)))
            .unwrap()
            .execute()
            .is_success()
    );
    assert_eq!(
        bound
            .prepare(request(make(true, true), make(true, false)))
            .err()
            .unwrap()
            .code(),
        "input-binding-Value"
    );
    assert_eq!(
        bound
            .prepare(request(make(false, false), make(false, false)))
            .err()
            .unwrap()
            .code(),
        "input-binding-Value"
    );
    let (run, program) = admitted(&d, &[vec![physical(&logical)], vec![physical(&logical)]]);
    // Dormant paths of every component produce the inactive expectation.
    let (bytes, pin) = produced(
        &run,
        request(make(false, false), make(false, true)),
        &program,
        json!([row(
            0,
            json!(["1", "2", "1", "2"]),
            "bool",
            json!("value"),
            json!(["inactive"])
        )]),
    );
    assert!(
        run.bind_common_inputs(&bytes, &pin)
            .unwrap()
            .prepare(request(make(false, false), make(false, true)))
            .unwrap()
            .execute()
            .is_success()
    );
}

#[test]
fn shared_root_role_permutations_keep_zero_width_supply_and_participant_positions() {
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let empty = schema("unit", "()", json!([]));
    let mut inner = schema("logical_record", "InnerState", json!([]));
    inner["constructible"] = json!(false);
    inner["roles"] = json!(["A", "B"]);
    let mut private = field("private", 0, boolean.clone());
    private["placement"] = data_placement(json!([1]));
    let mut shared_field = field("shared", 1, boolean.clone());
    shared_field["placement"] = data_placement(json!([0, 1]));
    let mut unit = field("empty", 2, empty.clone());
    unit["placement"] = data_placement(json!([0]));
    inner["fields"] = json!([private, shared_field, unit]);
    let inner_formula = json!({"kind":"product","instance":inner["identity"],"arguments":[1,0],"fields":[data_placement(json!([0])),data_placement(json!([0,1])),data_placement(json!([1]))]});
    let inner_actual = json!({"kind":"product","instance":inner["identity"],"arguments":[0,1],"fields":[data_placement(json!([1])),data_placement(json!([0,1])),data_placement(json!([0]))]});
    let mut outer = schema("logical_record", "OuterState", json!([]));
    outer["constructible"] = json!(false);
    outer["roles"] = json!(["X", "Y"]);
    let mut header = field("header", 0, boolean);
    header["placement"] = data_placement(json!([0]));
    let mut nested = field("nested", 1, inner);
    nested["placement"] = inner_formula;
    let mut tail = field("tail", 3, empty);
    tail["placement"] = data_placement(json!([1]));
    outer["fields"] = json!([header, nested, tail]);
    let placement = json!({"kind":"product","instance":outer["identity"],"arguments":[1,0],"fields":[data_placement(json!([1])),inner_actual,data_placement(json!([0]))]});
    let path = json!([{"kind":"field","index":1},{"kind":"field","index":1}]);
    let d = run_document(
        json!([placed_port("state", 0, json!([0, 1, 2]), placement, outer)]),
        json!([obligation(0, path, json!({"kind":"value"}))]),
    );
    let (run, program) = admitted(&d, &[vec![physical("bool")], vec![physical("bool"); 3]]);
    assert_eq!(run.interface().native_input_position("P", 2).unwrap(), 0);
    assert_eq!(run.interface().native_input_position("V", 2).unwrap(), 2);
    let requirements = run.common_input_requirements().unwrap();
    assert_eq!(
        requirements[0]
            .components
            .iter()
            .map(|c| c.input)
            .collect::<Vec<_>>(),
        [0, 2]
    );
    let rows = json!([[
        [["role00000000", "0", []], ["role00000001", "2", []]],
        physical("bool"),
        "value",
        ["active", native_hex(&Native::Bool(true))]
    ]]);
    let mut decoder = entry::inputs::Decoder::new(Default::default()).unwrap();
    let groups = run.interface().input_groups();
    let p = decoder
        .decode(
            &groups[0],
            br#"{"state_nested_shared":true,"state_nested_empty":null,"state_tail":null}"#,
            None,
        )
        .unwrap();
    let v = decoder
        .decode(
            &groups[1],
            br#"{"state_header":false,"state_nested_private":false,"state_nested_shared":true}"#,
            None,
        )
        .unwrap();
    let make = |p, v| RunRequest {
        session: "permutation".into(),
        setups: BTreeMap::new(),
        roles: [
            (
                "P".into(),
                RoleInputs {
                    inputs: p,
                    ..Default::default()
                },
            ),
            (
                "V".into(),
                RoleInputs {
                    inputs: v,
                    ..Default::default()
                },
            ),
        ]
        .into(),
    };
    let decode = |p: &[u8], v: &[u8]| {
        let mut decoder = entry::inputs::Decoder::new(Default::default()).unwrap();
        (
            decoder.decode(&groups[0], p, None).unwrap(),
            decoder.decode(&groups[1], v, None).unwrap(),
        )
    };
    let (p_copy, v_copy) = decode(
        br#"{"state_nested_shared":true,"state_nested_empty":null,"state_tail":null}"#,
        br#"{"state_header":false,"state_nested_private":false,"state_nested_shared":true}"#,
    );
    let (bytes, pin) = produced(&run, make(p_copy, v_copy), &program, rows);
    let bound = run.bind_common_inputs(&bytes, &pin).unwrap();
    assert!(bound.prepare(make(p, v)).unwrap().execute().is_success());
    // Empty semantic supplies remain mandatory and are never common native slots.
    let mut missing = BTreeMap::new();
    missing.insert("state_nested_shared".into(), Native::Bool(true).into());
    let error = bound.prepare(make(missing, BTreeMap::new())).err().unwrap();
    assert_eq!(error.phase, entry::EntryPhase::Request);
}

#[test]
fn authenticating_edited_package_does_not_rebind_a_stale_program_or_inventory_context() {
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let d = run_document(
        json!([
            port("subject", 0, json!([0]), json!([0, 1]), boolean.clone()),
            port("other", 1, json!([1]), json!([0, 1]), boolean)
        ]),
        json!([obligation(0, json!([]), json!({"kind":"value"}))]),
    );
    let (original, program) = package(&d, &[vec![physical("bool"); 2], vec![physical("bool"); 2]]);
    let run = RunEntry::admit(original.clone(), Default::default(), Default::default()).unwrap();
    let both = |role: &str, other| {
        (
            role.to_owned(),
            RoleInputs {
                inputs: [
                    ("subject".into(), Native::Bool(true).into()),
                    ("other".into(), Native::Bool(other).into()),
                ]
                .into(),
                ..Default::default()
            },
        )
    };
    let (bytes, pin) = produced(
        &run,
        RunRequest {
            session: "common-inputs".into(),
            setups: BTreeMap::new(),
            roles: [both("P", false), both("V", true)].into(),
        },
        &program,
        json!([row(
            0,
            json!([]),
            "bool",
            json!("value"),
            json!(["active", native_hex(&Native::Bool(true))])
        )]),
    );
    for attack in ["program-bytes", "inventory-slot", "inventory-extra"] {
        let mut frame: Value = serde_json::from_slice(original.bytes()).unwrap();
        if attack == "program-bytes" {
            let mut artifact: Value =
                serde_json::from_str(frame["artifact"].as_str().unwrap()).unwrap();
            artifact["candidate"] = json!(format!("{program} "));
            frame["artifact"] = json!(artifact.to_string());
        } else {
            let mut interface: Value =
                serde_json::from_str(frame["interface"].as_str().unwrap()).unwrap();
            if attack == "inventory-slot" {
                for c in interface["protocols"][0]["common_input_requirements"][0]["components"]
                    .as_array_mut()
                    .unwrap()
                {
                    c["input"] = json!(1);
                }
            } else {
                interface["protocols"][0]["common_input_requirements"]
                    .as_array_mut()
                    .unwrap()
                    .push(obligation(1, json!([]), json!({"kind":"value"})));
            }
            frame["interface"] = json!(interface.to_string());
        }
        let edited = frame.to_string();
        assert!(
            Package::capture(edited.as_bytes(), original.identity(), Package::MAX_BYTES).is_err()
        );
        let captured = Package::capture(
            edited.as_bytes(),
            &Sha256::digest(edited.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap();
        let run = RunEntry::admit(captured, Default::default(), Default::default()).unwrap();
        assert_eq!(
            run.bind_common_inputs(&bytes, &pin).err().unwrap(),
            if attack == "program-bytes" {
                BindingError::Subject
            } else {
                BindingError::Requirements
            }
        );
    }
}

#[test]
fn equal_logical_types_cannot_substitute_different_admitted_physical_carriers() {
    let logical = "field:bls12-381.fr";
    let d = shared(
        schema("field", "Fr", json!([logical])),
        json!({"kind":"value"}),
    );
    let (package, _) = package(
        &d,
        &[
            vec!["field:bls12-381.fr@blst/fr".into()],
            vec!["field:bls12-381.fr@arkworks.fr/0".into()],
        ],
    );
    let error = RunEntry::admit(package, Default::default(), Default::default())
        .err()
        .unwrap();
    assert_eq!(error.phase, entry::EntryPhase::Binding);
    assert_eq!(error.code(), "entry-interface-native-binding");
}
