//! Component supply controls independently authored against the current schema.
use super::*;
fn state(verifier: u32, prover: u32) -> Value {
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let mut state = schema("logical_record", "State", json!([]));
    state["constructible"] = json!(false);
    state["roles"] = json!(["A", "B"]);
    state["fields"] = json!([
        {"name":"statement","offset":0,"public":true,"placement":{"kind":"data","roles":[0,1]},"schema":boolean},
        {"name":"witness","offset":1,"public":true,"placement":{"kind":"data","roles":[prover]},"schema":boolean},
        {"name":"empty","offset":2,"public":true,"placement":{"kind":"data","roles":[verifier]},"schema":schema("unit","()",json!([]))}
    ]);
    let placement = json!({"kind":"product","instance":state["identity"],"arguments":[0,1],"fields":state["fields"].as_array().unwrap().iter().map(|f| f["placement"].clone()).collect::<Vec<_>>()});
    placed_port("state", 0, json!([0, 1]), placement, state)
}
pub(super) fn document_components() -> Value {
    let mut d = document();
    d["protocols"][0]["inputs"] = json!([state(1, 0)]);
    for (i, operand) in d["protocols"][0]["clauses"][0]["subject"]["operands"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .enumerate()
    {
        operand["port"] = json!(0);
        operand["path"] = json!([i]);
    }
    d["job"]["public"] = json!([
        {"port":0,"path":[0],"role":"V"}, {"port":0,"path":[2],"role":"V"}
    ]);
    d
}
#[test]
fn complete_public_witness_and_empty_supply_has_exact_coordinates() {
    let d = document_components();
    let view = read(&d).unwrap();
    view.check_executable_ports().unwrap();
    let groups = view.input_groups();
    assert_eq!(
        groups[0].template(),
        json!({"state_statement":null,"state_empty":null})
    );
    assert_eq!(groups[1].template(), json!({"state_witness":null}));
    let described = groups[0].describe();
    assert_eq!(
        described["ports"][1]["selection"],
        json!({"port":0,"path":[2],"role":"V"})
    );
    assert!(
        view.ordinary_input(0, &[2], "V")
            .unwrap()
            .native()
            .is_empty()
    );
    assert!(view.ordinary_input(0, &[2], "P").is_err());
    assert!(view.ordinary_input(0, &[], "V").is_err());
    for selections in [
        json!([{ "port":0,"path":[0],"role":"V"}]),
        json!([{ "port":0,"path":[0],"role":"P"},{"port":0,"path":[2],"role":"V"}]),
        json!([{ "port":0,"path":[0],"role":"V"},{"port":0,"path":[0],"role":"V"},{"port":0,"path":[2],"role":"V"}]),
        json!([{ "port":0,"path":[],"role":"V"}]),
        json!([0]),
    ] {
        let mut bad = d.clone();
        bad["job"]["public"] = selections;
        assert!(read(&bad).is_err());
    }
}
#[test]
fn sealing_is_required_and_empty_construction_is_not_vacuous() {
    let mut d = document_components();
    d["job"] = json!({"kind":"run"});
    for (field, reason) in [("sealed", "sealed"), ("private", "hidden")] {
        let mut bad = d.clone();
        if field == "sealed" {
            bad["protocols"][0]["inputs"][0]["schema"]["sealed"] = json!(true);
        } else {
            bad["protocols"][0]["inputs"][0]["schema"]["fields"][2]["public"] = json!(false);
        }
        let view = read(&bad).unwrap();
        assert!(view.check_executable_ports().is_err());
        assert!(
            view.outstanding_requirements()
                .iter()
                .any(|r| r.reason == reason)
        );
        assert!(view.ordinary_input(0, &[2], "V").is_err());
    }
    let mut missing = d.clone();
    missing["protocols"][0]["inputs"][0]["schema"]
        .as_object_mut()
        .unwrap()
        .remove("sealed");
    assert_eq!(read(&missing).unwrap_err(), InterfaceError::Format);
    let mut nonnominal = d.clone();
    nonnominal["protocols"][0]["inputs"][0]["schema"]["fields"][2]["schema"]["sealed"] =
        json!(true);
    assert_eq!(read(&nonnominal).unwrap_err(), InterfaceError::Schema);
    let mut empty = state(1, 0);
    empty["schema"]["fields"] = json!([]);
    empty["placement"]["fields"] = json!([]);
    empty["native"] = json!([]);
    empty["components"] = json!([]);
    d["protocols"][0]["inputs"] = json!([empty]);
    d["protocols"][0]["clauses"] = json!([]);
    read(&d).unwrap().check_executable_ports().unwrap();
    d["protocols"][0]["inputs"][0]["schema"]["sealed"] = json!(true);
    assert!(read(&d).unwrap().check_executable_ports().is_err());
}
#[test]
fn ordinary_public_subtree_covers_empty_descendants_and_rejects_overlap() {
    let mut pair = schema("tuple", "(bool,unit)", json!(["bool"]));
    pair["fields"] = json!([
        {"name":"0","offset":0,"public":true,"placement":null,"schema":schema("boolean","bool",json!(["bool"]))},
        {"name":"1","offset":1,"public":true,"placement":null,"schema":schema("unit","()",json!([]))}
    ]);
    let mut d = document_components();
    d["protocols"][0]["inputs"][0]["schema"]["fields"][0]["schema"] = pair;
    refresh_components(&mut d["protocols"][0]["inputs"][0]);
    d["protocols"][0]["clauses"] = json!([]);
    d["job"]["target"] = Value::Null;
    read(&d).unwrap();
    d["job"]["public"]
        .as_array_mut()
        .unwrap()
        .insert(1, json!({"port":0,"path":[0,1],"role":"V"}));
    assert_eq!(read(&d).unwrap_err(), InterfaceError::Selection);
}

#[cfg(feature = "cpu")]
mod cpu {
    use super::*;
    use crate::entry::{NamedValues, ProofOperation, arguments};
    #[test]
    fn empty_values_are_mandatory_and_scatter_uses_original_native_order() {
        let view = read(&document_components()).unwrap();
        let groups = view.input_groups();
        let mut decoder = crate::entry::inputs::Decoder::new(Default::default()).unwrap();
        assert!(
            decoder
                .decode(&groups[0], br#"{"state_statement":true}"#, None)
                .is_err()
        );
        let public = decoder
            .decode(
                &groups[0],
                br#"{"state_statement":true,"state_empty":null}"#,
                None,
            )
            .unwrap();
        let public = arguments::values(&view, view.public_ports(), public, None).unwrap();
        let private = decoder
            .decode(&groups[1], br#"{"state_witness":false}"#, None)
            .unwrap();
        let ty = zkc_runtime::vm::PhysicalType::default_for(
            zkc_runtime::vm::LogicalType::parse("bool").unwrap(),
        )
        .unwrap();
        let p = arguments::proof_inputs(
            &view,
            &view.roles()[0],
            &public,
            &[ty],
            private,
            Default::default(),
            crate::execution::MaterialLimits::DEFAULT.public_bytes,
            &Default::default(),
        )
        .unwrap();
        assert_eq!(p.len(), 2);
        let crate::execution::InputValue::Wire(a) = &p[0] else {
            panic!()
        };
        assert_eq!(a.last(), Some(&1));
        let crate::execution::InputValue::Wire(b) = &p[1] else {
            panic!()
        };
        assert_eq!(b.last(), Some(&0));
        assert!(arguments::values(&view, view.public_ports(), NamedValues::new(), None).is_err());
        arguments::check_proof_ports(&view, ProofOperation::Verify).unwrap();
    }
    #[test]
    fn ordinary_distributed_proof_assembles_against_independent_native_deployment() {
        let (mut d, artifact) = unicode::proof_fixture();
        d["protocols"][0]["inputs"] = json!([state(0, 1)]);
        d["job"]["public"] =
            json!([{"port":0,"path":[0],"role":"検証者"},{"port":0,"path":[2],"role":"検証者"}]);
        let bytes = json!({"format":"zkc.entry/0","original":"original","interface":d.to_string(),"artifact":artifact,"assets":[],"options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization":crate::entry::OracleSelection::default()}}).to_string();
        let package = crate::entry::Package::capture(
            bytes.as_bytes(),
            &Sha256::digest(bytes.as_bytes()).into(),
            crate::entry::Package::MAX_BYTES,
        )
        .unwrap();
        let host = crate::entry::ProofEntry::admit(
            package,
            crate::entry::ProofOptions {
                binding: crate::entry::BindingPolicy::AllowAuthored,
                ..Default::default()
            },
            Default::default(),
        )
        .unwrap();
        let call = host
            .preflight_memory_call(
                ProofOperation::Prove,
                Some(br#"{"state_statement":true,"state_empty":null}"#),
                Some(br#"{"state_witness":false}"#),
                &Default::default(),
                Default::default(),
                None,
                false,
            )
            .unwrap();
        let produced = call.execute(None).unwrap();
        assert!(produced.report.is_success());
        let proof = produced.report.native.outcome.as_ref().unwrap();
        let groups = host.interface().input_groups();
        let mut decoder = crate::entry::inputs::Decoder::new(Default::default()).unwrap();
        let public = decoder
            .decode(
                &groups[0],
                br#"{"state_statement":true,"state_empty":null}"#,
                None,
            )
            .unwrap();
        let checked = host
            .verify(
                crate::entry::ProofRequest {
                    public,
                    ..Default::default()
                },
                proof,
            )
            .unwrap();
        assert_eq!(checked.verification_result(), Some(true));
        let public = decoder
            .decode(
                &groups[0],
                br#"{"state_statement":false,"state_empty":null}"#,
                None,
            )
            .unwrap();
        assert!(
            !host
                .verify(
                    crate::entry::ProofRequest {
                        public,
                        ..Default::default()
                    },
                    proof
                )
                .unwrap()
                .is_success()
        );
    }
}

pub(super) fn nested_setup() -> Value {
    let mut d = setup_document();
    let previous = d["protocols"][0]["inputs"].as_array().unwrap();
    let mut root = schema("logical_record", "SetupState", json!([]));
    root["constructible"] = json!(false);
    root["roles"] = json!(["P", "V"]);
    let mut fields: Vec<_> = previous.iter().enumerate().map(|(i,p)| json!({"name":p["name"],"offset":i,"public":true,"placement":p["placement"],"schema":p["schema"]})).collect();
    fields[2]["placement"] = data_placement(json!([0, 1]));
    fields.push(json!({"name":"nonce","offset":3,"public":true,"placement":{"kind":"data","roles":[0]},"schema":schema("index","index",json!(["index"]))}));
    fields.push(json!({"name":"unit","offset":4,"public":true,"placement":{"kind":"data","roles":[1]},"schema":schema("unit","()",json!([]))}));
    let placement = json!({"kind":"product","instance":root["identity"],"arguments":[0,1],"fields":fields.iter().map(|f|f["placement"].clone()).collect::<Vec<_>>()});
    root["fields"] = json!(fields);
    d["protocols"][0]["inputs"] = json!([placed_port(
        "setup",
        0,
        json!([0, 1, 2, 3]),
        placement,
        root
    )]);
    d["job"]["public"] = json!([{"port":0,"path":[0],"role":"V"},{"port":0,"path":[2],"role":"V"},{"port":0,"path":[4],"role":"V"}]);
    d["setups"][0]["inputs"] = json!([{"port":0,"path":[]}]);
    d
}
#[test]
fn nested_setup_preserves_siblings_and_checks_exact_key_roles() {
    let d = nested_setup();
    let view = read(&d).unwrap();
    view.check_executable_ports().unwrap();
    assert_eq!(view.setups[0].inputs, [0, 1, 2].into());
    assert_eq!(view.setups[0].verifier_keys, [0].into());
    assert_eq!(
        view.input_groups()[0].template(),
        json!({"setup_statement":null,"setup_unit":null})
    );
    assert_eq!(
        view.input_groups()[1].template(),
        json!({"setup_pk":{"file":null,"fingerprint":null},"setup_nonce":null})
    );
    let source: Vec<_> = view
        .input_ports(&view.roles()[0])
        .filter(|p| view.is_source_data(*p))
        .map(|p| p.name.clone())
        .collect();
    assert_eq!(source, ["setup_nonce"]);
    assert_eq!(view.native_input_position("P", 1).unwrap(), 0);
    assert_eq!(view.native_input_position("P", 2).unwrap(), 1);
    assert_eq!(view.native_input_position("P", 3).unwrap(), 2);
    assert_eq!(view.native_input_position("V", 0).unwrap(), 0);
    assert_eq!(view.native_input_position("V", 2).unwrap(), 1);
    assert!(view.native_input_position("V", 1).is_err());
    let mut wrong = d.clone();
    wrong["protocols"][0]["inputs"][0]["schema"]["fields"][1]["placement"] =
        data_placement(json!([1]));
    wrong["protocols"][0]["inputs"][0]["placement"]["fields"][1] = data_placement(json!([1]));
    refresh_components(&mut wrong["protocols"][0]["inputs"][0]);
    wrong["job"]["public"]
        .as_array_mut()
        .unwrap()
        .insert(1, json!({"port":0,"path":[1],"role":"V"}));
    assert_eq!(read(&wrong).unwrap_err(), InterfaceError::Selection);
    let mut duplicate = d.clone();
    duplicate["setups"][0]["inputs"]
        .as_array_mut()
        .unwrap()
        .push(json!({"port":0,"path":[0]}));
    assert_eq!(read(&duplicate).unwrap_err(), InterfaceError::Selection);
}
#[cfg(feature = "cpu")]
#[test]
fn nested_setup_native_positions_and_duplicate_vk_supply_are_exact() {
    use crate::entry::{NamedValues, Value as Input, arguments};
    let view = read(&nested_setup()).unwrap();
    let authority = crate::entry::SetupAuthority {
        keys: [("pcs".into(), [7; 32])].into(),
    };
    let run = crate::entry::setups::run_authority(&view, authority).unwrap();
    assert_eq!(
        run.inputs.keys().cloned().collect::<Vec<_>>(),
        vec![
            ("role00000000".into(), 0),
            ("role00000000".into(), 1),
            ("role00000001".into(), 0),
            ("role00000001".into(), 1)
        ]
    );
    let keys = [(0, b"pinned-key".as_slice())].into();
    let supplied = || -> NamedValues {
        [
            ("setup_statement".into(), zkc_cpu::Value::Bool(true).into()),
            ("setup_unit".into(), Input::Unit),
        ]
        .into()
    };
    assert_eq!(
        arguments::values(&view, view.public_ports(), supplied(), Some(&keys))
            .unwrap()
            .len(),
        2
    );
    let mut duplicate = supplied();
    duplicate.insert("setup_vk".into(), zkc_cpu::Value::Bool(false).into());
    assert_eq!(
        arguments::values(&view, view.public_ports(), duplicate, Some(&keys)).unwrap_err(),
        "entry-input-names"
    );
    let mut missing = supplied();
    missing.remove("setup_statement");
    assert!(arguments::values(&view, view.public_ports(), missing, Some(&keys)).is_err());
}
#[test]
fn aliases_are_bounded_deterministic_and_do_not_change_coordinates() {
    let d = document_components();
    let view = read(&d).unwrap();
    let p = &view.selected_protocol().inputs[0];
    let mut whole = schema("boolean", "bool", json!(["bool"]));
    whole["identity"] = p.schema.fields[0].schema.identity.clone().into();
    let mut other = port("state_statement", 1, json!([2]), json!([0]), whole);
    let other: raw::Port = serde_json::from_value(other.take()).unwrap();
    let coords = [(p, [0].as_slice()), (&other, [].as_slice())];
    assert_eq!(
        super::super::boundary::family_aliases(&coords),
        ["state_statement_2", "state_statement"]
    );
    let mut long = p.schema.clone();
    long.fields[0].name = "x".repeat(128);
    let mut long_port: raw::Port =
        serde_json::from_value(d["protocols"][0]["inputs"][0].clone()).unwrap();
    long_port.schema = long;
    let names = super::super::boundary::family_aliases(&[(&long_port, &[0]), (&long_port, &[1])]);
    assert!(names[0].len() <= 113);
    assert_eq!(names[1], "state_witness");
    assert_eq!(
        names,
        super::super::boundary::family_aliases(&[(&long_port, &[0]), (&long_port, &[1])])
    );
    assert_eq!(view.ordinary_input(0, &[0], "V").unwrap().path(), [0]);
}

#[cfg(feature = "cpu")]
#[test]
fn complete_distributed_run_returns_only_ordinary_views() {
    use crate::entry::{self, RoleInputs, RunEntry, RunRequest};
    let mut d = document_components();
    d["job"] = json!({"kind":"run"});
    d["protocols"][0]["clauses"] = json!([]);
    d["relations"] = json!([]);
    d["protocol"] = json!("main");
    d["protocols"][0]["symbol"] = json!("main");
    d["protocols"][0]["outputs"] = d["protocols"][0]["inputs"].clone();
    let ty = zkc_runtime::vm::PhysicalType::default_for(
        zkc_runtime::vm::LogicalType::parse("bool").unwrap(),
    )
    .unwrap()
    .spelling();
    let program = json!([
        "zkc.program/0",
        [],
        [],
        [
            [
                "participant",
                "p",
                "root",
                "role00000000",
                [["s", ty], ["w", ty]],
                [ty, ty],
                [["return", ["s", "w"]]],
                []
            ],
            [
                "participant",
                "v",
                "root",
                "role00000001",
                [["s", ty]],
                [ty],
                [["return", ["s"]]],
                []
            ]
        ],
        [[
            "entry",
            "main",
            [["role00000000", "p"], ["role00000001", "v"]]
        ]]
    ])
    .to_string();
    let artifact = json!({"format":"zkc.run/0","candidate":program,"entry":"main","roles":["role00000000","role00000001"],"steps":[{"role":0,"instruction":0,"anchor":null},{"role":1,"instruction":0,"anchor":null}]}).to_string();
    let bytes = json!({"format":"zkc.entry/0","original":"original","interface":d.to_string(),"artifact":artifact,"assets":[],"options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization":entry::OracleSelection::default()}}).to_string();
    let package = Package::capture(
        bytes.as_bytes(),
        &Sha256::digest(bytes.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap();
    let host = RunEntry::admit(package, Default::default(), Default::default()).unwrap();
    let groups = host.interface().input_groups();
    let mut decoder = entry::inputs::Decoder::new(Default::default()).unwrap();
    let p = decoder
        .decode(
            &groups[0],
            br#"{"state_statement":true,"state_witness":false}"#,
            None,
        )
        .unwrap();
    let v = decoder
        .decode(
            &groups[1],
            br#"{"state_statement":false,"state_empty":null}"#,
            None,
        )
        .unwrap();
    // Role-local shared supply remains distinct; it establishes no common fact.
    let report = host
        .prepare(RunRequest {
            session: "components".into(),
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
            setups: Default::default(),
        })
        .unwrap()
        .execute();
    assert!(report.is_success(), "{:?}", report.output_error);
    let outputs = report.outputs.unwrap();
    assert_eq!(
        outputs["P"].keys().map(String::as_str).collect::<Vec<_>>(),
        ["state_statement", "state_witness"]
    );
    assert!(matches!(outputs["V"]["state_empty"], entry::Value::Unit));
    assert!(matches!(
        outputs["V"]["state_statement"],
        entry::Value::Leaf(_)
    ));
}

#[test]
fn zero_arrays_validate_templates_without_inventing_origins() {
    let element = schema("index", "index", json!(["index"]));
    let mut array = schema("array", "[index;0]", json!([]));
    array["element"] = element;
    let mut d = document_components();
    d["job"] = json!({"kind":"run"});
    d["relations"] = json!([]);
    d["protocols"][0]["clauses"] = json!([]);
    d["protocols"][0]["inputs"] = json!([port("empty", 0, json!([]), json!([0]), array.clone())]);
    let view = read(&d).unwrap();
    view.check_executable_ports().unwrap();
    assert_eq!(view.input_groups()[0].template(), json!({"empty":[]}));
    assert!(view.protocol_inputs().next().unwrap().components.is_empty());
    assert_eq!(view.ordinary_inputs("P").unwrap()[0].path(), &[] as &[u32]);
    array["element"]["constructible"] = json!(false);
    d["protocols"][0]["inputs"][0]["schema"] = array;
    let view = read(&d).unwrap();
    // Typed transport retains the template; external construction still checks
    // its private constructor even though the array has no physical elements.
    view.check_executable_ports().unwrap();
    assert!(view.ordinary_input(0, &[], "P").is_err());
    assert_eq!(
        schemas::check_import(view.protocol_inputs().next().unwrap().schema).unwrap_err(),
        "entry-input-constructor"
    );
    #[cfg(feature = "cpu")]
    {
        assert_eq!(
            crate::entry::arguments::check_ports(&view).unwrap_err(),
            "entry-input-constructor"
        );
        crate::entry::arguments::check_host_ports(&view, None).unwrap();
    }
}
#[test]
fn repeated_schema_identity_checks_sealing_and_private_empty_metadata() {
    let mut d = document_components();
    d["job"] = json!({"kind":"run"});
    d["relations"] = json!([]);
    d["protocols"][0]["clauses"] = json!([]);
    d["protocols"][0]["outputs"] = d["protocols"][0]["inputs"].clone();
    read(&d).unwrap();
    for (path, value) in [
        ("/sealed", json!(true)),
        ("/fields/2/public", json!(false)),
        ("/constructible", json!(true)),
        ("/generated", json!(digest("changed"))),
    ] {
        let mut bad = d.clone();
        *bad["protocols"][0]["outputs"][0]["schema"]
            .pointer_mut(path)
            .unwrap() = value;
        assert!(read(&bad).is_err(), "{path}");
    }
}

#[test]
fn ordinary_holder_data_never_discharges_handle_or_anchor_origins() {
    let mut d = document_components();
    let root = &mut d["protocols"][0]["inputs"][0];
    root["schema"]["fields"][1]["name"] = json!("word");
    root["schema"]["fields"][1]["schema"] = logical::handle("bool", Some("0"), None);
    root["schema"]["fields"][1]["placement"] = json!({"kind":"oracle","holder":0,"receivers":[1]});
    root["placement"]["fields"][1] = root["schema"]["fields"][1]["placement"].clone();
    root["native"] = json!([0, 1, 2]);
    refresh_components(root);
    d["protocols"][0]["clauses"] = json!([]);
    d["job"]["target"] = Value::Null;
    let view = read(&d).unwrap();
    assert!(view.ordinary_input(0, &[0], "P").is_ok());
    assert!(view.ordinary_input(0, &[1], "P").is_err());
    assert!(view.check_executable_ports().is_err());
    let reqs = view.outstanding_requirements();
    assert!(
        reqs.iter()
            .any(|r| r.path == [1] && r.role == "P" && r.facet == Some(raw::Facet::OracleData))
    );
    assert!(
        reqs.iter()
            .any(|r| r.path == [1] && r.role == "V" && r.facet == Some(raw::Facet::OracleAnchor))
    );
    assert!(
        !view
            .input_groups()
            .iter()
            .any(|g| g.template().get("state_word").is_some())
    );
}
#[cfg(feature = "cpu")]
#[test]
fn argument_iteration_order_does_not_reorder_the_native_abi() {
    let mut d = document_components();
    d["job"] = json!({"kind":"run"});
    let view = read(&d).unwrap();
    let ports: Vec<_> = view.input_ports(&view.roles()[0]).collect();
    let supplied = [
        ("state_statement".into(), zkc_cpu::Value::Bool(true).into()),
        ("state_witness".into(), zkc_cpu::Value::Bool(false).into()),
    ]
    .into();
    let values =
        crate::entry::arguments::values(&view, ports.into_iter().rev(), supplied, None).unwrap();
    assert!(
        matches!(&values[0], crate::execution::InputValue::Native(v) if matches!(v.as_ref(), zkc_cpu::Value::Bool(true)))
    );
    assert!(
        matches!(&values[1], crate::execution::InputValue::Native(v) if matches!(v.as_ref(), zkc_cpu::Value::Bool(false)))
    );
}

#[test]
fn ordinary_subtree_uses_intersection_of_actual_component_authority() {
    let mut tuple = schema("tuple", "(bool,bool)", json!(["bool", "bool"]));
    tuple["fields"] = json!([
        {"name":"0","offset":0,"public":true,"placement":null,"schema":schema("boolean","bool",json!(["bool"]))},
        {"name":"1","offset":1,"public":true,"placement":null,"schema":schema("boolean","bool",json!(["bool"]))}
    ]);
    let p = json!({"kind":"product","instance":tuple["identity"],"arguments":[0,1],"fields":[{"kind":"data","roles":[0,1]},{"kind":"data","roles":[1]}]});
    let mut d = document();
    d["protocols"][0]["inputs"] = json!([placed_port("pair", 0, json!([0, 1]), p, tuple)]);
    d["protocols"][0]["clauses"] = json!([]);
    d["job"]["target"] = Value::Null;
    let view = read(&d).unwrap();
    assert_eq!(view.ordinary_input(0, &[], "V").unwrap().native(), [0, 1]);
    assert!(view.ordinary_input(0, &[], "P").is_err());
    assert_eq!(
        view.input_groups()[0].template(),
        json!({"pair":[null,null]})
    );
    assert_eq!(view.native_input_position("P", 0).unwrap(), 0);
    assert!(view.native_input_position("P", 1).is_err());
}

#[test]
fn semantic_supply_descriptors_are_bounded_even_without_native_storage() {
    let unit = schema("unit", "()", json!([]));
    let mut tuple = schema("tuple", "EmptyTuple", json!([]));
    tuple["fields"] = json!((0..3000).map(|i|json!({"name":i.to_string(),"offset":0,"public":true,"placement":null,"schema":unit})).collect::<Vec<_>>());
    let mut d = document_components();
    d["job"] = json!({"kind":"run"});
    d["relations"] = json!([]);
    d["protocols"][0]["roles"] = json!((0..16).map(|i| format!("R{i}")).collect::<Vec<_>>());
    d["protocols"][0]["inputs"] = json!([port(
        "empty",
        0,
        json!([]),
        json!((0..16).collect::<Vec<_>>()),
        tuple
    )]);
    d["protocols"][0]["outputs"] = json!([]);
    d["protocols"][0]["clauses"] = json!([]);
    assert_eq!(read(&d).unwrap_err(), InterfaceError::DescriptorLimit);
}
