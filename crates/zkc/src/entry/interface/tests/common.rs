//! Adversarial inventories authored from source coordinates, without the adapter.
use super::*;

fn component(input: u32, role: &str, path: Value) -> Value {
    json!({"input":input,"role":role,"path":path})
}
fn obligation(input: u32, path: Value, observation: Value) -> Value {
    json!({"components":[component(input,"P",path.clone()),component(input,"V",path)],"observation":observation})
}
fn run_document(inputs: Value, inventory: Value) -> Value {
    let mut d = document();
    d["job"] = json!({"kind":"run"});
    d["relations"] = json!([]);
    d["protocols"][0]["inputs"] = inputs;
    d["protocols"][0]["outputs"] = json!([]);
    d["protocols"][0]["clauses"] = json!([]);
    d["protocols"][0]["common_input_requirements"] = inventory;
    d
}
fn shared(schema: Value, observation: Value) -> Value {
    run_document(
        json!([port("subject", 0, json!([0]), json!([0, 1]), schema)]),
        json!([obligation(0, json!([]), observation)]),
    )
}
fn field(name: &str, offset: u32, s: Value) -> Value {
    json!({"name":name,"offset":offset,"public":true,"placement":null,"schema":s})
}
fn variant(name: &str, fields: Vec<Value>) -> Value {
    let leaves: Vec<_> = fields
        .iter()
        .flat_map(|f| f["schema"]["leaves"].as_array().unwrap())
        .map(|v| {
            let text = v.as_str().unwrap();
            if text.starts_with("variant:") {
                zkc_test_support::variants::tree(text)
            } else {
                v.clone()
            }
        })
        .collect();
    let spelling = zkc_test_support::variants::encode_tree(json!([
        [
            "zkc.language",
            crate::source_names::encode_nominal_identity(name)
        ],
        [["case00000000", []], ["case00000001", leaves]]
    ]));
    let mut s = schema("variant", name, json!([spelling]));
    s["alternatives"] = json!([{"name":"Empty","fields":[]},{"name":"Payload","fields":fields}]);
    s
}

#[test]
fn common_inventory_is_required_closed_and_canonical_at_every_owner() {
    let d = shared(
        schema("boolean", "bool", json!(["bool"])),
        json!({"kind":"value"}),
    );
    read(&d).unwrap();
    let pointer = "/protocols/0/common_input_requirements";
    for invalid in [
        json!(null),
        json!({}),
        json!([{}]),
        json!([{"components":[],"observation":{"kind":"value"}}]),
    ] {
        let mut bad = d.clone();
        *bad.pointer_mut(pointer).unwrap() = invalid;
        assert!(read(&bad).is_err());
    }
    let mut missing = d.clone();
    missing["protocols"][0]
        .as_object_mut()
        .unwrap()
        .remove("common_input_requirements");
    assert_eq!(read(&missing).unwrap_err(), InterfaceError::Format);
    for observation in [
        json!("value"),
        json!({"kind":"tag","axis":0}),
        json!({"kind":"value","axis":0}),
        json!({"kind":"extent"}),
        json!({"kind":"extent","axis":-1}),
        json!({"kind":"extent","axis":0.0}),
        json!({"kind":"extent","axis":4294967296u64}),
        json!({"kind":"other"}),
    ] {
        let mut bad = d.clone();
        bad["protocols"][0]["common_input_requirements"][0]["observation"] = observation;
        assert_eq!(read(&bad).unwrap_err(), InterfaceError::Format);
    }
    for path in [
        json!([{"kind":"field","index":0,"native":0}]),
        json!([{"kind":"alternative","index":0}]),
        json!([{"kind":"payload","index":0}]),
        json!([{"kind":"field","index":true}]),
        json!([["field", 0]]),
    ] {
        let mut bad = d.clone();
        bad["protocols"][0]["common_input_requirements"][0]["components"][0]["path"] = path;
        assert!(read(&bad).is_err());
    }
    for attack in [
        "duplicate",
        "reorder",
        "wrong-role",
        "wrong-input",
        "native",
        "single-role",
    ] {
        let mut bad = d.clone();
        let r = &mut bad["protocols"][0]["common_input_requirements"][0];
        match attack {
            "duplicate" => {
                let c = r["components"][0].clone();
                r["components"].as_array_mut().unwrap().insert(0, c);
            }
            "reorder" => r["components"].as_array_mut().unwrap().reverse(),
            "wrong-role" => r["components"][0]["role"] = json!("absent"),
            "wrong-input" => r["components"][0]["input"] = json!(2),
            "native" => r["components"][0]["native"] = json!(0),
            _ => r["components"][1]["role"] = json!("P"),
        }
        assert!(read(&bad).is_err(), "{attack}");
    }
    let mut helper = d["protocols"][0].clone();
    helper["symbol"] = json!("helper");
    helper["common_input_requirements"][0]["components"][0]["input"] = json!(9);
    let mut bad = d.clone();
    bad["protocols"].as_array_mut().unwrap().push(helper);
    assert_eq!(read(&bad).unwrap_err(), InterfaceError::Selection);
    let text = d.to_string();
    for token in ["-0", "0.0", "1e0", "4294967296"] {
        let bad = text.replacen("\"input\":0", &format!("\"input\":{token}"), 1);
        assert_ne!(text, bad);
        assert_eq!(read_text(&bad).unwrap_err(), InterfaceError::Format);
    }
    for (key, value) in [("kind", "\"value\""), ("input", "0"), ("role", "\"P\"")] {
        let needle = format!("\"{key}\":{value}");
        let duplicate = format!(
            "{needle},\"\\u{:04x}{}\":{value}",
            key.as_bytes()[0],
            &key[1..]
        );
        let bad = text.replacen(&needle, &duplicate, 1);
        assert_ne!(text, bad);
        assert_eq!(read_text(&bad).unwrap_err(), InterfaceError::Format);
    }
}

#[test]
fn classes_are_maximal_per_exact_type_observation_and_conditional_subject() {
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let inputs = json!([
        port("first", 0, json!([0]), json!([0, 1]), boolean.clone()),
        port("second", 1, json!([1]), json!([0, 1]), boolean)
    ]);
    let first = obligation(0, json!([]), json!({"kind":"value"}));
    let second = obligation(1, json!([]), json!({"kind":"value"}));
    let d = run_document(inputs, json!([first.clone(), second.clone()]));
    read(&d).unwrap();
    for classes in [
        json!([second, first.clone()]),
        json!([first.clone(), first.clone()]),
        json!([first.clone(),{"components":[component(0,"V",json!([])),component(1,"P",json!([]))],"observation":{"kind":"value"}}]),
    ] {
        let mut bad = d.clone();
        bad["protocols"][0]["common_input_requirements"] = classes;
        assert_eq!(read(&bad).unwrap_err(), InterfaceError::Selection);
    }
    let mut unavailable = d.clone();
    unavailable["protocols"][0]["inputs"][0]["placement"]["roles"] = json!([0]);
    refresh_components(&mut unavailable["protocols"][0]["inputs"][0]);
    assert_eq!(read(&unavailable).unwrap_err(), InterfaceError::Selection);
    // A normalized connected class may contain two inputs at one role.
    let mut connected = d.clone();
    connected["protocols"][0]["common_input_requirements"] = json!([{"components":[component(0,"P",json!([])),component(0,"V",json!([])),component(1,"P",json!([])),component(1,"V",json!([]))],"observation":{"kind":"value"}}]);
    read(&connected).unwrap();
    let s = variant(
        "example::Choice",
        vec![field("flag", 0, schema("boolean", "bool", json!(["bool"])))],
    );
    let mut d = shared(s, json!({"kind":"value"}));
    d["protocols"][0]["common_input_requirements"]
        .as_array_mut()
        .unwrap()
        .push(obligation(0, json!([]), json!({"kind":"tag"})));
    read(&d).unwrap();
    d["protocols"][0]["common_input_requirements"]
        .as_array_mut()
        .unwrap()
        .reverse();
    assert_eq!(read(&d).unwrap_err(), InterfaceError::Selection);
}

#[test]
fn source_observations_keep_collection_axes_and_single_leaf_rules() {
    for (kind, spelling, axes) in [
        ("boolean", "bool", 0),
        ("builtin", "bytes", 1),
        ("builtin", "matrix:bls12-381.fr", 2),
        ("builtin", "field_array<bls12-381.fr,0>", 1),
    ] {
        for axis in 0..=2 {
            let d = shared(
                schema(kind, spelling, json!([spelling])),
                json!({"kind":"extent","axis":axis}),
            );
            assert_eq!(read(&d).is_ok(), axis < axes, "{spelling}/{axis}");
        }
    }
    let mut aggregate = schema("tuple", "(bool)", json!(["bool"]));
    aggregate["fields"] = json!([field("0", 0, schema("boolean", "bool", json!(["bool"])))]);
    let d = shared(aggregate, json!({"kind":"value"}));
    assert_eq!(read(&d).unwrap_err(), InterfaceError::Selection);
    let mut d = d;
    for c in d["protocols"][0]["common_input_requirements"][0]["components"]
        .as_array_mut()
        .unwrap()
    {
        c["path"] = json!([{"kind":"field","index":0}]);
    }
    read(&d).unwrap();
    d["protocols"][0]["inputs"][0]["schema"]["fields"][0]["offset"] = json!(1);
    assert_eq!(read(&d).unwrap_err(), InterfaceError::Schema);
    let d = shared(schema("unit", "()", json!([])), json!({"kind":"value"}));
    assert!(read(&d).is_err());
}

#[test]
fn nested_conditional_payload_offsets_are_not_source_payload_ordinals() {
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
    let path = json!([{"kind":"alternative","index":1},{"kind":"payload","index":1},{"kind":"alternative","index":1},{"kind":"payload","index":1}]);
    let mut d = shared(outer, json!({"kind":"value"}));
    for c in d["protocols"][0]["common_input_requirements"][0]["components"]
        .as_array_mut()
        .unwrap()
    {
        c["path"] = path.clone();
    }
    let view = read(&d).unwrap();
    assert_eq!(view.common[0].components[0].path, [(1, 2), (1, 2)]);
    for path in [
        json!([{"kind":"alternative","index":1},{"kind":"field","index":1}]),
        json!([{"kind":"alternative","index":1},{"kind":"payload","index":2}]),
        json!([{"kind":"alternative","index":1},{"kind":"payload","index":0}]),
    ] {
        let mut bad = d.clone();
        bad["protocols"][0]["common_input_requirements"][0]["components"][0]["path"] = path;
        assert!(read(&bad).is_err());
    }
}

#[test]
fn inventory_budgets_include_wide_and_zero_storage_inputs() {
    let empty = schema("unit", "()", json!([]));
    let inputs: Vec<_> = (0..512)
        .map(|i| {
            port(
                &format!("empty{i}"),
                i,
                json!([]),
                json!([0, 1]),
                empty.clone(),
            )
        })
        .collect();
    let d = run_document(json!(inputs), json!([]));
    read(&d).unwrap();
    let mut bad = d.clone();
    bad["protocols"][0]["common_input_requirements"] =
        json!([obligation(511, json!([]), json!({"kind":"value"}))]);
    assert!(read(&bad).is_err());
    let d = shared(
        schema("boolean", "bool", json!(["bool"])),
        json!({"kind":"value"}),
    );
    let mut excessive = d.clone();
    excessive["protocols"][0]["common_input_requirements"] = json!(vec![
            d["protocols"][0]["common_input_requirements"][0]
                .clone();
            1025
        ]);
    assert_eq!(read(&excessive).unwrap_err(), InterfaceError::Limit);
    let mut deep = d;
    deep["protocols"][0]["common_input_requirements"][0]["components"][0]["path"] =
        json!(vec![json!({"kind":"field","index":0}); 33]);
    assert_eq!(read(&deep).unwrap_err(), InterfaceError::Limit);
}

#[cfg(feature = "cpu")]
mod cpu;

#[test]
fn ordinary_observations_cross_custody_prefixes_without_selecting_custody() {
    let mut state = schema("logical_record", "example::Guard", json!([]));
    state["constructible"] = json!(false);
    state["custody"] = json!(2);
    state["permissions"] = json!(["Drop"]);
    state["roles"] = json!(["A", "B"]);
    let placed = data_placement(json!([0, 1]));
    let mut flag = field("flag", 2, schema("boolean", "bool", json!(["bool"])));
    flag["placement"] = placed.clone();
    state["fields"] = json!([flag]);
    let p = placed_port(
        "guard",
        0,
        json!([0, 1, 2]),
        json!({"kind":"product","instance":state["identity"],"arguments":[0,1],"fields":[placed]}),
        state,
    );
    let d = run_document(
        json!([p]),
        json!([obligation(
            0,
            json!([{"kind":"field","index":0}]),
            json!({"kind":"value"})
        )]),
    );
    let view = read(&d).unwrap();
    let requirements =
        super::super::common::check(&view.document.protocols[0], &mut schemas::Schemas::new())
            .unwrap();
    assert_eq!(requirements.len(), 1);
    assert!(requirements[0].components.iter().all(|c| c.original == 2));
    for path in [json!([]), json!([{"kind":"field","index":1}])] {
        let mut bad = d.clone();
        for c in bad["protocols"][0]["common_input_requirements"][0]["components"]
            .as_array_mut()
            .unwrap()
        {
            c["path"] = path.clone();
        }
        assert_eq!(read(&bad).unwrap_err(), InterfaceError::Selection);
    }
    let mut wrong_component = d;
    wrong_component["protocols"][0]["inputs"][0]["components"][2]["native"] = json!(0);
    assert!(read(&wrong_component).is_err());
}

#[test]
fn compiler_emitted_custody_inventory_selects_the_ordinary_data_facet() {
    let bytes = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../compiler/test/fixtures/common-inputs/custody-fields.json"
    ));
    for fixture in toolchain_parameters(bytes) {
        let view = Interface::decode(&fixture, None, InterfaceLimits::DEFAULT).unwrap();
        let protocol = &view.document.protocols[0];
        let requirements =
            super::super::common::check(protocol, &mut schemas::Schemas::new()).unwrap();
        assert_eq!(requirements.len(), 1);
        let requirement = &requirements[0];
        assert_eq!(requirement.spelling, "bool");
        assert!(matches!(
            requirement.observation,
            raw::CommonObservation::Value {}
        ));
        assert_eq!(requirement.components.len(), 2);
        for (role, component) in requirement.components.iter().enumerate() {
            assert_eq!(component.role as usize, role);
            assert_eq!(component.original, 2);
            assert!(component.path.is_empty());
        }
    }
    // The identity parameter relaxes nothing else: moving the ordinary field
    // onto a custody coordinate is still refused.
    let moved = replace_once(
        bytes,
        r#"{"path":[0],"leaf":0,"role":0,"facet":"data","native":2}"#,
        r#"{"path":[0],"leaf":0,"role":0,"facet":"data","native":0}"#,
    );
    assert!(Interface::decode(&moved, None, InterfaceLimits::DEFAULT).is_err());
}
