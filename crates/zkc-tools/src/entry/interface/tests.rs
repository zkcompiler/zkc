use super::*;
use serde_json::{Value, json};
fn digest(s: &str) -> String {
    format!("{:x}", Sha256::digest(s.as_bytes()))
}
fn schema(kind: &str, ty: &str, leaves: Value) -> Value {
    json!({"kind":kind,"identity":digest(ty),"type":ty,"custody":false,
        "permissions":["Copy","Drop","Share","Wire"],"fields":[],"alternatives":[],"leaves":leaves})
}
fn port(name: &str, index: u32, native: Value, roles: Value, schema: Value) -> Value {
    json!({"name":name,"index":index,"native":native,"roles":roles,"type":schema["type"],"schema":schema})
}
fn selector(direction: &str, port: u32, role: &str) -> Value {
    json!({"direction":direction,"port":port,"role":role,"path":[]})
}
fn document() -> Value {
    let boolean = schema("boolean", "bool", json!(["bool"]));
    json!({"format":"zkc.language-interface/0","setups":[],"capture":digest("capture"),"original":digest("original"),
        "toolchain":"test-toolchain","entry":"sample::Proof","protocol":"sample_Protocol",
        "protocols":[{"symbol":"sample_Protocol","roles":["P","V"],
            "inputs":[port("statement",0,json!([0]),json!(["P","V"]),boolean.clone()),
                port("witness",1,json!([1]),json!(["P"]),boolean.clone())],
            "outputs":[port("accepted",0,json!([0]),json!(["V"]),boolean.clone())],"services":[],
            "clauses":[{"name":"knowledge","kind":"target","subject":{"relation":"Predicate",
                "operands":[selector("input",0,"V"),selector("input",1,"P")]},
                "residual":null,"decision":selector("output",0,"V")}]}],
        "relations":[{"symbol":"Predicate","inputs":[
            {"name":"s","purpose":"statement","native":[0],"schema":boolean.clone()},
            {"name":"w","purpose":"witness","native":[1],"schema":boolean}],"definition":{"kind":"opaque"}}],
        "job":{"kind":"proof","prover":"P","verifier":"V","public":[0],
            "acceptance":selector("output",0,"V"),"completion":null,"target":"knowledge","construction":{"kind":"authored"}}})
}
fn read_text(interface: &str) -> Result<Interface> {
    let frame = json!({"format":"zkc.entry/0","original":"original","interface":interface,
        "artifact":"not interpreted by the metadata reader", "options":{"simplify":true,"release_storage":false},
        "assets":[]}).to_string();
    let package = Package::capture(
        frame.as_bytes(),
        &Sha256::digest(frame.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap();
    Interface::read(&package)
}
fn read(value: &Value) -> Result<Interface> {
    read_text(&value.to_string())
}
#[test]
fn escaped_duplicate_keys_refuse_in_nested_objects_and_tagged_records() {
    let original = document().to_string();
    for key in [
        "format", "kind", "public", "name", "custody", "native", "symbol",
    ] {
        let value = document();
        fn first<'a>(v: &'a Value, key: &str) -> Option<&'a Value> {
            match v {
                Value::Object(map) => map
                    .get(key)
                    .or_else(|| map.values().find_map(|v| first(v, key))),
                Value::Array(values) => values.iter().find_map(|v| first(v, key)),
                _ => None,
            }
        }
        let item = first(&value, key).unwrap();
        let field = format!("\"{key}\":{item}");
        let escaped = format!("\\u{:04x}{}", key.as_bytes()[0], &key[1..]);
        let changed = original.replacen(&field, &format!("{field},\"{escaped}\":{item}"), 1);
        assert_ne!(original, changed);
        assert_eq!(
            read_text(&changed).unwrap_err(),
            InterfaceError::Format,
            "{key}"
        );
    }
}
fn changed(path: &str, value: Value, error: InterfaceError) {
    let mut original = document();
    *original.pointer_mut(path).unwrap() = value;
    assert_eq!(read(&original).unwrap_err(), error, "{path}: {original}");
}
#[test]
fn complete_metadata_keeps_identity_job_and_leaf_types() {
    let value = read(&document()).unwrap();
    assert_eq!(value.entry(), "sample::Proof");
    assert_eq!(value.protocol(), "sample_Protocol");
    assert_eq!(value.capture(), digest("capture"));
    assert_eq!(value.original(), digest("original"));
    assert_eq!(value.toolchain(), "test-toolchain");
    assert!(value.is_proof());
    assert_eq!(value.logical_type("bool").unwrap().spelling(), "bool");
    assert!(value.logical_type("rng:bls12-381.fr").is_none());
    let mut run = document();
    run["job"] = json!({"kind":"run"});
    assert!(!read(&run).unwrap().is_proof());
}
#[test]
fn external_interface_bytes_require_canonical_unsigned_integer_indices() {
    let mut valid = document();
    // Numeric-looking string contents, booleans and null keep their own grammar.
    valid["toolchain"] = json!("quoted -0 +0 00 0.0 0e0 \"0\"");
    assert!(read_text(&valid.to_string()).is_ok());
    for path in [
        "/protocols/0/inputs/0/index",
        "/protocols/0/inputs/0/native/0",
        "/protocols/0/clauses/0/subject/operands/0/port",
        "/relations/0/inputs/0/native/0",
        "/job/public/0",
        "/job/acceptance/port",
    ] {
        let mut template = valid.clone();
        *template.pointer_mut(path).unwrap() = json!("NUMBER_TOKEN");
        let bytes = template.to_string();
        assert!(
            read_text(&bytes.replace("\"NUMBER_TOKEN\"", "0")).is_ok(),
            "{path}"
        );
        for token in [
            "-0",
            "-1",
            "+0",
            "+1",
            "00",
            "01",
            "0.0",
            "1.0",
            "0e0",
            "1e0",
            "0E+0",
            "4294967296",
        ] {
            assert_eq!(
                read_text(&bytes.replace("\"NUMBER_TOKEN\"", token)).map(|_| ()),
                Err(InterfaceError::Format),
                "{path}: {token}"
            );
        }
        assert_eq!(
            read_text(&bytes.replace("\"NUMBER_TOKEN\"", "10000000000")).unwrap_err(),
            InterfaceError::Limit,
            "scalar budget precedes schema decoding: {path}"
        );
    }
}
#[test]
fn exact_objects_reject_extra_duplicate_missing_fields_and_unknown_formats() {
    for path in [
        "",
        "/job",
        "/job/construction",
        "/protocols/0",
        "/protocols/0/inputs/0",
        "/relations/0/definition",
    ] {
        let mut value = document();
        value
            .pointer_mut(path)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert("extra".into(), json!(null));
        assert_eq!(read(&value).unwrap_err(), InterfaceError::Format, "{path}");
    }
    for path in [
        "/job/target",
        "/job/completion",
        "/protocols/0/clauses/0/residual",
        "/protocols/0/clauses/0/decision",
    ] {
        let mut value = document();
        let (parent, key) = path.rsplit_once('/').unwrap();
        value
            .pointer_mut(parent)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .remove(key);
        assert_eq!(
            read(&value).unwrap_err(),
            InterfaceError::Format,
            "missing {path}"
        );
    }
    let s = document().to_string();
    for bad in [
        s.replacen('{', "{\"entry\":\"sample::Proof\",", 1),
        s.replace(
            "\"kind\":\"authored\"",
            "\"kind\":\"authored\",\"kind\":\"authored\"",
        ),
        s.clone() + "{}",
        s.replace("zkc.language-interface/0", "invalid.language-interface"),
    ] {
        assert_eq!(read_text(&bad).unwrap_err(), InterfaceError::Format);
    }
    let mut value = document();
    value["job"] = json!({"kind":"run","extra":1});
    assert_eq!(read(&value).unwrap_err(), InterfaceError::Format);
}
#[test]
fn original_and_entry_identity_are_bound() {
    for (path, value) in [
        ("/original", json!(digest("other"))),
        ("/capture", json!("A".repeat(64))),
        ("/entry", json!("Proof")),
        ("/entry", json!("sample::bad-name")),
    ] {
        changed(path, value, InterfaceError::Identity);
    }
    changed("/protocol", json!("absent"), InterfaceError::Selection);
}
#[test]
fn ports_require_exact_logical_roles_order_and_native_slices() {
    for (path, value) in [
        ("/protocols/0/inputs/0/index", json!(1)),
        ("/protocols/0/inputs/0/native", json!([])),
        ("/protocols/0/inputs/0/native", json!([1])),
        ("/protocols/0/inputs/0/roles", json!(["V", "P"])),
        ("/protocols/0/inputs/0/roles", json!(["P", "P"])),
        ("/protocols/0/inputs/0/roles", json!([])),
        ("/protocols/0/inputs/0/roles", json!(["X"])),
        ("/protocols/0/inputs/1/name", json!("statement")),
        ("/protocols/0/roles", json!(["P", "P"])),
        ("/protocols/0/inputs/0/type", json!("index")),
        (
            "/protocols/0/inputs/0/schema/permissions",
            json!(["Copy", "Drop", "Wire"]),
        ),
    ] {
        changed(path, value, InterfaceError::Schema);
    }
}
#[test]
fn proof_and_clause_selections_are_complete() {
    for (path, value) in [
        ("/job/public", json!([])),
        ("/job/public", json!([0, 1])),
        ("/job/public", json!([0, 0])),
        ("/job/prover", json!("V")),
        ("/job/verifier", json!("X")),
        ("/job/acceptance/role", json!("P")),
        ("/job/acceptance/direction", json!("input")),
        ("/job/acceptance/path", json!([0])),
        ("/job/target", json!("absent")),
        ("/protocols/0/clauses/0/kind", json!("output")),
        ("/protocols/0/clauses/0/decision", json!(null)),
        ("/protocols/0/clauses/0/subject/relation", json!("absent")),
        ("/protocols/0/clauses/0/subject/operands/1/port", json!(0)),
        ("/protocols/0/clauses/0/subject/operands/1/role", json!("V")),
        (
            "/protocols/0/clauses/0/residual",
            json!({"relation":"Predicate","operands":[]}),
        ),
    ] {
        changed(path, value, InterfaceError::Selection);
    }
    let mut value = document();
    value["protocols"][0]["services"] =
        json!([{"name":"coins","owner":"V","contract":"random.bls12-381.fr/0","native":2}]);
    assert_eq!(read(&value).unwrap_err(), InterfaceError::Selection);
    value["job"]["construction"] =
        json!({"kind":"fiat_shamir","suite":"merlin3.bls12-381.fr64be/0","service":0});
    assert!(read(&value).is_ok());
    value["job"]["construction"]["suite"] = json!("merlin3.ristretto255.scalar64le/0");
    assert_eq!(read(&value).unwrap_err(), InterfaceError::Selection);
}
#[test]
fn conflicting_same_identity_and_unearned_permissions_are_refused() {
    for (path, value) in [
        (
            "/relations/0/inputs/0/schema/permissions",
            json!(["Copy", "Drop"]),
        ),
        ("/relations/0/inputs/0/schema/leaves", json!(["index"])),
        ("/relations/0/inputs/0/schema/custody", json!(true)),
        (
            "/relations/0/inputs/0/schema/permissions",
            json!(["Wire", "Copy", "Drop"]),
        ),
        (
            "/relations/0/inputs/0/schema/permissions",
            json!(["Copy", "Copy", "Drop"]),
        ),
        ("/relations/0/inputs/0/schema/identity", json!("x")),
    ] {
        changed(path, value, InterfaceError::Schema);
    }
    let mut value = document();
    value["job"] = json!({"kind":"run"});
    value["relations"] = json!([]);
    value["protocols"][0]["clauses"] = json!([]);
    value["protocols"][0]["inputs"] = json!([port(
        "polynomial",
        0,
        json!([0]),
        json!(["P"]),
        schema("builtin", "Polynomial", json!(["polynomial:bls12-381.fr"]))
    )]);
    assert_eq!(read(&value).unwrap_err(), InterfaceError::Schema);
    value["protocols"][0]["inputs"][0]["schema"]["permissions"] = json!(["Copy", "Drop", "Share"]);
    assert!(read(&value).is_ok());
}
fn run_with(input: Value) -> Value {
    let mut v = document();
    v["job"] = json!({"kind":"run"});
    v["relations"] = json!([]);
    v["protocols"][0]["clauses"] = json!([]);
    v["protocols"][0]["inputs"] = json!([input]);
    v
}
#[test]
fn products_empty_values_and_nominal_variants_preserve_structure() {
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let unit = schema("unit", "()", json!([]));
    let mut record = schema("record", "Record", json!(["bool"]));
    record["fields"] = json!([{"name":"empty","offset":0,"schema":unit}, {"name":"flag","offset":0,"schema":boolean}]);
    let value = run_with(port("record", 0, json!([0]), json!(["P"]), record));
    assert!(read(&value).is_ok());
    let mut bad = value.clone();
    bad["protocols"][0]["inputs"][0]["schema"]["fields"][1]["offset"] = json!(1);
    assert_eq!(read(&bad).unwrap_err(), InterfaceError::Schema);
    let mut bad = value;
    bad["protocols"][0]["inputs"][0]["schema"]["fields"][0]["name"] = json!("0");
    assert_eq!(read(&bad).unwrap_err(), InterfaceError::Schema);
    let key = "sample::Choice";
    let spelling = zkc_test_support::variants::encode_tree(json!([
        ["zkc.language", key],
        [["Empty", []], ["Flag", ["bool"]]]
    ]));
    let mut variant = schema("variant", key, json!([spelling]));
    variant["alternatives"] = json!([{"name":"Empty","fields":[]}, {"name":"Flag","fields":[{"name":"0","offset":0,"schema":boolean}]}]);
    let value = run_with(port("choice", 0, json!([0]), json!(["P"]), variant));
    assert!(read(&value).is_ok());
    for (path, replacement) in [
        ("identity", json!(digest("other"))),
        ("alternatives/0/name", json!("Flag")),
        ("alternatives/1/fields/0/offset", json!(1)),
    ] {
        let mut bad = value.clone();
        *bad.pointer_mut(&format!("/protocols/0/inputs/0/schema/{path}"))
            .unwrap() = replacement;
        assert_eq!(read(&bad).unwrap_err(), InterfaceError::Schema);
    }
}
#[test]
fn zero_leaf_verifier_inputs_remain_in_public_policy() {
    let mut value = document();
    value["protocols"][0]["inputs"]
        .as_array_mut()
        .unwrap()
        .push(port(
            "empty",
            2,
            json!([]),
            json!(["V"]),
            schema("unit", "()", json!([])),
        ));
    assert_eq!(read(&value).unwrap_err(), InterfaceError::Selection);
    value["job"]["public"] = json!([0, 2]);
    assert!(read(&value).is_ok());
}
#[test]
fn recursive_and_lexical_limits_precede_unbounded_allocation() {
    for depth in [32, 33] {
        let mut nested = schema("unit", "()", json!([]));
        for i in 1..depth {
            let mut outer = schema("tuple", &format!("Tuple{i}"), json!([]));
            outer["fields"] = json!([{"name":"0","offset":0,"schema":nested}]);
            nested = outer;
        }
        let result = read(&run_with(port(
            "nested",
            0,
            json!([]),
            json!(["P"]),
            nested,
        )));
        if depth == 32 {
            result.unwrap();
        } else {
            assert_eq!(result.unwrap_err(), InterfaceError::Limit);
        }
    }
    assert_eq!(
        preflight::check(format!("{}{}", "[".repeat(257), "]".repeat(257)).as_bytes()),
        Err(InterfaceError::Limit)
    );
    assert_eq!(preflight::check(b"12345678901"), Err(InterfaceError::Limit));
    assert_eq!(
        preflight::check(b"[-0,12345678901]"),
        Err(InterfaceError::Limit)
    );
    assert_eq!(
        preflight::check(format!("[-0,{}0{}]", "[".repeat(256), "]".repeat(256)).as_bytes()),
        Err(InterfaceError::Limit)
    );
    assert_eq!(preflight::check(b"{\"quoted\":\"[{}]\\\"\"}"), Ok(()));
    assert_eq!(
        preflight::check(&vec![b' '; 4 * 1024 * 1024 + 1]),
        Err(InterfaceError::Limit)
    );
    assert_eq!(
        preflight::check(format!("[{}]", vec!["0"; 200_000].join(",")).as_bytes()),
        Err(InterfaceError::Limit)
    );
    assert_eq!(
        preflight::check(format!("[{}]", vec!["0"; 199_999].join(",")).as_bytes()),
        Ok(())
    );
    for size in [6 * 256 * 1024, 6 * 256 * 1024 + 1] {
        let string = format!("\"{}\"", "a".repeat(size));
        assert_eq!(
            preflight::check(string.as_bytes()),
            if size == 6 * 256 * 1024 {
                Ok(())
            } else {
                Err(InterfaceError::Limit)
            }
        );
    }
    assert_eq!(preflight::check(b"]"), Err(InterfaceError::Format));
}

#[test]
fn carrier_records_and_enum_names_have_one_json_shape() {
    let mut value = document();
    value["job"]["acceptance"] = json!(["output", 0, "V", []]);
    assert_eq!(read(&value).unwrap_err(), InterfaceError::Format);
    let mut value = document();
    value["job"] = json!(["run"]);
    assert_eq!(read(&value).unwrap_err(), InterfaceError::Format);
    let mut value = document();
    value["job"]["construction"] = json!(["authored"]);
    assert_eq!(read(&value).unwrap_err(), InterfaceError::Format);
    let mut value = document();
    value["relations"][0]["definition"] = json!(["opaque"]);
    assert_eq!(read(&value).unwrap_err(), InterfaceError::Format);
    for (path, replacement) in [
        ("/job/acceptance/direction", json!({"output":null})),
        ("/relations/0/inputs/0/schema/kind", json!({"boolean":null})),
        (
            "/relations/0/inputs/0/schema/permissions/0",
            json!({"Copy":null}),
        ),
        ("/relations/0/inputs/0/purpose", json!({"statement":null})),
        ("/protocols/0/clauses/0/kind", json!({"target":null})),
    ] {
        changed(path, replacement, InterfaceError::Format);
    }
    let value = document();
    let array = json!([
        value["format"],
        value["capture"],
        value["original"],
        value["toolchain"],
        value["entry"],
        value["protocol"],
        value["protocols"],
        value["relations"],
        value["job"]
    ]);
    assert_eq!(read(&array).unwrap_err(), InterfaceError::Format);
}

#[test]
fn custody_optional_targets_and_continuations_have_positive_controls() {
    let id = digest("Guard");
    let mut guard = schema(
        "record",
        "Guard",
        json!([format!("resource_unit:zkl_resource_{id}")]),
    );
    guard["custody"] = json!(true);
    guard["permissions"] = json!(["Drop", "Share"]);
    read(&run_with(port("guard", 0, json!([0]), json!(["P"]), guard))).unwrap();
    let mut value = document();
    value["job"]["target"] = Value::Null;
    read(&value).unwrap();
    value["job"] = json!({"kind":"run"});
    value["protocols"][0]["clauses"][0]["kind"] = json!("continuation");
    value["protocols"][0]["clauses"][0]["decision"] = Value::Null;
    value["protocols"][0]["clauses"][0]["residual"] = json!({"relation":"Predicate","operands":[selector("output",0,"V"),selector("input",1,"P")]});
    read(&value).unwrap();
    let mut value = document();
    value["protocols"][0]["services"] = json!([
        {"name":"coins","owner":"V","contract":"random.bls12-381.fr/0","native":2},
        {"name":"other","owner":"V","contract":"random.bls12-381.fr/0","native":3}]);
    value["job"]["construction"] =
        json!({"kind":"fiat_shamir","suite":"merlin3.bls12-381.fr64be/0","service":0});
    assert_eq!(read(&value).unwrap_err(), InterfaceError::Selection);
}
#[test]
fn excessive_schema_depth_refuses_on_a_two_mebibyte_stack() {
    let mut nested = schema("unit", "()", json!([]));
    for i in 1..81 {
        let mut outer = schema("tuple", &format!("Tuple{i}"), json!([]));
        outer["fields"] = json!([{"name":"0","offset":0,"schema":nested}]);
        nested = outer;
    }
    let text = run_with(port("nested", 0, json!([]), json!(["P"]), nested)).to_string();
    preflight::check(text.as_bytes()).unwrap();
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(move || {
            assert_eq!(read_text(&text).unwrap_err(), InterfaceError::Limit);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn pcs_schemas_preserve_local_material_permissions() {
    let kzg = "multilinear.kzg.bls12-381/0";
    let rows = "rows.merkle-keccak256.koala-bear/0";
    for (head, domain, shared, wire) in [
        ("commitment", kzg, true, true),
        ("proof", kzg, true, true),
        ("commitments", rows, true, false),
        ("prover_key", kzg, false, false),
        ("verifier_key", kzg, false, false),
        ("opening_state", kzg, false, false),
        ("opening_states", rows, false, false),
    ] {
        let leaf = format!("{head}:{domain}");
        let mut value = schema("builtin", &leaf, json!([leaf]));
        let mut permissions = vec!["Copy", "Drop"];
        if shared {
            permissions.push("Share");
        }
        if wire {
            permissions.push("Wire");
        }
        value["permissions"] = json!(permissions);
        let parsed = serde_json::from_value(value.clone()).unwrap();
        schemas::Schemas::new().check(&parsed, 0).unwrap();
        if !shared {
            let mut forged = value.clone();
            forged["permissions"] = json!(["Copy", "Drop", "Share"]);
            let forged = serde_json::from_value(forged).unwrap();
            assert_eq!(
                schemas::Schemas::new().check(&forged, 0),
                Err(InterfaceError::Schema),
                "{head} acquired sharing"
            );
        }
        if !wire {
            permissions.push("Wire");
            value["permissions"] = json!(permissions);
            let forged = serde_json::from_value(value).unwrap();
            assert_eq!(
                schemas::Schemas::new().check(&forged, 0),
                Err(InterfaceError::Schema),
                "{head} acquired a message permission"
            );
        }
    }
}

fn setup_document() -> Value {
    let mut doc = document();
    doc["relations"] = json!([]);
    doc["protocols"][0]["clauses"] = json!([]);
    let mut inputs = Vec::new();
    for (i, (name, head, role, permissions)) in [
        ("vk", "verifier_key", "V", vec!["Copy", "Drop"]),
        ("pk", "prover_key", "P", vec!["Copy", "Drop"]),
        (
            "statement",
            "commitment",
            "V",
            vec!["Copy", "Drop", "Share", "Wire"],
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let leaf = format!("{head}:multilinear.kzg.bls12-381/0");
        let mut ty = schema("builtin", &leaf, json!([leaf]));
        ty["permissions"] = json!(permissions);
        inputs.push(port(name, i as u32, json!([i]), json!([role]), ty));
    }
    doc["protocols"][0]["inputs"] = json!(inputs);
    doc["job"]["public"] = json!([0, 2]);
    doc["job"]["target"] = Value::Null;
    doc["setups"] = json!([{"name":"pcs","inputs":[{"port":0,"path":[]},{"port":1,"path":[]},{"port":2,"path":[]}]}]);
    doc
}
#[test]
fn setup_selectors_derive_native_maps_independently() {
    let doc = setup_document();
    let interface = read(&doc).unwrap();
    let slot = &interface.setups[0];
    assert_eq!(slot.inputs, [0, 1, 2].into_iter().collect());
    assert_eq!(slot.verifier_keys, [0].into_iter().collect());
    let authority = crate::entry::SetupAuthority {
        keys: [("pcs".into(), [7; 32])].into(),
    };
    let proof = crate::entry::setups::proof_authority(&interface, authority.clone()).unwrap();
    assert_eq!(proof.keys, [(0, [7; 32])].into());
    assert_eq!(proof.inputs, [(1, 0), (2, 0)].into());
    let run = crate::entry::setups::run_authority(&interface, authority).unwrap();
    assert_eq!(
        run.inputs,
        [
            (("P".into(), 0), "pcs".into()),
            (("V".into(), 0), "pcs".into()),
            (("V".into(), 1), "pcs".into())
        ]
        .into()
    );
    assert_eq!(
        crate::entry::setups::run_authority(&interface, Default::default()).unwrap_err(),
        "entry-setup-authority"
    );
}
#[test]
fn malformed_setup_assignments_are_refused() {
    let valid = setup_document();
    for slots in [
        json!([]),
        json!([{"name":"pcs","inputs":[]}]),
        json!([{"name":"pcs","inputs":[{"port":0,"path":[]},{"port":1,"path":[]}]}]),
        json!([{"name":"pcs","inputs":[{"port":0,"path":[]},{"port":1,"path":[]},{"port":2,"path":[]},{"port":2,"path":[]}]}]),
        json!([{"name":"pcs","inputs":[{"port":0,"path":[]}]},{"name":"other","inputs":[{"port":1,"path":[]},{"port":2,"path":[]}]}]),
        json!([{"name":"pcs","inputs":[{"port":0,"path":[0]},{"port":1,"path":[]},{"port":2,"path":[]}]}]),
        json!([{"name":"pcs","inputs":[{"port":99,"path":[]},{"port":1,"path":[]},{"port":2,"path":[]}]}]),
    ] {
        let mut bad = valid.clone();
        bad["setups"] = slots;
        assert_eq!(read(&bad).unwrap_err(), InterfaceError::Selection, "{bad}");
    }
    let mut run = valid.clone();
    run["job"] = json!({"kind":"run"});
    run["setups"] = json!([{"name":"first","inputs":[{"port":0,"path":[]}]},{"name":"second","inputs":[{"port":1,"path":[]},{"port":2,"path":[]}]}]);
    read(&run).unwrap();
    run["setups"][1]["name"] = json!("first");
    assert_eq!(read(&run).unwrap_err(), InterfaceError::Selection);
    let mut unknown_format = valid;
    unknown_format["format"] = json!("invalid.language-interface");
    assert_eq!(read(&unknown_format).unwrap_err(), InterfaceError::Format);
}

#[test]
fn setup_alias_keys_share_the_pin_and_original_representative() {
    let mut doc = setup_document();
    let mut alias = doc["protocols"][0]["inputs"][0].clone();
    alias["name"] = json!("alias");
    alias["index"] = json!(3);
    alias["native"] = json!([3]);
    doc["protocols"][0]["inputs"]
        .as_array_mut()
        .unwrap()
        .push(alias);
    doc["job"]["public"] = json!([0, 2, 3]);
    doc["setups"][0]["inputs"] = json!([
        {"port":3,"path":[]}, {"port":2,"path":[]},
        {"port":1,"path":[]}, {"port":0,"path":[]}
    ]);
    let interface = read(&doc).unwrap();
    let authority = crate::entry::SetupAuthority {
        keys: [("pcs".into(), [9; 32])].into(),
    };
    let native = crate::entry::setups::proof_authority(&interface, authority).unwrap();
    assert_eq!(native.keys, [(0, [9; 32]), (3, [9; 32])].into());
    assert_eq!(native.inputs, [(1, 0), (2, 0)].into());
}

#[test]
fn proof_setup_refuses_prover_key_at_verifier() {
    let mut doc = setup_document();
    doc["protocols"][0]["inputs"][1]["roles"] = json!(["V"]);
    doc["job"]["public"] = json!([0, 1, 2]);
    assert_eq!(read(&doc).unwrap_err(), InterfaceError::Selection);
}
#[test]
fn proof_setup_bounds_total_verifier_keys_separately_from_slots() {
    let mut doc = setup_document();
    for index in 3..67 {
        let mut key = doc["protocols"][0]["inputs"][0].clone();
        key["name"] = json!(format!("key{index}"));
        key["index"] = json!(index);
        key["native"] = json!([index]);
        doc["protocols"][0]["inputs"]
            .as_array_mut()
            .unwrap()
            .push(key);
        doc["job"]["public"]
            .as_array_mut()
            .unwrap()
            .push(json!(index));
        doc["setups"][0]["inputs"]
            .as_array_mut()
            .unwrap()
            .push(json!({"port":index,"path":[]}));
    }
    assert_eq!(read(&doc).unwrap_err(), InterfaceError::Limit);
    doc["protocols"][0]["inputs"].as_array_mut().unwrap().pop();
    doc["job"]["public"].as_array_mut().unwrap().pop();
    doc["setups"][0]["inputs"].as_array_mut().unwrap().pop();
    assert_eq!(read(&doc).unwrap().setups[0].verifier_keys.len(), 64);
}

#[test]
fn completion_selects_a_prover_boolean_native_output() {
    let mut doc = document();
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let index = schema("index", "index", json!(["index"]));
    let mut product = schema("tuple", "(bool,index)", json!(["bool", "index"]));
    product["fields"] = json!([
        {"name":"0","offset":0,"schema":boolean},
        {"name":"1","offset":1,"schema":index}
    ]);
    doc["protocols"][0]["outputs"]
        .as_array_mut()
        .unwrap()
        .push(port("state", 1, json!([1, 2]), json!(["P", "V"]), product));
    doc["job"]["completion"] = json!({"direction":"output","port":1,"role":"P","path":[0]});
    assert_eq!(read(&doc).unwrap().proof().unwrap().completion, Some(1));
    for (field, value) in [
        ("direction", json!("input")),
        ("port", json!(99)),
        ("role", json!("V")),
        ("path", json!([1])),
    ] {
        let mut bad = doc.clone();
        bad["job"]["completion"][field] = value;
        assert_eq!(read(&bad).unwrap_err(), InterfaceError::Selection);
    }
    let mut unknown_format = doc;
    unknown_format["format"] = json!("invalid.language-interface");
    assert_eq!(read(&unknown_format).unwrap_err(), InterfaceError::Format);
}
