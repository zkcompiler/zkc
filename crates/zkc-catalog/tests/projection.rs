#[path = "../codegen/projection.rs"]
mod projection;

use serde_json::{Value, json};
use std::collections::BTreeMap;
use zkc_catalog::{CATALOG, Facet, Kind, NumericalResult, Signature, Term};

fn source() -> Value {
    serde_json::from_str(include_str!("../../../common/catalog/declarations.json")).unwrap()
}
fn installation() -> Value {
    serde_json::from_str(include_str!("../../../common/catalog/installation.json")).unwrap()
}
fn check_both(declarations: &Value, installation: &Value) -> Result<String, String> {
    projection::generate(
        &serde_json::to_vec(declarations).unwrap(),
        &serde_json::to_vec(installation).unwrap(),
    )
}
fn check(value: &Value) -> Result<String, String> {
    check_both(value, &installation())
}
fn check_installation(value: &Value) -> Result<String, String> {
    check_both(&source(), value)
}
fn operation<'a>(value: &'a mut Value, name: &str) -> &'a mut Value {
    value["operations"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|op| op["name"] == name)
        .unwrap()
}

#[test]
fn complete_static_inventory() {
    let value = source();
    for (key, count) in [
        ("frontendAssociations", CATALOG.frontend_associations.len()),
        ("frontendHomes", CATALOG.frontend_homes.len()),
        ("serviceMethods", CATALOG.service_methods.len()),
        ("sorts", CATALOG.sorts.len()),
        ("types", CATALOG.types.len()),
        ("operations", CATALOG.operations.len()),
        ("members", CATALOG.members.len()),
        ("rules", CATALOG.rules.len()),
        ("capabilities", CATALOG.capabilities.len()),
        ("exports", CATALOG.exports.len()),
        ("families", CATALOG.families.len()),
        ("consumerProfiles", CATALOG.consumer_profiles.len()),
        ("associatedTypes", CATALOG.associated_types.len()),
        (
            "mathematicalIdentities",
            CATALOG.mathematical_identities.len(),
        ),
        (
            "mathematicalIntrinsics",
            CATALOG.mathematical_intrinsics.len(),
        ),
    ] {
        assert_eq!(value[key].as_array().unwrap().len(), count, "{key}");
    }
    for (source, projected) in value["operations"]
        .as_array()
        .unwrap()
        .iter()
        .zip(CATALOG.operations)
    {
        assert_eq!(source["name"], projected.name);
        assert_eq!(
            source["scope"].as_array().unwrap().len(),
            projected.scope.len()
        );
        assert_eq!(
            source["facets"].as_array().unwrap().len(),
            projected.facets.len()
        );
        assert_eq!(
            source["facets"]
                .as_array()
                .unwrap()
                .contains(&json!({"kind": "DeterministicData"})),
            projected.facets.contains(&Facet::DeterministicData),
            "{} deterministic-data projection",
            projected.name
        );
        assert_eq!(
            source["requirements"].as_array().unwrap().len(),
            projected.requirements.len()
        );
    }
    assert!(zkc_catalog::operation("missing").is_none());
    assert!(zkc_catalog::constructor("scalar").is_none());
    let pass = zkc_catalog::operation("resource_unit.pass").unwrap();
    assert!(matches!(
        pass.scope,
        [Term::Root {
            parameter: Kind::Domain("Slot"),
            ..
        }]
    ));
    assert_eq!(
        pass.facets,
        [Facet::Succession {
            state_input: 0,
            state_output: 0
        }]
    );
    for name in ["resource_unit.create", "resource_unit.consume"] {
        assert!(zkc_catalog::operation(name).unwrap().facets.is_empty());
    }
    assert!(matches!(
        zkc_catalog::operation("numerical.map").unwrap().signature,
        Signature::Numerical {
            field: 0,
            result: NumericalResult::Map
        }
    ));
    assert!(matches!(
        zkc_catalog::operation("vector.mul").unwrap().facets,
        [
            Facet::Diagonal {
                factors_input: 0,
                values_input: 1,
                result_output: 0
            },
            Facet::DeterministicData
        ]
    ));
    assert_eq!(check(&value).unwrap(), check(&value).unwrap());
}

#[test]
fn deterministic_data_is_partial_and_independent_of_other_facets() {
    for name in [
        "index.div",
        "index.wrapping_add",
        "field.inverse",
        "control.require",
        "sequence.at",
        "vector.get",
        "bytes.at",
        "poly.domain_point",
        "oracle.check",
        "oracle.check_many",
        "shake128.squeeze",
    ] {
        let op = zkc_catalog::operation(name).unwrap();
        assert!(op.facets.contains(&Facet::DeterministicData), "{name}");
        assert!(!op.facets.contains(&Facet::PublicReplay), "{name}");
    }
    for name in [
        "random.draw",
        "transcript.challenge",
        "external.monero.hash",
        "resource_unit.pass",
        "representation.convert",
        "table.relayout",
        "oracle.commit",
        "oracle.open",
        "oracle.open_many",
        "pcs.check",
        "opening_states.at",
        "numerical.map",
    ] {
        assert!(
            !zkc_catalog::operation(name)
                .unwrap()
                .facets
                .contains(&Facet::DeterministicData),
            "{name}"
        );
    }
    assert!(zkc_catalog::operation("index.future").is_none());
    let mut value = source();
    let mut future = operation(&mut value, "index.add").clone();
    future["name"] = json!("index.future");
    future["facets"] = json!([]);
    value["operations"].as_array_mut().unwrap().push(future);
    let generated = check(&value).unwrap();
    assert_eq!(
        generated.matches("Facet::DeterministicData").count(),
        CATALOG
            .operations
            .iter()
            .filter(|op| op.facets.contains(&Facet::DeterministicData))
            .count()
    );
}

#[test]
fn deterministic_data_rejects_unknown_fields_kinds_and_duplicate_facets() {
    for facet in [
        json!({"kind": "DeterministicData", "total": true}),
        json!({"kind": "DeterministicData", "stateInput": 0}),
        json!({"kind": "UnknownDeterministicData"}),
        json!({"kind": "deterministicData"}),
    ] {
        let mut value = source();
        operation(&mut value, "index.add")["facets"] = json!([facet]);
        assert!(check(&value).is_err());
    }
    let mut value = source();
    operation(&mut value, "index.add")["facets"] = json!([
        {"kind": "DeterministicData"}, {"kind": "DeterministicData"}
    ]);
    assert!(
        check(&value)
            .unwrap_err()
            .contains("duplicate semantic facet")
    );
}

#[test]
fn owner_fixed_primitive_profile_preserves_exact_roots() {
    use zkc_catalog::{ConsumerImplementation, ParameterValidator};
    let profile = zkc_catalog::consumer_profile("structured-source-primitives").unwrap();
    assert_eq!(profile.implementation, ConsumerImplementation::Unselected);
    assert_eq!(
        profile.type_constructors,
        ["index", "bool", "field", "vector", "resource_unit"]
    );
    assert_eq!(
        profile.parameter_validators,
        [ParameterValidator::None, ParameterValidator::Natural]
    );
    let expected = [
        ("index.constant", false),
        ("index.add", false),
        ("index.sub", false),
        ("index.mul", false),
        ("index.div", false),
        ("index.mod", false),
        ("index.equal", false),
        ("index.less", false),
        ("vector.empty", true),
        ("vector.length", true),
        ("vector.sum", true),
        ("vector.split", true),
        ("vector.append", true),
        ("vector.equal", true),
        ("field.equal", true),
        ("field.embed", true),
        ("resource_unit.create", false),
        ("resource_unit.pass", false),
        ("resource_unit.consume", false),
    ];
    assert_eq!(profile.operations.len(), expected.len());
    for (entry, (name, field)) in profile.operations.iter().zip(expected) {
        assert_eq!(entry.operation, name);
        assert_eq!(
            entry.static_parameters,
            if name.starts_with("resource_unit.") {
                &[Kind::Domain("Slot")][..]
            } else if field {
                &[Kind::Domain("Field")][..]
            } else {
                &[]
            }
        );
        assert_eq!(
            zkc_catalog::consumer_profile_operation(profile.name, name),
            Some(entry)
        );
    }
    assert!(zkc_catalog::consumer_profile("missing").is_none());
    assert!(zkc_catalog::consumer_profile_operation("missing", "index.add").is_none());
    assert!(zkc_catalog::consumer_profile_operation(profile.name, "field.add").is_none());
    assert!(zkc_catalog::consumer_profile_operation(profile.name, "numerical.map").is_none());
    assert!(zkc_catalog::operation("field.add").is_some());
}

#[test]
fn profile_exact_fields_and_references_refuse() {
    for path in [
        "/consumerProfiles/0",
        "/consumerProfiles/0/operations/0",
        "/consumerProfiles/0/operations/0/parameters",
        "/consumerProfiles/0/operations/0/signature",
        "/consumerProfiles/0/operations/8/scope/0/parameter",
    ] {
        let mut changed = source();
        changed
            .pointer_mut(path)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert("unexpected".into(), json!(true));
        assert!(
            check(&changed).unwrap_err().contains("unknown field"),
            "{path}"
        );
    }
    let mut old = source();
    old.as_object_mut().unwrap().remove("consumerProfiles");
    assert!(
        check(&old)
            .unwrap_err()
            .contains("missing field consumerProfiles")
    );

    type Mutation = (&'static str, fn(&mut Value));
    let cases: &[Mutation] = &[
        ("unknown member", |p| {
            p["operations"][0]["operation"] = json!("missing")
        }),
        ("duplicate member", |p| {
            let member = p["operations"][0].clone();
            p["operations"].as_array_mut().unwrap().push(member);
        }),
        ("unknown constructor", |p| {
            p["typeConstructors"][0] = json!("missing")
        }),
        ("duplicate constructor", |p| {
            p["typeConstructors"][0] = json!("field")
        }),
        ("unsupported type", |p| {
            p["typeConstructors"] = json!(["index", "bool", "vector"])
        }),
        ("unknown validator", |p| {
            p["parameterValidators"][0] = json!("Unknown")
        }),
        ("unsupported parameter family", |p| {
            p["parameterValidators"][0] = json!("NumericalExpression")
        }),
        ("duplicate validator", |p| {
            p["parameterValidators"][1] = json!("None")
        }),
        ("unsupported validator", |p| {
            p["parameterValidators"] = json!(["None"])
        }),
        ("selected implementation", |p| {
            p["implementation"] = json!("selected")
        }),
    ];
    for (name, mutate) in cases {
        let mut changed = source();
        mutate(&mut changed["consumerProfiles"][0]);
        assert!(check(&changed).is_err(), "{name}");
    }
    let mut changed = source();
    let profile = changed["consumerProfiles"][0].clone();
    changed["consumerProfiles"]
        .as_array_mut()
        .unwrap()
        .push(profile);
    assert!(check(&changed).is_err());
}

#[test]
fn consumer_expectations_refuse_independently_valid_declaration_drift() {
    for (field, value) in [
        (
            "scope",
            json!([{"kind":"root","name":"Other","parameter":{"kind":"Domain","sort":"Field"}}]),
        ),
        ("stage", json!("Construction")),
        (
            "parameters",
            json!({"validator":"Natural","minimum":1,"maximum":1}),
        ),
        ("requirements", json!([])),
        (
            "signature",
            json!({"kind":"fixed","inputs":[],"outputs":[{"constructor":"bool","arguments":[]}]}),
        ),
    ] {
        for declaration in [false, true] {
            let mut changed = source();
            if declaration {
                operation(&mut changed, "field.equal")[field] = value.clone();
            } else {
                let member = changed["consumerProfiles"][0]["operations"]
                    .as_array_mut()
                    .unwrap()
                    .iter_mut()
                    .find(|m| m["operation"] == "field.equal")
                    .unwrap();
                member[field] = value.clone();
            }
            let error = check(&changed).unwrap_err();
            assert!(
                error.contains(&format!("consumer operation {field} mismatch")),
                "{field}/{declaration}: {error}"
            );
        }
    }
}

#[test]
fn adding_a_declaration_does_not_enroll_it() {
    let mut changed = source();
    let mut extra = operation(&mut changed, "field.equal").clone();
    extra["name"] = json!("example.unenrolled");
    changed["operations"].as_array_mut().unwrap().push(extra);
    assert!(check(&changed).is_ok());
    assert_eq!(changed["consumerProfiles"], source()["consumerProfiles"]);
}

// Collect one representative of every exact object shape. The two alternatives
// of a tagged record may have identical keys, so include its tag in the key.
fn shapes(value: &Value, path: String, out: &mut BTreeMap<String, String>) {
    if let Some(object) = value.as_object() {
        let key = format!(
            "{:?}/{}",
            object.keys().collect::<Vec<_>>(),
            value.get("kind").unwrap_or(&Value::Null)
        );
        out.entry(key).or_insert_with(|| path.clone());
        for (key, child) in object {
            shapes(child, format!("{path}/{key}"), out);
        }
    } else if let Some(items) = value.as_array() {
        for (i, child) in items.iter().enumerate() {
            shapes(child, format!("{path}/{i}"), out);
        }
    }
}

#[test]
fn unknown_and_missing_fields_refuse_at_every_record_shape() {
    type Check = fn(&Value) -> Result<String, String>;
    let documents: [(Value, Check, usize); 2] = [
        (source(), check, 30),
        (installation(), check_installation, 10),
    ];
    for (original, check, minimum) in documents {
        let mut cases = BTreeMap::new();
        shapes(&original, String::new(), &mut cases);
        assert!(cases.len() > minimum);
        for path in cases.values() {
            let mut changed = original.clone();
            changed
                .pointer_mut(path)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .insert("unexpected".into(), json!(0));
            assert!(check(&changed).is_err(), "unknown field at {path}");
            // Optional fields may legitimately disappear; remove all fields for a
            // missing-shape control instead of treating optional data as required.
            changed
                .pointer_mut(path)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .clear();
            assert!(check(&changed).is_err(), "missing fields at {path}");
        }
    }
}

#[test]
fn duplicate_keys_and_noninteger_counts_refuse() {
    let declarations = serde_json::to_string(&source()).unwrap();
    let installed = serde_json::to_string(&installation()).unwrap();
    let duplicate = declarations.replacen('{', "{\"format\":\"zkc.contract-declarations/0\",", 1);
    assert!(
        projection::generate(duplicate.as_bytes(), installed.as_bytes())
            .unwrap_err()
            .contains("duplicate key")
    );
    let duplicate = installed.replacen('{', "{\"format\":\"zkc.native-installation/0\",", 1);
    let error = projection::generate(declarations.as_bytes(), duplicate.as_bytes()).unwrap_err();
    assert!(
        error.contains("native installation: duplicate key"),
        "{error}"
    );
    for value in [
        json!(-1),
        json!(1.5),
        json!(true),
        json!("1"),
        Value::Null,
        json!(1_048_577),
    ] {
        let mut changed = source();
        operation(&mut changed, "field.add")["parameters"]["minimum"] = value;
        assert!(check(&changed).is_err());
    }
}

#[test]
fn cross_references_and_permissions_refuse() {
    let original = source();
    type Mutation = (&'static str, fn(&mut Value));
    let cases: &[Mutation] = &[
        ("duplicate identity", |v| {
            v["operations"][1]["name"] = v["operations"][0]["name"].clone();
        }),
        ("reserved sort", |v| {
            v["sorts"][0] = json!("Type");
        }),
        ("affine copy", |v| {
            let ty = v["types"]
                .as_array_mut()
                .unwrap()
                .iter_mut()
                .find(|t| t["custody"] == "Affine")
                .unwrap();
            ty["copy"] = json!(true);
        }),
        ("unknown constructor", |v| {
            operation(v, "field.add")["signature"]["inputs"][0]["constructor"] = json!("missing");
        }),
        ("unscoped term", |v| {
            operation(v, "field.add")["signature"]["inputs"][0]["arguments"][0] = json!(3);
        }),
        ("wrong nominal kind", |v| {
            operation(v, "field.add")["scope"][0]["parameter"] = json!({"kind":"Type","sort":""});
        }),
        ("wrong complete port kind", |v| {
            operation(v, "field.add")["signature"]["inputs"][0] = json!({"term":0});
        }),
        ("duplicate scope root", |v| {
            let op = operation(v, "field.add");
            let root = op["scope"][0].clone();
            op["scope"].as_array_mut().unwrap().push(root);
        }),
        ("unknown requirement", |v| {
            operation(v, "field.add")["requirements"][0]["capability"] = json!("missing");
        }),
        ("bounds", |v| {
            operation(v, "field.add")["parameters"]["minimum"] = json!(1);
        }),
        ("unscoped literal field", |v| {
            operation(v, "field.constant")["parameters"]["fieldTerm"] = json!(1);
        }),
        ("numerical stage", |v| {
            operation(v, "numerical.map")["stage"] = json!("Source");
        }),
        ("numerical field", |v| {
            operation(v, "numerical.map")["signature"]["fieldTerm"] = json!(1);
        }),
        ("numerical requirement", |v| {
            operation(v, "numerical.map")["requirements"] = json!([]);
        }),
        ("facet port", |v| {
            operation(v, "vector.mul")["facets"][0]["resultOutput"] = json!(1);
        }),
        ("facet overlap", |v| {
            operation(v, "vector.mul")["facets"][0]["valuesInput"] = json!(0);
        }),
        ("facet duplicate", |v| {
            let op = operation(v, "vector.mul");
            let f = op["facets"][0].clone();
            op["facets"].as_array_mut().unwrap().push(f);
        }),
        ("false mathematical law", |v| {
            v["mathematicalIdentities"][0]["laws"]["algebra"] = json!("GroupModule");
        }),
        ("unresolved intrinsic", |v| {
            v["mathematicalIntrinsics"][0]["identity"] = json!("missing");
        }),
        ("duplicate export", |v| {
            v["exports"][1] = v["exports"][0].clone();
        }),
        ("unknown family", |v| {
            v["families"][0]["resultConstructor"] = json!("missing");
        }),
        ("unknown associated sort", |v| {
            v["associatedTypes"][0]["sort"] = json!("missing");
        }),
    ];
    for (name, mutate) in cases {
        let mut changed = original.clone();
        mutate(&mut changed);
        assert!(check(&changed).is_err(), "{name}");
    }
}

#[test]
fn source_vocabulary_columns_are_exact() {
    let original = source();
    let row = |name: &str| -> usize {
        original["types"]
            .as_array()
            .unwrap()
            .iter()
            .position(|t| t["name"] == name)
            .unwrap()
    };
    for (name, field, value, message) in [
        ("field", "sourceData", Value::Null, "expected Boolean"),
        ("field", "sourceData", json!("true"), "expected Boolean"),
        (
            "vector",
            "collection",
            json!({"rank": 3, "element": "parameter"}),
            "collection rank",
        ),
        (
            "vector",
            "collection",
            json!({"rank": 0, "element": "parameter"}),
            "collection rank",
        ),
        (
            "vector",
            "collection",
            json!({"rank": 1, "element": "row"}),
            "unknown declaration alternative row",
        ),
        (
            "vector",
            "collection",
            json!({"rank": 1}),
            "missing field element",
        ),
        (
            "vector",
            "collection",
            json!("parameter"),
            "expected declaration object",
        ),
        (
            "prover_key",
            "setup",
            json!("both"),
            "unknown declaration alternative both",
        ),
        (
            "prover_key",
            "setup",
            json!(false),
            "expected declaration string",
        ),
    ] {
        let mut changed = original.clone();
        changed["types"][row(name)][field] = value;
        let error = check(&changed).unwrap_err();
        assert!(error.contains(message), "{name}.{field}: {error}");
    }
    for field in ["sourceData", "collection", "setup"] {
        let mut changed = original.clone();
        changed["types"][0].as_object_mut().unwrap().remove(field);
        let error = check(&changed).unwrap_err();
        assert!(error.contains(&format!("missing field {field}")), "{error}");
    }
}

#[test]
fn succession_transfers_exactly_one_resource_identity() {
    let mut base = source();
    let mut example = operation(&mut base, "resource_unit.pass").clone();
    example["name"] = json!("example.succession");
    base["operations"].as_array_mut().unwrap().push(example);
    assert!(check(&base).is_ok());
    type Mutation = (&'static str, fn(&mut Value));
    let cases: &[Mutation] = &[
        ("unscoped declaration reference", |op| {
            op["facets"][0]["stateInput"] = json!(1);
        }),
        ("unscoped declaration reference", |op| {
            op["facets"][0]["stateOutput"] = json!(1);
        }),
        ("facet port constructor mismatch", |op| {
            op["signature"]["inputs"][0] = json!({"constructor": "bool", "arguments": []});
        }),
        ("succession resource type mismatch", |op| {
            op["scope"].as_array_mut().unwrap().push(json!(
                {"kind": "root", "name": "T", "parameter": {"kind": "Domain", "sort": "Slot"}}
            ));
            op["signature"]["outputs"][0]["arguments"] = json!([1]);
        }),
        ("succession admits no other resource port", |op| {
            let extra = op["signature"]["inputs"][0].clone();
            op["signature"]["inputs"]
                .as_array_mut()
                .unwrap()
                .push(extra);
        }),
        ("succession admits no other resource port", |op| {
            let extra = op["signature"]["outputs"][0].clone();
            op["signature"]["outputs"]
                .as_array_mut()
                .unwrap()
                .insert(0, extra);
        }),
    ];
    for (message, mutate) in cases {
        let mut changed = base.clone();
        mutate(operation(&mut changed, "example.succession"));
        let error = check(&changed).unwrap_err();
        assert!(error.contains(message), "{message}: {error}");
    }
    // A Slot reached through an associated member is not the scope's root.
    let mut projected = base.clone();
    projected["members"].as_array_mut().unwrap().push(json!({
        "name": "Unit",
        "owner": {"kind": "Domain", "sort": "Field"},
        "result": {"kind": "Domain", "sort": "Slot"}
    }));
    let op = operation(&mut projected, "example.succession");
    op["scope"] = json!([
        {"kind": "root", "name": "F", "parameter": {"kind": "Domain", "sort": "Field"}},
        {"kind": "project", "member": "Unit", "parent": 0}
    ]);
    op["signature"]["inputs"][0]["arguments"] = json!([1]);
    op["signature"]["outputs"][0]["arguments"] = json!([1]);
    let error = check(&projected).unwrap_err();
    assert!(error.contains("succession requires a Slot root"), "{error}");
    operation(&mut projected, "example.succession")["facets"] = json!([]);
    assert!(check(&projected).is_ok());
}

#[test]
fn complete_type_ports_do_not_depend_on_authoring_inheritance() {
    let mut value = source();
    value["operations"].as_array_mut().unwrap().push(json!({
        "name":"example.identity", "scope":[{"kind":"root","name":"T","parameter":{"kind":"Type","sort":""}}],
        "stage":"Source", "parameters":{"validator":"None","minimum":0,"maximum":0},
        "signature":{"kind":"fixed","inputs":[{"term":0}],"outputs":[{"term":0}]},
        "requirements":[], "facets":[]
    }));
    assert!(check(&value).is_ok());
}

#[test]
fn construction_counterparts_require_the_declared_stage() {
    let mut value = source();
    let mut counterpart = operation(&mut value, "transcript.native.indexed.challenge").clone();
    counterpart["name"] = json!("example.derived");
    counterpart["signature"]["inputs"]
        .as_array_mut()
        .unwrap()
        .truncate(1);
    counterpart["parameters"] = json!({"validator":"None", "minimum":0, "maximum":0});
    value["operations"]
        .as_array_mut()
        .unwrap()
        .push(counterpart);
    operation(&mut value, "random.draw")["derivedCounterpart"] = json!("example.derived");
    assert!(check(&value).is_ok());
    operation(&mut value, "example.derived")["stage"] = json!("Source");
    assert!(check(&value).unwrap_err().contains("counterpart"));
}

#[test]
fn physical_adapters_declare_erasure_and_no_mathematical_rewrite_facet() {
    for name in ["representation.convert", "table.relayout"] {
        let operation = zkc_catalog::operation(name).unwrap();
        assert_eq!(operation.stage, zkc_catalog::Stage::Physical);
        assert!(operation.facets.is_empty());
        let Signature::Fixed { inputs, outputs } = operation.signature else {
            panic!("fixed erasure required")
        };
        assert_eq!(inputs, outputs);
        assert_eq!(inputs.len(), 1);
    }
}

#[test]
fn native_index_blocks_have_distinct_product_and_search_contracts() {
    use zkc_catalog::{ParameterValidator, SamplingDomain};
    let block = zkc_catalog::operation("transcript.native.indexed.indices").unwrap();
    assert_eq!(
        block.parameters.validator,
        ParameterValidator::NativeIndexBlock
    );
    assert_eq!(block.parameters.minimum, 3);
    assert!(block.facets.iter().any(|facet| matches!(
        facet,
        Facet::Sampling {
            domain: SamplingDomain::IndexBlock,
            bound_input: None,
            ..
        }
    )));
    for (name, successor) in [
        ("transcript.native.indexed.indices.search", 2),
        ("transcript.native.indexed.indices.gated", 1),
    ] {
        let op = zkc_catalog::operation(name).unwrap();
        assert_eq!(op.parameters.minimum, 4);
        assert!(
            matches!(op.facets, [Facet::History { state_input: 0, state_output }] if *state_output == successor)
        );
    }
    for (name, field, value) in [
        ("transcript.native.indexed.indices", "minimum", json!(4)),
        (
            "transcript.native.indexed.indices.search",
            "maximum",
            json!(3),
        ),
    ] {
        let mut invalid = source();
        operation(&mut invalid, name)["parameters"][field] = value;
        assert!(check(&invalid).is_err(), "{name}/{field}");
    }
    let mut scalar = source();
    operation(&mut scalar, "transcript.native.indexed.indices")["facets"][0]["domain"] =
        json!("BoundedIndex");
    assert!(check(&scalar).is_err());
}

#[test]
fn frontend_association_mutations_refuse() {
    let original = source();
    assert!(check(&original).is_ok());
    for (section, field, value) in [
        (
            "frontendAssociations",
            "signature",
            json!("RandomConstructor"),
        ),
        ("frontendAssociations", "identity", json!("record.unknown")),
        ("frontendAssociations", "authority", json!("all-records")),
        ("frontendHomes", "constructor", json!("Vector")),
        ("frontendHomes", "module", json!("foreign")),
        ("serviceMethods", "signature", json!("Unknown")),
        ("serviceMethods", "capability", json!("IndexRandomness")),
    ] {
        let mut changed = original.clone();
        changed[section][0][field] = value;
        assert!(check(&changed).is_err(), "{section}.{field}");
    }
    for section in ["frontendAssociations", "frontendHomes", "serviceMethods"] {
        let mut changed = original.clone();
        let duplicate = changed[section][0].clone();
        changed[section].as_array_mut().unwrap().push(duplicate);
        assert!(check(&changed).is_err(), "duplicate {section}");
    }
    let mut renamed = original.clone();
    renamed["frontendAssociations"][0]["name"] = json!("open_payload");
    assert!(check(&renamed).is_ok());
}

type Mutation = (&'static str, fn(&mut Value));

fn rows<'a>(value: &'a mut Value, table: &str) -> &'a mut Vec<Value> {
    value[table].as_array_mut().unwrap()
}
fn row<'a>(value: &'a mut Value, table: &str, key: &str, name: &str) -> &'a mut Value {
    rows(value, table)
        .iter_mut()
        .find(|row| row[key] == name)
        .unwrap_or_else(|| panic!("{table}: {name}"))
}
fn domain<'a>(value: &'a mut Value, name: &str) -> &'a mut Value {
    row(value, "domains", "identity", name)
}
fn codec<'a>(value: &'a mut Value, name: &str) -> &'a mut Value {
    row(value, "codecs", "identity", name)
}
fn representation<'a>(value: &'a mut Value, name: &str, kind: &str, on: &str) -> &'a mut Value {
    rows(value, "representations")
        .iter_mut()
        .find(|row| row["identity"] == name && row["kind"] == kind && row["domain"] == on)
        .unwrap_or_else(|| panic!("representation {name}"))
}
fn without(list: &mut Value, item: &str) {
    list.as_array_mut().unwrap().retain(|value| *value != item);
}
fn refuse(original: &Value, cases: &[Mutation], check: fn(&Value) -> Result<String, String>) {
    assert!(check(original).is_ok());
    for (message, mutate) in cases {
        let mut changed = original.clone();
        mutate(&mut changed);
        let error = check(&changed).expect_err(message);
        assert!(error.contains(message), "{message}: {error}");
    }
}

#[test]
fn staged_catalog_documents_validate_together() {
    let generated = check(&source()).unwrap();
    // A physical-only change leaves the logical projection unchanged: the
    // installation tables are the separate INSTALLATION static.
    let mut changed = installation();
    rows(&mut changed, "representations").retain(|row| row["identity"] != "arkworks.mle-msb/0");
    let physical = check_installation(&changed).unwrap();
    let logical = |code: &str| {
        code.split("pub static INSTALLATION")
            .next()
            .unwrap()
            .to_owned()
    };
    assert_eq!(logical(&physical), logical(&generated));
    assert_ne!(physical, generated);
    assert!(!logical(&generated).contains("arkworks.mle-msb/0"));
    for table in [
        "domains",
        "logicalTypes",
        "frameTags",
        "codecs",
        "aggregateFrames",
        "randomServices",
        "limits",
        "finiteDefinitions",
        "domainConstructors",
    ] {
        assert!(!source()[table].as_array().unwrap().is_empty(), "{table}");
    }
}

#[test]
fn unknown_and_missing_root_keys_refuse_in_each_document() {
    let mut declarations = source();
    declarations["unexpected"] = json!([]);
    let error = check(&declarations).unwrap_err();
    assert!(error.contains("unknown field unexpected"), "{error}");
    let mut installed = installation();
    installed["unexpected"] = json!([]);
    let error = check_installation(&installed).unwrap_err();
    assert!(
        error.contains("native installation: unknown field unexpected"),
        "{error}"
    );
    for key in [
        "domains",
        "logicalTypes",
        "frameTags",
        "codecs",
        "aggregateFrames",
        "randomServices",
        "limits",
        "finiteDefinitions",
        "domainConstructors",
    ] {
        let mut changed = source();
        changed.as_object_mut().unwrap().remove(key);
        let error = check(&changed).unwrap_err();
        assert!(error.contains(&format!("missing field {key}")), "{error}");
    }
    for key in [
        "format",
        "representations",
        "appliedRepresentations",
        "providers",
        "providerUnits",
        "fieldForms",
        "physicalArguments",
    ] {
        let mut changed = installation();
        changed.as_object_mut().unwrap().remove(key);
        let error = check_installation(&changed).unwrap_err();
        assert!(error.contains(&format!("missing field {key}")), "{error}");
    }
    let mut changed = installation();
    changed["format"] = json!("zkc.native-installation/1");
    assert!(
        check_installation(&changed)
            .unwrap_err()
            .contains("unknown declaration alternative zkc.native-installation/1")
    );
}

#[test]
fn nominal_domain_mutations_refuse_for_the_stated_rule() {
    let cases: &[Mutation] = &[
        ("invalid identity", |v| {
            domain(v, "bn254.gt")["identity"] = json!("9-gt");
        }),
        ("identity is not unique across domains and codecs", |v| {
            domain(v, "bn254.gt")["identity"] = json!("bn254.g2");
        }),
        ("identity is not unique across domains and codecs", |v| {
            codec(v, "zkcv.bool/0")["identity"] = json!("koala-bear");
        }),
        (
            "domain sort must be a declared sort other than Codec and Slot",
            |v| {
                domain(v, "bn254.gt")["sort"] = json!("Slot");
            },
        ),
        ("BaseField is not a declared member of sort Group", |v| {
            domain(v, "bn254.gt")["members"][0][0] = json!("BaseField");
        }),
        ("duplicate member Scalar", |v| {
            let members = &mut domain(v, "bn254.gt")["members"];
            let pair = members[0].clone();
            members.as_array_mut().unwrap().push(pair);
        }),
        (
            "member ChallengeField must name a domain of sort Field",
            |v| {
                domain(v, "merlin3.bls12-381.fr64be/0")["members"][0][1] = json!("bls12-381.g1");
            },
        ),
        ("member Scalar must name a domain of sort Field", |v| {
            domain(v, "bn254.gt")["members"][0][1] = json!("missing");
        }),
        ("unknown capability Missing", |v| {
            rows(domain(v, "koala-bear"), "capabilities").push(json!("Missing"));
        }),
        ("ScalarAction is not a unary predicate over Field", |v| {
            rows(domain(v, "koala-bear"), "capabilities").push(json!("ScalarAction"));
        }),
        ("duplicate capability Field", |v| {
            rows(domain(v, "koala-bear"), "capabilities").push(json!("Field"));
        }),
        ("capabilities are not closed under", |v| {
            without(&mut domain(v, "koala-bear")["capabilities"], "Field");
        }),
        ("a PairingField row names a PairingG2 group", |v| {
            rows(domain(v, "bn254.fr"), "members").retain(|pair| pair[0] != "PairingG2");
        }),
        ("pairing groups must be distinct", |v| {
            domain(v, "bn254.fr")["members"][1][1] = json!("bn254.g1");
        }),
        (
            "bn254.g1 must hold ScalarAction with bn254.fr as Scalar",
            |v| {
                without(&mut domain(v, "bn254.g1")["capabilities"], "ScalarAction");
            },
        ),
        (
            "PointField and EvaluationField occur only on multilinearKzg commitments",
            |v| {
                rows(domain(v, "rows.merkle-keccak256.koala-bear/0"), "members")
                    .push(json!(["PointField", "koala-bear"]));
            },
        ),
        ("noncanonical decimal", |v| {
            domain(v, "koala-bear")["field"]["characteristic"] = json!("02130706433");
        }),
        ("noncanonical decimal", |v| {
            domain(v, "koala-bear")["field"]["characteristic"] = json!("1".repeat(1025));
        }),
        ("characteristic must be at least 2", |v| {
            domain(v, "koala-bear")["field"]["characteristic"] = json!("1");
        }),
        (
            "CharacteristicNotTwo must hold exactly when the characteristic is not 2",
            |v| {
                without(
                    &mut domain(v, "baby-bear")["capabilities"],
                    "CharacteristicNotTwo",
                );
            },
        ),
        ("exactly the prime rows hold PrimeField", |v| {
            without(&mut domain(v, "goldilocks")["capabilities"], "PrimeField");
        }),
        ("exactly the rows over BaseField hold ExtensionField", |v| {
            without(
                &mut domain(v, "koala-bear.ext4-binomial3")["capabilities"],
                "ExtensionField",
            );
        }),
        (
            "exactly the rows over BaseField have a BaseField member",
            |v| {
                domain(v, "koala-bear.ext4-binomial3")["members"] = json!([]);
            },
        ),
        ("BaseField must have the same characteristic", |v| {
            domain(v, "koala-bear.ext4-binomial3")["members"][0][1] = json!("baby-bear");
        }),
        ("reduction is a nonempty list", |v| {
            domain(v, "goldilocks.ext2-binomial7")["field"]["structure"]["reduction"] = json!([]);
        }),
        ("extension degree must be at least 2", |v| {
            domain(v, "goldilocks.ext2-binomial7")["field"]["structure"]["degree"] = json!(1);
        }),
        (
            "reduction exponents must strictly decrease below the degree",
            |v| {
                domain(v, "gf2-64.pentanomial-4-3-1")["field"]["structure"]["reduction"][1][0] =
                    json!(4);
            },
        ),
        (
            "reduction exponents must strictly decrease below the degree",
            |v| {
                domain(v, "goldilocks.ext2-binomial7")["field"]["structure"]["reduction"][0][0] =
                    json!(2);
            },
        ),
        (
            "reduction coefficients must be nonzero and below the characteristic",
            |v| {
                domain(v, "koala-bear.ext4-binomial3")["field"]["structure"]["reduction"][0][1] =
                    json!("0");
            },
        ),
        (
            "reduction coefficients must be nonzero and below the characteristic",
            |v| {
                domain(v, "koala-bear.ext4-binomial3")["field"]["structure"]["reduction"][0][1] =
                    json!("2130706433");
            },
        ),
        ("twoAdic is only on prime rows", |v| {
            let mut two_adic = domain(v, "koala-bear")["field"]["twoAdic"].clone();
            two_adic["convention"] = json!("koala-bear.ext4.two-adic/0");
            domain(v, "koala-bear.ext4-binomial3")["field"]["twoAdic"] = two_adic;
        }),
        ("maximalRoot must be below the characteristic", |v| {
            domain(v, "koala-bear")["field"]["twoAdic"]["maximalRoot"] = json!("2130706433");
        }),
        ("twoAdicity must be between 1 and 64", |v| {
            domain(v, "koala-bear")["field"]["twoAdic"]["twoAdicity"] = json!(0);
        }),
        ("twoAdicity must be between 1 and 64", |v| {
            domain(v, "koala-bear")["field"]["twoAdic"]["twoAdicity"] = json!(65);
        }),
        ("unknown declaration alternative bitReversed", |v| {
            domain(v, "koala-bear")["field"]["twoAdic"]["ordering"] = json!("bitReversed");
        }),
        ("duplicate two-adic convention", |v| {
            domain(v, "baby-bear")["field"]["twoAdic"]["convention"] =
                json!("koala-bear.two-adic.1791270792/0");
        }),
        (
            "TwoAdicField must hold exactly when the row or its prime base has a convention",
            |v| {
                without(
                    &mut domain(v, "koala-bear.ext8-binomial3")["capabilities"],
                    "TwoAdicField",
                );
            },
        ),
        (
            "TwoAdicField must hold exactly when the row or its prime base has a convention",
            |v| {
                rows(domain(v, "bls12-381.fr"), "capabilities").push(json!("TwoAdicField"));
            },
        ),
        ("cyclic BaseField chain", |v| {
            let base = domain(v, "gf2-64.pentanomial-4-3-1");
            base["field"]["structure"]["over"] = json!("BaseField");
            base["members"] = json!([["BaseField", "gf2-64.pentanomial-4-3-1.ext3-trinomial1"]]);
            rows(base, "capabilities").push(json!("ExtensionField"));
        }),
    ];
    refuse(&source(), cases, check);
}

#[test]
fn transcript_and_commitment_mutations_refuse_for_the_stated_rule() {
    let cases: &[Mutation] = &[
        ("unknown declaration alternative merlin4", |v| {
            domain(v, "merlin3.bls12-381.fr64be/0")["transcript"]["family"] = json!("merlin4");
        }),
        (
            "hash is keccak256 exactly for hash-chain transcripts, otherwise null",
            |v| {
                domain(v, "hash-chain.keccak256.bls12-381.fr64be/0")["transcript"]["hash"] =
                    Value::Null;
            },
        ),
        (
            "hash is keccak256 exactly for hash-chain transcripts, otherwise null",
            |v| {
                domain(v, "merlin3.bls12-381.fr64be/0")["transcript"]["hash"] = json!("keccak256");
            },
        ),
        ("fr64be requires a prime challenge field", |v| {
            domain(v, "merlin3.koala-bear.ext8-binomial3.rejection31le/0")["transcript"]["decoder"] =
                json!("fr64be");
        }),
        (
            "rejection31le requires a challenge characteristic below 2^31",
            |v| {
                domain(v, "merlin3.goldilocks.ext2-binomial7.rejection64le/0")["transcript"]["decoder"] =
                    json!("rejection31le");
            },
        ),
        (
            "rejection64le requires a challenge characteristic below 2^64",
            |v| {
                domain(v, "merlin3.bls12-381.fr64be/0")["transcript"]["decoder"] =
                    json!("rejection64le");
            },
        ),
        (
            "a transcript row holds Transcript and FieldTranscript",
            |v| {
                without(
                    &mut domain(v, "merlin3.bls12-381.fr64be/0")["capabilities"],
                    "FieldTranscript",
                );
            },
        ),
        ("a transcript row has a ChallengeField member", |v| {
            domain(v, "merlin3.bls12-381.fr64be/0")["members"] = json!([]);
        }),
        ("unknown declaration alternative sha256Rows", |v| {
            domain(v, "rows.merkle-keccak256.koala-bear/0")["commitment"]["scheme"] =
                json!("sha256Rows");
        }),
        ("digestBytes must be 32", |v| {
            domain(v, "rows.merkle-keccak256.koala-bear/0")["commitment"]["digestBytes"] =
                json!(16);
        }),
        ("unknown permutation koala-bear.poseidon2-24", |v| {
            domain(v, "rows.merkle-poseidon2-16.koala-bear/0")["commitment"]["permutation"] =
                json!("koala-bear.poseidon2-24");
        }),
        (
            "the permutation field must be the ValueField member or its prime base",
            |v| {
                domain(v, "rows.merkle-poseidon2-16.koala-bear/0")["commitment"]["permutation"] =
                    json!("goldilocks.poseidon2-8");
            },
        ),
        (
            "digestWordBytes must equal the element width of the koala-bear field codec frame",
            |v| {
                domain(v, "rows.merkle-poseidon2-16.koala-bear/0")["commitment"]["digestWordBytes"] =
                    json!(8);
            },
        ),
        ("a commitment row has a ValueField member", |v| {
            domain(v, "rows.merkle-keccak256.koala-bear/0")["members"] = json!([]);
        }),
    ];
    refuse(&source(), cases, check);
}

#[test]
fn instance_frame_and_codec_mutations_refuse_for_the_stated_rule() {
    let cases: &[Mutation] = &[
        ("duplicate logical type instance", |v| {
            rows(v, "logicalTypes").push(json!({"kind": "bool", "domain": ""}));
        }),
        ("a nullary instance has the empty domain", |v| {
            rows(v, "logicalTypes").push(json!({"kind": "bool", "domain": "koala-bear"}));
        }),
        ("a unary instance names a domain of sort Field", |v| {
            rows(v, "logicalTypes").push(json!({"kind": "field", "domain": "bn254.g1"}));
        }),
        ("variant and resource_unit have their own formation", |v| {
            rows(v, "logicalTypes").push(json!({"kind": "resource_unit", "domain": ""}));
        }),
        (
            "only nullary and unary domain constructors have logical type instances",
            |v| {
                rows(v, "logicalTypes").push(json!({"kind": "sequence", "domain": ""}));
            },
        ),
        ("undeclared constructor variant", |v| {
            rows(v, "logicalTypes").push(json!({"kind": "variant", "domain": ""}));
        }),
        (
            "setup keys are admitted only over multilinearKzg commitments",
            |v| {
                rows(v, "logicalTypes").push(
                    json!({"kind": "prover_key", "domain": "rows.merkle-keccak256.koala-bear/0"}),
                );
            },
        ),
        ("frame tags are between 1 and 255", |v| {
            rows(v, "frameTags").push(json!({"tag": 256, "layout": "Scalar", "shared": null}));
        }),
        ("duplicate frame tag 1", |v| {
            rows(v, "frameTags").push(json!({"tag": 1, "layout": "Scalar", "shared": null}));
        }),
        ("unknown declaration alternative Matrix", |v| {
            v["frameTags"][0]["layout"] = json!("Matrix");
        }),
        ("unshared frame tag 254 needs exactly one user", |v| {
            rows(v, "frameTags").push(json!({"tag": 254, "layout": "Scalar", "shared": null}));
        }),
        ("unshared frame tag 19 needs exactly one user", |v| {
            codec(v, "zkcv.field.baby-bear/0")["frame"]["tag"] = json!(19);
        }),
        (
            "frame tag 71 must be shared by exactly the proof codecs over poseidon2Rows commitments, at least two",
            |v| {
                // The commitment codecs keep tag 71 while its listing names
                // another kind, so its actual users are unlisted.
                for tag in rows(v, "frameTags") {
                    if tag["tag"] == 71 {
                        tag["shared"]["kind"] = json!("proof");
                    }
                }
            },
        ),
        (
            "frame tag 72 must be shared by exactly the proof codecs over poseidon2Rows commitments, at least two",
            |v| {
                rows(v, "frameTags")
                    .push(json!({"tag": 200, "layout": "DigestProof", "shared": null}));
                codec(v, "zkcv.proof.rows-merkle-poseidon2-8.goldilocks/0")["frame"]["tag"] =
                    json!(200);
            },
        ),
        ("shared frame tags name a declared constructor", |v| {
            for tag in rows(v, "frameTags") {
                if tag["tag"] == 71 {
                    tag["shared"]["kind"] = json!("missing");
                }
            }
        }),
        ("(field, bn254.g1) is not a logical type instance", |v| {
            codec(v, "zkcv.field.koala-bear/0")["domain"] = json!("bn254.g1");
        }),
        ("at most one codec per logical type instance", |v| {
            let mut copy = codec(v, "zkcv.polynomial.koala-bear/0").clone();
            copy["identity"] = json!("zkcv.polynomial.koala-bear/1");
            rows(v, "codecs").push(copy);
        }),
        (
            "Encodes.field must be declared over Codec and the payload sort",
            |v| {
                row(v, "capabilities", "name", "Encodes.field")["parameters"] =
                    json!([{"kind": "Domain", "sort": "Codec"}]);
            },
        ),
        ("Encodes.round is not declared", |v| {
            rows(v, "capabilities").retain(|c| c["name"] != "Encodes.round");
        }),
        ("a message type's codec has a frame", |v| {
            codec(v, "zkcv.field.koala-bear/0")["frame"] = Value::Null;
        }),
        (
            "only message types and the input-only table frame have frames",
            |v| {
                rows(v, "frameTags").push(json!({"tag": 254, "layout": "Vector", "shared": null}));
                codec(v, "zkcv.polynomial.koala-bear/0")["frame"] =
                    json!({"tag": 254, "elementBytes": 4});
            },
        ),
        ("unknown frame tag 254", |v| {
            codec(v, "zkcv.field.koala-bear/0")["frame"]["tag"] = json!(254);
        }),
        ("unknown field elementBytes", |v| {
            codec(v, "zkcv.commitment.rows-merkle-keccak256.koala-bear/0")["frame"]["elementBytes"] =
                json!(32);
        }),
        ("missing field elementBytes", |v| {
            codec(v, "zkcv.field.koala-bear/0")["frame"] = json!({"tag": 19});
        }),
        ("Sequence is not a codec frame layout", |v| {
            codec(v, "zkcv.field.koala-bear/0")["frame"] = json!({"tag": 69});
        }),
        ("vector codecs do not use the Scalar layout", |v| {
            codec(v, "zkcv.vector.koala-bear/0")["frame"]["tag"] = json!(19);
        }),
        ("elementBytes must follow the field structure", |v| {
            codec(v, "zkcv.field.koala-bear/0")["frame"]["elementBytes"] = json!(8);
        }),
        ("elementBytes must follow the field structure", |v| {
            codec(v, "zkcv.matrix.gf2-64.pentanomial-4-3-1.ext3-trinomial1/0")["frame"]["elementBytes"] =
                json!(8);
        }),
        ("gf2-64.pentanomial-4-3-1 has no element width rule", |v| {
            domain(v, "gf2-64.pentanomial-4-3-1")["field"]["structure"]["degree"] = json!(60);
        }),
        (
            "group and groups codecs of bls12-381.g1 must have equal elementBytes",
            |v| {
                codec(v, "zkcv.groups.bls12-381.g1/0")["frame"]["elementBytes"] = json!(96);
            },
        ),
        (
            "sequence and variant frames have the empty domain and field_array frames a Field domain",
            |v| {
                row(v, "aggregateFrames", "constructor", "sequence")["domain"] =
                    json!("koala-bear");
            },
        ),
        (
            "sequence and variant frames have the empty domain and field_array frames a Field domain",
            |v| {
                row(v, "aggregateFrames", "constructor", "field_array")["domain"] =
                    json!("bls12-381.g1");
            },
        ),
        // The field's scalar codec frame encodes the array's elements.
        (
            "field_array frames need a field codec of bls12-381.fr with a Scalar frame",
            |v| {
                rows(v, "codecs").retain(|c| c["identity"] != "zkcv.field.bls12-381.fr/0");
            },
        ),
        ("sequence frames do not use the Variant layout", |v| {
            row(v, "aggregateFrames", "constructor", "sequence")["tag"] = json!(65);
        }),
        ("duplicate aggregate frame (sequence, )", |v| {
            rows(v, "frameTags").push(json!({"tag": 254, "layout": "Sequence", "shared": null}));
            rows(v, "aggregateFrames")
                .push(json!({"constructor": "sequence", "domain": "", "tag": 254}));
        }),
        ("unknown declaration alternative map", |v| {
            row(v, "aggregateFrames", "constructor", "sequence")["constructor"] = json!("map");
        }),
    ];
    refuse(&source(), cases, check);
}

#[test]
fn service_limit_and_vocabulary_mutations_refuse_for_the_stated_rule() {
    let cases: &[Mutation] = &[
        ("random services and rng types correspond one to one", |v| {
            rows(v, "randomServices").retain(|s| s["field"] != "goldilocks.ext2-binomial7");
        }),
        ("random services and rng types correspond one to one", |v| {
            rows(v, "randomServices")
                .push(json!({"contract": "random.koala-bear/0", "field": "koala-bear"}));
        }),
        ("duplicate random service random.bn254.fr/0", |v| {
            v["randomServices"][0]["contract"] = json!("random.bn254.fr/0");
        }),
        ("a random service draws from a declared Field domain", |v| {
            v["randomServices"][0]["field"] = json!("bls12-381.g1");
        }),
        ("duplicate limit protocol.roles", |v| {
            let limit = v["limits"][0].clone();
            rows(v, "limits").push(limit);
        }),
        (
            "limit value must be a JSON integer from 0 to 2^63 - 1",
            |v| {
                v["limits"][0]["value"] = json!("1024");
            },
        ),
        (
            "limit value must be a JSON integer from 0 to 2^63 - 1",
            |v| {
                v["limits"][0]["value"] = json!(-1);
            },
        ),
        (
            "limit value must be a JSON integer from 0 to 2^63 - 1",
            |v| {
                v["limits"][0]["value"] = json!(1_u64 << 63);
            },
        ),
        ("unknown declaration alternative seconds", |v| {
            v["limits"][0]["unit"] = json!("seconds");
        }),
        ("unknown declaration alternative runtime", |v| {
            v["limits"][0]["phase"] = json!("runtime");
        }),
        ("limit owner and scope are nonempty", |v| {
            v["limits"][0]["owner"] = json!("");
        }),
        ("invalid identity", |v| {
            v["limits"][0]["name"] = json!("protocol roles");
        }),
        ("math.fold: collection is null exactly for fold", |v| {
            row(v, "finiteDefinitions", "identity", "math.fold")["collection"] = json!("vector");
        }),
        ("collection is null exactly for fold", |v| {
            row(v, "finiteDefinitions", "identity", "math.collect.vector")["collection"] =
                Value::Null;
        }),
        ("field_array collections are not filtered", |v| {
            row(
                v,
                "finiteDefinitions",
                "identity",
                "local.collect.field_array",
            )["filtered"] = json!(true);
        }),
        ("duplicate finite definition math.fold", |v| {
            row(v, "finiteDefinitions", "identity", "local.fold")["identity"] = json!("math.fold");
        }),
        ("unknown declaration alternative global", |v| {
            row(v, "finiteDefinitions", "identity", "math.fold")["mode"] = json!("global");
        }),
        ("unknown declaration alternative matrix", |v| {
            row(v, "finiteDefinitions", "identity", "math.collect.vector")["collection"] =
                json!("matrix");
        }),
        ("axis is 0 or 1", |v| {
            row(v, "domainConstructors", "identity", "zip")["axis"] = json!(2);
        }),
        ("unknown declaration alternative Columns", |v| {
            row(v, "domainConstructors", "identity", "zip")["kind"] = json!("Columns");
        }),
        ("duplicate domain constructor range", |v| {
            row(v, "domainConstructors", "identity", "zip")["identity"] = json!("range");
        }),
        (
            "a parameter collection element needs a Field, Group or Type first parameter",
            |v| {
                row(v, "types", "name", "bool")["collection"] =
                    json!({"rank": 1, "element": "parameter"});
            },
        ),
        // The installation document's references are checked against the
        // declarations: an instance it names must remain declared.
        ("undeclared logical type instance", |v| {
            rows(v, "logicalTypes")
                .retain(|t| !(t["kind"] == "nonce" && t["domain"] == "bls12-381.fr"));
        }),
    ];
    refuse(&source(), cases, check);
}

#[test]
fn native_installation_mutations_refuse_for_the_stated_rule() {
    let cases: &[Mutation] = &[
        ("undeclared logical type instance", |v| {
            representation(v, "arkworks.point/0", "point", "bls12-381.fr")["domain"] =
                json!("bn254.fr");
        }),
        ("duplicate representation", |v| {
            let copy = representation(v, "blst/fr", "field", "bls12-381.fr").clone();
            rows(v, "representations").push(copy);
        }),
        ("second default representation", |v| {
            representation(v, "arkworks.mle-msb/0", "table", "bls12-381.fr")["default"] =
                json!(true);
        }),
        ("(point, bls12-381.fr) has no default representation", |v| {
            representation(v, "arkworks.point/0", "point", "bls12-381.fr")["default"] =
                json!(false);
        }),
        ("layout lsb is selected twice for one instance", |v| {
            representation(v, "arkworks.mle-msb/0", "table", "bls12-381.fr")["layout"] =
                json!("lsb");
        }),
        ("invalid identity", |v| {
            representation(v, "arkworks.mle-msb/0", "table", "bls12-381.fr")["layout"] =
                json!("most significant");
        }),
        ("invalid identity", |v| {
            representation(v, "blst/fr", "field", "bls12-381.fr")["identity"] = json!("");
        }),
        (
            "the default of an instance with a framed codec is canonical",
            |v| {
                representation(v, "plonky3.koala-bear/0", "field", "koala-bear")["frame"] =
                    json!("local");
            },
        ),
        // The table input codec's frame counts as a codec frame.
        (
            "the default of an instance with a framed codec is canonical",
            |v| {
                representation(v, "arkworks.mle-lsb/0", "table", "bls12-381.fr")["frame"] =
                    json!("local");
            },
        ),
        ("a canonical representation requires a framed codec", |v| {
            representation(v, "arkworks.polynomial/0", "polynomial", "bls12-381.fr")["frame"] =
                json!("canonical");
        }),
        ("a canonical representation requires a framed codec", |v| {
            representation(v, "host.resource/0", "rng", "bls12-381.fr")["frame"] =
                json!("canonical");
        }),
        (
            "the default of a unary instance has the unit of its domain's default provider",
            |v| {
                representation(v, "arkworks.fr/0", "field", "bls12-381.fr")["unit"] = json!("blst");
            },
        ),
        (
            "the default of a nullary instance has unit independent",
            |v| {
                representation(v, "native.bool/0", "bool", "")["unit"] = json!("arkworks");
            },
        ),
        ("unknown declaration alternative remote", |v| {
            representation(v, "blst/fr", "field", "bls12-381.fr")["frame"] = json!("remote");
        }),
        ("unknown declaration alternative native", |v| {
            representation(v, "blst/fr", "field", "bls12-381.fr")["unit"] = json!("native");
        }),
        ("undeclared constructor", |v| {
            v["appliedRepresentations"][0]["constructor"] = json!("missing");
        }),
        (
            "applied representations need a constructor with parameters",
            |v| {
                v["appliedRepresentations"][0]["constructor"] = json!("bool");
                v["appliedRepresentations"][0]["arguments"] = json!([]);
                v["appliedRepresentations"][0]["child"] = Value::Null;
            },
        ),
        ("one pattern per parameter", |v| {
            rows(&mut v["appliedRepresentations"][0], "arguments").pop();
        }),
        ("pattern does not match its parameter kind", |v| {
            v["appliedRepresentations"][0]["arguments"][1] =
                json!(["domain", "Field", "bls12-381.fr"]);
        }),
        ("domain pattern must name a declared Field domain", |v| {
            v["appliedRepresentations"][0]["arguments"][0] = json!(["domain", "Field", "bn254.g1"]);
        }),
        ("natural range minimum exceeds its maximum", |v| {
            v["appliedRepresentations"][0]["arguments"][1] = json!(["natRange", "5", "4"]);
        }),
        ("natural range bound above 1,048,576", |v| {
            v["appliedRepresentations"][0]["arguments"][1] = json!(["natRange", "0", "1048577"]);
        }),
        ("noncanonical natural", |v| {
            v["appliedRepresentations"][0]["arguments"][1] = json!(["natRange", "00", "1"]);
        }),
        (
            "(missing, ) is not an admitted logical type instance",
            |v| {
                v["appliedRepresentations"][2]["arguments"][0] =
                    json!(["type", ["apply", "missing", []]]);
            },
        ),
        (
            "(rng, koala-bear) is not an admitted logical type instance",
            |v| {
                v["appliedRepresentations"][2]["arguments"][0] = json!([
                    "type",
                    ["apply", "rng", [["domain", "Field", "koala-bear"]]]
                ]);
            },
        ),
        ("field_array pattern is not a logical type instance", |v| {
            v["appliedRepresentations"][2]["arguments"][0] = json!([
                "type",
                [
                    "apply",
                    "field_array",
                    [["domain", "Field", "bls12-381.fr"], ["nat", "4"]]
                ]
            ]);
        }),
        (
            "field pattern argument must name a declared domain of its sort",
            |v| {
                v["appliedRepresentations"][2]["arguments"][0] = json!([
                    "type",
                    ["apply", "field", [["domain", "Field", "bn254.g1"]]]
                ]);
            },
        ),
        ("field pattern argument is not a domain", |v| {
            v["appliedRepresentations"][2]["arguments"][0] =
                json!(["type", ["apply", "field", [["nat", "1"]]]]);
        }),
        (
            "Type patterns are constructor applications, never variant, oracle or service trees",
            |v| {
                v["appliedRepresentations"][2]["arguments"][0] =
                    json!(["type", ["variant", ["atom", "Choice"], [["some", []]]]]);
            },
        ),
        (
            "Type patterns are constructor applications, never variant, oracle or service trees",
            |v| {
                v["appliedRepresentations"][2]["arguments"][0] =
                    json!(["type", ["oracle", "vector", []]]);
            },
        ),
        ("Type patterns are constructor applications", |v| {
            v["appliedRepresentations"][2]["arguments"][0] =
                json!(["type", ["service", "random.bls12-381.fr/0"]]);
        }),
        ("child names no representation row", |v| {
            v["appliedRepresentations"][0]["child"]["representation"] = json!("missing");
        }),
        ("child is not the logical child of the applied type", |v| {
            v["appliedRepresentations"][3]["child"] =
                json!({"kind": "field", "domain": "bls12-381.fr", "representation": "blst/fr"});
        }),
        ("child is not the logical child of the applied type", |v| {
            v["appliedRepresentations"][4]["child"] = json!(
                {"kind": "field", "domain": "koala-bear", "representation": "plonky3.koala-bear/0"}
            );
        }),
        ("overlapping patterns share an identity or a default", |v| {
            v["appliedRepresentations"][1]["default"] = json!(true);
        }),
        ("overlapping patterns share an identity or a default", |v| {
            v["appliedRepresentations"][1]["identity"] = json!("arkworks.field-array/0");
        }),
        (
            "a canonical applied representation requires an aggregate frame for its constructor",
            |v| {
                v["appliedRepresentations"][3]["frame"] = json!("canonical");
            },
        ),
        (
            "a canonical applied representation requires an aggregate frame for its constructor",
            |v| {
                v["appliedRepresentations"][6]["frame"] = json!("canonical");
            },
        ),
        // A field_array frame belongs to its exact field: koala-bear has none.
        (
            "a canonical applied representation requires an aggregate frame for its constructor",
            |v| {
                let applied = &mut v["appliedRepresentations"][0];
                applied["arguments"][0] = json!(["domain", "Field", "koala-bear"]);
                applied["child"] = json!(
                    {"kind": "field", "domain": "koala-bear", "representation": "plonky3.koala-bear/0"}
                );
                applied["provider"] = json!("plonky3");
                applied["unit"] = json!("plonky3");
                applied["vectorPort"] = json!(
                    {"kind": "vector", "domain": "koala-bear", "representation": "plonky3.koala-bear-vector/0"}
                );
            },
        ),
        ("goldilocks has no provider row", |v| {
            rows(v, "providers").retain(|p| p["domain"] != "goldilocks");
        }),
        ("koala-bear has more than one provider row", |v| {
            let copy = row(v, "providers", "domain", "koala-bear").clone();
            rows(v, "providers").push(copy);
        }),
        ("bn254.fr: provider arkworks appears twice", |v| {
            row(v, "providers", "domain", "bn254.fr")["alternatives"] = json!(["arkworks"]);
        }),
        ("unknown declaration alternative risc0", |v| {
            row(v, "providers", "domain", "koala-bear")["default"] = json!("risc0");
        }),
        ("missing is not a declared domain", |v| {
            row(v, "providers", "domain", "koala-bear")["domain"] = json!("missing");
        }),
        ("spongefish has no installation unit row", |v| {
            rows(v, "providerUnits").retain(|u| u["provider"] != "spongefish");
        }),
        ("blst has no installation unit row", |v| {
            rows(v, "providerUnits").retain(|u| u["provider"] != "blst");
        }),
        ("plonky3 has more than one unit row", |v| {
            let copy = row(v, "providerUnits", "provider", "plonky3").clone();
            rows(v, "providerUnits").push(copy);
        }),
        ("spongefish is installed by the arkworks unit", |v| {
            row(v, "providerUnits", "provider", "spongefish")["unit"] = json!("plonky3");
        }),
        ("independent is the unit of provider-free storage", |v| {
            row(v, "providerUnits", "provider", "plonky3")["unit"] = json!("independent");
        }),
        (
            "koala-bear: arithmetic names the default representation of its field instance",
            |v| {
                row(v, "fieldForms", "field", "koala-bear")["arithmetic"]["representation"] =
                    json!("plonky3.koala-bear-vector/0");
            },
        ),
        ("unknown declaration alternative montgomery", |v| {
            row(v, "fieldForms", "field", "koala-bear")["arithmetic"]["form"] = json!("montgomery");
        }),
        ("koala-bear: wordBytes * 8 must equal radixBits", |v| {
            row(v, "fieldForms", "field", "koala-bear")["montgomery"]["radixBits"] = json!(31);
        }),
        ("koala-bear: montgomery requires an arithmetic row", |v| {
            row(v, "fieldForms", "field", "koala-bear")["arithmetic"] = Value::Null;
        }),
        (
            "goldilocks: montgomery requires a characteristic below 2^radixBits",
            |v| {
                row(v, "fieldForms", "field", "goldilocks")["montgomery"] =
                    json!({"wordBytes": 4, "radixBits": 32});
            },
        ),
        (
            "koala-bear: byteEncoding names the framed field codec of its field",
            |v| {
                row(v, "fieldForms", "field", "koala-bear")["byteEncoding"]["codec"] =
                    json!("zkcv.vector.koala-bear/0");
            },
        ),
        ("unknown declaration alternative bigEndian", |v| {
            row(v, "fieldForms", "field", "koala-bear")["byteEncoding"]["order"] =
                json!("bigEndian");
        }),
        ("bn254.g1 is not a declared Field domain", |v| {
            row(v, "fieldForms", "field", "koala-bear")["field"] = json!("bn254.g1");
        }),
        ("goldilocks has more than one field form", |v| {
            let copy = row(v, "fieldForms", "field", "goldilocks").clone();
            rows(v, "fieldForms").push(copy);
        }),
        ("missing.operation is not a declared operation", |v| {
            v["physicalArguments"][0]["operation"] = json!("missing.operation");
        }),
        ("sequence.at is listed twice", |v| {
            rows(v, "physicalArguments").push(json!({"operation": "sequence.at"}));
        }),
    ];
    refuse(&installation(), cases, check_installation);
}
