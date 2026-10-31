#[path = "../codegen/projection.rs"]
mod projection;

use serde_json::{Value, json};
use std::collections::BTreeMap;
use zkc_catalog::{CATALOG, Facet, Kind, NumericalResult, Signature, Term};

fn source() -> Value {
    serde_json::from_str(include_str!("../../../common/catalog/declarations.json")).unwrap()
}
fn check(value: &Value) -> Result<String, String> {
    projection::generate(&serde_json::to_vec(value).unwrap())
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
        ["index", "bool", "field", "vector"]
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
    ];
    assert_eq!(profile.operations.len(), expected.len());
    for (entry, (name, field)) in profile.operations.iter().zip(expected) {
        assert_eq!(entry.operation, name);
        assert_eq!(
            entry.static_parameters,
            if field {
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
    let original = source();
    let mut cases = BTreeMap::new();
    shapes(&original, String::new(), &mut cases);
    assert!(cases.len() > 30);
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

#[test]
fn duplicate_keys_and_noninteger_counts_refuse() {
    let text = serde_json::to_string(&source()).unwrap();
    let duplicate = text.replacen('{', "{\"format\":\"zkc.contract-declarations/0\",", 1);
    assert!(
        projection::generate(duplicate.as_bytes())
            .unwrap_err()
            .contains("duplicate key")
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
