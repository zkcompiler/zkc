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
        [Facet::Diagonal {
            factors_input: 0,
            values_input: 1,
            result_output: 0
        }]
    ));
    assert_eq!(check(&value).unwrap(), check(&value).unwrap());
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
