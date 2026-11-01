use super::*;
use crate::entry::interface::{raw::*, schemas};
use serde_json::json;
use sha2::{Digest, Sha256};

fn schema(kind: &str, name: &str, leaves: serde_json::Value) -> Schema {
    serde_json::from_value(json!({"kind":kind,"identity":crate::io::bytes::hex(&Sha256::digest(name.as_bytes())),
        "type":name,"generated":null,"custody":0,"sealed":false,"roles":[],"element":null,"constructible":true,
        "permissions":["Copy","Drop"],"fields":[],"alternatives":[],"leaves":leaves})).unwrap()
}
fn index() -> Schema {
    schema("index", "index", json!(["index"]))
}
fn unit() -> Schema {
    schema("unit", "()", json!([]))
}
fn record(name: &str, fields: Vec<(&str, bool, Schema)>) -> Schema {
    let mut s = schema("record", name, json!([]));
    for (name, public, child) in fields {
        s.fields.push(Field {
            name: name.into(),
            public,
            offset: s.leaves.len() as u32,
            placement: None,
            maximum_rows: Default::default(),
            schema: child.clone(),
        });
        s.leaves.extend(child.leaves);
        s.constructible &= public && child.constructible;
    }
    s
}
fn output(s: &Schema, values: Vec<NativeValue>) -> Value {
    let mut inventory = schemas::Schemas::new();
    inventory.check(s, 0).unwrap();
    let mut values = values.into_iter();
    let value = collect(s, &mut values).unwrap();
    assert!(values.next().is_none());
    value
}
fn opaque(value: Value) -> OpaqueValue {
    let Value::Opaque(value) = value else {
        panic!("expected opaque storage")
    };
    value
}
#[test]
fn mixed_record_exposes_only_public_children_and_retains_exact_transport() {
    let secret = record("Secret", vec![("hidden", false, index())]);
    let mixed = record(
        "Mixed",
        vec![
            ("visible", true, index()),
            ("child", true, secret),
            ("sibling", false, index()),
        ],
    );
    let value = opaque(output(
        &mixed,
        vec![
            NativeValue::Index(5),
            NativeValue::Index(173),
            NativeValue::Index(281),
        ],
    ));
    assert_eq!(u64::try_from(value.field("visible").unwrap()).unwrap(), 5);
    assert_eq!(
        value.field("sibling").unwrap_err(),
        "entry-value-projection"
    );
    assert_eq!(
        opaque(value.field("child").unwrap())
            .field("hidden")
            .unwrap_err(),
        "entry-value-projection"
    );
    assert_eq!(
        value.field("child.hidden").unwrap_err(),
        "entry-value-projection"
    );
    let debug = format!("{value:?}");
    assert!(!debug.contains("173") && !debug.contains("281") && !debug.contains("hidden"));
    let mut flat = Vec::new();
    flatten(&mixed, Value::Opaque(value.clone()), &mut flat).unwrap();
    assert_eq!(flat.len(), 3);
    let mut forged = mixed.clone();
    forged.identity = crate::io::bytes::hex(&Sha256::digest(b"SameLayout"));
    assert_eq!(
        flatten(&forged, Value::Opaque(value.clone()), &mut vec![]).unwrap_err(),
        "entry-value-schema"
    );
    forged = mixed.clone();
    forged.fields[2].public = true;
    assert_eq!(
        flatten(&forged, Value::Opaque(value.clone()), &mut vec![]).unwrap_err(),
        "entry-value-schema"
    );
    assert_eq!(
        check_readable(&Value::Opaque(value)).unwrap_err(),
        "entry-output-opaque"
    );
}
#[test]
fn sealed_and_hidden_ancestors_block_even_public_descendants() {
    let child = record("Child", vec![("visible", true, index())]);
    let mut sealed = record("Sealed", vec![("child", true, child.clone())]);
    sealed.sealed = true;
    sealed.constructible = false;
    let value = opaque(output(&sealed, vec![NativeValue::Index(7)]));
    assert_eq!(value.field("child").unwrap_err(), "entry-value-projection");
    let hidden = record("Hidden", vec![("child", false, child)]);
    let value = opaque(output(&hidden, vec![NativeValue::Index(7)]));
    assert_eq!(value.field("child").unwrap_err(), "entry-value-projection");
    assert_eq!(
        value.field("child.visible").unwrap_err(),
        "entry-value-projection"
    );
}
#[test]
fn empty_private_fields_and_array_element_authority_are_retained() {
    let empty = record("Empty", vec![("private", false, unit())]);
    let value = output(&empty, vec![]);
    assert_eq!(
        flatten(
            &empty,
            Value::Record([("private".into(), Value::Unit)].into()),
            &mut vec![]
        )
        .unwrap_err(),
        "entry-input-constructor"
    );
    flatten(&empty, value, &mut vec![]).unwrap();
    let mut array = schema("array", "[Empty;0]", json!([]));
    array.element = Some(Box::new(empty));
    array.constructible = false;
    let value = output(&array, vec![]);
    assert!(matches!(value, Value::Opaque(_)));
    assert_eq!(
        flatten(&array, Value::Array(vec![]), &mut vec![]).unwrap_err(),
        "entry-input-constructor"
    );
    flatten(&array, value, &mut vec![]).unwrap();
}
#[test]
fn variant_payloads_and_associated_representations_do_not_erase_barriers() {
    let secret = record("Secret", vec![("hidden", false, index())]);
    let name = "Choice";
    let native = zkc_test_support::variants::encode_tree(json!([
        [
            "zkc.language",
            crate::source_names::encode_nominal_identity(name)
        ],
        [["case00000000", ["index"]]]
    ]));
    let mut s = schema("variant", name, json!([native]));
    s.constructible = false;
    s.alternatives = vec![Alternative {
        name: "Some".into(),
        fields: vec![Field {
            name: "0".into(),
            public: true,
            offset: 0,
            placement: None,
            maximum_rows: Default::default(),
            schema: secret,
        }],
    }];
    let ty = zkc_runtime::vm::PhysicalType::default_for(
        zkc_runtime::vm::LogicalType::parse(&s.leaves[0]).unwrap(),
    )
    .unwrap();
    let variant =
        NativeValue::Variant(zkc_cpu::Variant::new(ty, 0, vec![NativeValue::Index(19)]).unwrap());
    let value = opaque(output(&s, vec![variant.clone()]));
    assert_eq!(value.alternative().unwrap(), "Some");
    assert_eq!(
        value.variant_field("Other", "0").unwrap_err(),
        "entry-value-alternative"
    );
    assert_eq!(
        opaque(value.variant_field("Some", "0").unwrap())
            .field("hidden")
            .unwrap_err(),
        "entry-value-projection"
    );
    let mut fields = Vec::new();
    flatten(&s, Value::Opaque(value), &mut fields).unwrap();
    assert_eq!(fields.len(), 1);
    s.sealed = true;
    let value = opaque(output(&s, vec![variant]));
    assert_eq!(value.alternative().unwrap_err(), "entry-value-projection");
    let mut associated = record("Alias", vec![("value", true, index())]);
    associated.kind = Kind::Associated;
    associated.constructible = false;
    let value = opaque(output(&associated, vec![NativeValue::Index(7)]));
    assert_eq!(value.field("value").unwrap_err(), "entry-value-projection");
    flatten(&associated, Value::Opaque(value), &mut vec![]).unwrap();
}
#[test]
fn custody_and_logical_values_never_acquire_an_ordinary_owner() {
    for mut s in [unit(), record("NonCopy", vec![])] {
        s.permissions.clear();
        assert_eq!(
            collect(&s, &mut [].into_iter()).unwrap_err(),
            "entry-output-custody"
        );
    }
    let mut s = record("Custody", vec![]);
    s.custody = 1;
    assert_eq!(
        collect(&s, &mut [].into_iter()).unwrap_err(),
        "entry-output-custody"
    );
    s.kind = Kind::LogicalRecord;
    assert_eq!(
        collect(&s, &mut [].into_iter()).unwrap_err(),
        "entry-output-custody"
    );
}

fn package(document: &serde_json::Value, artifact: &str) -> crate::entry::Package {
    let bytes = json!({"format":"zkc.entry/0","original":"original","interface":document.to_string(),"artifact":artifact,"assets":[],
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization":crate::entry::OracleSelection::default()}}).to_string();
    crate::entry::Package::capture(
        bytes.as_bytes(),
        &Sha256::digest(bytes.as_bytes()).into(),
        crate::entry::Package::MAX_BYTES,
    )
    .unwrap()
}
fn replace_output(document: &mut serde_json::Value, port: usize, schema: &Schema) {
    let p = &mut document["protocols"][0]["outputs"][port];
    p["schema"] = schema.describe();
    p["type"] = json!(schema.display_type);
    for component in p["components"].as_array_mut().unwrap() {
        component["path"] = json!([0]);
    }
}
#[test]
fn normal_run_and_proof_output_collection_retain_private_storage() {
    use crate::entry::*;
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let secret = record("BooleanSecret", vec![("hidden", false, boolean.clone())]);
    let (mut doc, artifact) = crate::entry::interface::tests::unicode::run_fixture(
        &boolean.describe(),
        &["P"],
        &["role00000000"],
    );
    replace_output(&mut doc, 0, &secret);
    let host = RunEntry::admit(
        package(&doc, &artifact),
        Default::default(),
        Default::default(),
    )
    .unwrap();
    let report = host
        .prepare(RunRequest {
            session: "opaque-run".into(),
            roles: [(
                "P".into(),
                RoleInputs {
                    inputs: [("入力".into(), true.into())].into(),
                    ..Default::default()
                },
            )]
            .into(),
            setups: Default::default(),
        })
        .unwrap()
        .execute();
    assert!(report.is_success(), "{:?}", report.output_error);
    assert!(
        report
            .native
            .execution
            .as_ref()
            .unwrap()
            .roles
            .iter()
            .all(|r| r.outputs.is_empty())
    );
    let outputs = report.outputs.unwrap();
    assert!(matches!(outputs["P"]["結果"], Value::Opaque(_)));
    assert_eq!(
        outputs["P"]["結果"].field("hidden").unwrap_err(),
        "entry-value-projection"
    );
    let (mut doc, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
    replace_output(&mut doc, 1, &secret);
    let host = ProofEntry::admit(
        package(&doc, &artifact),
        ProofOptions {
            binding: BindingPolicy::AllowAuthored,
            ..Default::default()
        },
        Default::default(),
    )
    .unwrap();
    let report = host
        .prove(ProofRequest {
            public: [("公開".into(), true.into())].into(),
            private: RoleInputs {
                inputs: [("秘密".into(), false.into())].into(),
                ..Default::default()
            },
            context: vec![],
            transcript_budget: Some(0),
            setups: Default::default(),
        })
        .unwrap();
    assert!(report.is_success(), "{:?}", report.output_error);
    assert!(report.native.outputs.is_none());
    assert!(matches!(report.outputs.unwrap()["結果"], Value::Opaque(_)));
    assert_eq!(
        host.check_result_encoding(ProofOperation::Prove)
            .unwrap_err(),
        "entry-output-opaque"
    );
    assert!(host.check_result_encoding(ProofOperation::Verify).is_ok());
}

#[test]
fn public_enum_constructor_accepts_retained_children_without_minting_them() {
    let child = record("SecretPayload", vec![("hidden", false, index())]);
    let native = zkc_test_support::variants::encode_tree(json!([
        [
            "zkc.language",
            crate::source_names::encode_nominal_identity("PublicChoice")
        ],
        [["case00000000", ["index"]]]
    ]));
    let mut s = schema("variant", "PublicChoice", json!([native]));
    s.alternatives = vec![Alternative {
        name: "Some".into(),
        fields: vec![Field {
            name: "0".into(),
            public: true,
            offset: 0,
            placement: None,
            maximum_rows: Default::default(),
            schema: child.clone(),
        }],
    }];
    let retained = output(&child, vec![NativeValue::Index(7)]);
    let mut flat = vec![];
    flatten(
        &s,
        Value::Variant {
            alternative: "Some".into(),
            fields: [("0".into(), retained)].into(),
        },
        &mut flat,
    )
    .unwrap();
    assert_eq!(flat.len(), 1);
    assert_eq!(
        flatten(
            &s,
            Value::Variant {
                alternative: "Some".into(),
                fields: [(
                    "0".into(),
                    Value::Record([("hidden".into(), 7u64.into())].into())
                )]
                .into()
            },
            &mut vec![]
        )
        .unwrap_err(),
        "entry-input-constructor"
    );
}
#[test]
fn public_nonconstructible_results_still_export_but_do_not_grant_input_authority() {
    let mut s = record("ProjectionOnly", vec![("visible", true, index())]);
    s.constructible = false;
    let owner = opaque(output(&s, vec![NativeValue::Index(11)]));
    let bytes = crate::entry::outputs::function_output(
        &Value::Opaque(owner.clone()),
        Default::default(),
        Default::default(),
    )
    .unwrap();
    let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(json["value"]["visible"], "11");
    assert_eq!(
        flatten(
            &s,
            Value::Record([("visible".into(), 11u64.into())].into()),
            &mut vec![]
        )
        .unwrap_err(),
        "entry-input-constructor"
    );
    flatten(&s, Value::Opaque(owner), &mut vec![]).unwrap();
}

fn fingerprint_schema() -> Schema {
    let empty = record("HiddenEmpty", vec![("hidden", false, unit())]);
    let mut array = schema("array", "[HiddenEmpty;0]", json!([]));
    array.element = Some(Box::new(empty));
    array.constructible = false;
    record(
        "Envelope",
        vec![("values", true, array), ("marker", false, unit())],
    )
}

#[test]
fn binding_fingerprint_has_stable_canonical_bytes_and_keeps_authority() {
    let original = fingerprint_schema();
    let fingerprint = schema_fingerprint(&original);
    // Independent recursively sorted compact-JSON vector, including an empty
    // array's private element template. Default-generated bindings keep this hash.
    assert_eq!(
        crate::io::bytes::hex(&fingerprint),
        "978f56cdd3753bb425260130a347135dd07b2b6a9da6e73f987948b003d81138"
    );
    type Mutation = fn(&mut Schema);
    let mutations: &[(&str, Mutation)] = &[
        ("privacy", |s| s.fields[0].public = false),
        ("sealing", |s| s.sealed = true),
        ("construction", |s| s.constructible = true),
        ("permissions", |s| s.permissions.clear()),
        ("custody", |s| s.custody = 1),
        ("nominal identity", |s| s.identity = index().identity),
        ("generated identity", |s| {
            s.generated = Some(index().identity)
        }),
        ("field name", |s| s.fields[0].name = "changed".into()),
        ("field offset", |s| s.fields[0].offset = 1),
        ("field order", |s| s.fields.swap(0, 1)),
        ("empty element identity", |s| {
            s.fields[0].schema.element.as_mut().unwrap().identity = unit().identity;
        }),
        ("nested privacy", |s| {
            s.fields[0].schema.element.as_mut().unwrap().fields[0].public = true;
        }),
        ("nested sealing", |s| {
            s.fields[0].schema.element.as_mut().unwrap().sealed = true;
        }),
    ];
    for (name, mutate) in mutations {
        let mut changed = original.clone();
        mutate(&mut changed);
        assert_ne!(schema_fingerprint(&changed), fingerprint, "{name}");
    }
}

#[test]
fn binding_fingerprint_includes_nested_alternative_payloads() {
    let mut variant = schema("variant", "Choice", json!([]));
    variant.alternatives = vec![Alternative {
        name: "Some".into(),
        fields: fingerprint_schema().fields,
    }];
    let fingerprint = schema_fingerprint(&variant);
    let mut changed = variant.clone();
    changed.alternatives[0].fields[0]
        .schema
        .element
        .as_mut()
        .unwrap()
        .fields[0]
        .public = true;
    assert_ne!(schema_fingerprint(&changed), fingerprint);
    let mut changed = variant.clone();
    changed.alternatives[0].fields.swap(0, 1);
    assert_ne!(schema_fingerprint(&changed), fingerprint);
    variant.alternatives[0].name = "Changed".into();
    assert_ne!(schema_fingerprint(&variant), fingerprint);
}
