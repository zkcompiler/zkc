//! Source metadata semantics must remain checked in a portable application.
use super::*;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

fn digest(bytes: &[u8]) -> String {
    crate::io::bytes::hex(&Sha256::digest(bytes))
}
fn schema(kind: &str, spelling: &str) -> Value {
    json!({"kind":kind,"type":spelling,"identity":digest(spelling.as_bytes()),
        "generated":null,"custody":0,"sealed":false,"roles":[],"element":null,"constructible":true,"permissions":["Copy","Drop"],
        "fields":[],"alternatives":[],"leaves":[spelling]})
}
fn document(schema: Value) -> Value {
    json!({"format":"zkc.language-interface/0","capture":digest(b"source capture"),
        "original":digest(b"original source"),"toolchain":"test","entry":"example::Main",
        "selection":{"kind":"function","function":"example::Main"},
        "functions":[{"symbol":"example::Main","parameters":[{"name":"value","schema":schema}],
            "result":{"kind":"unit","type":"()","identity":digest(b"()"),"generated":null,"custody":0,"sealed":false,"roles":[],"element":null,
                "constructible":true,"permissions":["Copy","Drop"],"fields":[],"alternatives":[],"leaves":[]}}],
        "protocols":[],"relations":[],"setups":[]})
}
fn read(document: Value) -> Result<FunctionInterface> {
    let bytes = json!({"format":"zkc.entry/0","original":"original source",
        "interface":document.to_string(),"artifact":"not interpreted by source inspection","assets":[],
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
            "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization":crate::entry::OracleSelection::default()}}).to_string();
    let package = Package::capture(
        bytes.as_bytes(),
        &Sha256::digest(bytes.as_bytes()).into(),
        Package::MAX_BYTES,
    )?;
    FunctionInterface::read(&package)
}

#[test]
fn source_inspection_does_not_require_a_native_program_or_installed_domain_pair() {
    let view = read(document(schema("boolean", "bool"))).unwrap();
    assert_eq!(view.entry(), "example::Main");
    view.check_input(&view.signature().parameters[0].schema)
        .unwrap();
    assert!(view.input_group().template().is_object());
    // A declared Field argument is meaningful to metadata even when the native
    // owner has no table implementation for this field. It is not message data.
    let view = read(document(schema("builtin", "table:koala-bear"))).unwrap();
    assert_eq!(
        view.check_input(&view.signature().parameters[0].schema)
            .unwrap_err()
            .code(),
        "entry-input-codec"
    );
    assert!(!view.result_requires_setup());
}

#[test]
fn source_inspection_keeps_identity_permissions_and_constructor_checks() {
    for spelling in [
        "field:unknown",
        "field:bn254.g1",
        "[\"field\",\"koala-bear\"]",
    ] {
        assert!(
            read(document(schema("field", spelling))).is_err(),
            "{spelling}"
        );
    }
    let mut bad = document(schema("boolean", "bool"));
    bad["original"] = json!(digest(b"another source"));
    assert_eq!(read(bad).unwrap_err().code(), "entry-host-identity");
    let mut bad = document(schema("boolean", "bool"));
    bad["functions"][0]["parameters"][0]["schema"]["permissions"] = json!(["Copy"]);
    assert_eq!(read(bad).unwrap_err().code(), "entry-interface-schema");
    let bad = document(schema("builtin", "prover_key:multilinear.kzg.bls12-381/0"));
    assert_eq!(read(bad).unwrap_err().code(), "entry-interface-schema");
}

#[test]
fn host_signatures_refuse_logical_handles_sequences_and_records() {
    for kind in ["oracle", "oracle_sequence", "logical_record"] {
        let mut logical = schema("oracle", "Logical");
        logical["constructible"] = json!(false);
        logical["leaves"] = json!([]);
        logical["oracle"] = json!({"kind":"table","arguments":[["type","bool"],["nat","0"]]});
        logical["data_schema"] = schema("builtin", "sequence<bool>");
        if kind == "oracle_sequence" {
            logical["kind"] = json!(kind);
            logical["maximum"] = json!("0");
            logical["data_schema"] = schema("builtin", "sequence<sequence<bool>>");
        } else if kind == "logical_record" {
            let child = logical;
            logical = schema(kind, "State");
            logical["constructible"] = json!(false);
            logical["leaves"] = json!([]);
            logical["roles"] = json!(["H", "R"]);
            logical["fields"] = json!([{"name":"word","offset":0,"public":true,"placement":{"kind":"oracle","holder":0,"receivers":[1]},"schema":child}]);
        }
        for output in [false, true] {
            let mut d = document(logical.clone());
            if output {
                d["functions"][0]["result"] = logical.clone();
                d["functions"][0]["parameters"] = json!([]);
            }
            assert_eq!(
                read(d).unwrap_err().code(),
                "entry-host-schema",
                "{kind} output={output}"
            );
        }
    }
}

#[test]
fn host_schemas_require_sealing_and_generated_metadata_in_every_position() {
    let original = document(schema("boolean", "bool"));
    for path in ["/functions/0/parameters/0/schema", "/functions/0/result"] {
        for member in ["sealed", "generated"] {
            let mut bad = original.clone();
            bad.pointer_mut(path)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .remove(member);
            assert_eq!(
                read(bad).unwrap_err().code(),
                "entry-host-format",
                "{path}/{member}"
            );
        }
        for malformed in [json!(null), json!(0), json!("false")] {
            let mut bad = original.clone();
            bad.pointer_mut(path).unwrap()["sealed"] = malformed;
            assert_eq!(read(bad).unwrap_err().code(), "entry-host-format");
        }
        let mut bad = original.clone();
        bad.pointer_mut(path).unwrap()["sealed"] = json!(true);
        assert_eq!(read(bad).unwrap_err().code(), "entry-interface-schema");
    }
}

#[test]
fn generated_path_aliases_keep_the_source_field_identifier_limit() {
    let alias = format!("{}_{}", "x".repeat(48), "a".repeat(64));
    let mut record = schema("record", "example::Demo::Public");
    record["generated"] = json!(digest(b"generated family"));
    record["leaves"] = json!(["bool"]);
    record["fields"] = json!([{"name":alias,"offset":0,"public":true,"placement":null,"schema":schema("boolean","bool")}]);
    let view = read(document(record.clone())).unwrap();
    view.check_input(&view.signature().parameters[0].schema)
        .unwrap();
    record["fields"][0]["name"] = json!("x".repeat(129));
    assert!(read(document(record.clone())).is_err());
    record["generated"] = Value::Null;
    assert!(read(document(record)).is_err());
}
