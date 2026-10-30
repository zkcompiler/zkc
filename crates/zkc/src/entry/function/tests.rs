//! Source metadata semantics must remain checked in a portable application.
use super::*;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

fn digest(bytes: &[u8]) -> String {
    crate::io::bytes::hex(&Sha256::digest(bytes))
}
fn schema(kind: &str, spelling: &str) -> Value {
    json!({"kind":kind,"type":spelling,"identity":digest(spelling.as_bytes()),
        "custody":false,"constructible":true,"permissions":["Copy","Drop"],
        "fields":[],"alternatives":[],"leaves":[spelling]})
}
fn document(schema: Value) -> Value {
    json!({"format":"zkc.language-interface/0","capture":digest(b"source capture"),
        "original":digest(b"original source"),"toolchain":"test","entry":"example::Main",
        "selection":{"kind":"function","function":"example::Main"},
        "functions":[{"symbol":"example::Main","parameters":[{"name":"value","schema":schema}],
            "result":{"kind":"unit","type":"()","identity":digest(b"()"),"custody":false,
                "constructible":true,"permissions":["Copy","Drop"],"fields":[],"alternatives":[],"leaves":[]}}],
        "protocols":[],"relations":[],"setups":[]})
}
fn read(document: Value) -> Result<FunctionInterface> {
    let bytes = json!({"format":"zkc.entry/0","original":"original source",
        "interface":document.to_string(),"artifact":"not interpreted by source inspection","assets":[],
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
            "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true}}).to_string();
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
