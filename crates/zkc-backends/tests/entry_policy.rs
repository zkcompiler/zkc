mod common;
use common::*;
use std::collections::BTreeMap;
use zkc_backends::*;
use zkc_runtime::interactive::{Runner, admit_supplied};

#[test]
fn parameter_names_do_not_select_shapes() {
    let original = program(Some(9), &[("t", "table")], vec![], &["table"], &["t"]);
    for parameters in [
        serde_json::json!([["n", "9"]]),
        serde_json::json!([["rounds", "9"]]),
        serde_json::json!([]),
    ] {
        let mut artifact: serde_json::Value = serde_json::from_slice(&original).unwrap();
        artifact[4][0][4] = parameters;
        let bytes = serde_json::to_vec(&artifact).unwrap();
        let backend = ark_backend(Some(1));
        let admitted = admit_supplied(&bytes, &backend).unwrap();
        let runner = Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            backend,
            vec![table(&[3, 5])],
        );
        assert!(runner.is_ok(), "table shape is an explicit host policy");
    }
}

#[test]
fn heterogeneous_tables_and_explicit_parameter_pins() {
    let bytes = program(
        Some(3),
        &[("small", "table"), ("large", "table")],
        vec![],
        &[],
        &[],
    );
    let backend = ark_backend(None);
    let admitted = admit_supplied(&bytes, &backend).unwrap();
    assert!(
        Runner::new(
            &admitted,
            "main",
            "P",
            "session",
            backend,
            vec![table(&[1, 2]), table(&[3, 4, 5, 6])]
        )
        .is_ok()
    );
    let policy = entry(None).with_parameters(BTreeMap::from([("n".into(), 2)]));
    let backend = NativeBackend::new(Policy::default(), policy, None).unwrap();
    let error = Runner::new(
        &admitted,
        "main",
        "P",
        "session",
        backend,
        vec![table(&[1, 2]), table(&[3, 4, 5, 6])],
    );
    match error {
        Err(failure) => assert!(failure.error.to_string().contains("entry-parameters")),
        Ok(_) => panic!("mismatched explicit parameter pin must fail"),
    }
}
