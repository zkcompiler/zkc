//! Independent reference-service wire validation; no source arithmetic callback.
use serde_json::json;
use zkc_tools::artifact::primitive::respond;

fn validate(kind: &str, bytes: &[u8]) -> serde_json::Value {
    let hex = zkc_test_support::hex(bytes);
    respond(&json!([
        "zkc.public-primitive/1",
        [],
        "validate",
        [],
        [],
        [[kind, hex]]
    ]))
    .unwrap()
}

#[test]
fn numerical_reference_validation_accepts_canonical_bytes_without_setup() {
    for (kind, bytes) in [
        (
            "field:koala-bear",
            vec![90, 75, 67, 86, 1, 19, 0, 0, 0, 127],
        ),
        (
            "vector:koala-bear",
            vec![90, 75, 67, 86, 1, 20, 2, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0],
        ),
        (
            "polynomial:koala-bear",
            vec![90, 75, 67, 86, 1, 21, 0, 0, 0, 0],
        ),
        (
            "round:koala-bear",
            vec![90, 75, 67, 86, 1, 22, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0],
        ),
    ] {
        assert_eq!(validate(kind, &bytes), json!(["ok"]));
        for len in 0..bytes.len() {
            assert_eq!(validate(kind, &bytes[..len])[0], "error");
        }
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_eq!(validate(kind, &trailing)[0], "error");
        let mut header = bytes.clone();
        header[5] ^= 1;
        assert_eq!(
            validate(kind, &header),
            json!(["error", "primitive-wire-header"])
        );
        assert_eq!(
            validate(&kind.replace("koala-bear", "bls12-381.fr"), &bytes)[0],
            "error"
        );
    }
}

#[test]
fn numerical_reference_validation_refuses_noncanonical_and_unsupported_requests() {
    assert_eq!(
        validate("field:koala-bear", &[90, 75, 67, 86, 1, 19, 1, 0, 0, 127]),
        json!(["error", "primitive-field"])
    );
    assert_eq!(
        validate(
            "polynomial:koala-bear",
            &[90, 75, 67, 86, 1, 21, 1, 0, 0, 0, 0, 0, 0, 0]
        ),
        json!(["error", "primitive-polynomial"])
    );
    assert_eq!(
        validate(
            "vector:koala-bear",
            &[90, 75, 67, 86, 1, 20, 255, 255, 255, 255]
        ),
        json!(["error", "primitive-wire-length"])
    );
    for kind in ["table", "group", "transcript", "rng", "proof"] {
        assert_eq!(
            validate(&format!("{kind}:koala-bear"), &[]),
            json!(["error", "primitive-nominal-type"])
        );
    }
    let value = json!(["field:koala-bear", "5a4b4356011301000000"]);
    for (op, args, attrs, values, code) in [
        (
            "validate",
            json!([]),
            json!(["1"]),
            json!([value]),
            "primitive-attributes",
        ),
        (
            "validate",
            json!([]),
            json!([]),
            json!([value, value]),
            "primitive-operation",
        ),
        (
            "field.add",
            json!(["koala-bear"]),
            json!([]),
            json!([value, value]),
            "primitive-operation",
        ),
    ] {
        assert_eq!(
            respond(&json!([
                "zkc.public-primitive/1",
                [],
                op,
                args,
                attrs,
                values
            ]))
            .unwrap(),
            json!(["error", code])
        );
    }
}
