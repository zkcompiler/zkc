//! Independent primitive ingress validates public matrices without executing them.
use serde_json::json;
use zkc_tools::artifact::primitive::respond;

fn validate(field: &str, b: &[u8]) -> serde_json::Value {
    respond(&json!([
        "zkc.public-primitive/1",
        [],
        "validate",
        [],
        [],
        [[format!("matrix:{field}"), zkc_test_support::hex(b)]]
    ]))
    .unwrap()
}
#[test]
fn canonical_matrix_primitive_validation_in_all_fields() {
    for (field, tag, width) in [
        ("bls12-381.fr", 23, 32),
        ("ristretto255.scalar", 24, 32),
        ("koala-bear", 25, 4),
    ] {
        let mut b = b"ZKCV\x01".to_vec();
        b.push(tag);
        for n in [2u32, 3, 2] {
            b.extend(n.to_le_bytes());
        }
        for (r, c, a) in [(0u32, 1u32, 3u32), (1, 0, 4)] {
            b.extend(r.to_le_bytes());
            b.extend(c.to_le_bytes());
            b.extend(a.to_le_bytes());
            b.extend(vec![0; width - 4]);
        }
        assert_eq!(validate(field, &b), json!(["ok"]));
        for n in 0..b.len() {
            assert_eq!(validate(field, &b[..n])[0], "error");
        }
        let mut wrong = b.clone();
        wrong.push(0);
        assert_eq!(validate(field, &wrong)[0], "error");
        let mut wrong = b.clone();
        wrong[5] ^= 1;
        assert_eq!(
            validate(field, &wrong),
            json!(["error", "primitive-wire-header"])
        );
        let mut wrong = b.clone();
        wrong[26..26 + width].fill(0);
        assert_eq!(
            validate(field, &wrong),
            json!(["error", "primitive-matrix-zero"])
        );
        let mut wrong = b.clone();
        wrong[26..26 + width].fill(255);
        assert_eq!(validate(field, &wrong), json!(["error", "primitive-field"]));
        let mut wrong = b.clone();
        wrong[6..10].copy_from_slice(&65537u32.to_le_bytes());
        assert_eq!(
            validate(field, &wrong),
            json!(["error", "primitive-matrix-limit"])
        );
        let mut wrong = b.clone();
        wrong[14..18].copy_from_slice(&1048577u32.to_le_bytes());
        assert_eq!(
            validate(field, &wrong),
            json!(["error", "primitive-matrix-limit"])
        );
        let mut wrong = b.clone();
        wrong[26 + width..34 + width].copy_from_slice(&b[18..26]);
        assert_eq!(
            validate(field, &wrong),
            json!(["error", "primitive-matrix-order"])
        );
        let mut wrong = b.clone();
        wrong[18..22].copy_from_slice(&2u32.to_le_bytes());
        assert_eq!(
            validate(field, &wrong),
            json!(["error", "primitive-matrix-order"])
        );
        let hex = zkc_test_support::hex(&b);
        for (name, args, attrs, inputs, code) in [
            (
                "validate",
                json!([]),
                json!(["1"]),
                json!([[format!("matrix:{field}"), hex]]),
                "primitive-attributes",
            ),
            (
                "matrix.bilinear",
                json!([field]),
                json!([]),
                json!([]),
                "primitive-operation",
            ),
        ] {
            assert_eq!(
                respond(&json!([
                    "zkc.public-primitive/1",
                    [],
                    name,
                    args,
                    attrs,
                    inputs
                ]))
                .unwrap(),
                json!(["error", code])
            );
        }
    }
}
