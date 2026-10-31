use super::*;

fn encode_origin(protocol: &str, query: bool) -> String {
    let event = if query {
        json!([
            "query",
            protocol,
            "draw",
            "input_0",
            "random.bls12-381.fr/0",
            "draw",
            "V"
        ])
    } else {
        json!([
            "message",
            protocol,
            "oracle_0_7_opening_request",
            "oracle_0_7_opening_request",
            "V",
            "P"
        ])
    };
    let value = json!([
        "zkc.native-origin-template/0",
        "main",
        [["apply", "Root", "call"], ["repeat", "Leaf", "round"]],
        [],
        event
    ]);
    zkc_format::logical::encode_tree(&value)
        .unwrap()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

#[test]
fn generated_origin_keeps_loop_lineage_without_reapplying_site_prefix() {
    let protocol = format!("zkc.oracle.{}", "a".repeat(64));
    let origin = encode_origin(&protocol, false);
    assert_eq!(
        native_origin_site(&origin, "message").unwrap(),
        "oracle_0_7_opening_request"
    );
    let decoded = zkc_format::logical::decode_tree(
        &zkc_format::logical::native_origin_template(&[origin], "message").unwrap(),
    )
    .unwrap();
    assert_eq!(
        decoded[2],
        json!([["apply", "Root", "call"], ["repeat", "Leaf", "round"]])
    );
    assert_eq!(
        native_origin_site(&encode_origin("Leaf", false), "message").unwrap(),
        "apply_4_call_oracle_0_7_opening_request"
    );
}

#[test]
fn generated_namespace_refuses_noncanonical_identity_or_query() {
    for suffix in [
        String::new(),
        "a".repeat(63),
        "A".repeat(64),
        "g".repeat(64),
    ] {
        assert!(
            native_origin_site(
                &encode_origin(&format!("zkc.oracle.{suffix}"), false),
                "message"
            )
            .is_err()
        );
    }
    assert!(
        native_origin_site(
            &encode_origin(&format!("zkc.oracle.{}", "a".repeat(64)), true),
            "query"
        )
        .is_err()
    );
}
