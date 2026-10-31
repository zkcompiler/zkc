use serde_json::json;
use zkc_format::types::{VariantError, variant_spelling, variant_tree};
use zkc_test_support::hex;

fn spelling(json: &[u8]) -> String {
    format!("variant:{}", hex(json))
}

#[test]
fn native_variant_graph_matches_independently_spelled_bytes() {
    let expected = spelling(br#"["zkc.variant/0",["T",[],["0","1"]]]"#);
    let tree = json!(["T", []]);
    assert_eq!(variant_spelling(&tree).unwrap(), expected);
    assert_eq!(variant_tree(&expected).unwrap(), tree);
    // Graph syntax alone admits this tree. Native payload/permission formation
    // remains the independent consumer's responsibility.
    assert_eq!(
        variant_tree(&spelling(br#"["zkc.variant/0",["bool"]]"#)).unwrap(),
        json!("bool")
    );
}

#[test]
fn graph_refusals_keep_exact_categories_and_order() {
    for (bytes, detail) in [
        (&b"["[..], "json"),
        (&b"[]"[..], "descriptor"),
        (&br#"["other",[]]"#[..], "format"),
        (&br#"["zkc.variant/0",[]]"#[..], "descriptor"),
        (&br#"["zkc.variant/0",[false]]"#[..], "graph-node"),
        (&br#"["zkc.variant/0",[["0"]]]"#[..], "graph-reference"),
        (&br#"["zkc.variant/0",["T",["00"]]]"#[..], "graph-reference"),
        (&br#"["zkc.variant/0",["T",["2"]]]"#[..], "graph-reference"),
        (
            &br#"["zkc.variant/0",["T",["18446744073709551616"]]]"#[..],
            "graph-reference",
        ),
        (&br#"["zkc.variant/0",["unused","T"]]"#[..], "canonical"),
        (
            &br#"["zkc.variant/0",["T","T",["0","1"]]]"#[..],
            "canonical",
        ),
        (&br#"["zkc.variant/0",["\u0054"]]"#[..], "canonical"),
    ] {
        let error = variant_tree(&spelling(bytes)).unwrap_err();
        assert_eq!(error, VariantError(detail), "{bytes:?}");
        assert_eq!(error.to_string(), format!("variant:{detail}"));
    }
    for value in [
        "",
        "other:00",
        "variant:",
        "variant:0",
        "variant:AF",
        "variant:gg",
    ] {
        assert_eq!(variant_tree(value), Err(VariantError("hex")));
    }
    // Spelling limits refuse before the hex or JSON parser.
    assert_eq!(
        variant_tree(&"x".repeat(256 * 1024 + 1)),
        Err(VariantError("limit"))
    );
    for tree in [json!(false), json!("é"), json!("\n")] {
        assert_eq!(variant_spelling(&tree), Err(VariantError("graph-node")));
    }
}

#[test]
fn graph_depth_and_expansion_are_bounded_before_materialization() {
    let mut tree = json!("T");
    for _ in 0..64 {
        tree = json!([tree]);
    }
    assert_eq!(variant_spelling(&tree), Err(VariantError("graph-limit")));
    // A compact DAG whose repeated references expand exponentially.
    let mut nodes = vec![json!("T")];
    for i in 0..30 {
        nodes.push(json!([i.to_string(), i.to_string()]));
    }
    let graph = serde_json::to_vec(&json!(["zkc.variant/0", nodes])).unwrap();
    assert_eq!(
        variant_tree(&spelling(&graph)),
        Err(VariantError("graph-limit"))
    );
}
