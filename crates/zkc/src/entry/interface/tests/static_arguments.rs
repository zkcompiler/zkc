use super::*;
use crate::entry::interface::origin::{NominalKind, OriginTerm};

fn with_arguments(arguments: Value) -> Value {
    let mut value = document();
    value["relations"][0]["static_arguments"] = arguments;
    value
}

#[test]
fn ordered_arguments_retain_every_typed_constructor_and_identity() {
    let arguments = json!([
        ["nat", "0"],
        ["nat", "184467440737095516160"],
        ["field", "bls12-381.fr"],
        ["group", "bls12-381.g1"],
        ["domain", "Ring", "vendor.ring/0"],
        ["asset", "Bundle", "asset-id"],
        ["bool"],
        ["index"],
        ["unit"],
        ["tuple", [["bool"], ["index"]]],
        ["array", ["field", "koala-bear"], "0"],
        ["nominal", "record", "数学::Record", [["nat", "2"]]],
        ["nominal", "variant", "sample::Choice", []],
        ["nominal", "associated", "sample::Module::Value", []],
        ["nominal", "module", "sample::Module", []],
        ["builtin", "Vector", [["field", "koala-bear"]]],
        ["formal", "vendor.Family", [["nat", "3"]]]
    ]);
    let view = read(&with_arguments(arguments)).unwrap();
    let actual = &view.document.relations[0].static_arguments;
    assert_eq!(actual[0], OriginTerm::Natural("0".into()));
    assert_eq!(
        actual[1],
        OriginTerm::Natural("184467440737095516160".into())
    );
    assert_eq!(actual[2], OriginTerm::Field("bls12-381.fr".into()));
    assert_eq!(actual[3], OriginTerm::Group("bls12-381.g1".into()));
    assert_eq!(
        actual[4],
        OriginTerm::Domain("Ring".into(), "vendor.ring/0".into())
    );
    assert_eq!(
        actual[5],
        OriginTerm::Asset("Bundle".into(), "asset-id".into())
    );
    assert_eq!(actual[6], OriginTerm::Boolean);
    assert_eq!(actual[7], OriginTerm::Index);
    assert_eq!(actual[8], OriginTerm::Unit);
    assert_eq!(
        actual[9],
        OriginTerm::Tuple(vec![OriginTerm::Boolean, OriginTerm::Index])
    );
    assert_eq!(
        actual[10],
        OriginTerm::Array(Box::new(OriginTerm::Field("koala-bear".into())), "0".into())
    );
    for (index, kind, name, children) in [
        (
            11,
            NominalKind::Record,
            "数学::Record",
            vec![OriginTerm::Natural("2".into())],
        ),
        (12, NominalKind::Variant, "sample::Choice", vec![]),
        (13, NominalKind::Associated, "sample::Module::Value", vec![]),
        (14, NominalKind::Module, "sample::Module", vec![]),
    ] {
        assert_eq!(
            actual[index],
            OriginTerm::Nominal(kind, name.into(), children)
        );
    }
    assert_eq!(
        actual[15],
        OriginTerm::Builtin(
            "Vector".into(),
            vec![OriginTerm::Field("koala-bear".into())]
        )
    );
    assert_eq!(
        actual[16],
        OriginTerm::Formal(
            "vendor.Family".into(),
            vec![OriginTerm::Natural("3".into())]
        )
    );

    let other = read(&with_arguments(json!([
        ["field", "koala-bear"],
        ["nat", "0"]
    ])))
    .unwrap();
    assert_ne!(&actual[..2], other.document.relations[0].static_arguments);
}

#[test]
fn relation_rows_require_the_exact_current_fields() {
    let mut missing = document();
    missing["relations"][0]
        .as_object_mut()
        .unwrap()
        .remove("static_arguments");
    assert_eq!(read(&missing).unwrap_err(), InterfaceError::Format);
    let mut extra = document();
    extra["relations"][0]["arguments"] = json!([]);
    assert_eq!(read(&extra).unwrap_err(), InterfaceError::Format);
    let original = document().to_string();
    let repeated = original.replacen(
        "\"static_arguments\":[]",
        "\"static_arguments\":[],\"static_\\u0061rguments\":[]",
        1,
    );
    assert_ne!(original, repeated);
    assert_eq!(read_text(&repeated).unwrap_err(), InterfaceError::Format);
}

#[test]
fn malformed_or_open_static_trees_refuse() {
    for arguments in [
        json!(null),
        json!({}),
        json!([null]),
        json!([{}]),
        json!(["bool"]),
        json!([[]]),
        json!([["bool", 0]]),
        json!([["nat"]]),
        json!([["nat", 0]]),
        json!([["nat", "00"]]),
        json!([["nat", "-0"]]),
        json!([["nat", "1e3"]]),
        json!([["nat", ""]]),
        json!([["field", ""]]),
        json!([["group", "x\u{0}"]]),
        json!([["domain", "Field"]]),
        json!([["asset", "", "id"]]),
        json!([["tuple", {}]]),
        json!([["array", ["bool"]]]),
        json!([["array", ["bool"], "01"]]),
        json!([["nominal", "tuple", "sample::T", []]]),
        json!([["nominal", "record", "sample::::T", []]]),
        json!([["nominal", "record", "sample::1T", []]]),
        json!([["nominal", "record", "e\u{301}", []]]),
        json!([["builtin", "Vector", ["field"]]]),
        json!([["formal", "F", [["parameter", "T"]]]]),
        json!([["symbolic", "N"]]),
        json!([["parameter", "T"]]),
        json!([["unit", {"extra": true}]]),
        json!([["field", "x".repeat(513)]]),
    ] {
        assert_eq!(
            read(&with_arguments(arguments.clone())).unwrap_err(),
            InterfaceError::Format,
            "{arguments}"
        );
    }
}

#[test]
fn formula_and_captured_relations_require_empty_arguments() {
    for definition in [
        json!({"kind":"formula", "function":"predicate"}),
        json!({"kind":"r1cs", "asset":digest("asset")}),
        json!({"kind":"air", "asset":digest("asset")}),
        json!({"kind":"bundle", "asset":digest("asset")}),
    ] {
        let mut value = with_arguments(json!([["nat", "1"]]));
        value["relations"][0]["definition"] = definition;
        assert_eq!(read(&value).unwrap_err(), InterfaceError::Schema);
    }
    let mut formula = document();
    formula["relations"][0]["definition"] = json!({"kind":"formula", "function":"predicate"});
    read(&formula).unwrap();
    read(&bundle_document()).unwrap();
}

fn nested(levels: usize) -> Value {
    let mut term = json!(["bool"]);
    for _ in 1..levels {
        term = json!(["array", term, "0"]);
    }
    term
}

#[test]
fn static_argument_limits_are_aggregate_and_inclusive() {
    read(&with_arguments(json!(vec![json!(["bool"]); 128]))).unwrap();
    assert_eq!(
        read(&with_arguments(json!(vec![json!(["bool"]); 129]))).unwrap_err(),
        InterfaceError::Format
    );
    read(&with_arguments(json!([[
        "tuple",
        vec![json!(["bool"]); 512]
    ]])))
    .unwrap();
    assert_eq!(
        read(&with_arguments(json!([[
            "tuple",
            vec![json!(["bool"]); 513]
        ]])))
        .unwrap_err(),
        InterfaceError::Format
    );
    read(&with_arguments(json!([["nat", "9".repeat(512)]]))).unwrap();
    let mut arguments = vec![json!(["tuple", vec![json!(["bool"]); 511]]); 8];
    read(&with_arguments(json!(arguments))).unwrap(); // 8 * 512 = 4096 nodes.
    arguments.push(json!(["bool"]));
    assert_eq!(
        read(&with_arguments(json!(arguments))).unwrap_err(),
        InterfaceError::Format
    );
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            read(&with_arguments(json!([nested(64)]))).unwrap();
            assert_eq!(
                read(&with_arguments(json!([nested(65)]))).unwrap_err(),
                InterfaceError::Format
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn public_cpp_descriptor_terms_retain_structure_and_existing_bytes() {
    let fixtures: Value = serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../compiler/test/fixtures/source-terms/descriptors.json"
    )))
    .unwrap();
    assert_eq!(fixtures["format"], "zkc.source-term-fixtures/0");
    let terms: Vec<_> = fixtures["terms"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row["term"].clone())
        .collect();
    let view = read(&with_arguments(json!(terms))).unwrap();
    let actual = &view.document.relations[0].static_arguments;
    use OriginTerm::*;
    let boolean = || Builtin("finite".into(), vec![Boolean]);
    let field = || Builtin("finite".into(), vec![Field("bls12-381.fr".into())]);
    assert_eq!(actual[0], boolean());
    assert_eq!(actual[1], field());
    assert_eq!(actual[2], DescriptorProduct(vec![]));
    assert_eq!(actual[3], DescriptorProduct(vec![boolean(), field()]));
    assert_eq!(actual[4], DescriptorProduct(vec![field(), boolean()]));
    assert_ne!(actual[3], actual[4]);
    assert_eq!(actual[5], DescriptorSequence(Box::new(boolean()), None));
    assert_eq!(
        actual[6],
        DescriptorSequence(Box::new(boolean()), Some("0".into()))
    );
    assert_ne!(actual[5], actual[6]);
    assert_eq!(
        actual[7],
        DescriptorSequence(Box::new(field()), Some("7".into()))
    );
    assert_eq!(
        actual[8],
        DescriptorProduct(vec![
            DescriptorSequence(
                Box::new(DescriptorProduct(vec![field(), boolean()])),
                Some("2".into())
            ),
            DescriptorSequence(Box::new(DescriptorProduct(vec![])), None),
            DescriptorProduct(vec![boolean()]),
        ])
    );
    assert_eq!(actual[9], Boolean);
    assert_eq!(actual[10], Tuple(vec![Boolean, Index]));
    assert_eq!(actual[11], Array(Box::new(Boolean), "0".into()));
    assert_eq!(
        actual[12],
        Formal("vendor.Family".into(), vec![Field("koala-bear".into())])
    );
    assert_eq!(
        actual[13],
        Nominal(
            NominalKind::LogicalRecord,
            "sample::Logical".into(),
            vec![Boolean]
        )
    );
}

#[test]
fn structural_descriptors_refuse_small_wrong_shapes_categories_and_extents() {
    for term in [
        json!(["descriptor-product"]),
        json!(["descriptor-product", [], 0]),
        json!(["descriptor-product", {}]),
        json!(["descriptor-product", [["bool"]]]),
        json!(["descriptor-product", [["tuple", []]]]),
        json!(["descriptor-product", [["array", ["bool"], "0"]]]),
        json!([
            "descriptor-product",
            [["builtin", "descriptor_product", []]]
        ]),
        json!(["descriptor-product", [["builtin", "Constraint", []]]]),
        json!(["descriptor-product", [["formal", "finite", [["bool"]]]]]),
        json!(["descriptor-product", [["builtin", "Finite", [["bool"]]]]]),
        json!(["descriptor-product", [["builtin", "finite", []]]]),
        json!([
            "descriptor-product",
            [["builtin", "finite", [["bool"], ["index"]]]]
        ]),
        json!(["descriptor-product", [["builtin", "finite", [["bool"]], 0]]]),
        json!(["descriptor-sequence", ["descriptor-product", []]]),
        json!(["descriptor-sequence", ["descriptor-product", []], null, 0]),
        json!(["descriptor-sequence", ["bool"], null]),
        json!(["descriptor-sequence", ["descriptor-product", []], "0"]),
        json!(["descriptor-sequence", ["descriptor-product", []], 0]),
        json!([
            "descriptor-sequence",
            ["descriptor-product", []],
            ["nat", 0]
        ]),
        json!([
            "descriptor-sequence",
            ["descriptor-product", []],
            ["nat", "00"]
        ]),
        json!([
            "descriptor-sequence",
            ["descriptor-product", []],
            ["nat", "-1"]
        ]),
        json!([
            "descriptor-sequence",
            ["descriptor-product", []],
            ["nat", "1e2"]
        ]),
        json!([
            "descriptor-sequence",
            ["descriptor-product", []],
            ["nat", "0", 0]
        ]),
        json!(["descriptor-sequence", ["descriptor-product", []], ["index"]]),
        json!([
            "descriptor-sequence",
            ["descriptor-product", []],
            ["parameter", "N"]
        ]),
        json!(["descriptor_sequence", ["descriptor-product", []], null]),
    ] {
        assert_eq!(
            read(&with_arguments(json!([term]))).unwrap_err(),
            InterfaceError::Format,
            "{term}"
        );
    }
    // General closed terms remain general; syntax alone is not source formation.
    for term in [
        json!(["builtin", "finite", []]),
        json!(["builtin", "Constraint", []]),
        json!([
            "descriptor-product",
            [["builtin", "finite", [["nat", "0"]]]]
        ]),
    ] {
        read(&with_arguments(json!([term]))).unwrap();
    }
}

#[test]
fn descriptor_wire_limits_count_present_naturals_and_preserve_null() {
    let empty = json!(["descriptor-product", []]);
    read(&with_arguments(json!([[
        "descriptor-product",
        vec![empty.clone(); 512]
    ]])))
    .unwrap();
    assert_eq!(
        read(&with_arguments(json!([[
            "descriptor-product",
            vec![empty.clone(); 513]
        ]])))
        .unwrap_err(),
        InterfaceError::Format
    );
    for size in [512, 513] {
        let result = read(&with_arguments(json!([[
            "descriptor-sequence",
            empty,
            ["nat", "9".repeat(size)]
        ]])));
        assert_eq!(result.is_ok(), size == 512);
    }
    // Eight roots of 512 terms each; size and value are independent of allocation.
    let mut arguments = vec![json!(["descriptor-product", vec![empty.clone(); 511]]); 8];
    arguments[0][1][0] = json!(["descriptor-sequence", empty, null]); // 4097.
    arguments[7][1].as_array_mut().unwrap().pop(); // 4096 with null.
    read(&with_arguments(json!(arguments))).unwrap();
    arguments[0][1][0][2] = json!(["nat", "0"]); // 4097: present Natural counted.
    assert_eq!(
        read(&with_arguments(json!(arguments))).unwrap_err(),
        InterfaceError::Format
    );
    arguments[7][1].as_array_mut().unwrap().pop(); // 4096 with Natural.
    read(&with_arguments(json!(arguments))).unwrap();
    arguments.push(json!(["nat", "0"])); // Aggregate includes later roots.
    assert_eq!(
        read(&with_arguments(json!(arguments))).unwrap_err(),
        InterfaceError::Format
    );
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(move || {
            let mut tree = json!(["descriptor-sequence", empty, ["nat", "0"]]);
            for _ in 0..62 {
                tree = json!(["descriptor-sequence", tree, null]);
            }
            read(&with_arguments(json!([tree]))).unwrap(); // Both children at level 64.
            tree = json!(["descriptor-sequence", tree, null]);
            assert_eq!(
                read(&with_arguments(json!([tree]))).unwrap_err(),
                InterfaceError::Format
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
