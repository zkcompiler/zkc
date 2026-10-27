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
