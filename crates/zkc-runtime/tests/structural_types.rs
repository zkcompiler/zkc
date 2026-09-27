use serde_json::json;
use zkc_runtime::interactive::{
    ArgumentKind, AttributeRule, ErrorCode, Identity, LogicalType, OperationBinding, PhysicalType,
    Representation, Type, TypeArgument,
};
use zkc_test_support::variants::{encode_tree, logical};

fn binding(operation: &str, field: &str, length: &str) -> OperationBinding {
    OperationBinding {
        contract: format!("fixed_vector.{operation}"),
        arguments: vec![field.into(), length.into()],
        implementation: format!("plonky3/fixed_vector.{operation}"),
    }
}
fn nested(mut element: String, depth: usize) -> String {
    for _ in 0..depth {
        element = format!("fixed_vector<{element},0>");
    }
    element
}

#[test]
fn canonical_types_keep_typed_arguments_and_atomic_spellings() {
    for spelling in [
        "bool",
        "field:koala-bear",
        "vector:bls12-381.fr",
        "resource_unit:Slot.A",
        "fixed_vector<field:koala-bear,4>",
        "fixed_vector<bool,0>",
        "fixed_vector<field:bls12-381.fr,1048576>",
        "fixed_vector<fixed_vector<field:koala-bear,3>,2>",
    ] {
        let ty = LogicalType::parse(spelling).unwrap();
        assert_eq!(ty.spelling(), spelling);
        assert_eq!(LogicalType::parse(&ty.spelling()).unwrap(), ty);
    }
    let element = LogicalType::new(Type::Field, Identity::KoalaBear).unwrap();
    let ty = LogicalType::fixed_vector(element.clone(), 4).unwrap();
    assert_eq!(ty.fixed_vector_parts(), Some((&element, 4)));
    let application = ty.structural().unwrap();
    assert_eq!(application.head(), "fixed_vector");
    assert_eq!(
        application.parameter_kinds(),
        &[ArgumentKind::Type, ArgumentKind::Nat]
    );
    assert_eq!(
        application.arguments(),
        &[TypeArgument::Type(element), TypeArgument::Nat(4)]
    );
    assert_eq!(ty.identity(), Identity::None);
    assert!(LogicalType::new(Type::FixedVector, Identity::KoalaBear).is_err());
    assert!(
        LogicalType::application(
            "fixed_vector",
            &[
                TypeArgument::Domain(Identity::KoalaBear),
                TypeArgument::Nat(4)
            ]
        )
        .is_err()
    );
}

#[test]
fn noncanonical_or_ill_kinded_applications_refuse() {
    for spelling in [
        "fixed_vector",
        "fixed_vector<>",
        "fixed_vector<field:koala-bear>",
        "fixed_vector<field:koala-bear,1,2>",
        "fixed_vector<koala-bear,4>",
        "fixed_vector<4,field:koala-bear>",
        "fixed_vector<field:koala-bear,bool>",
        "fixed_vector<field:koala-bear,-1>",
        "fixed_vector<field:koala-bear,+1>",
        "fixed_vector<field:koala-bear,01>",
        "fixed_vector<field:koala-bear,00>",
        "fixed_vector<field:koala-bear,1048577>",
        "fixed_vector<field:koala-bear,18446744073709551616>",
        "fixed_vector<field:koala-bear, 1>",
        " fixed_vector<field:koala-bear,1>",
        "fixed_vector <field:koala-bear,1>",
        "fixed_vector<field:koala-bear,1>\n",
        "fixed_vector<field:koala-bear,\t1>",
        "fixed_vector<field:koala-bear,１>",
        "fixed_vector<field:koala-bear@plonky3.koala-bear/1,1>",
        "fixed_vector<fixed_vector<bool,0>@plonky3.fixed-vector/1,1>",
        "fixed_vector<field<koala-bear>,1>",
        "field<koala-bear>",
        "bool<>",
        "unknown<field:koala-bear,1>",
        "fixed_vector<field:unknown,1>",
        "fixed_vector<bool:,1>",
        "fixed_vector<field:koala-bear,1>>",
        "fixed_vector<field:koala-bear,1",
        "fixed_vector<<bool>,1>",
    ] {
        assert_eq!(
            LogicalType::parse(spelling).unwrap_err().code,
            ErrorCode::Type,
            "{spelling}"
        );
    }
    assert_eq!(
        LogicalType::parse("unknown<bool,1>").unwrap_err().detail,
        "uninstalled structural constructor"
    );
}

#[test]
fn permissions_are_conjunctions_and_never_grant_a_codec() {
    for (element, copy, drop) in [
        ("bool", true, true),
        ("field:koala-bear", true, true),
        ("resource_unit:Slot.A", false, true),
        ("rng:bls12-381.fr", false, false),
        ("fixed_vector<resource_unit:Slot.A,0>", false, true),
    ] {
        for length in [0, 3] {
            let ty = LogicalType::parse(&format!("fixed_vector<{element},{length}>")).unwrap();
            assert_eq!(ty.is_duplicable(), copy);
            assert_eq!(ty.is_discardable(), drop);
            assert!(ty.codec().is_none());
        }
    }
    let resource_sum = logical(
        "Choice",
        json!([["unit", ["resource_unit:Slot.A"]], ["empty", []]]),
    );
    let ty = LogicalType::parse(&format!("fixed_vector<{resource_sum},0>")).unwrap();
    assert!(!ty.is_duplicable());
    assert!(ty.is_discardable());
    assert!(!Type::FixedVector.is_serializable());
    // Kind-only queries are conservative; concrete permissions need the arguments.
    assert!(!Type::FixedVector.is_duplicable());
}

#[test]
fn head_permissions_are_conservative_and_ground_permissions_use_payloads() {
    for kind in [Type::FixedVector, Type::Variant] {
        assert!(kind.is_affine());
        assert!(!kind.is_duplicable());
        assert!(!kind.is_discardable());
    }
    for (element, copy, drop) in [
        ("field:koala-bear", true, true),
        ("resource_unit:Slot.A", false, true),
        ("rng:bls12-381.fr", false, false),
    ] {
        let fixed = LogicalType::parse(&format!("fixed_vector<{element},0>")).unwrap();
        let variant = LogicalType::parse(&logical(
            "Choice",
            json!([["value", [element]], ["empty", []]]),
        ))
        .unwrap();
        for ty in [&fixed, &variant] {
            assert_eq!(ty.is_duplicable(), copy);
            assert_eq!(ty.is_discardable(), drop);
            // A conservative head answer must never grant an absent ground permission.
            assert!(!ty.kind().is_duplicable() || ty.is_duplicable());
            assert!(!ty.kind().is_discardable() || ty.is_discardable());
        }
        let physical = PhysicalType::default_for(variant).unwrap();
        assert_eq!(physical.is_affine(), !copy);
        assert_eq!(physical.is_duplicable(), copy);
        assert_eq!(physical.is_discardable(), drop);
        if element == "field:koala-bear" {
            let physical = PhysicalType::default_for(fixed).unwrap();
            assert!(!physical.is_affine());
            assert!(physical.is_duplicable() && physical.is_discardable());
        }
    }
}

#[test]
fn shared_depth_and_byte_limits_cover_variant_type_interleaving() {
    assert!(LogicalType::parse(&nested("bool".into(), 8)).is_ok());
    assert_eq!(
        LogicalType::parse(&nested("bool".into(), 9))
            .unwrap_err()
            .code,
        ErrorCode::Type
    );
    let empty = logical("Empty", json!([["empty", []]]));
    assert!(LogicalType::parse(&nested(empty.clone(), 7)).is_ok());
    assert!(LogicalType::parse(&nested(empty, 8)).is_err());
    let inside = logical("Outer", json!([["value", [nested("bool".into(), 7)]]]));
    assert!(LogicalType::parse(&inside).is_ok());
    let too_deep = logical("Outer", json!([["value", [nested("bool".into(), 8)]]]));
    assert!(LogicalType::parse(&too_deep).is_err());
    // A structural payload may itself contain a variant; neither parser resets depth.
    let inner = logical("Inner", json!([["value", [nested("bool".into(), 5)]]]));
    let mixed = logical(
        "Outer",
        json!([["value", [format!("fixed_vector<{inner},0>")]]]),
    );
    assert!(LogicalType::parse(&mixed).is_ok());
    assert!(LogicalType::parse(&nested(mixed, 1)).is_err());

    let base = logical("X", json!([["empty", []]]));
    let padding = (4096 - base.len() - 16) / 2;
    let at_limit = logical(&"X".repeat(1 + padding), json!([["empty", []]]));
    let at_limit = format!("fixed_vector<{at_limit},0>");
    assert_eq!(at_limit.len(), 4096);
    assert!(LogicalType::parse(&at_limit).is_ok());
    let over = logical(&"X".repeat(2 + padding), json!([["empty", []]]));
    assert!(LogicalType::parse(&format!("fixed_vector<{over},0>")).is_err());
    let large_variant = logical(&"X".repeat(3000), json!([["empty", []]]));
    assert!(large_variant.len() > 4096);
    assert!(LogicalType::parse(&large_variant).is_ok());
}

#[test]
fn existing_variant_graph_budget_also_bounds_large_structural_payloads() {
    let leaf = nested("bool".into(), 6);
    let arm = json!(["Inner", [["values", vec![leaf; 128]]]]);
    let tree = json!(["Outer", [["values", vec![arm; 128]]]]);
    let spelling = encode_tree(tree);
    let error = LogicalType::parse(&spelling).unwrap_err();
    assert_eq!(error.code, ErrorCode::Type);
    assert_eq!(error.detail, "variant:graph-limit");
}

#[test]
fn logical_admission_survives_missing_physical_realization() {
    for field in ["koala-bear", "bls12-381.fr"] {
        for operation in ["from_vector", "to_vector", "dot"] {
            let b = binding(operation, field, "4");
            let mut open = b.clone();
            open.implementation.clear();
            let logical = open.logical_signature().unwrap();
            assert_eq!(logical.attributes, AttributeRule::None);
            let fixed = format!("fixed_vector<field:{field},4>");
            assert!(
                logical
                    .inputs
                    .iter()
                    .chain(&logical.outputs)
                    .any(|t| t.spelling() == fixed)
            );
            let ty = LogicalType::parse(&fixed).unwrap();
            if field == "koala-bear" {
                let physical = PhysicalType::default_for(ty).unwrap();
                assert_eq!(physical.representation(), Representation::FixedVector);
                assert_eq!(PhysicalType::parse(&physical.spelling()).unwrap(), physical);
                assert!(!physical.is_serializable());
                assert!(b.signature().is_ok());
            } else {
                for error in [
                    PhysicalType::default_for(ty.clone()).unwrap_err(),
                    PhysicalType::new(ty, Representation::FixedVector).unwrap_err(),
                    b.signature().unwrap_err(),
                ] {
                    assert_eq!(error.code, ErrorCode::Representation);
                    assert_eq!(error.detail, "unrepresented logical type");
                }
            }
            let mut unbound = b;
            unbound.implementation = "unknown-provider/anything".into();
            assert!(unbound.logical_signature().is_err());
            assert!(unbound.signature().is_err());
        }
    }
    let unsupported = logical(
        "Choice",
        json!([
            ["value", ["fixed_vector<field:bls12-381.fr,0>"]],
            ["empty", []]
        ]),
    );
    let error = PhysicalType::default_for(LogicalType::parse(&unsupported).unwrap()).unwrap_err();
    assert_eq!(error.code, ErrorCode::Representation);
    assert_eq!(error.detail, "unrepresented logical type");
    assert!(
        PhysicalType::parse("fixed_vector<field:koala-bear,1>@plonky3.koala-bear-vector/1")
            .is_err()
    );
    assert!(PhysicalType::parse("vector:koala-bear@plonky3.fixed-vector/1").is_err());
}

#[test]
fn binding_arguments_are_kinded_and_observation_is_explicitly_uninstalled() {
    for arguments in [
        vec![],
        vec!["koala-bear"],
        vec!["koala-bear", "1", "2"],
        vec!["field:koala-bear", "1"],
        vec!["bls12-381.g1", "1"],
        vec!["koala-bear", "01"],
        vec!["koala-bear", "1048577"],
        vec!["koala-bear", "bool"],
        vec!["koala-bear", " 1"],
    ] {
        let mut b = binding("dot", "koala-bear", "1");
        b.arguments = arguments.into_iter().map(str::to_owned).collect();
        assert!(b.logical_signature().is_err());
        assert!(b.signature().is_err());
    }
    let mut observe = binding("dot", "koala-bear", "1");
    observe.contract = "transcript.observe.fixed_vector".into();
    assert_eq!(
        observe.signature().unwrap_err().detail,
        "fixed-vector-observation-uninstalled"
    );
    for name in [
        "fixed_vector.unknown",
        "fixed_vector.encode",
        "fixed_vector.decode",
    ] {
        observe.contract = name.into();
        assert_eq!(observe.signature().unwrap_err().code, ErrorCode::Signature);
    }
}
