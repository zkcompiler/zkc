//! Trusted selected transcript payloads require exact schemas and codec grants.
use serde_json::json;
use zkc_runtime::vm::*;

const OBSERVE: &str = "transcript.native.indexed.observe.data";
fn binding(payload: &PhysicalType) -> OperationBinding {
    OperationBinding {
        contract: OBSERVE.into(),
        arguments: vec![
            Identity::Merlin3Fr64Be.name().into(),
            payload.logical().spelling(),
        ],
        implementation: format!("arkworks/{OBSERVE}"),
        physical_arguments: vec![payload.spelling()],
    }
}
fn context(permission: bool) -> (Contracts, PhysicalType) {
    let mut builder = ContractsBuilder::standard();
    let field = builder
        .add_representation(
            "independent/scalar",
            LogicalType::parse("field:bls12-381.fr").unwrap(),
        )
        .unwrap();
    if permission {
        builder
            .add_wire_permission(field.clone(), WireCodec::Native)
            .unwrap();
    }
    (builder.finish(ExecutionPolicy::general_purpose()), field)
}
fn variant(contracts: &Contracts, field: PhysicalType) -> PhysicalType {
    let logical = LogicalType::parse(&zkc_test_support::variants::logical(
        "Observed",
        json!([["empty", []], ["value", ["field:bls12-381.fr"]]]),
    ))
    .unwrap();
    contracts
        .aggregate_type(logical, Representation::Variant, vec![field])
        .unwrap()
}

#[test]
fn expected_payload_selection_preserves_fixed_ports_and_complete_inactive_layouts() {
    let (contracts, field) = context(true);
    for payload in [field.clone(), variant(&contracts, field)] {
        let selected = contracts.resolve(binding(&payload)).unwrap();
        assert_eq!(selected.signature().inputs[1], payload);
        let mut default = binding(&payload);
        default.physical_arguments.clear();
        let baseline = contracts.resolve(default.clone()).unwrap();
        assert_eq!(
            baseline.signature().inputs[1],
            PhysicalType::default_for(payload.logical()).unwrap()
        );
        assert_eq!(
            selected.signature().inputs[0],
            baseline.signature().inputs[0]
        );
        assert_eq!(
            selected.signature().inputs[2],
            baseline.signature().inputs[2]
        );
        assert_eq!(selected.signature().outputs, baseline.signature().outputs);
        assert_eq!(
            selected.signature().attributes,
            AttributeRule::NativeMessageTemplate
        );
        assert_eq!(selected.implementation_id(), baseline.implementation_id());
        assert_eq!(selected.requirements(), baseline.requirements());
        // Context discovery/logical admission stays a separate, unspecialized query.
        assert_eq!(
            contracts.logical_signature(&default).unwrap().inputs[1],
            payload.logical()
        );
        assert!(contracts.logical_signature(selected.declaration()).is_err());
    }
}

#[test]
fn expected_selected_payload_requires_positive_codec_permission_even_for_inactive_children() {
    let (contracts, field) = context(false);
    for payload in [field.clone(), variant(&contracts, field)] {
        assert!(!contracts.permits_wire(&payload, WireCodec::Native));
        let error = contracts.resolve(binding(&payload)).unwrap_err();
        assert_eq!(error.code, ErrorCode::Signature);
        assert_eq!(error.detail, "transcript-native-wire");
    }
}

#[test]
fn expected_selection_refuses_wrong_schema_arity_owner_local_data_and_foreign_catalog() {
    let (contracts, field) = context(true);
    let (foreign, foreign_field) = context(true);
    assert_ne!(field, foreign_field);
    let local = variant(&contracts, field.clone());
    assert!(
        contracts
            .aggregate_type(
                local.logical(),
                Representation::Variant,
                vec![foreign_field]
            )
            .is_err()
    );
    assert!(
        foreign
            .aggregate_type(local.logical(), Representation::Variant, vec![field])
            .is_err()
    );
    let valid = binding(&local);
    let mut cases = vec![];
    let mut wrong = valid.clone();
    wrong.arguments[1] = "index".into();
    cases.push(wrong);
    let mut wrong = valid.clone();
    wrong.physical_arguments.push(local.spelling());
    cases.push(wrong);
    let mut wrong = valid.clone();
    wrong.implementation = format!("spongefish/{OBSERVE}");
    cases.push(wrong);
    let mut wrong = valid.clone();
    wrong.contract = "transcript.native.indexed.challenge".into();
    cases.push(wrong);
    let mut wrong = valid.clone();
    wrong.arguments[0] = Identity::Merlin3Ristretto64Le.name().into();
    cases.push(wrong);
    let fixed = contracts
        .physical_type("fixed_vector<field:koala-bear,2>@plonky3.fixed-vector/0")
        .unwrap();
    cases.push(binding(&fixed));
    for wrong in cases {
        assert!(contracts.resolve(wrong.clone()).is_err(), "{wrong:?}");
    }
    for (contract, args, implementation) in [
        ("field.add", vec!["bls12-381.fr"], "arkworks/field.add"),
        (
            "transcript.native.indexed.challenge",
            vec![Identity::Merlin3Fr64Be.name()],
            "arkworks/transcript.native.indexed.challenge",
        ),
        (
            "transcript.observe",
            vec![Identity::Merlin3Fr64Be.name()],
            "arkworks/transcript.observe",
        ),
    ] {
        let wrong = OperationBinding {
            contract: contract.into(),
            arguments: args.into_iter().map(str::to_owned).collect(),
            implementation: implementation.into(),
            physical_arguments: valid.physical_arguments.clone(),
        };
        assert_eq!(
            contracts.resolve(wrong).unwrap_err().detail,
            "unexpected-physical-arguments"
        );
    }
}
