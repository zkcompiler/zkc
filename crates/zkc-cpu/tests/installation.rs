//! Installation selection is independent of compiled availability and timing grants.
use zkc_cpu::{
    CpuBackend, CpuExecution, CpuInstallation, Domain, EntryPolicy, Policy, SetupRegistry, Value,
    providers,
};
use zkc_runtime::vm::{
    Backend, ExecutionPolicy, Identity, OperationBinding, PhysicalType, ServiceContract, Value as _,
};

fn make_backend(installation: CpuInstallation) -> CpuBackend {
    CpuBackend::new_with_installation(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        SetupRegistry::default(),
        CpuExecution::serial().unwrap(),
        installation,
    )
    .unwrap()
}
fn add(identity: &str, implementation: &str) -> OperationBinding {
    OperationBinding {
        contract: "field.add".into(),
        arguments: vec![identity.into()],
        implementation: implementation.into(),
        physical_arguments: vec![],
    }
}
#[test]
fn selection_preserves_ids_and_cannot_be_expanded_by_policy() {
    let selected = CpuInstallation::builder()
        .include(providers::Blst)
        .finish()
        .unwrap();
    let full = CpuInstallation::standard().unwrap();
    let ty = "field:bls12-381.fr@blst/fr";
    assert_eq!(
        selected.contracts().physical_type(ty).unwrap(),
        full.contracts().physical_type(ty).unwrap()
    );
    let resident = add("bls12-381.fr", "blst/resident/field.add");
    assert_eq!(
        selected
            .contracts()
            .resolve(resident.clone())
            .unwrap()
            .implementation_id(),
        full.contracts()
            .resolve(resident.clone())
            .unwrap()
            .implementation_id()
    );
    let omitted = add("bls12-381.fr", "arkworks/field.add");
    let permissive = selected.contracts().with_policy(ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: true,
    });
    assert!(permissive.resolve(omitted.clone()).is_err());
    assert!(
        make_backend(selected.clone())
            .with_contracts(full.contracts().clone())
            .is_err()
    );
    assert!(
        make_backend(full.clone())
            .with_contracts(selected.contracts().clone())
            .is_err()
    );
    let backend = make_backend(selected);
    assert!(backend.prepare_binding(&resident).is_some());
    assert!(backend.prepare_binding(&omitted).is_none());
    assert!(backend.validate_value(&Value::Field(1.into())).is_err());
    assert!(!backend.installation().supports_setup());
}
#[test]
fn selection_closes_input_codec_and_both_conversion_endpoints() {
    let full = make_backend(CpuInstallation::default());
    let selected = CpuInstallation::builder()
        .include(providers::Blst)
        .finish()
        .unwrap();
    let backend = make_backend(selected.clone());
    let ordinary = Value::Field(5.into());
    let ordinary_type = ordinary.physical_type();
    let resident_type = selected
        .contracts()
        .physical_type("field:bls12-381.fr@blst/fr")
        .unwrap();
    let wire = full.encode_native_value(&ordinary).unwrap();
    assert!(backend.decode_native_value(&ordinary_type, &wire).is_err());
    assert!(backend.measure_native_wire(&ordinary_type, &wire).is_err());
    assert!(backend.encode_native_value(&ordinary).is_err());
    let resident = backend.decode_native_value(&resident_type, &wire).unwrap();
    backend.validate_value(&resident).unwrap();
    assert_eq!(backend.encode_native_value(&resident).unwrap(), wire);
    for (source, target) in [
        (&ordinary_type, &resident_type),
        (&resident_type, &ordinary_type),
    ] {
        let declaration = OperationBinding {
            contract: "representation.convert".into(),
            arguments: vec!["field:bls12-381.fr".into()],
            implementation: "native/representation.convert".into(),
            physical_arguments: vec![source.spelling(), target.spelling()],
        };
        assert!(selected.contracts().resolve(declaration.clone()).is_err());
        assert!(backend.prepare_binding(&declaration).is_none());
    }
}
#[test]
fn random_roots_and_index_only_services_follow_the_selected_field() {
    let installation = CpuInstallation::builder()
        .include(providers::Plonky3)
        .finish()
        .unwrap();
    let mut backend = make_backend(installation.clone());
    let registry =
        zkc_cpu::services::ServiceRegistry::with_installation(Policy::default(), installation);
    let residue = ServiceContract::RandomGoldilocksExt2;
    let omitted = ServiceContract::RandomBls12381Field;
    assert!(registry.issue_random_for("P", residue, 2).is_ok());
    assert!(registry.issue_random_for("P", omitted, 2).is_err());
    assert!(backend.service_support(residue, "index").is_some());
    assert!(backend.service_support(omitted, "draw").is_none());
    assert!(
        backend
            .issue_rng_for(
                Identity::Bls12381Fr,
                Domain::new("P", "session", "main", None),
                1
            )
            .is_err()
    );
    assert!(
        backend
            .issue_rng_for(
                Identity::GoldilocksExt2,
                Domain::new("P", "session", "main", None),
                1
            )
            .is_ok()
    );
    let empty = make_backend(CpuInstallation::builder().finish().unwrap());
    assert!(empty.service_support(residue, "index").is_none());
    assert!(empty.validate_value(&Value::Index(3)).is_ok());
    assert!(empty.validate_value(&Value::Bool(true)).is_ok());
    assert!(
        empty
            .installation()
            .supports_wire(&PhysicalType::parse("bool@native.bool/0").unwrap())
    );
}
#[test]
fn descriptor_is_deterministic_and_inclusion_is_idempotent() {
    let one = CpuInstallation::builder()
        .include(providers::Plonky3)
        .include(providers::Arkworks)
        .include(providers::Plonky3)
        .finish()
        .unwrap();
    let two = CpuInstallation::builder()
        .include(providers::Arkworks)
        .include(providers::Plonky3)
        .finish()
        .unwrap();
    assert_eq!(
        serde_json::to_value(one.target()).unwrap(),
        serde_json::json!({"format":"zkc.cpu-target/0","providers":["arkworks", "plonky3"]})
    );
    assert_eq!(
        serde_json::to_value(one.target()).unwrap(),
        serde_json::to_value(two.target()).unwrap()
    );
}

#[test]
fn base_controls_and_inactive_variant_measurements_obey_the_installation() {
    let installation = CpuInstallation::builder().finish().unwrap();
    let backend = make_backend(installation.clone());
    for contract in ["bool.and", "bool.or", "bool.not", "control.require"] {
        let declaration = OperationBinding {
            contract: contract.into(),
            arguments: vec![],
            implementation: format!("arkworks/{contract}"),
            physical_arguments: vec![],
        };
        assert!(
            installation
                .contracts()
                .resolve(declaration.clone())
                .is_ok()
        );
        assert!(backend.prepare_binding(&declaration).is_some());
    }
    let logical = zkc_test_support::variants::logical(
        "Choice",
        serde_json::json!([["empty", []], ["number", ["field:bls12-381.fr"]]]),
    );
    let ty =
        PhysicalType::default_for(zkc_runtime::vm::LogicalType::parse(&logical).unwrap()).unwrap();
    assert!(
        make_backend(CpuInstallation::default())
            .measure_native_variant(&ty, 0, &[])
            .is_ok()
    );
    assert!(backend.measure_native_variant(&ty, 0, &[]).is_err());
}
