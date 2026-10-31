//! Native consumer limits and sampling policy remain independent of format syntax.
use zkc_format::logical::TreeLimits;
use zkc_runtime::vm::{Limits, LogicalType, PhysicalType, ServiceContract};

#[test]
fn native_admission_and_tree_limits_have_separate_owners() {
    assert_eq!(Limits::STRING_BYTES, 4096);
    assert_eq!(Limits::ARTIFACT_BYTES, 4 * 1024 * 1024);
    assert_eq!(TreeLimits::BYTES, 16 * 1024 * 1024);
}

#[test]
fn uniform_index_realization_checks_its_supported_algorithm() {
    let index_type = PhysicalType::default_for(LogicalType::parse("index").unwrap()).unwrap();
    let signature = ServiceContract::RandomExtensionField
        .signature("index")
        .unwrap();
    assert_eq!(signature.inputs, vec![index_type.clone()]);
    assert_eq!(signature.outputs, vec![index_type]);
    for contract in [
        ServiceContract::RandomBls12381Field,
        ServiceContract::RandomBn254Field,
        ServiceContract::RandomRistrettoField,
    ] {
        assert!(contract.signature("index").is_none());
        assert!(contract.signature("draw").is_some());
    }
}
