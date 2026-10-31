use zkc_catalog::{CATALOG, Facet, IntrinsicDomain, ParameterValidator, Port, Signature, Stage};

#[test]
fn total_index_identities_and_exact_signatures_use_existing_catalog_projection() {
    for (identity, name) in [
        ("IndexWrappingAdd", "index.wrapping_add"),
        ("IndexWrappingSubtract", "index.wrapping_sub"),
        ("IndexBitAnd", "index.bit_and"),
        ("IndexLogicalShiftRight", "index.logical_shift_right"),
    ] {
        let meaning = CATALOG
            .mathematical_identities
            .iter()
            .find(|m| m.name == identity)
            .unwrap();
        // These identities do not grant field/group equations or proof authority.
        assert!(meaning.laws.is_none());
        let intrinsic = CATALOG
            .mathematical_intrinsics
            .iter()
            .find(|i| i.name == name)
            .unwrap();
        assert_eq!(intrinsic.identity, identity);
        assert_eq!(intrinsic.domain, IntrinsicDomain::Index);
        assert_eq!(intrinsic.naturals, 0);
        assert!(!intrinsic.domain_points && !intrinsic.scalar);
        let operation = zkc_catalog::operation(name).unwrap();
        assert_eq!(operation.stage, Stage::Source);
        assert!(operation.scope.is_empty() && operation.requirements.is_empty());
        assert_eq!(operation.facets, &[Facet::DeterministicData]);
        assert_eq!(operation.parameters.minimum, 0);
        assert_eq!(operation.parameters.maximum, Some(0));
        assert_eq!(operation.parameters.validator, ParameterValidator::None);
        let index = Port::Apply {
            constructor: "index",
            arguments: &[],
        };
        match operation.signature {
            Signature::Fixed { inputs, outputs } => {
                assert_eq!(inputs, &[index, index]);
                assert_eq!(outputs, &[index]);
            }
            _ => panic!("total index signature must be fixed"),
        }
        // Adding these contracts must not enroll an unsupported consumer.
        assert!(
            zkc_catalog::consumer_profile_operation("structured-source-primitives", name).is_none()
        );
    }
}
