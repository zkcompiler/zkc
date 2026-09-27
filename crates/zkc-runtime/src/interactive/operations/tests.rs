use super::*;

fn with_alternative(
    owner: &'static Contribution,
    name: &'static str,
    primary: Identity,
) -> Result<Registry> {
    let alternatives = Box::leak(Box::new([Alternative {
        implementation: "independent/test",
        contract: name,
        primary,
        ports: super::super::domain_bindings::PortTransform::Default,
    }]));
    let aliases = Box::leak(Box::new(Contribution {
        contracts: &[],
        alternatives,
        logical_refusals: &[],
        ..*owner
    }));
    Registry::assemble(&[aliases, owner])
}

#[test]
fn fixed_owners_refuse_alternative_installation() {
    for (owner, name) in [
        (&table::CONTRIBUTION, "table.relayout"),
        (
            &super::super::fixed_vector::CONTRIBUTION,
            "fixed_vector.dot",
        ),
        (&curve::CONTRIBUTION, "pairing.check"),
        (&field::CONTRIBUTION, "field.embed"),
        (&vector::CONTRIBUTION, "vector.embed"),
        (&control::CONTRIBUTION, "bool.and"),
        (&random::CONTRIBUTION, "random.draw"),
        (&transcript::CONTRIBUTION, "transcript.challenge"),
    ] {
        assert_eq!(
            with_alternative(owner, name, Identity::Bls12381Fr)
                .err()
                .unwrap()
                .detail,
            "implementation-owner-shape",
            "{name}"
        );
    }
}

#[test]
fn transcript_alternatives_keep_payload_codec_and_primary_checks() {
    let registry = with_alternative(
        &transcript::CONTRIBUTION,
        "transcript.observe.field",
        Identity::Merlin3Fr64Be,
    )
    .unwrap();
    for (suite, field, codec, accepted) in [
        (
            "merlin3.bls12-381.fr64be/1",
            "bls12-381.fr",
            "zkcv.field.bls12-381.fr/1",
            true,
        ),
        (
            "merlin3.bls12-381.fr64be/1",
            "bn254.fr",
            "zkcv.field.bn254.fr/1",
            false,
        ),
        (
            "merlin3.bls12-381.fr64be/1",
            "bls12-381.fr",
            "wrong-codec",
            false,
        ),
        (
            "merlin3.ristretto255.scalar64le/1",
            "ristretto255.scalar",
            "zkcv.field.ristretto255.scalar/1",
            false,
        ),
        (
            "spongefish0.7.4.keccak.bls12-381.fr64be/1",
            "bls12-381.fr",
            "zkcv.field.bls12-381.fr/1",
            false,
        ),
    ] {
        let binding = OperationBinding {
            contract: "transcript.observe.field".into(),
            implementation: "independent/test".into(),
            arguments: [suite, field, codec]
                .into_iter()
                .map(str::to_owned)
                .collect(),
        };
        let result =
            logical_signature(&binding).and_then(|logical| registry.select(&binding, &logical));
        assert_eq!(result.is_ok(), accepted, "{binding:?}");
    }
    // Start with a valid logical signature: the registry, not the family, must
    // enforce the alternative's primary identity before invoking its selector.
    let mut binding = OperationBinding {
        contract: "transcript.observe.field".into(),
        implementation: "independent/test".into(),
        arguments: vec![
            "merlin3.bls12-381.fr64be/1".into(),
            "bls12-381.fr".into(),
            "zkcv.field.bls12-381.fr/1".into(),
        ],
    };
    let logical = logical_signature(&binding).unwrap();
    binding.arguments[0] = "spongefish0.7.4.keccak.bls12-381.fr64be/1".into();
    assert!(registry.select(&binding, &logical).is_err());
}

#[test]
fn transcript_table_alternative_applies_the_payload_layout() {
    static ROW: Alternative = Alternative {
        implementation: "independent/msb-observation",
        contract: "transcript.observe.table",
        primary: Identity::Merlin3Fr64Be,
        ports: super::super::domain_bindings::PortTransform::Msb,
    };
    let mut registry = Registry::assemble(&[&transcript::CONTRIBUTION]).unwrap();
    registry
        .install_physical(
            ROW.implementation,
            ROW.contract,
            Selection::Alternative(&ROW),
        )
        .unwrap();
    let binding = OperationBinding {
        contract: ROW.contract.into(),
        implementation: ROW.implementation.into(),
        arguments: [
            "merlin3.bls12-381.fr64be/1",
            "bls12-381.fr",
            "zkcv.table.bls12-381.fr/1",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect(),
    };
    let logical = logical_signature(&binding).unwrap();
    let signature = registry.select(&binding, &logical).unwrap();
    let mut expected = super::super::domain_bindings::physical_signature(
        &logical,
        super::super::domain_bindings::PortTransform::Default,
    )
    .unwrap();
    expected.inputs[1] = super::super::PhysicalType::new(
        logical.inputs[1].clone(),
        super::super::Representation::TableMsb,
    )
    .unwrap();
    assert_eq!(signature, expected);
}

#[test]
fn registry_dispatch_enforces_fixed_contracts() {
    static ROW: Alternative = Alternative {
        implementation: "independent/embedding",
        contract: "field.embed",
        primary: Identity::KoalaBearExt8,
        ports: super::super::domain_bindings::PortTransform::Default,
    };
    // Deliberately bypass completed assembly to test the dispatch guard itself.
    let mut registry = Registry::assemble(&[&field::CONTRIBUTION]).unwrap();
    registry
        .install_physical(
            ROW.implementation,
            ROW.contract,
            Selection::Alternative(&ROW),
        )
        .unwrap();
    let binding = OperationBinding {
        contract: ROW.contract.into(),
        implementation: ROW.implementation.into(),
        arguments: vec![ROW.primary.name().into()],
    };
    assert_eq!(
        registry
            .select(&binding, &logical_signature(&binding).unwrap())
            .unwrap_err()
            .detail,
        "uninstalled operation binding"
    );
}

#[test]
fn alternative_eligibility_is_an_explicit_finite_policy() {
    use std::collections::BTreeSet;
    let expected = "
        field.from_index field.sub field.neg field.inverse field.constant field.add field.mul field.equal
        vector.get vector.slice vector.length vector.rotate vector.interleave vector.prefix_product
        vector.prefix_sum vector.inverse vector.fill vector.geometric vector.constant vector.scatter_sum
        vector.empty vector.append vector.splat vector.powers vector.add vector.sub vector.mul vector.concat
        vector.kronecker vector.scale vector.sum vector.dot vector.split vector.at vector.length_check
        vector.gather vector.matvec vector.from_point vector.to_point vector.from_table vector.to_table
        matrix.mul_vector matrix.transpose_mul_vector matrix.bilinear matrix.identity_check matrix.shape_check
        poly.coefficient_count poly.coset_evaluate poly.coset_interpolate poly.domain_point poly.domain_root
        poly.domain_points poly.even_odd_fold poly.divide_opening poly.opening_quotient poly.equality_weights
        poly.from_coefficients poly.coefficients poly.degree_check poly.univariate_evaluate poly.univariate_boundary
        poly.product_sum poly.product_round poly.boundary poly.round_evaluate poly.fold poly.evaluate
        poly.empty_point poly.append_point
        curve.neg curve.nonidentity curve.msm curve.scale_each curve.vector_add curve.concat curve.vector_scale
        curve.split curve.generator curve.add curve.scale curve.equal curve.empty curve.append curve.at
        curve.get curve.length curve.commit curve.response
        pcs.commit pcs.open pcs.check pcs.equal
        transcript.observe.bool transcript.observe.index transcript.observe.indices transcript.observe.field
        transcript.observe.matrix transcript.observe.vector transcript.observe.polynomial transcript.observe.round
        transcript.observe.table transcript.observe.point transcript.observe.group transcript.observe.groups
        transcript.observe.commitment transcript.observe.proof transcript.observe.commitments
    ".split_whitespace().collect::<BTreeSet<_>>();
    let actual = installed()
        .unwrap()
        .logical
        .iter()
        .filter_map(|(name, (contract, _))| contract.alternatives.then_some(*name))
        .collect::<BTreeSet<_>>();
    assert_eq!(actual, expected);
}
#[test]
fn duplicate_owners_refuse_assembly() {
    assert_eq!(
        Registry::assemble(&[&field::CONTRIBUTION, &field::CONTRIBUTION])
            .err()
            .unwrap()
            .detail,
        "duplicate-logical-owner"
    );
    let mut registry = Registry::assemble(&[&field::CONTRIBUTION]).unwrap();
    assert_eq!(
        registry
            .install_physical("arkworks/field.add", "field.add", Selection::Default)
            .unwrap_err()
            .detail,
        "duplicate-implementation-owner"
    );
    assert!(installed().is_ok());
}
#[test]
fn alternatives_require_a_logical_owner_after_complete_assembly() {
    static ALTERNATIVE: Contribution = Contribution {
        contracts: &[],
        resolve: support::field_signature,
        providers: &[],
        select: default_ports,
        physical_only: false,
        physical_error: "binding-implementation",
        alternatives: &[Alternative {
            implementation: "separate/field.mul",
            contract: "field.mul",
            primary: Identity::Bls12381Fr,
            ports: super::super::domain_bindings::PortTransform::Default,
        }],
        logical_refusals: &[],
    };
    assert_eq!(
        Registry::assemble(&[&ALTERNATIVE]).err().unwrap().detail,
        "implementation-owner-missing"
    );
    assert!(Registry::assemble(&[&ALTERNATIVE, &field::CONTRIBUTION]).is_ok());
    assert!(Registry::assemble(&[&field::CONTRIBUTION, &ALTERNATIVE]).is_ok());
}

#[test]
fn exact_same_port_provider_does_not_depend_on_default_provider() {
    static ROW: Alternative = Alternative {
        implementation: "independent/field.mul",
        contract: "field.mul",
        primary: Identity::Bls12381Fr,
        ports: super::super::domain_bindings::PortTransform::Default,
    };
    let mut registry = Registry::assemble(&[&field::CONTRIBUTION]).unwrap();
    registry
        .install_physical(
            ROW.implementation,
            ROW.contract,
            Selection::Alternative(&ROW),
        )
        .unwrap();
    let mut binding = OperationBinding {
        contract: "field.mul".into(),
        arguments: vec!["bls12-381.fr".into()],
        implementation: ROW.implementation.into(),
    };
    let logical = logical_signature(&binding).unwrap();
    let exact = registry.select(&binding, &logical).unwrap();
    binding.implementation = "arkworks/field.mul".into();
    assert_eq!(exact, registry.select(&binding, &logical).unwrap());
    binding.implementation = "unregistered/field.mul".into();
    assert_eq!(
        registry.select(&binding, &logical).unwrap_err().detail,
        "uninstalled operation binding"
    );
    binding.implementation = ROW.implementation.into();
    binding.arguments = vec!["bn254.fr".into()];
    let logical = logical_signature(&binding).unwrap();
    assert_eq!(
        registry.select(&binding, &logical).unwrap_err().detail,
        "uninstalled operation binding"
    );
    binding.contract = "field.add".into();
    assert_eq!(
        registry.select(&binding, &logical).unwrap_err().detail,
        "uninstalled operation binding"
    );
}

#[test]
fn contribution_refusals_and_custom_shapes_keep_their_own_errors() {
    for (contract, args, expected) in [
        (
            "fixed_vector.dot",
            vec!["koala-bear", "2"],
            "binding-implementation",
        ),
        (
            "resource_unit.create",
            vec!["Slot.A"],
            "binding-implementation",
        ),
        (
            "field.mul",
            vec!["bls12-381.fr"],
            "uninstalled operation binding",
        ),
    ] {
        let binding = OperationBinding {
            contract: contract.into(),
            arguments: args.into_iter().map(str::to_owned).collect(),
            implementation: "missing/owner".into(),
        };
        assert_eq!(binding.signature().unwrap_err().detail, expected);
    }
    for (contract, detail) in [
        ("table.relayout", "binding-adapter-at-logical-stage"),
        (
            "transcript.observe.fixed_vector",
            "fixed-vector-observation-uninstalled",
        ),
    ] {
        let binding = OperationBinding {
            contract: contract.into(),
            arguments: vec![],
            implementation: String::new(),
        };
        assert_eq!(binding.logical_signature().unwrap_err().detail, detail);
    }
    assert_eq!(
        Contract::custom("custom").shape().unwrap_err().detail,
        "contract-shape-missing"
    );
}
