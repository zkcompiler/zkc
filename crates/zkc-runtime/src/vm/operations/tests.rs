use super::*;

#[test]
fn selected_matrix_contractions_preserve_field_and_explicit_provider() {
    for name in ["matrix.row_dot", "matrix.column_dot"] {
        for (field, provider) in [
            ("bls12-381.fr", "arkworks"),
            ("bn254.fr", "arkworks"),
            ("ristretto255.scalar", "dalek"),
            ("koala-bear", "plonky3"),
            ("koala-bear.ext8-binomial3", "plonky3"),
        ] {
            let binding = OperationBinding {
                physical_arguments: vec![],
                contract: name.into(),
                arguments: vec![field.into()],
                implementation: format!("{provider}/{name}"),
            };
            let identity = Identity::parse(field).unwrap();
            let signature = logical_signature(&binding).unwrap();
            assert_eq!(
                signature.inputs,
                [
                    LogicalType::new(Type::Matrix, identity).unwrap(),
                    LogicalType::new(Type::Vector, identity).unwrap(),
                    LogicalType::parse("index").unwrap(),
                ]
            );
            assert_eq!(
                signature.outputs,
                [LogicalType::new(Type::Field, identity).unwrap()]
            );
            assert_eq!(signature.attributes, AttributeRule::None);
            assert!(binding.signature().is_ok());
            for arguments in [
                vec![],
                vec![field.into(), "0".into()],
                vec!["bls12-381.g1".into()],
            ] {
                assert_eq!(
                    OperationBinding {
                        arguments,
                        ..binding.clone()
                    }
                    .signature()
                    .unwrap_err()
                    .code,
                    ErrorCode::Signature
                );
            }
            for other in ["arkworks", "dalek", "plonky3", "missing"] {
                let selected = OperationBinding {
                    physical_arguments: vec![],
                    implementation: format!("{other}/{name}"),
                    ..binding.clone()
                };
                assert_eq!(selected.signature().is_ok(), other == provider);
            }
            let wrong_operation = OperationBinding {
                physical_arguments: vec![],
                implementation: format!("{provider}/matrix.bilinear"),
                ..binding
            };
            assert_eq!(
                wrong_operation.signature().unwrap_err().code,
                ErrorCode::Signature
            );
        }
    }
}

#[test]
fn vector_product_has_one_vector_and_same_field_scalar_result() {
    for (field, provider) in [
        ("bls12-381.fr", "arkworks"),
        ("bn254.fr", "arkworks"),
        ("ristretto255.scalar", "dalek"),
        ("koala-bear", "plonky3"),
        ("koala-bear.ext8-binomial3", "plonky3"),
    ] {
        let binding = OperationBinding {
            physical_arguments: vec![],
            contract: "vector.product".into(),
            arguments: vec![field.into()],
            implementation: format!("{provider}/vector.product"),
        };
        let identity = Identity::parse(field).unwrap();
        let signature = logical_signature(&binding).unwrap();
        assert_eq!(
            signature.inputs,
            [LogicalType::new(Type::Vector, identity).unwrap()]
        );
        assert_eq!(
            signature.outputs,
            [LogicalType::new(Type::Field, identity).unwrap()]
        );
        assert_eq!(signature.attributes, AttributeRule::None);
        assert!(binding.signature().is_ok());
        for arguments in [
            vec![],
            vec![field.into(), field.into()],
            vec!["bls12-381.g1".into()],
        ] {
            assert_eq!(
                OperationBinding {
                    arguments,
                    ..binding.clone()
                }
                .signature()
                .unwrap_err()
                .code,
                ErrorCode::Signature
            );
        }
        for implementation in ["missing/vector.product", "arkworks/vector.sum"] {
            assert_eq!(
                OperationBinding {
                    physical_arguments: vec![],
                    implementation: implementation.into(),
                    ..binding.clone()
                }
                .signature()
                .unwrap_err()
                .code,
                ErrorCode::Signature
            );
        }
    }
}

fn with_alternative(
    owner: &'static Contribution,
    name: &'static str,
    primary: Identity,
) -> Result<Registry> {
    let alternatives = Box::leak(Box::new([Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "independent/test",
        contract: name,
        domains: Box::leak(Box::new([primary])),
        ports: super::super::domain_bindings::PortTransform::Default,
    }]));
    let aliases = Box::leak(Box::new(Contribution {
        contracts: &[],
        alternatives,
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
        (&curve::CONTRIBUTION, "pairing.apply"),
        (&field::CONTRIBUTION, "field.embed"),
        (&vector::CONTRIBUTION, "vector.embed"),
        (&control::CONTRIBUTION, "bool.and"),
        (&random::CONTRIBUTION, "random.draw"),
        (
            &transcript::CONTRIBUTION,
            "transcript.native.indexed.challenge",
        ),
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
fn transcript_alternatives_keep_payload_and_primary_checks() {
    let registry = with_alternative(
        &transcript::CONTRIBUTION,
        "transcript.native.indexed.observe.data",
        Identity::Merlin3Fr64Be,
    )
    .unwrap();
    for (suite, payload, accepted) in [
        ("merlin3.bls12-381.fr64be/0", "field:bls12-381.fr", true),
        ("merlin3.bls12-381.fr64be/0", "field:bn254.fr", true),
        ("merlin3.bls12-381.fr64be/0", "wrong-type", false),
        (
            "merlin3.ristretto255.scalar64le/0",
            "field:ristretto255.scalar",
            false,
        ),
        (
            "spongefish0.8.0.keccak.bls12-381.fr64be/0",
            "field:bls12-381.fr",
            false,
        ),
    ] {
        let binding = OperationBinding {
            physical_arguments: vec![],
            contract: "transcript.native.indexed.observe.data".into(),
            implementation: "independent/test".into(),
            arguments: vec![suite.into(), payload.into()],
        };
        let result =
            logical_signature(&binding).and_then(|logical| registry.select(&binding, &logical));
        assert_eq!(result.is_ok(), accepted, "{binding:?}");
    }
    let mut binding = OperationBinding {
        physical_arguments: vec![],
        contract: "transcript.native.indexed.observe.data".into(),
        implementation: "independent/test".into(),
        arguments: vec![
            "merlin3.bls12-381.fr64be/0".into(),
            "field:bls12-381.fr".into(),
        ],
    };
    let logical = logical_signature(&binding).unwrap();
    binding.arguments[0] = "spongefish0.8.0.keccak.bls12-381.fr64be/0".into();
    assert!(registry.select(&binding, &logical).is_err());
}

#[test]
fn transcript_data_refuses_local_table_layouts() {
    for payload in [
        "table:bls12-381.fr",
        "polynomial:bls12-381.fr",
        "point:bls12-381.fr",
    ] {
        let binding = OperationBinding {
            physical_arguments: vec![],
            contract: "transcript.native.indexed.observe.data".into(),
            implementation: "arkworks/transcript.native.indexed.observe.data".into(),
            arguments: vec!["merlin3.bls12-381.fr64be/0".into(), payload.into()],
        };
        assert!(binding.signature().is_err());
    }
}

#[test]
fn registry_dispatch_enforces_fixed_contracts() {
    static ROW: Alternative = Alternative {
        timing: TimingRequirement::Unspecified,
        implementation: "independent/embedding",
        contract: "field.embed",
        domains: &[Identity::KoalaBearExt8],
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
        physical_arguments: vec![],
        contract: ROW.contract.into(),
        implementation: ROW.implementation.into(),
        arguments: vec![ROW.domains[0].name().into()],
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
        multilinear.restrict_prefix
        vector.transpose vector.equal vector.find_last vector.get vector.slice vector.length vector.rotate vector.interleave vector.prefix_product
        vector.bit_reverse vector.bit_reverse_rows
        vector.prefix_sum vector.inverse vector.fill vector.geometric vector.constant vector.scatter_sum
        vector.empty vector.append vector.splat vector.powers vector.add vector.sub vector.mul vector.concat
        vector.kronecker vector.scale vector.sum vector.product vector.dot vector.split vector.at vector.length_check
        vector.gather vector.matvec vector.from_point vector.to_point vector.from_table vector.to_table
        matrix.mul_vector matrix.transpose_mul_vector matrix.bilinear matrix.identity_check matrix.shape_check matrix.dimension matrix.get matrix.row_dot matrix.column_dot
        poly.coefficient_count poly.coset_evaluate poly.coset_evaluate_batch poly.coset_extend poly.coset_evaluate_at poly.coset_interpolate poly.domain_point poly.domain_root
        poly.domain_points poly.even_odd_fold poly.divide_opening poly.opening_quotient poly.opening_quotient_sum poly.equality_weights
        poly.from_coefficients poly.coefficients poly.degree_check poly.univariate_evaluate poly.univariate_boundary
        ring.point ring.rows ring.coefficients ring.affine_sum
        poly.table_arity poly.product_sum poly.product_round poly.boundary poly.round_evaluate poly.fold poly.evaluate
        poly.empty_point poly.append_point
        curve.neg curve.nonidentity curve.msm curve.scale_each curve.vector_add curve.concat curve.vector_scale
        curve.split curve.generator curve.identity curve.add curve.scale curve.equal curve.empty curve.append curve.at
        curve.get curve.length curve.commit curve.response
        pairing.check
        pcs.commit pcs.open pcs.check pcs.equal
        transcript.native.indexed.observe.data
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

        select: default_ports,
        physical_error: "binding-implementation",
        alternatives: &[Alternative {
            timing: TimingRequirement::Unspecified,
            implementation: "separate/field.mul",
            contract: "field.mul",
            domains: &[Identity::Bls12381Fr],
            ports: super::super::domain_bindings::PortTransform::Default,
        }],
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
        timing: TimingRequirement::Unspecified,
        implementation: "independent/field.mul",
        contract: "field.mul",
        domains: &[Identity::Bls12381Fr],
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
        physical_arguments: vec![],
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
            physical_arguments: vec![],
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
            "uninstalled operation binding",
        ),
    ] {
        let binding = OperationBinding {
            physical_arguments: vec![],
            contract: contract.into(),
            arguments: vec![],
            implementation: String::new(),
        };
        assert_eq!(binding.logical_signature().unwrap_err().detail, detail);
    }
}

#[test]
fn independent_history_classification_matches_installed_inventory() {
    let fixture =
        include_str!("../../../../zkc-test-support/fixtures/variants/history-contracts.txt");
    let mut seen = std::collections::BTreeSet::new();
    // Native-only contracts have no portable Lean source interpretation. Keep
    // the shared portable inventory unchanged and enumerate this extension.
    let native = "quotient.add 0
quotient.subtract 0
quotient.multiply 0
quotient.norm_within 0
quotient.project 0
quotient.ntt 0
quotient.intt 0
quotient.pointwise 0
quotient.prepare_matrix 0
quotient.matvec 0
representation.convert 0
numerical.map 0
numerical.sum 0
numerical.product 0
vector.find_last 0
poly.coset_extend 0
poly.coset_evaluate_batch 0
poly.coset_evaluate_at 0
poly.opening_quotient_sum 0
matrix.row_dot 0
matrix.column_dot 0
transcript.native.indexed.challenge 1
transcript.native.indexed.index 1
transcript.native.indexed.indices 1
transcript.native.indexed.indices.search 1
transcript.native.indexed.indices.gated 1
transcript.native.indexed.observe.data 1
transcript.observe 1
transcript.challenge 1
transcript.index 1
ring.point 0
ring.rows 0
ring.coefficients 0
ring.affine_sum 0
relation.table_rows 0
relation.table_shape 0
relation.table_input 0
relation.table_scope 0
relation.table_point 0
relation.table_points 0
relation.table_widths 0
relation.table_policy 0
relation.table_interactions 0
relation.table_interaction 0
relation.table_record_points 0
vector.transpose 0
vector.bit_reverse 0
vector.bit_reverse_rows 0
oracle.open_many 0
oracle.check_many 0";
    let sequences = "sequence.empty 0\nsequence.append 0\nsequence.length 0\nsequence.at 0";
    let bytes = "encoding.index_uleb128 0\nbytes.repeat 0\nbytes.join 0\nencoding.fields_be 0\nencoding.fields_le 0\nencoding.groups_compressed 0\nbytes.empty 0\nbytes.append 0\nbytes.concat 0\nbytes.slice 0\nbytes.at 0\nbytes.length 0\nbytes.equal 0
shake128.init 0
shake128.absorb 1
shake128.squeeze 1
encoding.field_be 0
encoding.field_from_be 0
encoding.field_reduce_be 0
encoding.group_compressed 0
encoding.group_from_compressed 0
encoding.field_le 0
encoding.field_from_le 0
encoding.field_reduce_le 0
encoding.group_decode_cofactor 0
encoding.cryptonote_map 0
encoding.fields_from_be 0
encoding.fields_from_le 0
encoding.field_montgomery_le 0
encoding.field_from_montgomery_le 0
encoding.fields_montgomery_le 0
encoding.fields_from_montgomery_le 0
hash.keccak256 0
hash.sha256 0
hash.poseidon2_16 0";
    for line in fixture
        .lines()
        .chain(native.lines())
        .chain(sequences.lines())
        .chain(bytes.lines())
    {
        let (contract, expected) = line.split_once(' ').expect("inventory row");
        assert!(seen.insert(contract), "duplicate inventory contract");
        assert!(matches!(expected, "0" | "1"));
        assert_eq!(
            observes_history(contract).unwrap(),
            expected == "1",
            "{contract}"
        );
    }
    for contract in installed().unwrap().logical.keys() {
        assert!(
            seen.contains(contract),
            "missing history contract: {contract}"
        );
    }
}

#[test]
fn installation_cannot_invent_a_logical_contract_or_history_facet() {
    static OWNER: Contribution = Contribution {
        contracts: &[Installation::new("independent.absorb")],
        ..control::CONTRIBUTION
    };
    assert_eq!(
        Registry::assemble(&[&OWNER]).err().unwrap().detail,
        "undeclared-logical-contract"
    );
    let registry = Registry::assemble(&[&hash::CONTRIBUTION, &transcript::CONTRIBUTION]).unwrap();
    assert!(registry.observes_history("shake128.absorb").unwrap());
    assert!(!registry.observes_history("hash.keccak256").unwrap());
    assert!(registry.observes_history("transcript.unknown").is_err());
}

#[test]
fn multilinear_prefix_restriction_has_exact_vector_ports_and_binding() {
    for (field, provider) in [
        ("bls12-381.fr", "arkworks"),
        ("bn254.fr", "arkworks"),
        ("ristretto255.scalar", "dalek"),
        ("koala-bear.ext8-binomial3", "plonky3"),
        ("gf2-64.pentanomial-4-3-1", "plonky3"),
    ] {
        let binding = OperationBinding {
            contract: "multilinear.restrict_prefix".into(),
            arguments: vec![field.into()],
            implementation: format!("{provider}/multilinear.restrict_prefix"),
            physical_arguments: vec![],
        };
        let vector = LogicalType::new(Type::Vector, Identity::parse(field).unwrap()).unwrap();
        let signature = logical_signature(&binding).unwrap();
        assert_eq!(signature.inputs, [vector.clone(), vector.clone()]);
        assert_eq!(signature.outputs, [vector]);
        assert_eq!(signature.attributes, AttributeRule::None);
        assert!(binding.signature().is_ok());
        for arguments in [
            vec![],
            vec![field.into(), "0".into()],
            vec!["bls12-381.g1".into()],
        ] {
            assert_eq!(
                OperationBinding {
                    arguments,
                    ..binding.clone()
                }
                .signature()
                .unwrap_err()
                .code,
                ErrorCode::Signature
            );
        }
        for implementation in [
            "missing/multilinear.restrict_prefix",
            "arkworks/vector.split",
        ] {
            assert_eq!(
                OperationBinding {
                    implementation: implementation.into(),
                    ..binding.clone()
                }
                .signature()
                .unwrap_err()
                .code,
                ErrorCode::Signature
            );
        }
    }
}

#[test]
fn physical_erasure_is_declared_without_source_or_installation_authority() {
    for (contract, arguments, logical) in [
        (
            "representation.convert",
            vec!["field:bls12-381.fr"],
            "field:bls12-381.fr",
        ),
        (
            "table.relayout",
            vec!["bls12-381.fr", "arkworks.mle-lsb/0", "arkworks.mle-msb/0"],
            "table:bls12-381.fr",
        ),
    ] {
        let binding = OperationBinding {
            contract: contract.into(),
            arguments: arguments.into_iter().map(String::from).collect(),
            implementation: String::new(),
            physical_arguments: vec![],
        };
        assert_eq!(
            zkc_catalog::operation(contract).unwrap().stage,
            zkc_catalog::Stage::Physical
        );
        let signature = declared_logical_signature(&binding).unwrap();
        assert_eq!(signature.inputs, [LogicalType::parse(logical).unwrap()]);
        assert_eq!(signature.outputs, signature.inputs);
        assert_eq!(signature.attributes, AttributeRule::None);
        assert_eq!(
            logical_signature(&binding).unwrap_err().detail,
            "binding-adapter-at-logical-stage"
        );
        assert!(
            binding.signature().is_err(),
            "erasure installed an implementation"
        );
        let malformed = OperationBinding {
            arguments: vec![],
            ..binding
        };
        assert!(declared_logical_signature(&malformed).is_err());
    }
}

#[test]
fn physical_installation_cannot_invent_a_contract() {
    static OWNER: Contribution = Contribution {
        contracts: &[Installation::new("independent.convert")],
        ..representation::CONTRIBUTION
    };
    assert_eq!(
        Registry::assemble(&[&OWNER]).err().unwrap().detail,
        "undeclared-logical-contract"
    );
}

#[test]
fn index_blocks_require_explicit_keccak_installation_and_exact_ports() {
    for suite in [
        "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0",
        "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0",
        "merlin3.koala-bear.ext8-binomial3.rejection31le/0",
        "hash-chain.keccak256.bls12-381.fr64be/0",
    ] {
        let identity = Identity::parse(suite).unwrap();
        for (contract, inputs, outputs, rule) in [
            (
                "transcript.native.indexed.indices",
                vec!["transcript", "indices"],
                vec!["indices", "transcript"],
                AttributeRule::NativeIndexBlock,
            ),
            (
                "transcript.native.indexed.indices.search",
                vec!["transcript", "indices"],
                vec!["indices", "index", "transcript"],
                AttributeRule::NativeGatedIndexBlock,
            ),
            (
                "transcript.native.indexed.indices.gated",
                vec!["transcript", "index", "indices"],
                vec!["indices", "transcript"],
                AttributeRule::NativeGatedIndexBlock,
            ),
        ] {
            let binding = OperationBinding {
                contract: contract.into(),
                arguments: vec![suite.into()],
                implementation: format!("plonky3/{contract}"),
                physical_arguments: vec![],
            };
            if !identity.has_index_block_transcript() {
                assert!(binding.logical_signature().is_err());
                assert!(binding.signature().is_err());
                continue;
            }
            let signature = binding.signature().unwrap();
            assert_eq!(signature.attributes, rule);
            assert_eq!(
                signature
                    .inputs
                    .iter()
                    .map(|t| t.kind().name())
                    .collect::<Vec<_>>(),
                inputs
            );
            assert_eq!(
                signature
                    .outputs
                    .iter()
                    .map(|t| t.kind().name())
                    .collect::<Vec<_>>(),
                outputs
            );
            assert!(
                signature
                    .inputs
                    .iter()
                    .chain(&signature.outputs)
                    .filter(|t| t.kind() == Type::Transcript)
                    .all(|t| t.logical().identity() == identity)
            );
            let mut unknown = binding.clone();
            unknown.implementation = format!("native/{contract}");
            assert!(unknown.signature().is_err());
            let mut unknown = binding;
            unknown.arguments.push("3".into());
            assert!(unknown.signature().is_err());
        }
    }
}
