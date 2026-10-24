//! Native's immutable composition root. Expected contributions are registered
//! before admission; actual handlers resolve their own family port facts.
use std::sync::OnceLock;
use zkc_runtime::vm::{
    Contracts, ContractsBuilder, ExecutionPolicy, Identity, ImplementationId,
    ImplementationRequirements, LogicalType, OperationBinding, PhysicalType, TimingRequirement,
    Type, WireCodec,
};

struct Installation {
    contracts: Contracts,
    families: Vec<(&'static str, ImplementationId)>,
    dense_layouts: Vec<(Type, zkc_runtime::vm::Representation)>,
    layouts: Vec<PhysicalType>,
    identities: Vec<(OperationBinding, ImplementationId)>,
}
fn installed() -> &'static Installation {
    static INSTALLATION: OnceLock<Installation> = OnceLock::new();
    INSTALLATION.get_or_init(|| {
        let mut builder = ContractsBuilder::standard();
        let mut layouts = Vec::new();
        for (name, kind, identity) in [
            ("blst/fr", Type::Field, Identity::Bls12381Fr),
            ("blst/fr", Type::Vector, Identity::Bls12381Fr),
            ("blst/g1", Type::Group, Identity::Bls12381G1),
            ("blst/g1", Type::Groups, Identity::Bls12381G1),
            ("blst/g2", Type::Group, Identity::Bls12381G2),
            ("blst/g2", Type::Groups, Identity::Bls12381G2),
            ("halo2curves-axiom/bn254.fr", Type::Field, Identity::Bn254Fr),
            (
                "halo2curves-axiom/bn254.fr",
                Type::Vector,
                Identity::Bn254Fr,
            ),
            ("halo2curves-axiom/bn254.g1", Type::Group, Identity::Bn254G1),
            (
                "halo2curves-axiom/bn254.g1",
                Type::Groups,
                Identity::Bn254G1,
            ),
            ("halo2curves-axiom/bn254.g2", Type::Group, Identity::Bn254G2),
            (
                "halo2curves-axiom/bn254.g2",
                Type::Groups,
                Identity::Bn254G2,
            ),
        ] {
            layouts.push(
                builder
                    .add_representation(
                        name,
                        LogicalType::new(kind, identity).expect("native logical layout"),
                    )
                    .expect("native physical layout"),
            );
        }
        for ty in &layouts {
            builder
                .add_wire_permission(ty.clone(), WireCodec::Native)
                .expect("native resident canonical codec");
        }
        let physical = |kind, identity| {
            layouts
                .iter()
                .find(|ty| ty.kind() == kind && ty.logical().identity() == identity)
                .cloned()
        };
        let mut identities = Vec::new();
        for row in crate::operations::arithmetic::CONTRACTS
            .iter()
            .chain(crate::operations::curve::CONTRACTS)
            .chain(crate::operations::curve::PAIRINGS)
        {
            let domains: &[&str] = if row.name.starts_with("curve.") {
                &["bls12-381.g1", "bls12-381.g2"]
            } else {
                &["bls12-381.fr"]
            };
            for domain in domains {
                let declaration = OperationBinding {
                    contract: row.name.into(),
                    arguments: vec![(*domain).into()],
                    implementation: format!("blst/resident/{}", row.name),
                    physical_arguments: vec![],
                };
                if let Some(signature) =
                    crate::operations::blst::signature_with(&declaration, &physical)
                {
                    let requirements = requirements(&declaration);
                    let id = builder
                        .add_implementation(declaration.clone(), signature, requirements)
                        .expect("native resident contract");
                    identities.push((declaration, id));
                }
            }
        }
        // Expected installation inventory is deliberately authored here rather
        // than inferred from the actual Registry or a nominal field match.
        for contract in [
            "field.constant",
            "field.from_index",
            "field.add",
            "field.sub",
            "field.neg",
            "field.mul",
            "field.inverse",
            "field.equal",
            "vector.empty",
            "vector.constant",
            "vector.splat",
            "vector.append",
            "vector.at",
            "vector.get",
            "vector.length",
            "vector.length_check",
            "vector.add",
            "vector.sub",
            "vector.mul",
            "vector.dot",
            "vector.scale",
            "vector.sum",
            "vector.product",
            "vector.split",
            "vector.concat",
            "vector.slice",
            "vector.equal",
            "curve.generator",
            "curve.identity",
            "curve.add",
            "curve.neg",
            "curve.equal",
            "curve.nonidentity",
            "curve.scale",
            "curve.empty",
            "curve.append",
            "curve.at",
            "curve.get",
            "curve.length",
            "curve.vector_add",
            "curve.scale_each",
            "curve.vector_scale",
            "curve.split",
            "curve.concat",
            "curve.msm",
            "pairing.check",
        ] {
            let domains: &[&str] = if contract.starts_with("curve.") {
                &["bn254.g1", "bn254.g2"]
            } else {
                &["bn254.fr"]
            };
            for domain in domains {
                let declaration = OperationBinding {
                    contract: contract.into(),
                    arguments: vec![(*domain).into()],
                    implementation: format!("halo2curves-axiom/resident/{contract}"),
                    physical_arguments: vec![],
                };
                let signature = crate::operations::resident::signature_with(
                    &declaration,
                    "halo2curves-axiom",
                    &physical,
                )
                .expect("expected BN254 resident ports");
                let id = builder
                    .add_implementation(declaration.clone(), signature, requirements(&declaration))
                    .expect("expected BN254 resident contract");
                identities.push((declaration, id));
            }
        }
        let scalar = physical(Type::Field, Identity::Bls12381Fr).expect("resident scalar");
        let vector = physical(Type::Vector, Identity::Bls12381Fr).expect("resident vector");
        let mut families = Vec::new();
        let mut dense_layouts = Vec::new();
        for (name, kind, rows) in [
            (
                "blst/field-array",
                Type::FieldArray,
                crate::field_array::RESIDENT_IMPLEMENTATIONS,
            ),
            (
                "blst/fixed-vector",
                Type::FixedVector,
                crate::fixed_vector::RESIDENT_IMPLEMENTATIONS,
            ),
        ] {
            let representation = builder
                .add_aggregate_representation(
                    name,
                    kind,
                    zkc_runtime::vm::AggregateChildRule::Repeated {
                        element: scalar.clone(),
                        maximum_length: 1_048_576,
                    },
                )
                .expect("resident dense storage");
            dense_layouts.push((kind, representation));
            if kind == Type::FieldArray {
                builder
                    .allow_aggregate_native_message(representation)
                    .expect("resident array canonical frame");
            }
            let family = if kind == Type::FieldArray {
                zkc_runtime::vm::AggregateImplementationFamily::FieldArray {
                    representation,
                    scalar: scalar.clone(),
                    vector: vector.clone(),
                }
            } else {
                zkc_runtime::vm::AggregateImplementationFamily::FixedVector {
                    representation,
                    scalar: scalar.clone(),
                    vector: vector.clone(),
                }
            };
            for &(implementation, contract) in rows {
                let id = builder
                    .add_implementation_family(
                        contract,
                        implementation,
                        family.clone(),
                        ImplementationRequirements::default(),
                    )
                    .expect("resident dense family");
                families.push((implementation, id));
            }
        }
        for resident in &layouts {
            let default =
                PhysicalType::default_for(resident.logical().clone()).expect("native Ark layout");
            for (source, target) in [(&default, resident), (resident, &default)] {
                let declaration = OperationBinding {
                    contract: "representation.convert".into(),
                    arguments: vec![resident.logical().spelling()],
                    physical_arguments: vec![source.spelling(), target.spelling()],
                    implementation: "native/representation.convert".into(),
                };
                let signature = zkc_runtime::vm::OperationSignature {
                    inputs: vec![source.clone()],
                    outputs: vec![target.clone()],
                    attributes: zkc_runtime::vm::AttributeRule::None,
                };
                let requirements = requirements(&declaration);
                let id = builder
                    .add_implementation(declaration.clone(), signature, requirements)
                    .expect("native direct conversion contract");
                identities.push((declaration, id));
            }
        }
        Installation {
            families,
            dense_layouts,
            contracts: builder.finish(ExecutionPolicy {
                allow_unspecified_timing: true,
                allow_variable_time: false,
            }),
            layouts,
            identities,
        }
    })
}
fn requirements(binding: &OperationBinding) -> ImplementationRequirements {
    ImplementationRequirements {
        timing: if matches!(
            binding.implementation.as_str(),
            "blst/resident/curve.msm" | "halo2curves-axiom/resident/curve.msm"
        ) {
            TimingRequirement::VariableTime
        } else {
            TimingRequirement::Unspecified
        },
        timing_operands: if matches!(
            binding.implementation.as_str(),
            "blst/resident/curve.msm" | "halo2curves-axiom/resident/curve.msm"
        ) {
            &[0, 1]
        } else {
            &[]
        },
    }
}
/// Explicit trusted Native inventory. Default policy does not authorize MSM.
pub fn native_contracts() -> &'static Contracts {
    &installed().contracts
}
/// Select a trusted execution policy while retaining the installed layout IDs.
pub fn native_contracts_with_policy(policy: ExecutionPolicy) -> Contracts {
    native_contracts().with_policy(policy)
}

pub(crate) fn physical(kind: Type, identity: Identity) -> Option<&'static PhysicalType> {
    if !matches!(
        (kind, identity),
        (
            Type::Field | Type::Vector,
            Identity::Bls12381Fr | Identity::Bn254Fr
        ) | (
            Type::Group | Type::Groups,
            Identity::Bls12381G1 | Identity::Bls12381G2 | Identity::Bn254G1 | Identity::Bn254G2
        )
    ) {
        return None;
    }
    installed()
        .layouts
        .iter()
        .find(|ty| ty.kind() == kind && ty.logical().identity() == identity)
}
pub(crate) fn actual_identity(binding: &OperationBinding) -> Option<ImplementationId> {
    installed()
        .identities
        .iter()
        .find(|(declaration, _)| declaration == binding)
        .map(|(_, id)| *id)
        .or_else(|| {
            installed()
                .families
                .iter()
                .find(|(name, _)| *name == binding.implementation)
                .map(|(_, id)| *id)
        })
}

pub(crate) fn dense_representation(kind: Type) -> Option<zkc_runtime::vm::Representation> {
    installed()
        .dense_layouts
        .iter()
        .find(|(constructor, _)| *constructor == kind)
        .map(|(_, representation)| *representation)
}
