//! Independently installed Arkworks implementations. Do not advertise signatures
//! by calling the runtime's source-contract resolver.

mod catalogue;
mod vectors;
use self::catalogue::CONTRACTS;
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, KernelSignature, LogicalType, OperationBinding,
    PhysicalType, Representation, Type,
};

fn table_type(msb: bool) -> Option<PhysicalType> {
    PhysicalType::new(
        LogicalType::new(Type::Table, Identity::Bls12381Fr).ok()?,
        if msb {
            Representation::TableMsb
        } else {
            Representation::TableLsb
        },
    )
    .ok()
}

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    if matches!(
        binding.contract.as_str(),
        "resource_unit.create" | "resource_unit.pass" | "resource_unit.consume"
    ) {
        let [domain] = binding.arguments.as_slice() else {
            return None;
        };
        if binding.implementation != format!("logical/{}", binding.contract) {
            return None;
        }
        let ty = PhysicalType::default_for(LogicalType::resource_unit(
            zkc_runtime::interactive::ResourceDomain::parse(domain).ok()?,
        ));
        let (inputs, outputs) = match binding.contract.as_str() {
            "resource_unit.create" => (vec![], vec![ty]),
            "resource_unit.pass" => (vec![ty.clone()], vec![ty]),
            "resource_unit.consume" => (vec![ty], vec![]),
            _ => return None,
        };
        return Some(KernelSignature {
            inputs,
            outputs,
            attributes: AttributeRule::None,
        });
    }
    let args: Vec<_> = binding.arguments.iter().map(String::as_str).collect();
    let contract = binding.contract.as_str();
    if contract.starts_with("oracle.")
        || contract.starts_with("commitments.")
        || contract.starts_with("opening_states.")
    {
        return crate::oracle::signature(binding);
    }
    if contract.starts_with("index.") || contract.starts_with("indices.") {
        return crate::kernels::indices::signature(binding);
    }
    if matches!(contract, "field.embed" | "vector.embed") {
        if args != ["koala-bear.ext8-binomial3"]
            || binding.implementation != format!("plonky3/{contract}")
        {
            return None;
        }
        let kind = if contract == "field.embed" {
            Type::Field
        } else {
            Type::Vector
        };
        return Some(KernelSignature {
            inputs: vec![crate::domains::KOALA_BEAR.physical(kind)?],
            outputs: vec![crate::domains::KOALA_BEAR_EXT8.physical(kind)?],
            attributes: AttributeRule::None,
        });
    }
    if contract == "table.relayout" {
        if binding.implementation != "arkworks/table.relayout"
            || args.len() != 3
            || args[0] != "bls12-381.fr"
        {
            return None;
        }
        let msb = |name| match name {
            "arkworks.mle-lsb/1" => Some(false),
            "arkworks.mle-msb/1" => Some(true),
            _ => None,
        };
        let from = table_type(msb(args[1])?)?;
        let to = table_type(msb(args[2])?)?;
        return (from != to).then(|| KernelSignature {
            inputs: vec![from],
            outputs: vec![to],
            attributes: AttributeRule::None,
        });
    }
    if binding.contract == "pairing.check" {
        if binding.arguments != ["bn254.fr"] || binding.implementation != "arkworks/pairing.check" {
            return None;
        }
        let make = |kind, identity| {
            Some(PhysicalType::default_for(
                LogicalType::new(kind, identity).ok()?,
            ))
        };
        return Some(KernelSignature {
            inputs: vec![
                make(Type::Groups, Identity::Bn254G1)?,
                make(Type::Groups, Identity::Bn254G2)?,
            ],
            outputs: vec![make(Type::Bool, Identity::None)?],
            attributes: AttributeRule::None,
        });
    }
    let (row, payload) = if let Some(name) = contract.strip_prefix("transcript.observe.") {
        let kind = [
            Type::Index,
            Type::Indices,
            Type::Commitments,
            Type::Bool,
            Type::Field,
            Type::Matrix,
            Type::Vector,
            Type::Polynomial,
            Type::Round,
            Type::Table,
            Type::Point,
            Type::Group,
            Type::Groups,
            Type::Commitment,
            Type::Proof,
        ]
        .into_iter()
        .find(|t| t.name() == name)?;
        (None, Some(kind))
    } else {
        (
            Some(
                CONTRACTS
                    .iter()
                    .chain(crate::bindings::vectors::CONTRACTS)
                    .find(|c| c.0 == contract)?,
            ),
            None,
        )
    };
    let common = matches!(
        contract,
        "bool.and" | "bool.not" | "bool.or" | "control.require"
    );
    let transcript = if contract.starts_with("transcript.") {
        Some(
            crate::domains::TRANSCRIPTS
                .iter()
                .copied()
                .find(|t| args.first() == Some(&t.suite.name()))?,
        )
    } else {
        None
    };
    let domain = if let Some(t) = transcript {
        t.domain
    } else if common {
        crate::domains::BLS
    } else {
        crate::domains::INSTALLED.iter().copied().find(|d| {
            let expected = if contract.starts_with("curve.") && contract != "curve.response" {
                d.group.map(Identity::name)
            } else if contract.starts_with("pcs.") && d.provider == "arkworks" {
                Some("multilinear.kzg.bls12-381/1")
            } else {
                Some(d.field.name())
            };
            expected.is_some_and(|name| args.first() == Some(&name))
        })?
    };
    if matches!(
        contract,
        "poly.coset_evaluate"
            | "poly.coset_interpolate"
            | "poly.domain_point"
            | "poly.domain_root"
            | "poly.domain_points"
            | "poly.even_odd_fold"
            | "poly.opening_quotient"
    ) && !matches!(
        domain.field,
        Identity::Bn254Fr | Identity::KoalaBear | Identity::KoalaBearExt8
    ) {
        return None;
    }
    if contract == "poly.even_odd_fold" && !domain.field.has_characteristic_not_two() {
        return None;
    }
    let payload_type = if let Some(kind) = payload {
        let independent = matches!(kind, Type::Bool | Type::Index | Type::Indices);
        let identity = if independent {
            Identity::None
        } else {
            Identity::parse(args.get(1)?).ok()?
        };
        let logical = LogicalType::new(kind, identity).ok()?;
        let t = transcript?;
        let supported = identity == Identity::None
            || if t.suite == Identity::Merlin3KoalaBearExt8 {
                matches!(
                    identity,
                    Identity::KoalaBear
                        | Identity::KoalaBearExt8
                        | Identity::MerkleKoalaBear
                        | Identity::MerkleKoalaBearExt8
                )
            } else {
                identity.scalar_field() == Some(domain.field)
            };
        if !supported
            || args.len() != if independent { 2 } else { 3 }
            || args.last().copied() != logical.codec().as_deref()
        {
            return None;
        }
        Some(if identity.is_row_commitment() {
            PhysicalType::default_for(logical)
        } else {
            let d = if independent {
                domain
            } else {
                crate::domains::for_identity(identity)?
            };
            d.physical(kind)?
        })
    } else {
        None
    };
    if payload.is_none() && args.len() != usize::from(!common) {
        return None;
    }
    if contract == "random.index" && domain.field != Identity::KoalaBearExt8 {
        return None;
    }
    if contract == "transcript.draw_index" && transcript?.suite != Identity::Merlin3KoalaBearExt8 {
        return None;
    }
    let provider = transcript.map_or(domain.provider, |t| t.provider);
    let dense = binding.implementation == format!("{provider}/{contract}");
    let msb = domain.field == Identity::Bls12381Fr
        && domain.provider == "arkworks"
        && binding.implementation == format!("arkworks-msb/{contract}")
        && matches!(
            contract,
            "poly.product_sum"
                | "poly.product_round"
                | "poly.boundary"
                | "poly.round_evaluate"
                | "poly.fold"
                | "poly.evaluate"
                | "poly.empty_point"
                | "poly.append_point"
                | "vector.from_table"
                | "vector.to_table"
        );
    let diagonal = domain.field != Identity::Bn254Fr
        && matches!(
            (binding.implementation.as_str(), domain.provider),
            (
                "arkworks-diagonal/vector.mul" | "arkworks-diagonal/vector.dot",
                "arkworks"
            ) | (
                "dalek-diagonal/curve.scale_each" | "dalek-diagonal/curve.msm",
                "dalek"
            )
        )
        && binding.implementation.split_once('/')?.1 == contract;
    let public_msm = domain.field == Identity::Ristretto255Scalar
        && contract == "curve.msm"
        && binding.implementation == crate::public_operands::MSM_IMPLEMENTATION;
    if !dense && !msb && !diagonal && !public_msm {
        return None;
    }
    let (inputs, outputs, mut attributes) = if let Some(kind) = payload {
        (
            vec![Type::Transcript, kind],
            vec![Type::Transcript],
            AttributeRule::MessageOrigin,
        )
    } else {
        let (_, ins, outs, attrs) = row?;
        (ins.to_vec(), outs.to_vec(), *attrs)
    };
    let physical = |kind| {
        if payload == Some(kind) {
            return payload_type.clone();
        }
        let ty = if kind == Type::Transcript {
            PhysicalType::new(
                LogicalType::new(kind, transcript?.suite).ok()?,
                Representation::Resource,
            )
            .ok()?
        } else {
            domain.physical(kind)?
        };
        if msb && kind == Type::Table {
            PhysicalType::new(ty.logical(), Representation::TableMsb).ok()
        } else {
            Some(ty)
        }
    };
    let mut inputs = inputs
        .into_iter()
        .map(physical)
        .collect::<Option<Vec<_>>>()?;
    let mut outputs = outputs
        .into_iter()
        .map(physical)
        .collect::<Option<Vec<_>>>()?;
    if domain.provider == "dalek" && attributes == AttributeRule::FieldDecimal {
        attributes = AttributeRule::RistrettoDecimal;
    }
    if matches!(domain.field, Identity::KoalaBear | Identity::KoalaBearExt8)
        && attributes == AttributeRule::FieldDecimal
    {
        attributes = AttributeRule::KoalaBearDecimal;
    }
    if domain.field == Identity::Bn254Fr {
        if attributes == AttributeRule::FieldDecimal {
            attributes = AttributeRule::Bn254Decimal;
        }
        if attributes == AttributeRule::FieldDecimals {
            attributes = AttributeRule::Bn254Decimals;
        }
    }
    if domain.field == Identity::Ristretto255Scalar && attributes == AttributeRule::FieldDecimals {
        attributes = AttributeRule::RistrettoDecimals;
    }
    if matches!(domain.field, Identity::KoalaBear | Identity::KoalaBearExt8)
        && attributes == AttributeRule::FieldDecimals
    {
        attributes = AttributeRule::KoalaBearDecimals;
    }
    if diagonal {
        let repr = if domain.provider == "dalek" {
            Representation::RistrettoDiagonal
        } else {
            Representation::FrDiagonal
        };
        let port = if matches!(contract, "vector.mul" | "curve.scale_each") {
            outputs.first_mut()?
        } else {
            inputs.get_mut(1)?
        };
        *port = PhysicalType::new(port.logical(), repr).ok()?;
    }
    Some(KernelSignature {
        inputs,
        outputs,
        attributes,
    })
}
