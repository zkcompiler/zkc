//! Nominal instantiation of mathematical contracts; native advertisements are
//! checked separately. This catalogue does not install arbitrary identities.
use super::{
    AdmissionError, AttributeRule, BoundSignature, ErrorCode, Identity, KernelSignature,
    LogicalType, OperationBinding, PhysicalType, Representation, Type,
};

pub(super) fn signature(b: &OperationBinding) -> Result<BoundSignature, AdmissionError> {
    let fail = || AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding");
    let mut shape = super::model::operation_shape(&b.contract).ok_or_else(fail)?;
    if b.contract.starts_with("index.")
        || b.contract.starts_with("indices.")
        || b.contract.starts_with("external.")
    {
        if !b.arguments.is_empty() || b.implementation != format!("native/{}", b.contract) {
            return Err(fail());
        }
        let make = |kind| LogicalType::new(kind, Identity::None).map(PhysicalType::default_for);
        return Ok(KernelSignature {
            inputs: shape
                .inputs
                .into_iter()
                .map(make)
                .collect::<Result<_, _>>()?,
            outputs: shape
                .outputs
                .into_iter()
                .map(make)
                .collect::<Result<_, _>>()?,
            attributes: shape.attributes,
        });
    }
    if b.contract.starts_with("oracle.")
        || b.contract.starts_with("commitments.")
        || b.contract.starts_with("opening_states.")
    {
        if b.arguments.len() != 1 || b.implementation != format!("plonky3/{}", b.contract) {
            return Err(fail());
        }
        let scheme = Identity::parse(&b.arguments[0])?;
        if !scheme.is_row_commitment() {
            return Err(fail());
        }
        let make = |kind| {
            let identity = match kind {
                Type::Bool | Type::Index => Identity::None,
                Type::Vector => scheme.scalar_field().ok_or_else(fail)?,
                _ => scheme,
            };
            LogicalType::new(kind, identity).map(PhysicalType::default_for)
        };
        return Ok(KernelSignature {
            inputs: shape
                .inputs
                .into_iter()
                .map(make)
                .collect::<Result<_, _>>()?,
            outputs: shape
                .outputs
                .into_iter()
                .map(make)
                .collect::<Result<_, _>>()?,
            attributes: shape.attributes,
        });
    }
    if b.contract == "pairing.check" {
        if b.arguments != ["bn254.fr"] || b.implementation != "arkworks/pairing.check" {
            return Err(fail());
        }
        let make = |kind, identity| {
            Ok::<_, AdmissionError>(PhysicalType::default_for(LogicalType::new(kind, identity)?))
        };
        return Ok(KernelSignature {
            inputs: vec![
                make(Type::Groups, Identity::Bn254G1)?,
                make(Type::Groups, Identity::Bn254G2)?,
            ],
            outputs: vec![make(Type::Bool, Identity::None)?],
            attributes: AttributeRule::None,
        });
    }
    let common = matches!(
        b.contract.as_str(),
        "bool.and" | "bool.not" | "bool.or" | "control.require"
    );
    let primary = if common {
        if !b.arguments.is_empty() {
            return Err(fail());
        }
        Identity::Bls12381Fr
    } else {
        Identity::parse(b.arguments.first().ok_or_else(fail)?)?
    };
    let field = primary.scalar_field().ok_or_else(fail)?;
    if b.contract == "poly.even_odd_fold" && !field.has_characteristic_not_two() {
        return Err(fail());
    }
    if matches!(
        b.contract.as_str(),
        "poly.coset_evaluate"
            | "poly.coset_interpolate"
            | "poly.domain_point"
            | "poly.domain_root"
            | "poly.domain_points"
            | "poly.even_odd_fold"
            | "poly.opening_quotient"
    ) && !matches!(
        field,
        Identity::Bn254Fr | Identity::KoalaBear | Identity::KoalaBearExt8
    ) {
        return Err(fail());
    }
    let group = primary.group();
    let transcript = primary.transcript();
    let observe = b.contract.strip_prefix("transcript.observe.");
    let payload = if let Some(kind) = observe {
        if Some(primary) != transcript {
            return Err(fail());
        }
        let kind = Type::parse_kind(kind)?;
        let identity = if matches!(kind, Type::Bool | Type::Index | Type::Indices) {
            Identity::None
        } else {
            Identity::parse(b.arguments.get(1).ok_or_else(fail)?)?
        };
        let ty = LogicalType::new(kind, identity)?;
        // One suite admits only matching scalar/group payload domains plus Bool.
        if identity != Identity::None
            && !(if primary == Identity::Merlin3KoalaBearExt8 {
                matches!(
                    identity,
                    Identity::KoalaBear
                        | Identity::KoalaBearExt8
                        | Identity::MerkleKoalaBear
                        | Identity::MerkleKoalaBearExt8
                )
            } else {
                identity.scalar_field() == Some(field)
            })
        {
            return Err(fail());
        }
        let count = if matches!(kind, Type::Bool | Type::Index | Type::Indices) {
            2
        } else {
            3
        };
        if b.arguments.len() != count || b.arguments.last() != ty.codec().as_ref() {
            return Err(fail());
        }
        Some(ty)
    } else {
        if !common && b.arguments.len() != 1 {
            return Err(fail());
        }
        let required = if b.contract.starts_with("pcs.") {
            Identity::MultilinearKzgBls12381
        } else if b.contract.starts_with("curve.") && b.contract != "curve.response" {
            group.ok_or_else(fail)?
        } else if matches!(
            b.contract.as_str(),
            "transcript.challenge" | "transcript.draw_index"
        ) {
            transcript.ok_or_else(fail)?
        } else {
            field
        };
        if primary != required {
            return Err(fail());
        }
        None
    };
    if (b.contract == "random.index" && primary != Identity::KoalaBearExt8)
        || (b.contract == "transcript.draw_index" && primary != Identity::Merlin3KoalaBearExt8)
    {
        return Err(fail());
    }
    let provider = primary.provider().ok_or_else(fail)?;
    let dense = b.implementation == format!("{provider}/{}", b.contract);
    let msb = field == Identity::Bls12381Fr
        && provider == "arkworks"
        && b.implementation == format!("arkworks-msb/{}", b.contract)
        && matches!(
            b.contract.as_str(),
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
    let diagonal = b.implementation == format!("{provider}-diagonal/{}", b.contract)
        && matches!(
            (field, b.contract.as_str()),
            (Identity::Bls12381Fr, "vector.mul" | "vector.dot")
                | (
                    Identity::Ristretto255Scalar,
                    "curve.scale_each" | "curve.msm"
                )
        );
    let public_msm = primary == Identity::Ristretto255Group
        && b.contract == "curve.msm"
        && b.implementation == "dalek-vartime/curve.msm";
    if !dense && !msb && !diagonal && !public_msm {
        return Err(fail());
    }
    if field == Identity::Ristretto255Scalar && shape.attributes == AttributeRule::FieldDecimal {
        shape.attributes = AttributeRule::RistrettoDecimal;
    }
    if matches!(field, Identity::KoalaBear | Identity::KoalaBearExt8)
        && shape.attributes == AttributeRule::FieldDecimal
    {
        shape.attributes = AttributeRule::KoalaBearDecimal;
    }
    if field == Identity::Bn254Fr {
        if shape.attributes == AttributeRule::FieldDecimal {
            shape.attributes = AttributeRule::Bn254Decimal;
        }
        if shape.attributes == AttributeRule::FieldDecimals {
            shape.attributes = AttributeRule::Bn254Decimals;
        }
    }
    if field == Identity::Ristretto255Scalar && shape.attributes == AttributeRule::FieldDecimals {
        shape.attributes = AttributeRule::RistrettoDecimals;
    }
    if matches!(field, Identity::KoalaBear | Identity::KoalaBearExt8)
        && shape.attributes == AttributeRule::FieldDecimals
    {
        shape.attributes = AttributeRule::KoalaBearDecimals;
    }
    let make = |kind| {
        if payload.as_ref().is_some_and(|p| p.kind() == kind) {
            return Ok(PhysicalType::default_for(payload.clone().unwrap()));
        }
        let identity = match kind {
            Type::Bool | Type::Index | Type::Indices => Identity::None,
            Type::Group | Type::Groups => group.ok_or_else(fail)?,
            Type::Transcript => transcript.ok_or_else(fail)?,
            Type::Commitment
            | Type::Proof
            | Type::ProverKey
            | Type::VerifierKey
            | Type::OpeningState => Identity::MultilinearKzgBls12381,
            _ => field,
        };
        if field != Identity::Bls12381Fr && identity == Identity::MultilinearKzgBls12381 {
            return Err(fail());
        }
        let logical = LogicalType::new(kind, identity)?;
        if msb && kind == Type::Table {
            PhysicalType::new(logical, Representation::TableMsb)
        } else {
            Ok(PhysicalType::default_for(logical))
        }
    };
    let mut inputs = shape
        .inputs
        .into_iter()
        .map(make)
        .collect::<Result<Vec<_>, _>>()?;
    let mut outputs = shape
        .outputs
        .into_iter()
        .map(make)
        .collect::<Result<Vec<_>, _>>()?;
    if matches!(b.contract.as_str(), "field.embed" | "vector.embed") {
        let base = field.base_field().ok_or_else(fail)?;
        inputs[0] = PhysicalType::default_for(LogicalType::new(
            if b.contract == "field.embed" {
                Type::Field
            } else {
                Type::Vector
            },
            base,
        )?);
    }
    if let Some(payload) = payload {
        inputs[1] = PhysicalType::default_for(payload);
    }
    if diagonal {
        let repr = if field == Identity::Bls12381Fr {
            Representation::FrDiagonal
        } else {
            Representation::RistrettoDiagonal
        };
        let port = if matches!(b.contract.as_str(), "vector.mul" | "curve.scale_each") {
            &mut outputs[0]
        } else {
            &mut inputs[1]
        };
        *port = PhysicalType::new(port.logical(), repr)?;
    }
    Ok(KernelSignature {
        inputs,
        outputs,
        attributes: shape.attributes,
    })
}
