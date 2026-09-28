//! Typed construction shared by family owners, without family dispatch.
use super::super::domain_bindings::{PortTransform, physical_signature};
use super::*;

pub(super) fn failure() -> AdmissionError {
    AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding")
}

pub(super) fn primary(binding: &OperationBinding) -> Result<Identity> {
    Identity::parse(binding.arguments.first().ok_or_else(failure)?)
}

pub(super) fn require_primary(binding: &OperationBinding, identity: Identity) -> Result<()> {
    if binding.arguments.len() != 1 || primary(binding)? != identity {
        return Err(failure());
    }
    Ok(())
}

pub(super) fn field_type(kind: Type, field: Identity) -> Result<LogicalType> {
    let identity = match kind {
        Type::Bool | Type::Index | Type::Indices => Identity::None,
        Type::Field
        | Type::NonzeroField
        | Type::Matrix
        | Type::Vector
        | Type::Polynomial
        | Type::Round
        | Type::Table
        | Type::Point
        | Type::Rng
        | Type::Nonce => field,
        _ => return Err(failure()),
    };
    LogicalType::new(kind, identity)
}

pub(super) fn literal_rule(rule: AttributeRule, field: Identity) -> AttributeRule {
    match (rule, field) {
        (AttributeRule::FieldDecimal, Identity::Ristretto255Scalar) => {
            AttributeRule::RistrettoDecimal
        }
        (AttributeRule::FieldDecimals, Identity::Ristretto255Scalar) => {
            AttributeRule::RistrettoDecimals
        }
        (AttributeRule::FieldDecimal, Identity::KoalaBear | Identity::KoalaBearExt8) => {
            AttributeRule::KoalaBearDecimal
        }
        (AttributeRule::FieldDecimals, Identity::KoalaBear | Identity::KoalaBearExt8) => {
            AttributeRule::KoalaBearDecimals
        }
        (AttributeRule::FieldDecimal, Identity::Bn254Fr) => AttributeRule::Bn254Decimal,
        (AttributeRule::FieldDecimals, Identity::Bn254Fr) => AttributeRule::Bn254Decimals,
        _ => rule,
    }
}

pub(super) fn instantiate(
    shape: KernelSignature,
    field: Identity,
    make: impl Fn(Type) -> Result<LogicalType>,
) -> Result<KernelSignature<LogicalType>> {
    Ok(KernelSignature {
        inputs: shape.inputs.into_iter().map(&make).collect::<Result<_>>()?,
        outputs: shape.outputs.into_iter().map(make).collect::<Result<_>>()?,
        attributes: literal_rule(shape.attributes, field),
    })
}

pub(super) fn field_signature(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let shape = contract.shape()?;
    let primary = primary(binding)?;
    let field = primary.scalar_field().ok_or_else(failure)?;
    require_primary(binding, field)?;
    instantiate(shape, field, |kind| field_type(kind, field))
}

/// Family rules have already checked the binding. Registry dispatch owns exact
/// alternative identity matching; default selection checks its nominal provider.
pub(super) fn select_nominal(
    binding: &OperationBinding,
    logical: &KernelSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    let ports = match selection {
        Selection::Default => {
            let provider = primary(binding)?.provider().ok_or_else(failure)?;
            if binding.implementation != format!("{provider}/{}", binding.contract) {
                return Err(failure());
            }
            PortTransform::Default
        }
        Selection::Alternative(row) => row.ports,
    };
    physical_signature(logical, ports)
}
