//! Typed construction shared by family owners, without family dispatch.
use super::super::domain_bindings::{PortTransform, physical_signature};
use super::*;

pub(super) fn failure() -> AdmissionError {
    AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding")
}

pub(super) fn primary(binding: &OperationBinding) -> Result<Identity> {
    Identity::parse(binding.arguments.first().ok_or_else(failure)?)
}

pub(super) fn literal_rule(rule: AttributeRule, field: Identity) -> AttributeRule {
    match (rule, field) {
        (
            AttributeRule::FieldDecimal,
            Identity::BabyBear
            | Identity::BabyBearExt4
            | Identity::Goldilocks
            | Identity::GoldilocksExt2,
        ) => AttributeRule::ResidueLiteral(field),
        (
            AttributeRule::FieldDecimals,
            Identity::BabyBear
            | Identity::BabyBearExt4
            | Identity::Goldilocks
            | Identity::GoldilocksExt2,
        ) => AttributeRule::ResidueLiterals(field),
        (AttributeRule::FieldDecimal, Identity::Ristretto255Scalar) => {
            AttributeRule::RistrettoDecimal
        }
        (AttributeRule::FieldDecimals, Identity::Ristretto255Scalar) => {
            AttributeRule::RistrettoDecimals
        }
        (
            AttributeRule::FieldDecimal,
            Identity::KoalaBear | Identity::KoalaBearExt8 | Identity::KoalaBearExt4,
        ) => AttributeRule::KoalaBearDecimal,
        (
            AttributeRule::FieldDecimals,
            Identity::KoalaBear | Identity::KoalaBearExt8 | Identity::KoalaBearExt4,
        ) => AttributeRule::KoalaBearDecimals,
        (AttributeRule::FieldDecimal, Identity::Binary64) => AttributeRule::Binary64Literal,
        (AttributeRule::FieldDecimals, Identity::Binary64) => AttributeRule::Binary64Literals,
        (AttributeRule::FieldDecimal, Identity::Binary64Ext3) => AttributeRule::Binary64Ext3Literal,
        (AttributeRule::FieldDecimals, Identity::Binary64Ext3) => {
            AttributeRule::Binary64Ext3Literals
        }
        (AttributeRule::FieldDecimal, Identity::Bn254Fr) => AttributeRule::Bn254Decimal,
        (AttributeRule::FieldDecimals, Identity::Bn254Fr) => AttributeRule::Bn254Decimals,
        _ => rule,
    }
}

/// Family rules have already checked the binding. Registry dispatch owns exact
/// alternative identity matching; default selection checks its nominal provider.
pub(super) fn select_nominal(
    binding: &OperationBinding,
    logical: &OperationSignature<LogicalType>,
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
