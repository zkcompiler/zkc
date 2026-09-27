//! Structural materialization; family owners select domains and applicability.
use super::*;
use crate::domains::NativeDomain;
use zkc_runtime::interactive::{KernelSignature, PhysicalType};

pub(super) fn field_domain(binding: &OperationBinding) -> Option<NativeDomain> {
    let [name] = binding.arguments.as_slice() else {
        return None;
    };
    crate::domains::INSTALLED
        .iter()
        .copied()
        .find(|d| name == d.field.name())
}

pub(super) fn ports(
    binding: &OperationBinding,
    selection: Selection,
    provider: &str,
) -> Option<PortTransform> {
    match selection {
        Selection::Default => (binding.implementation
            == format!("{provider}/{}", binding.contract))
        .then_some(PortTransform::Default),
        // Exact primary identity is checked by registry dispatch before the
        // family resolver; the owner still validates domain applicability.
        Selection::Alternative { ports, .. } => Some(ports),
    }
}

// Independently authored here: do not import the runtime's literal refinement.
fn literal_rule(rule: AttributeRule, field: Identity) -> AttributeRule {
    match (field, rule) {
        (Identity::Ristretto255Scalar, AttributeRule::FieldDecimal) => {
            AttributeRule::RistrettoDecimal
        }
        (Identity::Ristretto255Scalar, AttributeRule::FieldDecimals) => {
            AttributeRule::RistrettoDecimals
        }
        (Identity::KoalaBear | Identity::KoalaBearExt8, AttributeRule::FieldDecimal) => {
            AttributeRule::KoalaBearDecimal
        }
        (Identity::KoalaBear | Identity::KoalaBearExt8, AttributeRule::FieldDecimals) => {
            AttributeRule::KoalaBearDecimals
        }
        (Identity::Bn254Fr, AttributeRule::FieldDecimal) => AttributeRule::Bn254Decimal,
        (Identity::Bn254Fr, AttributeRule::FieldDecimals) => AttributeRule::Bn254Decimals,
        _ => rule,
    }
}

pub(super) fn materialize(
    row: &Contract,
    field: Identity,
    ports: PortTransform,
    make: impl Fn(Type) -> Option<PhysicalType>,
) -> Option<BoundSignature> {
    let make = |kind| {
        let ty = make(kind)?;
        if matches!(ports, PortTransform::Msb) && kind == Type::Table {
            PhysicalType::new(ty.logical(), Representation::TableMsb).ok()
        } else {
            Some(ty)
        }
    };
    let mut inputs = row
        .inputs
        .iter()
        .copied()
        .map(&make)
        .collect::<Option<Vec<_>>>()?;
    let mut outputs = row
        .outputs
        .iter()
        .copied()
        .map(make)
        .collect::<Option<Vec<_>>>()?;
    if let PortTransform::Diagonal {
        output,
        port,
        representation,
    } = ports
    {
        let port = if output {
            outputs.get_mut(port)?
        } else {
            inputs.get_mut(port)?
        };
        *port = PhysicalType::new(port.logical(), representation).ok()?;
    }
    Some(KernelSignature {
        inputs,
        outputs,
        attributes: literal_rule(row.attributes, field),
    })
}

pub(super) fn domain_signature(
    binding: &OperationBinding,
    row: &Contract,
    selection: Selection,
    domain: NativeDomain,
) -> Option<BoundSignature> {
    let ports = ports(binding, selection, domain.provider)?;
    materialize(row, domain.field, ports, |kind| domain.physical(kind))
}
