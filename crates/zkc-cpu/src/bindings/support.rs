//! Structural materialization; family owners select domains and applicability.
use super::*;
use crate::domains::NativeDomain;
use zkc_runtime::vm::PhysicalType;

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
        // Exact domain applicability is checked by registry dispatch before the
        // family resolver; the owner still validates domain applicability.
        Selection::Alternative { ports, .. } => Some(ports),
    }
}

/// The declared signature with each port in the family's representation. A
/// family that has no representation of a declared port, or whose
/// representation implements another logical type, refuses the binding.
pub(super) fn materialize(
    binding: &OperationBinding,
    ports: PortTransform,
    make: impl Fn(&LogicalType) -> Option<PhysicalType>,
) -> Option<BoundSignature> {
    let declared = declared(binding)?;
    let make = |logical: &LogicalType| {
        let ty = make(logical).filter(|ty| ty.logical() == logical)?;
        if matches!(ports, PortTransform::Msb) && ty.kind() == Type::Table {
            PhysicalType::new(ty.logical().clone(), Representation::TableMsb).ok()
        } else {
            Some(ty)
        }
    };
    let mut inputs = declared
        .inputs
        .iter()
        .map(&make)
        .collect::<Option<Vec<_>>>()?;
    let mut outputs = declared
        .outputs
        .iter()
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
        *port = PhysicalType::new(port.logical().clone(), representation).ok()?;
    }
    Some(OperationSignature {
        inputs,
        outputs,
        attributes: declared.attributes,
    })
}

pub(super) fn domain_signature(
    binding: &OperationBinding,
    selection: Selection,
    domain: NativeDomain,
) -> Option<BoundSignature> {
    let ports = ports(binding, selection, domain.provider())?;
    materialize(binding, ports, |logical| domain.physical(logical.kind()))
}
