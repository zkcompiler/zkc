//! Physical port construction, independent of operation-family admission.
use super::{
    AdmissionError, BoundSignature, ErrorCode, KernelSignature, LogicalType, PhysicalType,
    Representation, Type,
};

#[derive(Clone, Copy)]
pub(super) enum PortTransform {
    Default,
    Msb,
    Diagonal {
        output: bool,
        port: usize,
        representation: Representation,
    },
}

pub(super) fn physical_signature(
    logical: &KernelSignature<LogicalType>,
    ports: PortTransform,
) -> Result<BoundSignature, AdmissionError> {
    let make = |ty: &LogicalType| {
        if matches!(ports, PortTransform::Msb) && ty.kind() == Type::Table {
            PhysicalType::new(ty.clone(), Representation::TableMsb)
        } else {
            PhysicalType::default_for(ty.clone())
        }
    };
    let mut inputs = logical
        .inputs
        .iter()
        .map(make)
        .collect::<Result<Vec<_>, _>>()?;
    let mut outputs = logical
        .outputs
        .iter()
        .map(make)
        .collect::<Result<Vec<_>, _>>()?;
    if let PortTransform::Diagonal {
        output,
        port,
        representation,
    } = ports
    {
        let port = if output {
            outputs
                .get_mut(port)
                .ok_or_else(|| AdmissionError::new(ErrorCode::Signature, "binding-port"))?
        } else {
            inputs
                .get_mut(port)
                .ok_or_else(|| AdmissionError::new(ErrorCode::Signature, "binding-port"))?
        };
        *port = PhysicalType::new(port.logical(), representation)?;
    }
    Ok(KernelSignature {
        inputs,
        outputs,
        attributes: logical.attributes,
    })
}
