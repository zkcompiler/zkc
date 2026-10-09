//! Physical-only table layout adaptation.
use super::*;
use zkc_runtime::interactive::{KernelSignature, LogicalType, PhysicalType};
pub(crate) fn relayout(binding: &OperationBinding) -> Option<BoundSignature> {
    let [field, from, to] = binding.arguments.as_slice() else {
        return None;
    };
    if binding.implementation != "arkworks/table.relayout" || field != "bls12-381.fr" {
        return None;
    }
    let make = |name: &str| {
        let representation = match name {
            "arkworks.mle-lsb/0" => Representation::TableLsb,
            "arkworks.mle-msb/0" => Representation::TableMsb,
            _ => return None,
        };
        PhysicalType::new(
            LogicalType::new(Type::Table, Identity::Bls12381Fr).ok()?,
            representation,
        )
        .ok()
    };
    let from = make(from)?;
    let to = make(to)?;
    (from != to).then(|| KernelSignature {
        inputs: vec![from],
        outputs: vec![to],
        attributes: AttributeRule::None,
    })
}
