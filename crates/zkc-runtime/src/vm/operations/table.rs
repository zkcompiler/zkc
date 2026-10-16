//! Physical table layout adaptation has no logical-stage source operation.
use super::super::{PhysicalType, Representation};
use super::*;
pub(super) fn select(
    binding: &OperationBinding,
    _: &KernelSignature<LogicalType>,
    selection: Selection,
) -> Result<BoundSignature> {
    selection.require_default()?;
    let fail = || AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding");
    if binding.implementation != "arkworks/table.relayout"
        || binding.arguments.len() != 3
        || binding.arguments[0] != Identity::Bls12381Fr.name()
    {
        return Err(fail());
    }
    let logical = LogicalType::new(Type::Table, Identity::Bls12381Fr)?;
    let from = PhysicalType::new(
        logical.clone(),
        Representation::parse(&binding.arguments[1])?,
    )?;
    let to = PhysicalType::new(logical, Representation::parse(&binding.arguments[2])?)?;
    if from == to {
        return Err(fail());
    }
    Ok(KernelSignature {
        inputs: vec![from],
        outputs: vec![to],
        attributes: AttributeRule::None,
    })
}

pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: &[Contract::custom("table.relayout").implemented_by(&["arkworks/table.relayout"])],
    resolve: |_, _| {
        Err(AdmissionError::new(
            ErrorCode::Signature,
            "binding-adapter-at-logical-stage",
        ))
    },
    select,
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: true,
};
