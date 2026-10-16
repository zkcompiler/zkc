//! Independently authored index operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new("index.constant", (&[], &[Index], AttributeRule::Unsigned64))
        .implemented_by(&["native/index.constant"]),
    Contract::new(
        "index.add",
        (&[Index, Index], &[Index], AttributeRule::None),
    )
    .implemented_by(&["native/index.add"]),
    Contract::new(
        "index.sub",
        (&[Index, Index], &[Index], AttributeRule::None),
    )
    .implemented_by(&["native/index.sub"]),
    Contract::new(
        "index.mul",
        (&[Index, Index], &[Index], AttributeRule::None),
    )
    .implemented_by(&["native/index.mul"]),
    Contract::new(
        "index.div",
        (&[Index, Index], &[Index], AttributeRule::None),
    )
    .implemented_by(&["native/index.div"]),
    Contract::new(
        "index.mod",
        (&[Index, Index], &[Index], AttributeRule::None),
    )
    .implemented_by(&["native/index.mod"]),
    Contract::new(
        "index.equal",
        (&[Index, Index], &[Bool], AttributeRule::None),
    )
    .implemented_by(&["native/index.equal"]),
    Contract::new(
        "index.less",
        (&[Index, Index], &[Bool], AttributeRule::None),
    )
    .implemented_by(&["native/index.less"]),
    Contract::new("indices.empty", (&[], &[Indices], AttributeRule::None))
        .implemented_by(&["native/indices.empty"]),
    Contract::new(
        "indices.append",
        (&[Indices, Index], &[Indices], AttributeRule::None),
    )
    .implemented_by(&["native/indices.append"]),
    Contract::new(
        "indices.at",
        (&[Indices, Index], &[Index], AttributeRule::None),
    )
    .implemented_by(&["native/indices.at"]),
    Contract::new(
        "indices.length",
        (&[Indices], &[Index], AttributeRule::None),
    )
    .implemented_by(&["native/indices.length"]),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
    select: default_ports,
};

pub(super) fn resolve(
    binding: &OperationBinding,
    contract: &Contract,
) -> Result<KernelSignature<LogicalType>> {
    let fail = || AdmissionError::new(ErrorCode::Signature, "uninstalled operation binding");
    let shape = contract.shape()?;
    if !binding.arguments.is_empty() {
        return Err(fail());
    }
    let make = |kind| LogicalType::new(kind, Identity::None);
    Ok(KernelSignature {
        inputs: shape.inputs.into_iter().map(make).collect::<Result<_>>()?,
        outputs: shape.outputs.into_iter().map(make).collect::<Result<_>>()?,
        attributes: shape.attributes,
    })
}
