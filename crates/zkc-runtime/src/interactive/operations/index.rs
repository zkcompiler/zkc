//! Independently authored index operation contracts and physical policy.
use super::*;
use Type::*;

pub(super) const CONTRACTS: &[Contract] = &[
    Contract::new("index.constant", (&[], &[Index], AttributeRule::Unsigned64)),
    Contract::new(
        "index.add",
        (&[Index, Index], &[Index], AttributeRule::None),
    ),
    Contract::new(
        "index.sub",
        (&[Index, Index], &[Index], AttributeRule::None),
    ),
    Contract::new(
        "index.mul",
        (&[Index, Index], &[Index], AttributeRule::None),
    ),
    Contract::new(
        "index.div",
        (&[Index, Index], &[Index], AttributeRule::None),
    ),
    Contract::new(
        "index.mod",
        (&[Index, Index], &[Index], AttributeRule::None),
    ),
    Contract::new(
        "index.equal",
        (&[Index, Index], &[Bool], AttributeRule::None),
    ),
    Contract::new(
        "index.less",
        (&[Index, Index], &[Bool], AttributeRule::None),
    ),
    Contract::new("indices.empty", (&[], &[Indices], AttributeRule::None)),
    Contract::new(
        "indices.append",
        (&[Indices, Index], &[Indices], AttributeRule::None),
    ),
    Contract::new(
        "indices.at",
        (&[Indices, Index], &[Index], AttributeRule::None),
    ),
    Contract::new(
        "indices.length",
        (&[Indices], &[Index], AttributeRule::None),
    ),
];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "uninstalled operation binding",
    physical_only: false,

    contracts: CONTRACTS,
    resolve,
    providers: &["native"],
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
