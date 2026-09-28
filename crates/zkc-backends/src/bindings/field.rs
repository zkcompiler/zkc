//! Scalar, vector and matrix arithmetic over an independently installed field.
use super::*;
use zkc_runtime::interactive::KernelSignature;

pub(crate) const fn operation(
    name: &'static str,
    inputs: &'static [Type],
    outputs: &'static [Type],
    attributes: AttributeRule,
) -> Contract {
    fixed(name, inputs, outputs, attributes).selectable()
}

pub(crate) const fn fixed(
    name: &'static str,
    inputs: &'static [Type],
    outputs: &'static [Type],
    attributes: AttributeRule,
) -> Contract {
    Contract::new(name, inputs, outputs, attributes, resolve)
}
fn resolve(
    binding: &OperationBinding,
    row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    support::domain_signature(binding, row, selection, support::field_domain(binding)?)
}

pub(crate) const fn embedding(
    name: &'static str,
    inputs: &'static [Type],
    outputs: &'static [Type],
    attributes: AttributeRule,
) -> Contract {
    Contract::new(name, inputs, outputs, attributes, embed)
}
fn embed(
    binding: &OperationBinding,
    row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    if !matches!(selection, Selection::Default)
        || binding.arguments != ["koala-bear.ext8-binomial3"]
        || binding.implementation != format!("plonky3/{}", binding.contract)
    {
        return None;
    }
    Some(KernelSignature {
        inputs: row
            .inputs
            .iter()
            .map(|&kind| crate::domains::KOALA_BEAR.physical(kind))
            .collect::<Option<_>>()?,
        outputs: row
            .outputs
            .iter()
            .map(|&kind| crate::domains::KOALA_BEAR_EXT8.physical(kind))
            .collect::<Option<_>>()?,
        attributes: row.attributes,
    })
}
