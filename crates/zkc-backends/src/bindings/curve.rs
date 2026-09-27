//! Group/scalar association and fixed pairing admission.
use super::*;
use zkc_runtime::interactive::{KernelSignature, LogicalType, PhysicalType};
pub(crate) const fn operation(
    name: &'static str,
    inputs: &'static [Type],
    outputs: &'static [Type],
    attributes: AttributeRule,
) -> Contract {
    Contract::new(name, inputs, outputs, attributes, resolve).selectable()
}
fn resolve(
    binding: &OperationBinding,
    row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    let [name] = binding.arguments.as_slice() else {
        return None;
    };
    let domain = if binding.contract == "curve.response" {
        support::field_domain(binding)?
    } else {
        crate::domains::INSTALLED
            .iter()
            .copied()
            .find(|d| d.group.is_some_and(|g| g.name() == name))?
    };
    support::domain_signature(binding, row, selection, domain)
}

pub(crate) const fn pairing(
    name: &'static str,
    inputs: &'static [Type],
    outputs: &'static [Type],
    attributes: AttributeRule,
) -> Contract {
    Contract::new(name, inputs, outputs, attributes, check_pairing)
}
fn check_pairing(
    binding: &OperationBinding,
    row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    if !matches!(selection, Selection::Default)
        || binding.arguments != ["bn254.fr"]
        || binding.implementation != "arkworks/pairing.check"
    {
        return None;
    }
    let make =
        |kind, identity| PhysicalType::default_for(LogicalType::new(kind, identity).ok()?).ok();
    let [left, right] = row.inputs else {
        return None;
    };
    Some(KernelSignature {
        inputs: vec![
            make(*left, Identity::Bn254G1)?,
            make(*right, Identity::Bn254G2)?,
        ],
        outputs: row
            .outputs
            .iter()
            .map(|&kind| make(kind, Identity::None))
            .collect::<Option<_>>()?,
        attributes: row.attributes,
    })
}
