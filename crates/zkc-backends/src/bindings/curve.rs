//! Group/scalar association and fixed pairing admission.
use super::*;
use zkc_runtime::vm::{LogicalType, OperationSignature, PhysicalType};
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
        || binding.implementation != format!("arkworks/{}", binding.contract)
    {
        return None;
    }
    // Each installed pairing field fixes its ordered source and target groups.
    let (g1, g2, gt) = match binding.arguments.as_slice() {
        [field] if field == "bn254.fr" => (Identity::Bn254G1, Identity::Bn254G2, Identity::Bn254Gt),
        [field] if field == "bls12-381.fr" => (
            Identity::Bls12381G1,
            Identity::Bls12381G2,
            Identity::Bls12381Gt,
        ),
        _ => return None,
    };
    let make =
        |kind, identity| PhysicalType::default_for(LogicalType::new(kind, identity).ok()?).ok();
    let [left, right] = row.inputs else {
        return None;
    };
    Some(OperationSignature {
        inputs: vec![make(*left, g1)?, make(*right, g2)?],
        outputs: row
            .outputs
            .iter()
            .map(|&kind| {
                make(
                    kind,
                    if kind == Type::Group {
                        gt
                    } else {
                        Identity::None
                    },
                )
            })
            .collect::<Option<_>>()?,
        attributes: row.attributes,
    })
}
