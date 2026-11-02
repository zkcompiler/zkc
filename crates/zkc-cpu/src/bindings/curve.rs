//! Group/scalar association and fixed pairing admission.
use super::*;
use zkc_runtime::vm::PhysicalType;
pub(crate) const fn operation(name: &'static str) -> Contract {
    Contract::new(name, resolve).selectable()
}
fn resolve(
    binding: &OperationBinding,
    _row: &Contract,
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
    support::domain_signature(binding, selection, domain)
}

pub(crate) const fn pairing(name: &'static str) -> Contract {
    Contract::new(name, check_pairing)
}
fn check_pairing(
    binding: &OperationBinding,
    _row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    match selection {
        Selection::Default
            if binding.implementation == format!("arkworks/{}", binding.contract) => {}
        Selection::Alternative {
            ports: PortTransform::Default,
            ..
        } => {}
        _ => return None,
    }
    // The arkworks pairing kernels; the declared ports name each field's
    // installed source and target groups.
    if !matches!(
        binding.arguments.as_slice(),
        [field] if field == "bn254.fr" || field == "bls12-381.fr"
    ) {
        return None;
    }
    support::materialize(binding, PortTransform::Default, |logical| {
        PhysicalType::default_for(logical.clone()).ok()
    })
}
