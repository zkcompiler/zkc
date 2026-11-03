//! Scalar, vector and matrix arithmetic over an independently installed field.
use super::*;

pub(crate) const fn operation(name: &'static str) -> Contract {
    Contract::new(name, resolve).selectable()
}
fn resolve(
    binding: &OperationBinding,
    _row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    support::domain_signature(binding, selection, support::field_domain(binding)?)
}

pub(crate) const fn embedding(name: &'static str) -> Contract {
    Contract::new(name, embed)
}
fn embed(
    binding: &OperationBinding,
    _row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    // An installed extension embeds its declared base field: the declared
    // ports name both fields, and Plonky3 implements both.
    let [name] = binding.arguments.as_slice() else {
        return None;
    };
    let extension = Identity::parse(name).ok()?;
    let base = extension.base_field()?;
    if !matches!(selection, Selection::Default)
        || binding.implementation != format!("plonky3/{}", binding.contract)
        || [base, extension]
            .iter()
            .any(|field| field.provider() != Some("plonky3"))
    {
        return None;
    }
    support::materialize(binding, PortTransform::Default, |logical| {
        crate::domains::for_identity(logical.identity())?.physical(logical.kind())
    })
}
