//! Scalar, vector and matrix arithmetic over an independently installed field.
use super::*;
use zkc_runtime::vm::OperationSignature;

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
    // Installed extensions embed their declared base field.
    use crate::domains::{BINARY64, BINARY64_EXT3, KOALA_BEAR, KOALA_BEAR_EXT4, KOALA_BEAR_EXT8};
    let (base, extension) = match binding.arguments.as_slice() {
        [name] if name == "baby-bear.ext4-binomial11" => {
            (crate::domains::BABY_BEAR, crate::domains::BABY_BEAR_EXT4)
        }
        [name] if name == "goldilocks.ext2-binomial7" => {
            (crate::domains::GOLDILOCKS, crate::domains::GOLDILOCKS_EXT2)
        }
        [name] if name == "koala-bear.ext8-binomial3" => (KOALA_BEAR, KOALA_BEAR_EXT8),
        [name] if name == "koala-bear.ext4-binomial3" => (KOALA_BEAR, KOALA_BEAR_EXT4),
        [name] if name == "gf2-64.pentanomial-4-3-1.ext3-trinomial1" => (BINARY64, BINARY64_EXT3),
        _ => return None,
    };
    if !matches!(selection, Selection::Default)
        || binding.implementation != format!("plonky3/{}", binding.contract)
    {
        return None;
    }
    Some(OperationSignature {
        inputs: row
            .inputs
            .iter()
            .map(|&kind| base.physical(kind))
            .collect::<Option<_>>()?,
        outputs: row
            .outputs
            .iter()
            .map(|&kind| extension.physical(kind))
            .collect::<Option<_>>()?,
        attributes: row.attributes,
    })
}
