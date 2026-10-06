//! Concrete transcript suites, codecs and supported observation payloads.
use super::*;
use zkc_runtime::interactive::{LogicalType, PhysicalType};

pub(crate) const fn challenge(
    name: &'static str,
    inputs: &'static [Type],
    outputs: &'static [Type],
    attributes: AttributeRule,
) -> Contract {
    Contract::new(name, inputs, outputs, attributes, derive)
}
pub(crate) const fn observation(
    name: &'static str,
    inputs: &'static [Type],
    outputs: &'static [Type],
    attributes: AttributeRule,
) -> Contract {
    Contract::new(name, inputs, outputs, attributes, observe).selectable()
}

fn suite(binding: &OperationBinding) -> Option<crate::domains::NativeTranscript> {
    let t = crate::domains::TRANSCRIPTS
        .iter()
        .copied()
        .find(|t| binding.arguments.first().map(String::as_str) == Some(t.suite.name()))?;
    if binding.contract.starts_with("transcript.native.indexed.")
        && !matches!(
            binding.contract.as_str(),
            "transcript.native.indexed.challenge" | "transcript.native.indexed.observe.data"
        )
        && t.domain.field != Identity::Bls12381Fr
    {
        return None;
    }
    Some(t)
}
fn state(suite: Identity) -> Option<PhysicalType> {
    PhysicalType::new(
        LogicalType::new(Type::Transcript, suite).ok()?,
        Representation::Resource,
    )
    .ok()
}
fn derive(
    binding: &OperationBinding,
    row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    if !matches!(selection, Selection::Default) || binding.arguments.len() != 1 {
        return None;
    }
    let t = suite(binding)?;
    if binding.contract == "transcript.draw_index" && t.suite != Identity::Merlin3KoalaBearExt8 {
        return None;
    }
    let ports = support::ports(binding, selection, t.provider)?;
    support::materialize(row, t.domain.field, ports, |kind| {
        if kind == Type::Transcript {
            state(t.suite)
        } else {
            t.domain.physical(kind)
        }
    })
}
fn observe(
    binding: &OperationBinding,
    row: &Contract,
    selection: Selection,
) -> Option<BoundSignature> {
    let t = suite(binding)?;
    if binding.contract == "transcript.native.indexed.observe.data" {
        if binding.arguments.len() != 2 {
            return None;
        }
        let logical = LogicalType::parse(&binding.arguments[1]).ok()?;
        if !logical.is_native_message_data() {
            return None;
        }
        let payload = PhysicalType::default_for(logical).ok()?;
        if !crate::has_native_wire(&payload) {
            return None;
        }
        support::ports(binding, selection, t.provider)?;
        let state = state(t.suite)?;
        return Some(zkc_runtime::interactive::KernelSignature {
            inputs: vec![state.clone(), payload, t.domain.physical(Type::Indices)?],
            outputs: vec![state],
            attributes: AttributeRule::NativeMessageTemplate,
        });
    }
    let kind = *row.inputs.get(1)?;
    let independent = matches!(kind, Type::Bool | Type::Index | Type::Indices);
    let identity = if independent {
        Identity::None
    } else {
        Identity::parse(binding.arguments.get(1)?).ok()?
    };
    let array = kind == Type::FieldArray;
    let logical = if array {
        if binding.arguments.len() != 3 || identity != Identity::Bls12381Fr {
            return None;
        }
        LogicalType::field_array(
            identity,
            zkc_runtime::logical::natural_index(&binding.arguments[2]).ok()?,
        )
        .ok()?
    } else {
        LogicalType::new(kind, identity).ok()?
    };
    let supported = identity == Identity::None
        || if t.suite == Identity::Merlin3KoalaBearExt8 {
            matches!(
                identity,
                Identity::KoalaBear
                    | Identity::KoalaBearExt8
                    | Identity::MerkleKoalaBear
                    | Identity::MerkleKoalaBearExt8
            )
        } else {
            identity.scalar_field() == Some(t.domain.field)
        };
    if !supported
        || binding.arguments.len() != if independent { 2 } else { 3 }
        || !array && binding.arguments.last().map(String::as_str) != logical.codec().as_deref()
    {
        return None;
    }
    let payload = if array || identity.is_row_commitment() {
        PhysicalType::default_for(logical).ok()?
    } else {
        let domain = if independent {
            t.domain
        } else {
            crate::domains::for_identity(identity)?
        };
        domain.physical(kind)?
    };
    let ports = support::ports(binding, selection, t.provider)?;
    support::materialize(row, t.domain.field, ports, |ty| {
        if ty == kind {
            Some(payload.clone())
        } else if ty == Type::Transcript {
            state(t.suite)
        } else {
            t.domain.physical(ty)
        }
    })
}
