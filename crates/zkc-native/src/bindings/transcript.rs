//! Concrete transcript suites, codecs and supported observation payloads.
use super::*;
use zkc_runtime::vm::{LogicalType, PhysicalType};

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
    // Only the octic suites install the UniformIndex byte sampler.
    if matches!(
        binding.contract.as_str(),
        "transcript.native.indexed.index" | "transcript.index"
    ) && !t.suite.has_index_transcript()
    {
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
    _row: &Contract,
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
        let payload = match binding.physical_arguments.as_slice() {
            [] => PhysicalType::default_for(logical.clone()).ok()?,
            [selected] => crate::native_contracts().physical_type(selected).ok()?,
            _ => return None,
        };
        if payload.logical() != logical {
            return None;
        }
        if !crate::has_native_wire(&payload)
            || !crate::native_contracts().permits_wire(&payload, zkc_runtime::vm::WireCodec::Native)
        {
            return None;
        }
        support::ports(binding, selection, t.provider)?;
        let state = state(t.suite)?;
        return Some(zkc_runtime::vm::OperationSignature {
            inputs: vec![state.clone(), payload, t.domain.physical(Type::Indices)?],
            outputs: vec![state],
            attributes: AttributeRule::NativeMessageTemplate,
        });
    }
    None
}
