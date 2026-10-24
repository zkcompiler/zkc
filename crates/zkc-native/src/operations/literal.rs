//! Reached static literal decoding and invocation-local result publication.
//! Preparation shares typed facts; each vector result keeps its fresh allocation.
use super::{
    arithmetic::reserve,
    field::{Family, with_field},
};
use crate::{Policy, Result, Value, refused, value::size};
use zkc_runtime::vm::{Invocation, Value as _};

// Literal preparation and publication use the exact physical output family,
// including resident providers. No conversion through another provider occurs.
macro_rules! with_literal_family {
    ($output:expr, |$coefficient:ident| $body:expr) => {
        if super::blst::is_resident($output) {
            type $coefficient = zkc_kernels::blst::bls12_381::ScalarElement;
            $body
        } else if super::halo2curves::is_resident($output) {
            type $coefficient = zkc_kernels::halo2curves::bn254::ScalarElement;
            $body
        } else {
            with_field!($output.logical().identity(), |$coefficient| $body)
        }
    };
}

/// Decode one immutable literal at the reached attribute checkpoint. Vector
/// storage is bounded before allocation; invalid attributes still precede any
/// pending size, output or numerical-memory refusal, as in ordinary validation.
pub(crate) fn prepare(
    output: &zkc_runtime::vm::PhysicalType,
    attributes: &[String],
    policy: &Policy,
    available: usize,
) -> Result<Value> {
    with_literal_family!(output, |S| match output.kind() {
        zkc_runtime::vm::Type::Field => super::field::literal::<S>(attributes),
        zkc_runtime::vm::Type::Vector => vector::<S>(attributes, policy, available),
        _ => Err(refused("kernel-operands")),
    })
}

pub(super) fn vector<S: Family>(
    attributes: &[String],
    p: &Policy,
    available: usize,
) -> Result<Value> {
    let call = crate::numerical::Call::new(p, available);
    let mut destination = (|| {
        let n = attributes.len();
        let width = std::mem::size_of::<S>();
        p.vector_width(n, width)?;
        let bytes = size(n, width)?;
        p.output(bytes, available)?;
        call.destination(S::RESIDENT_STORAGE, bytes, || reserve::<S>(n))
    })();
    for literal in attributes {
        let coefficient = S::decimal(literal)?;
        if let Ok(destination) = &mut destination {
            destination.push(coefficient);
        }
    }
    let value = destination?.finish(|values| Ok(S::vector_value(values)))?;
    // Constructors may retain capacity beyond the logical extent. Check the
    // actual immutable owner's charge before publishing preparation storage.
    p.output(value.retained_bytes(), available)?;
    Ok(value)
}

/// Preparation grants no invocation allowance. Even a warm literal checks the
/// current element, retained-byte and resident numerical-storage ceilings.
pub(crate) fn publish(value: &Value, i: &Invocation<'_>, p: &Policy) -> Result<Vec<Value>> {
    let output = i
        .binding
        .signature()
        .outputs
        .first()
        .ok_or_else(|| refused("kernel-operands"))?;
    if output.kind() == zkc_runtime::vm::Type::Field {
        return super::field::publish_literal(value, i, p);
    }
    with_literal_family!(output, |S| {
        let values = S::vector(value)?;
        p.vector_width(values.len(), std::mem::size_of::<S>())?;
        let bytes = value.retained_bytes();
        p.output(bytes, i.max_output_bytes)?;
        let call = crate::numerical::Call::new(p, i.max_output_bytes);
        // Preparation reuses decoding, not result allocation identity. Each
        // reached vector constant retains its original fresh-result charge and
        // fallible allocation boundary, including when another result is live.
        let mut destination =
            call.destination(S::RESIDENT_STORAGE, bytes, || reserve::<S>(values.len()))?;
        destination.extend_from_slice(values);
        let result = destination.finish(|values| Ok(S::vector_value(values)))?;
        p.output(result.retained_bytes(), i.max_output_bytes)?;
        Ok(vec![result])
    })
}
