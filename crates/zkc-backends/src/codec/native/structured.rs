//! Expected-type framing for immutable records, sums and dynamic numeric data.
//! Framing is scanned and the entire retained allocation is charged before any
//! payload value is constructed. Descriptors never come from message bytes.
use super::{NativeWireError as Error, unsupported};
use crate::{NativeBackend, Policy, Value};
use zkc_runtime::interactive::{DecodeReason, PhysicalType, Type, Value as RuntimeValue};

type Result<T> = std::result::Result<T, Error>;
pub(super) fn add(a: usize, b: usize) -> Result<usize> {
    a.checked_add(b).ok_or(Error::Limit)
}
pub(super) fn mul(a: usize, b: usize) -> Result<usize> {
    a.checked_mul(b).ok_or(Error::Limit)
}
pub(super) fn invalid(reason: DecodeReason) -> Error {
    Error::Invalid(reason)
}
fn physical(ty: &zkc_runtime::interactive::LogicalType) -> Result<PhysicalType> {
    PhysicalType::default_for(ty.clone()).map_err(|_| unsupported())
}
pub(super) fn tag(ty: &PhysicalType) -> Option<u8> {
    if !ty.has_native_data_frame() {
        return None;
    }
    match ty.kind() {
        Type::Sequence => Some(69),
        Type::Variant => Some(65),
        Type::Indices => Some(68),
        _ => None,
    }
}
// Counts are per complete message, so nesting cannot multiply a collection's
// configured work limit. Retained allocation is charged separately.
#[derive(Default)]
struct Counts {
    nodes: usize,
    elements: usize,
    groups: usize,
}
impl Counts {
    pub(super) fn add(&mut self, elements: usize, groups: usize) -> Result<()> {
        self.elements = add(self.elements, elements)?;
        self.groups = add(self.groups, groups)?;
        Ok(())
    }
    fn admit(&self, policy: &Policy) -> Result<()> {
        policy
            .vector_width(self.nodes, 512)
            .map_err(|_| Error::Limit)?;
        policy
            .vector_width(self.elements, 32)
            .map_err(|_| Error::Limit)?;
        policy.groups(self.groups).map_err(|_| Error::Limit)
    }
}
// Typed ingress follows the same whole-value collection accounting as wire
// scans. It does not reserve encoded buffers or charge decoding peak memory.
pub(super) fn check_value_counts(value: &Value, policy: &Policy) -> Result<()> {
    fn visit(ty: &PhysicalType, value: &Value, policy: &Policy, counts: &mut Counts) -> Result<()> {
        if value.physical_type() != *ty {
            return Err(unsupported());
        }
        counts.nodes = add(counts.nodes, 1)?;
        counts.admit(policy)?;
        if let Some(tag) = tag(ty) {
            match (tag, value) {
                (69, Value::Sequence(v)) => {
                    let logical = ty.logical();
                    let element = physical(logical.sequence_element().ok_or_else(unsupported)?)?;
                    for child in v.elements() {
                        visit(&element, child, policy, counts)?;
                    }
                }
                (65, Value::Variant(v)) => {
                    let logical = ty.logical();
                    let descriptor = logical.variant_descriptor().ok_or_else(unsupported)?;
                    let arm = descriptor
                        .alternatives()
                        .get(v.alternative())
                        .ok_or_else(unsupported)?;
                    if arm.payload().len() != v.payload().len() {
                        return Err(unsupported());
                    }
                    for (leaf, child) in arm.payload().iter().zip(v.payload()) {
                        visit(&physical(leaf)?, child, policy, counts)?;
                    }
                }
                (68, Value::Indices(v)) => counts.add(v.len(), 0)?,
                _ => return Err(unsupported()),
            }
        } else if super::bulk::format(ty).is_some() {
            let (elements, groups) = super::bulk::value_counts(value, policy)?;
            counts.add(elements, groups)?;
        } else if let Some((_, width)) = super::frame(ty) {
            let (elements, groups) = fixed_counts(ty, width);
            counts.add(elements, groups)?;
        } else if super::pcs::tag(ty).is_some() {
            match value {
                Value::Commitment(_) => counts.add(0, 1)?,
                Value::Proof(p) => counts.add(0, p.metadata().arity())?,
                _ => return Err(unsupported()),
            }
        } else {
            return Err(unsupported());
        }
        counts.admit(policy)
    }
    visit(
        &value.physical_type(),
        value,
        policy,
        &mut Counts::default(),
    )
}

fn fixed_counts(ty: &PhysicalType, width: usize) -> (usize, usize) {
    (
        match ty.kind() {
            Type::Field | Type::Index => 1,
            Type::FieldArray => (width - 6) / 32,
            _ => 0,
        },
        usize::from(ty.kind() == Type::Group),
    )
}
pub(super) fn peak(policy: &Policy, charge: usize, wire: usize) -> Result<()> {
    // Decoding can temporarily retain Vec and Arc; observation retains the
    // decoded value, output frame and two temporary PCS leaf buffers. Both directions
    // use this same conservative bound, including at nondefault policy ratios.
    let bytes = mul(charge, 2)?.max(add(charge, mul(wire, 3)?)?);
    policy.output(bytes, usize::MAX).map_err(|_| Error::Limit)
}
fn width(value: &Value, policy: &Policy, key: &crate::setups::Setups) -> Result<usize> {
    if let Value::Sequence(v) = value {
        if tag(&value.physical_type()) != Some(69) {
            return Err(unsupported());
        }
        v.validate(policy).map_err(Error::Backend)?;
        let mut n = 10;
        for child in v.elements() {
            n = add(n, add(4, width(child, policy, key)?)?)?;
        }
        return Ok(n);
    }
    if let Value::Variant(v) = value {
        if tag(&value.physical_type()) != Some(65) {
            return Err(unsupported());
        }
        v.validate().map_err(Error::Backend)?;
        let mut size = 10;
        for child in v.payload() {
            size = add(size, add(4, width(child, policy, key)?)?)?;
        }
        policy.wire(size).map_err(|_| Error::Limit)?;
        return Ok(size);
    }
    if let Value::Indices(v) = value {
        policy.vector_width(v.len(), 8).map_err(|_| Error::Limit)?;
        return add(10, mul(v.len(), 8)?);
    }
    if super::bulk::format(&value.physical_type()).is_some() {
        return super::bulk::width(value, policy);
    }
    if let Some((_, size)) = super::frame(&value.physical_type()) {
        return Ok(size);
    }
    match value {
        Value::Commitment(_) | Value::Proof(_) => super::pcs::encoded_width(value, key),
        _ => Err(unsupported()),
    }
}
fn write(
    value: &Value,
    policy: &Policy,
    key: &crate::setups::Setups,
    out: &mut Vec<u8>,
) -> Result<()> {
    let Some(tag) = tag(&value.physical_type()) else {
        out.extend_from_slice(&super::encode(value, policy, key)?);
        return Ok(());
    };
    out.extend_from_slice(super::super::MAGIC);
    out.push(tag);
    let integer = |n| {
        u32::try_from(n)
            .map(u32::to_le_bytes)
            .map_err(|_| Error::Limit)
    };
    match value {
        Value::Sequence(v) => {
            out.extend_from_slice(&integer(v.elements().len())?);
            for child in v.elements() {
                let prefix = out.len();
                out.extend_from_slice(&[0; 4]);
                write(child, policy, key, out)?;
                let length = integer(out.len() - prefix - 4)?;
                out[prefix..prefix + 4].copy_from_slice(&length);
            }
        }
        Value::Variant(v) => {
            out.extend_from_slice(&integer(v.alternative())?);
            for child in v.payload() {
                let prefix = out.len();
                out.extend_from_slice(&[0; 4]);
                write(child, policy, key, out)?;
                let length = integer(out.len() - prefix - 4)?;
                out[prefix..prefix + 4].copy_from_slice(&length);
            }
        }
        Value::Indices(v) => {
            out.extend_from_slice(&integer(v.len())?);
            for x in v.iter() {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
        _ => return Err(unsupported()),
    }
    Ok(())
}
pub(super) fn encode(
    value: &Value,
    policy: &Policy,
    key: &crate::setups::Setups,
) -> Result<Vec<u8>> {
    let size = width(value, policy, key)?;
    policy.wire(size).map_err(|_| Error::Limit)?;
    // Output plus a leaf codec's temporary frame coexist with the input value.
    policy
        .output(add(value.retained_bytes(), mul(size, 3)?)?, usize::MAX)
        .map_err(|_| Error::Limit)?;
    let mut out = Vec::new();
    out.try_reserve_exact(size).map_err(|_| Error::Limit)?;
    write(value, policy, key, &mut out)?;
    if out.len() != size {
        return Err(unsupported());
    }
    // A producer must satisfy the same aggregate receive preflight. This check
    // constructs no decoded values and keeps policy asymmetry from emitting a
    // frame which the same configured receiver must refuse.
    let mut counts = Counts::default();
    let retained = scan(&value.physical_type(), &out, policy, key, &mut counts).map_err(
        |error| match error {
            Error::Invalid(_) => Error::Backend(zkc_runtime::interactive::BackendError::new(
                "native-wire-value",
            )),
            other => other,
        },
    )?;
    counts.admit(policy)?;
    peak(policy, retained, out.len())?;
    Ok(out)
}
pub(super) fn header(bytes: &[u8], tag: u8) -> Result<usize> {
    if bytes.len() < 10 {
        return Err(invalid(DecodeReason::Length));
    }
    if &bytes[..5] != super::super::MAGIC || bytes[5] != tag {
        return Err(invalid(DecodeReason::Header));
    }
    Ok(u32::from_le_bytes(bytes[6..10].try_into().unwrap()) as usize)
}
fn child<'a>(bytes: &mut &'a [u8]) -> Result<&'a [u8]> {
    let prefix = bytes
        .get(..4)
        .ok_or_else(|| invalid(DecodeReason::Length))?;
    let length = u32::from_le_bytes(prefix.try_into().unwrap()) as usize;
    if length > bytes.len() - 4 {
        return Err(invalid(DecodeReason::Length));
    }
    let end = 4 + length;
    let value = &bytes[4..end];
    *bytes = &bytes[end..];
    Ok(value)
}
// This preflight does not allocate payload containers. Physical descriptors are
// derived from an already admitted bounded type; their charge is included below.
fn scan(
    ty: &PhysicalType,
    bytes: &[u8],
    policy: &Policy,
    key: &crate::setups::Setups,
    counts: &mut Counts,
) -> Result<usize> {
    policy.wire(bytes.len()).map_err(|_| Error::Limit)?;
    counts.nodes = add(counts.nodes, 1)?;
    counts.admit(policy)?;
    if let Some(tag) = tag(ty) {
        let n = header(bytes, tag)?;
        if tag == 69 {
            policy.vector_width(n, 512).map_err(|_| Error::Limit)?;
            if n > (bytes.len() - 10) / 4 {
                return Err(invalid(DecodeReason::Length));
            }
            let logical = ty.logical();
            let element = physical(logical.sequence_element().ok_or_else(unsupported)?)?;
            let mut total = add(add(256, logical.descriptor_bytes())?, mul(n, 512)?)?;
            let mut rest = &bytes[10..];
            for _ in 0..n {
                total = add(
                    total,
                    scan(&element, child(&mut rest)?, policy, key, counts)?,
                )?;
            }
            if !rest.is_empty() {
                return Err(invalid(DecodeReason::Length));
            }
            policy.output(total, usize::MAX).map_err(|_| Error::Limit)?;
            return Ok(total);
        }
        if tag == 65 {
            let logical = ty.logical();
            let descriptor = logical.variant_descriptor().ok_or_else(unsupported)?;
            let arm = descriptor
                .alternatives()
                .get(n)
                .ok_or_else(|| invalid(DecodeReason::Header))?;
            let mut total = add(
                descriptor.retained_bytes(),
                add(256, mul(arm.payload().len(), 512)?)?,
            )?;
            let mut rest = &bytes[10..];
            for leaf in arm.payload() {
                total = add(
                    total,
                    scan(&physical(leaf)?, child(&mut rest)?, policy, key, counts)?,
                )?;
            }
            if !rest.is_empty() {
                return Err(invalid(DecodeReason::Length));
            }
            policy.output(total, usize::MAX).map_err(|_| Error::Limit)?;
            return Ok(total);
        }
        // The remaining structured leaf is an index vector.
        policy.vector_width(n, 8).map_err(|_| Error::Limit)?;
        counts.add(n, 0)?;
        if bytes.len() != add(10, mul(n, 8)?)? {
            return Err(invalid(DecodeReason::Length));
        }
        return add(256, mul(n, 8)?);
    }
    if super::bulk::format(ty).is_some() {
        let (retained, elements, groups) = super::bulk::scan(ty, bytes, policy)?;
        counts.add(elements, groups)?;
        return Ok(retained);
    }
    if let Some((tag, width)) = super::frame(ty) {
        if bytes.len() != width {
            return Err(invalid(DecodeReason::Length));
        }
        if &bytes[..5] != super::super::MAGIC || bytes[5] != tag {
            return Err(invalid(DecodeReason::Header));
        }
        let (elements, groups) = fixed_counts(ty, width);
        counts.add(elements, groups)?;
    } else if let Some(tag) = super::pcs::tag(ty) {
        // Both production/observation and receive check active setup identity.
        // Receive performs this check before group decoding or payload allocation.
        super::pcs::preflight(key, tag, bytes)?;
        counts.add(
            0,
            if tag == 6 {
                1
            } else {
                bytes.len().saturating_sub(87) / 96
            },
        )?;
    } else {
        return Err(unsupported());
    }
    // Covers the widest installed leaf backing (including KZG G2 quotients),
    // fixed-array storage and scalar wrappers. Leaf decoders retain typed errors.
    let charge = add(512, mul(bytes.len(), 4)?)?;
    if let Some((_, length)) = ty.logical().field_array_parts() {
        // Empty/small arrays retain the complete physical-type wrapper too.
        Ok(charge.max(crate::field_array::bytes(length as usize).map_err(|_| Error::Limit)?))
    } else {
        Ok(charge)
    }
}
fn read(backend: &NativeBackend, ty: &PhysicalType, bytes: &[u8]) -> Result<Value> {
    let Some(tag) = tag(ty) else {
        return backend.decode_native_value(ty, bytes);
    };
    let n = header(bytes, tag)?;
    if tag == 69 {
        let logical = ty.logical();
        let element = logical.sequence_element().ok_or_else(unsupported)?;
        let physical = physical(element)?;
        let mut values = Vec::new();
        values.try_reserve_exact(n).map_err(|_| Error::Limit)?;
        let mut rest = &bytes[10..];
        for _ in 0..n {
            values.push(read(backend, &physical, child(&mut rest)?)?);
        }
        return crate::Sequence::new(element.clone(), values, backend.policy())
            .map(Value::Sequence)
            .map_err(Error::Backend);
    }
    if tag == 65 {
        let logical = ty.logical();
        let descriptor = logical.variant_descriptor().ok_or_else(unsupported)?;
        let arm = &descriptor.alternatives()[n];
        let mut payload = Vec::new();
        payload
            .try_reserve_exact(arm.payload().len())
            .map_err(|_| Error::Limit)?;
        let mut rest = &bytes[10..];
        for leaf in arm.payload() {
            payload.push(read(backend, &physical(leaf)?, child(&mut rest)?)?);
        }
        return crate::Variant::new(descriptor.clone(), n, payload)
            .map(Value::Variant)
            .map_err(Error::Backend);
    }
    let mut out = Vec::new();
    out.try_reserve_exact(n).map_err(|_| Error::Limit)?;
    for bytes in bytes[10..].as_chunks::<8>().0 {
        out.push(u64::from_le_bytes(*bytes));
    }
    Ok(Value::Indices(out.into()))
}
/// Framing and conservative retention only; no curve/scalar decoding.
pub(super) fn retained(backend: &NativeBackend, ty: &PhysicalType, bytes: &[u8]) -> Result<usize> {
    let mut counts = Counts::default();
    let retained = scan(ty, bytes, backend.policy(), backend.setups(), &mut counts)?;
    counts.admit(backend.policy())?;
    // Vec-to-Arc conversion can retain both backing stores. Include the full
    // accumulated result, not merely each leaf's individual policy check.
    peak(backend.policy(), retained, bytes.len())?;
    Ok(retained)
}
pub(super) fn decode(backend: &NativeBackend, ty: &PhysicalType, bytes: &[u8]) -> Result<Value> {
    retained(backend, ty, bytes)?;
    let value = read(backend, ty, bytes)?;
    backend
        .policy()
        .output(value.retained_bytes(), usize::MAX)
        .map_err(|_| Error::Limit)?;
    Ok(value)
}
