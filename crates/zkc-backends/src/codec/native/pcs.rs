//! PCS messages resolve only previously authorized setup material. Peer
//! metadata cannot register a key. Opening state remains local.
use super::{NativeWireError, unsupported};
use crate::{NativeBackend, Policy, Value};
use zkc_runtime::interactive::{DecodeReason, Identity, PhysicalType, Type};

pub(super) fn tag(ty: &PhysicalType) -> Option<u8> {
    let logical = ty.logical();
    if logical.identity() != Identity::MultilinearKzgBls12381
        || PhysicalType::default_for(logical.clone()).ok().as_ref() != Some(ty)
    {
        return None;
    }
    match logical.kind() {
        Type::Commitment => Some(6),
        Type::Proof => Some(7),
        _ => None,
    }
}
fn width(tag: u8, arity: usize) -> Result<usize, NativeWireError> {
    if tag == 6 {
        Ok(135)
    } else {
        arity
            .checked_mul(96)
            .and_then(|n| n.checked_add(87))
            .ok_or(NativeWireError::Limit)
    }
}
// Structured producers must match the receiver's authorized setup before
// allocating a complete frame. Registered backends also apply this check to
// standalone leaves; direct InputKeys codecs retain key-independent encoding.
pub(super) fn encoded_width(
    value: &Value,
    key: &crate::setups::Setups,
) -> Result<usize, NativeWireError> {
    let (tag, metadata) = match value {
        Value::Commitment(c) => (6, c.metadata()),
        Value::Proof(p) => (7, p.metadata()),
        _ => return Err(unsupported()),
    };
    if key.get(metadata).is_none() {
        return Err(NativeWireError::Backend(
            zkc_runtime::interactive::BackendError::new(if key.is_empty() {
                "native-wire-setup-required"
            } else {
                "native-wire-setup-mismatch"
            }),
        ));
    }
    width(tag, metadata.arity())
}
fn error(error: zkc_arkworks::Error) -> NativeWireError {
    use NativeWireError::{Invalid, Limit};
    use zkc_arkworks::Error::*;
    match error {
        InvalidHeader | KeyMismatch | ArityMismatch { .. } | PositiveArityRequired | InvalidKey => {
            Invalid(DecodeReason::Header)
        }
        InvalidEncoding | NonCanonicalEncoding => Invalid(DecodeReason::Group),
        ArityLimit | ElementLimit | ByteLimit | SetupLimit | CapacityOverflow | Allocation => Limit,
        other => NativeWireError::Backend(crate::ark(other)),
    }
}

pub(super) fn encode(value: &Value, policy: &Policy) -> Result<Vec<u8>, NativeWireError> {
    use zkc_runtime::interactive::Value as RuntimeValue;
    let (tag, metadata) = match value {
        Value::Commitment(c) => (6, c.metadata()),
        Value::Proof(p) => (7, p.metadata()),
        _ => return Err(unsupported()),
    };
    let size = width(tag, metadata.arity())?;
    policy.wire(size).map_err(|_| NativeWireError::Limit)?;
    policy
        .output(value.retained_bytes(), usize::MAX)
        .map_err(|_| NativeWireError::Limit)?;
    policy
        .output(
            size.checked_mul(2).ok_or(NativeWireError::Limit)?,
            usize::MAX,
        )
        .map_err(|_| NativeWireError::Limit)?;
    let payload = match value {
        Value::Commitment(c) => c.to_bytes(&policy.ark_bounds()),
        Value::Proof(p) => p.to_bytes(&policy.ark_bounds()),
        _ => unreachable!(),
    }
    .map_err(error)?;
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(size)
        .map_err(|_| NativeWireError::Limit)?;
    bytes.extend_from_slice(super::super::MAGIC);
    bytes.push(tag);
    bytes.extend_from_slice(&payload);
    if bytes.len() != size {
        return Err(NativeWireError::Backend(
            zkc_runtime::interactive::BackendError::new("native-wire-width"),
        ));
    }
    Ok(bytes)
}

pub(super) fn preflight<'a>(
    setups: &'a crate::setups::Setups,
    tag: u8,
    bytes: &[u8],
) -> Result<&'a zkc_arkworks::VerifierKey, NativeWireError> {
    use NativeWireError::Invalid;
    // A singleton can reject length before reading metadata. Multiple setups
    // inspect only a fixed-size header to locate already authorized material.
    let key = if let Some(key) = setups.only() {
        key
    } else {
        if setups.is_empty() {
            return Err(NativeWireError::Backend(
                zkc_runtime::interactive::BackendError::new("native-wire-setup-required"),
            ));
        }
        if bytes.len() < 87 {
            return Err(Invalid(DecodeReason::Length));
        }
        setups
            .by_key_id(&bytes[55..87])
            .ok_or(Invalid(DecodeReason::Header))?
    };
    let size = width(tag, key.metadata().arity())?;
    if bytes.len() != size {
        return Err(Invalid(DecodeReason::Length));
    }
    if &bytes[..5] != super::super::MAGIC || bytes[5] != tag {
        return Err(Invalid(DecodeReason::Header));
    }
    if bytes[15..23] != (key.metadata().arity() as u64).to_le_bytes()
        || &bytes[6..14] != b"ZKCAR006"
        || bytes[14] != if tag == 6 { 2 } else { 3 }
        || bytes[23..55] != key.metadata().setup_id()
        || bytes[55..87] != key.metadata().key_id()
    {
        return Err(Invalid(DecodeReason::Header));
    }
    Ok(key)
}
pub(super) fn decode(
    backend: &NativeBackend,
    tag: u8,
    bytes: &[u8],
) -> Result<Value, NativeWireError> {
    use NativeWireError::Limit;
    use zkc_runtime::interactive::Value as RuntimeValue;
    let key = preflight(backend.setups(), tag, bytes)?;
    let size = bytes.len();
    let policy = backend.policy();
    policy.wire(size).map_err(|_| Limit)?;
    // Conservative bound covers the G2 quotient vector and immutable wrapper.
    policy
        .output(
            size.checked_mul(4)
                .and_then(|n| n.checked_add(512))
                .ok_or(Limit)?,
            usize::MAX,
        )
        .map_err(|_| Limit)?;
    let value = match tag {
        6 => Value::Commitment(std::sync::Arc::new(
            key.decode_commitment(&bytes[6..], &policy.ark_bounds())
                .map_err(error)?,
        )),
        7 => Value::Proof(std::sync::Arc::new(
            key.decode_proof(&bytes[6..], &policy.ark_bounds())
                .map_err(error)?,
        )),
        _ => unreachable!(),
    };
    policy
        .output(value.retained_bytes(), usize::MAX)
        .map_err(|_| Limit)?;
    Ok(value)
}
