//! Canonical field and Ristretto group vectors in the native wire grammar.
use crate::{Policy, Result, Value, ark, exhausted, kernels::arithmetic::reserve};
use zkc_runtime::interactive::Value as _;

pub(super) fn encode(value: &Value, policy: &Policy) -> Option<Result<Vec<u8>>> {
    let (tag, width, count) = match value {
        Value::KoalaBearVector(v) => (20, 4usize, v.len()),
        Value::KoalaBearExt8Vector(v) => (27, 32, v.len()),
        Value::Vector(v) => (66, 32, v.len()),
        Value::RistrettoVector(v) => (14, 32, v.len()),
        Value::RistrettoGroups(v) => (17, 32, v.len()),
        _ => return None,
    };
    Some((|| {
        value.validate_serializable()?;
        if matches!(value, Value::RistrettoGroups(_)) {
            policy.ristretto_groups(count)?;
        } else {
            policy.vector_width(count, width)?;
        }
        let length = count
            .checked_mul(width)
            .and_then(|n| n.checked_add(10))
            .ok_or_else(|| exhausted("wire-bytes"))?;
        policy.wire(length)?;
        let mut out = reserve(length)?;
        out.extend_from_slice(b"ZKCV\x00");
        out.push(tag);
        out.extend(
            u32::try_from(count)
                .map_err(|_| exhausted("element-limit"))?
                .to_le_bytes(),
        );
        match value {
            Value::KoalaBearVector(values) => {
                for x in values.iter() {
                    out.extend(crate::plonky3::encode_scalar(*x));
                }
            }
            Value::KoalaBearExt8Vector(values) => {
                for x in values.iter() {
                    out.extend(crate::plonky3::encode_extension(*x));
                }
            }
            Value::Vector(values) => {
                for x in values.iter() {
                    out.extend(zkc_arkworks::encode_scalar(x).map_err(ark)?);
                }
            }
            Value::RistrettoVector(values) => {
                for x in values.iter() {
                    out.extend(x.to_bytes());
                }
            }
            Value::RistrettoGroups(values) => {
                for x in values.iter() {
                    out.extend(x.compress().to_bytes());
                }
            }
            _ => unreachable!("selected native vector"),
        }
        Ok(out)
    })())
}
