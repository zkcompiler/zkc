//! Canonical BN254 vector and group-vector payloads for the native wire codec.
use crate::{Policy, Result, Value, ark, exhausted, kernels::arithmetic::reserve};
use zkc_arkworks::bn254::{G1, G2, encode_scalar};

pub(super) fn encode(value: &Value, policy: &Policy) -> Option<Result<Vec<u8>>> {
    let (tag, width, count) = match value {
        Value::Bn254Vector(v) => (41, 32usize, v.len()),
        Value::Bn254G1Vector(v) => (47, 32, v.len()),
        Value::Bn254G2Vector(v) => (49, 64, v.len()),
        _ => return None,
    };
    Some((|| {
        match value {
            Value::Bn254G1Vector(_) => policy.bn254_groups::<G1>(count)?,
            Value::Bn254G2Vector(_) => policy.bn254_groups::<G2>(count)?,
            _ => policy.vector(count)?,
        }
        let length = count
            .checked_mul(width)
            .and_then(|n| n.checked_add(10))
            .ok_or_else(|| exhausted("wire-bytes"))?;
        policy.wire(length)?;
        let mut out = reserve(length)?;
        out.extend_from_slice(b"ZKCV\x01");
        out.push(tag);
        out.extend(
            u32::try_from(count)
                .map_err(|_| exhausted("element-limit"))?
                .to_le_bytes(),
        );
        match value {
            Value::Bn254Vector(values) => {
                for x in values.iter() {
                    out.extend(encode_scalar(x).map_err(ark)?);
                }
            }
            Value::Bn254G1Vector(values) => {
                for x in values.iter() {
                    out.extend(x.to_bytes().map_err(ark)?);
                }
            }
            Value::Bn254G2Vector(values) => {
                for x in values.iter() {
                    out.extend(x.to_bytes().map_err(ark)?);
                }
            }
            _ => unreachable!("selected native vector"),
        }
        Ok(out)
    })())
}
