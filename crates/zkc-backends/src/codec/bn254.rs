//! BN254 canonical wire carriers; framing remains the shared ZKCV version.
use crate::{
    Policy, Result, Value, ark, exhausted,
    kernels::arithmetic::{normalized, reserve},
    refused,
    value::size,
};
use zkc_arkworks::bn254::{G1, G2, decode_scalar, encode_scalar};
use zkc_runtime::interactive::{Identity, PhysicalType, Type, Value as RuntimeValue};
fn format(ty: PhysicalType) -> Option<(u8, usize, usize)> {
    use Identity::*;
    use Type::*;
    Some(match (ty.logical().identity(), ty.kind()) {
        (Bn254Fr, Field) => (40, 32, 32),
        (Bn254Fr, Vector) => (41, 32, 32),
        (Bn254Fr, Polynomial) => (42, 32, 32),
        (Bn254Fr, Round) => (43, 32, 32),
        (Bn254G1, Group) => (46, 32, std::mem::size_of::<G1>()),
        (Bn254G1, Groups) => (47, 32, std::mem::size_of::<G1>()),
        (Bn254G2, Group) => (48, 64, std::mem::size_of::<G2>()),
        (Bn254G2, Groups) => (49, 64, std::mem::size_of::<G2>()),
        _ => return Option::None,
    })
}
fn limit(ty: PhysicalType, n: usize, p: &Policy) -> Result<()> {
    match (ty.logical().identity(), ty.kind()) {
        (Identity::Bn254G1, Type::Groups) => p.bn254_groups::<G1>(n),
        (Identity::Bn254G2, Type::Groups) => p.bn254_groups::<G2>(n),
        (_, Type::Vector | Type::Polynomial) => p.vector(n),
        _ => p.output(512, usize::MAX),
    }
}
pub(crate) fn encode(v: &Value, p: &Policy) -> Option<Result<Vec<u8>>> {
    let ty = v.physical_type();
    let (tag, width, _) = format(ty.clone())?;
    Some((|| {
        let n = match v {
            Value::Bn254Vector(v) | Value::Bn254Polynomial(v) => v.len(),
            Value::Bn254G1Vector(v) => v.len(),
            Value::Bn254G2Vector(v) => v.len(),
            Value::Bn254Round(_) => 3,
            _ => 1,
        };
        limit(ty.clone(), n, p)?;
        let sequence = matches!(ty.kind(), Type::Vector | Type::Polynomial | Type::Groups);
        let len = n
            .checked_mul(width)
            .and_then(|x| x.checked_add(if sequence { 10 } else { 6 }))
            .ok_or_else(|| exhausted("wire-bytes"))?;
        p.wire(len)?;
        let mut out = reserve(len)?;
        out.extend_from_slice(b"ZKCV\x01");
        out.push(tag);
        if sequence {
            out.extend(
                u32::try_from(n)
                    .map_err(|_| exhausted("element-limit"))?
                    .to_le_bytes(),
            );
        }
        match v {
            Value::Bn254Field(x) => out.extend(encode_scalar(x).map_err(ark)?),
            Value::Bn254Vector(v) | Value::Bn254Polynomial(v) => {
                if ty.kind() == Type::Polynomial && !normalized(v) {
                    return Err(refused("polynomial-normalization"));
                }
                for x in v.iter() {
                    out.extend(encode_scalar(x).map_err(ark)?);
                }
            }
            Value::Bn254Round(v) => {
                for x in v {
                    out.extend(encode_scalar(x).map_err(ark)?);
                }
            }
            Value::Bn254G1(x) => out.extend(x.to_bytes().map_err(ark)?),
            Value::Bn254G2(x) => out.extend(x.to_bytes().map_err(ark)?),
            Value::Bn254G1Vector(v) => {
                for x in v.iter() {
                    out.extend(x.to_bytes().map_err(ark)?);
                }
            }
            Value::Bn254G2Vector(v) => {
                for x in v.iter() {
                    out.extend(x.to_bytes().map_err(ark)?);
                }
            }
            _ => return Err(refused("nonserializable")),
        }
        Ok(out)
    })())
}
pub(crate) fn decode(ty: PhysicalType, b: &[u8], p: &Policy) -> Option<Result<Value>> {
    let (tag, width, memory) = format(ty.clone())?;
    Some((|| {
        p.wire(b.len())?;
        if b.len() < 6 || &b[..5] != b"ZKCV\x01" || b[5] != tag {
            return Err(refused("wire-header"));
        }
        let mut body = &b[6..];
        let sequence = matches!(ty.kind(), Type::Vector | Type::Polynomial | Type::Groups);
        let n = if sequence {
            let (count, tail) = body
                .split_first_chunk::<4>()
                .ok_or_else(|| refused("wire-length"))?;
            body = tail;
            u32::from_le_bytes(*count) as usize
        } else if ty.kind() == Type::Round {
            3
        } else {
            1
        };
        if n.checked_mul(width) != Some(body.len()) {
            return Err(refused("wire-length"));
        }
        limit(ty.clone(), n, p)?;
        p.output(if sequence { size(n, memory)? } else { 512 }, usize::MAX)?;
        Ok(match tag {
            40 => Value::Bn254Field(decode_scalar(body).map_err(ark)?),
            41..=43 => {
                let mut out = reserve(n)?;
                for b in body.as_chunks::<32>().0.iter() {
                    out.push(decode_scalar(b).map_err(ark)?);
                }
                match tag {
                    41 => Value::Bn254Vector(out.into()),
                    42 => {
                        if !normalized(&out) {
                            return Err(refused("polynomial-normalization"));
                        }
                        Value::Bn254Polynomial(out.into())
                    }
                    _ => Value::Bn254Round(out.try_into().map_err(|_| refused("wire-round"))?),
                }
            }
            46 => Value::Bn254G1(G1::from_bytes(body).map_err(ark)?),
            48 => Value::Bn254G2(G2::from_bytes(body).map_err(ark)?),
            47 => {
                let mut v = reserve(n)?;
                for b in body.as_chunks::<32>().0.iter() {
                    v.push(G1::from_bytes(b).map_err(ark)?);
                }
                Value::Bn254G1Vector(v.into())
            }
            49 => {
                let mut v = reserve(n)?;
                for b in body.as_chunks::<64>().0.iter() {
                    v.push(G2::from_bytes(b).map_err(ark)?);
                }
                Value::Bn254G2Vector(v.into())
            }
            _ => return Err(refused("wire-header")),
        })
    })())
}
