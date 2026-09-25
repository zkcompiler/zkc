//! Canonical additional ZKCV encodings. Legacy tags/bytes are untouched.
//! Header ZKCV 01 + domain-specific tag; sequence count is u32 little-endian.
//! Exact lengths and policy bounds are checked before allocation.
use crate::kernels::arithmetic::{normalized, reserve};
use crate::{
    Policy, Result, RistrettoPoint, RistrettoScalar, Value, ark, exhausted, refused, value::size,
};
use curve25519_dalek::ristretto::CompressedRistretto;
use zkc_runtime::interactive::{Identity, PhysicalType, Type, Value as RuntimeValue};
fn tag(ty: PhysicalType) -> Option<u8> {
    match (ty.kind(), ty.logical().identity()) {
        (Type::Field, Identity::KoalaBearExt8) => Some(26),
        (Type::Vector, Identity::KoalaBearExt8) => Some(27),
        (Type::Polynomial, Identity::KoalaBearExt8) => Some(28),
        (Type::Round, Identity::KoalaBearExt8) => Some(29),
        (Type::Field, Identity::KoalaBear) => Some(19),
        (Type::Vector, Identity::KoalaBear) => Some(20),
        (Type::Polynomial, Identity::KoalaBear) => Some(21),
        (Type::Round, Identity::KoalaBear) => Some(22),
        (Type::Vector, Identity::Bls12381Fr) => Some(11),
        (Type::Polynomial, Identity::Bls12381Fr) => Some(12),
        (Type::Field, Identity::Ristretto255Scalar) => Some(13),
        (Type::Vector, Identity::Ristretto255Scalar) => Some(14),
        (Type::Polynomial, Identity::Ristretto255Scalar) => Some(15),
        (Type::Group, Identity::Ristretto255Group) => Some(16),
        (Type::Groups, Identity::Ristretto255Group) => Some(17),
        (Type::Round, Identity::Ristretto255Scalar) => Some(18),
        _ => None,
    }
}
pub(crate) fn encode(v: &Value, p: &Policy) -> Option<Result<Vec<u8>>> {
    let tag = tag(v.physical_type())?;
    Some((|| {
        v.validate_serializable()?;
        let width = if v.physical_type().logical().identity() == Identity::KoalaBear {
            4
        } else {
            32
        };
        let count = match v {
            Value::KoalaBearVector(v) | Value::KoalaBearPolynomial(v) => Some(v.len()),
            Value::KoalaBearExt8Vector(v) | Value::KoalaBearExt8Polynomial(v) => Some(v.len()),
            Value::Vector(v) | Value::Polynomial(v) => Some(v.len()),
            Value::RistrettoVector(v) | Value::RistrettoPolynomial(v) => Some(v.len()),
            Value::RistrettoGroups(v) => Some(v.len()),
            _ => None,
        };
        let n = count.unwrap_or(
            if matches!(
                v,
                Value::RistrettoRound(_) | Value::KoalaBearRound(_) | Value::KoalaBearExt8Round(_)
            ) {
                3
            } else {
                1
            },
        );
        if let Some(n) = count {
            if matches!(v, Value::RistrettoGroups(_)) {
                p.ristretto_groups(n)?;
            } else {
                p.vector_width(n, width)?;
            }
        }
        let len = n
            .checked_mul(width)
            .and_then(|n| n.checked_add(if count.is_some() { 10 } else { 6 }))
            .ok_or_else(|| exhausted("wire-bytes"))?;
        p.wire(len)?;
        let mut out = reserve(len)?;
        out.extend_from_slice(b"ZKCV\x01");
        out.push(tag);
        if let Some(n) = count {
            out.extend(
                u32::try_from(n)
                    .map_err(|_| exhausted("element-limit"))?
                    .to_le_bytes(),
            );
        }
        match v {
            Value::KoalaBearExt8Field(v) => out.extend(crate::plonky3::encode_extension(*v)),
            Value::KoalaBearExt8Vector(v) | Value::KoalaBearExt8Polynomial(v) => {
                if tag == 28 && !normalized(v) {
                    return Err(refused("polynomial-normalization"));
                }
                for s in v.iter() {
                    out.extend(crate::plonky3::encode_extension(*s));
                }
            }
            Value::KoalaBearExt8Round(v) => {
                for s in v {
                    out.extend(crate::plonky3::encode_extension(*s));
                }
            }
            Value::KoalaBearField(v) => out.extend(crate::plonky3::encode_scalar(*v)),
            Value::KoalaBearVector(v) | Value::KoalaBearPolynomial(v) => {
                if tag == 21 && !normalized(v) {
                    return Err(refused("polynomial-normalization"));
                }
                for s in v.iter() {
                    out.extend(crate::plonky3::encode_scalar(*s));
                }
            }
            Value::KoalaBearRound(v) => {
                for s in v {
                    out.extend(crate::plonky3::encode_scalar(*s));
                }
            }
            Value::Vector(v) | Value::Polynomial(v) => {
                if matches!(tag, 12) && !normalized(v) {
                    return Err(refused("polynomial-normalization"));
                }
                for s in v.iter() {
                    out.extend(zkc_arkworks::encode_scalar(s).map_err(ark)?);
                }
            }
            Value::RistrettoField(s) => out.extend(s.to_bytes()),
            Value::RistrettoVector(v) | Value::RistrettoPolynomial(v) => {
                if tag == 15 && !normalized(v) {
                    return Err(refused("polynomial-normalization"));
                }
                for s in v.iter() {
                    out.extend(s.to_bytes());
                }
            }
            Value::RistrettoRound(v) => {
                for s in v {
                    out.extend(s.to_bytes());
                }
            }
            Value::RistrettoGroup(v) => out.extend(v.compress().to_bytes()),
            Value::RistrettoGroups(v) => {
                for s in v.iter() {
                    out.extend(s.compress().to_bytes());
                }
            }
            _ => return Err(refused("nonserializable")),
        }
        Ok(out)
    })())
}
fn scalar(bytes: &[u8]) -> Result<RistrettoScalar> {
    let bytes: [u8; 32] = bytes.try_into().map_err(|_| refused("wire-length"))?;
    Option::from(RistrettoScalar::from_canonical_bytes(bytes))
        .ok_or_else(|| refused("noncanonical-scalar"))
}
fn point(bytes: &[u8]) -> Result<RistrettoPoint> {
    let bytes: [u8; 32] = bytes.try_into().map_err(|_| refused("wire-length"))?;
    let point = CompressedRistretto(bytes)
        .decompress()
        .ok_or_else(|| refused("noncanonical-point"))?;
    if point.compress().to_bytes() != bytes {
        return Err(refused("noncanonical-point"));
    }
    Ok(point)
}
pub(crate) fn decode(ty: PhysicalType, bytes: &[u8], p: &Policy) -> Option<Result<Value>> {
    let expected = tag(ty.clone())?;
    Some((|| {
        if !ty.is_serializable() {
            return Err(refused("nonserializable"));
        }
        p.wire(bytes.len())?;
        if bytes.len() < 6 || &bytes[..5] != b"ZKCV\x01" || bytes[5] != expected {
            return Err(refused("wire-header"));
        }
        let mut body = &bytes[6..];
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
        let scalar_width = if ty.logical().identity() == Identity::KoalaBear {
            4
        } else {
            32
        };
        // Refuse impossible/trailing/truncated lengths before any allocation.
        if n.checked_mul(scalar_width) != Some(body.len()) {
            return Err(refused("wire-length"));
        }
        if sequence {
            if ty.kind() == Type::Groups {
                p.ristretto_groups(n)?;
            } else {
                p.vector_width(n, scalar_width)?;
            }
        }
        let width = if ty.kind() == Type::Groups {
            std::mem::size_of::<RistrettoPoint>()
        } else {
            scalar_width
        };
        p.output(if sequence { size(n, width)? } else { 512 }, usize::MAX)?;
        let v = match expected {
            26 => Value::KoalaBearExt8Field(crate::plonky3::decode_extension(body)?),
            27..=29 => {
                let mut v = reserve(n)?;
                for b in body.as_chunks::<32>().0 {
                    v.push(crate::plonky3::decode_extension(b)?);
                }
                match expected {
                    27 => Value::KoalaBearExt8Vector(v.into()),
                    28 => {
                        if !normalized(&v) {
                            return Err(refused("polynomial-normalization"));
                        }
                        Value::KoalaBearExt8Polynomial(v.into())
                    }
                    _ => {
                        Value::KoalaBearExt8Round(v.try_into().map_err(|_| refused("wire-round"))?)
                    }
                }
            }
            19 => Value::KoalaBearField(crate::plonky3::decode_scalar(body)?),
            20..=22 => {
                let mut v = reserve(n)?;
                for b in body.as_chunks::<4>().0 {
                    v.push(crate::plonky3::decode_scalar(b)?);
                }
                match expected {
                    20 => Value::KoalaBearVector(v.into()),
                    21 => {
                        if !normalized(&v) {
                            return Err(refused("polynomial-normalization"));
                        }
                        Value::KoalaBearPolynomial(v.into())
                    }
                    _ => Value::KoalaBearRound(v.try_into().map_err(|_| refused("wire-round"))?),
                }
            }
            11 | 12 => {
                let mut v = reserve(n)?;
                for b in body.as_chunks::<32>().0 {
                    v.push(zkc_arkworks::decode_scalar(b).map_err(ark)?);
                }
                if expected == 12 {
                    if !normalized(&v) {
                        return Err(refused("polynomial-normalization"));
                    }
                    Value::Polynomial(v.into())
                } else {
                    Value::Vector(v.into())
                }
            }
            13 => Value::RistrettoField(scalar(body)?),
            14 | 15 | 18 => {
                let mut v = reserve(n)?;
                for b in body.as_chunks::<32>().0 {
                    v.push(scalar(b)?);
                }
                match expected {
                    14 => Value::RistrettoVector(v.into()),
                    15 => {
                        if !normalized(&v) {
                            return Err(refused("polynomial-normalization"));
                        }
                        Value::RistrettoPolynomial(v.into())
                    }
                    _ => Value::RistrettoRound(v.try_into().map_err(|_| refused("wire-round"))?),
                }
            }
            16 => Value::RistrettoGroup(point(body)?),
            17 => {
                let mut v = reserve(n)?;
                for b in body.as_chunks::<32>().0 {
                    v.push(point(b)?);
                }
                Value::RistrettoGroups(v.into())
            }
            _ => return Err(refused("wire-header")),
        };
        if v.physical_type() != ty {
            return Err(refused("wire-type"));
        }
        Ok(v)
    })())
}
