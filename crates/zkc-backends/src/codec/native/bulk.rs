//! Typed numeric and row-oracle leaves of the native message grammar.
//! The caller supplies the complete type. Shape/count and peak allocation are
//! checked before any scalar, group, matrix or path payload is allocated.
use super::structured::{add, header, invalid, mul, peak};
use super::{NativeWireError as Error, unsupported};
use crate::{NativeBackend, Policy, Value};
use zkc_runtime::interactive::{DecodeReason, Identity, PhysicalType, Type, Value as RuntimeValue};
type Result<T> = std::result::Result<T, Error>;

// Tag, scalar/point wire width, retained element width. Matrix entries add two
// u32 coordinates. Existing BLS native vector tags intentionally remain 66/67.
pub(super) fn format(ty: &PhysicalType) -> Option<(u8, usize, usize)> {
    if PhysicalType::default_for(ty.logical()).ok().as_ref() != Some(ty) {
        return Option::None;
    }
    use Identity::*;
    use Type::*;
    Some(match (ty.kind(), ty.logical().identity()) {
        (Vector, Bls12381Fr) => (66, 32, 32),
        (Vector, Bn254Fr) => (41, 32, 32),
        (Vector, Ristretto255Scalar) => (14, 32, 32),
        (Vector, KoalaBear) => (20, 4, 4),
        (Vector, KoalaBearExt8) => (27, 32, 32),
        (Groups, Bls12381G1) => (67, 48, 128),
        (Groups, Bn254G1) => (47, 32, std::mem::size_of::<crate::Bn254G1>()),
        (Groups, Bn254G2) => (49, 64, std::mem::size_of::<crate::Bn254G2>()),
        (Groups, Ristretto255Group) => (17, 32, std::mem::size_of::<crate::RistrettoPoint>()),
        (Matrix, Bls12381Fr) => (23, 40, 40),
        (Matrix, Bn254Fr) => (45, 40, 40),
        (Matrix, Ristretto255Scalar) => (24, 40, 40),
        (Matrix, KoalaBear) => (25, 12, 12),
        (Matrix, KoalaBearExt8) => (30, 40, 40),
        (Commitment, MerkleKoalaBear) => (33, 32, 32),
        (Proof, MerkleKoalaBear) => (34, 32, 32),
        (Commitment, MerkleKoalaBearExt8) => (35, 32, 32),
        (Proof, MerkleKoalaBearExt8) => (36, 32, 32),
        _ => return Option::None,
    })
}
fn limit(kind: Type, count: usize, memory: usize, p: &Policy) -> Result<()> {
    if kind == Type::Groups {
        if count > p.max_groups.min(32768) {
            return Err(Error::Limit);
        }
        p.output(add(256, mul(count, memory)?)?, usize::MAX)
            .map_err(|_| Error::Limit)?;
    } else {
        p.vector_width(count, memory).map_err(|_| Error::Limit)?;
    }
    if kind == Type::Proof && count > 24 {
        return Err(invalid(DecodeReason::Length));
    }
    Ok(())
}
fn count(value: &Value) -> Result<usize> {
    Ok(match value {
        Value::Vector(v) => v.len(),
        Value::Bn254Vector(v) => v.len(),
        Value::RistrettoVector(v) => v.len(),
        Value::KoalaBearVector(v) => v.len(),
        Value::KoalaBearExt8Vector(v) => v.len(),
        Value::Groups(v) => v.len(),
        Value::Bn254G1Vector(v) => v.len(),
        Value::Bn254G2Vector(v) => v.len(),
        Value::RistrettoGroups(v) => v.len(),
        Value::Matrix(v) => v.entries().len(),
        Value::Bn254Matrix(v) => v.entries().len(),
        Value::RistrettoMatrix(v) => v.entries().len(),
        Value::KoalaBearMatrix(v) => v.entries().len(),
        Value::KoalaBearExt8Matrix(v) => v.entries().len(),
        Value::OracleRoot(..) => 1,
        Value::OraclePath(_, v) => v.len(),
        _ => return Err(unsupported()),
    })
}
fn quantities(kind: Type, count: usize) -> (usize, usize) {
    if kind == Type::Groups {
        (0, count)
    } else {
        (count, 0)
    }
}
pub(super) fn value_counts(value: &Value, policy: &Policy) -> Result<(usize, usize)> {
    let (_, _, memory) = format(&value.physical_type()).ok_or_else(unsupported)?;
    let count = count(value)?;
    limit(value.ty(), count, memory, policy)?;
    Ok(quantities(value.ty(), count))
}
fn prefix(kind: Type) -> usize {
    match kind {
        Type::Matrix => 18,
        Type::Commitment => 6,
        _ => 10,
    }
}
pub(super) fn width(value: &Value, policy: &Policy) -> Result<usize> {
    let ty = value.physical_type();
    let (_, wire, memory) = format(&ty).ok_or_else(unsupported)?;
    let n = count(value)?;
    limit(ty.kind(), n, memory, policy)?;
    add(prefix(ty.kind()), mul(n, wire)?)
}
pub(super) fn scan(
    ty: &PhysicalType,
    bytes: &[u8],
    policy: &Policy,
) -> Result<(usize, usize, usize)> {
    let (tag, wire, memory) = format(ty).ok_or_else(unsupported)?;
    policy.wire(bytes.len()).map_err(|_| Error::Limit)?;
    let kind = ty.kind();
    let n = if kind == Type::Commitment {
        if bytes.len() != 38 {
            return Err(invalid(DecodeReason::Length));
        }
        if &bytes[..5] != super::super::MAGIC || bytes[5] != tag {
            return Err(invalid(DecodeReason::Header));
        }
        1
    } else {
        let count = header(bytes, tag)?;
        if kind == Type::Matrix {
            if bytes.len() < 18 {
                return Err(invalid(DecodeReason::Length));
            }
            let rows = count;
            let cols = u32::from_le_bytes(bytes[10..14].try_into().unwrap()) as usize;
            let n = u32::from_le_bytes(bytes[14..18].try_into().unwrap()) as usize;
            if rows > crate::matrix::MATRIX_DIMENSION_LIMIT
                || cols > crate::matrix::MATRIX_DIMENSION_LIMIT
                || n > crate::matrix::MATRIX_NONZERO_LIMIT
            {
                return Err(Error::Limit);
            }
            if n > mul(rows, cols)? {
                return Err(invalid(DecodeReason::Length));
            }
            n
        } else {
            count
        }
    };
    limit(kind, n, memory, policy)?;
    if bytes.len() != add(prefix(kind), mul(n, wire)?)? {
        return Err(invalid(DecodeReason::Length));
    }
    let (elements, groups) = quantities(kind, n);
    Ok((
        if kind == Type::Commitment {
            512
        } else {
            add(256, mul(n, memory)?)?
        },
        elements,
        groups,
    ))
}
pub(super) fn encode(value: &Value, policy: &Policy) -> Result<Vec<u8>> {
    let width = width(value, policy)?;
    policy.wire(width).map_err(|_| Error::Limit)?;
    peak(policy, value.retained_bytes(), width)?;
    // Reuse checked canonical producers. Only BLS native vector tags differ
    // from the older logical codec; their payload layout is identical.
    let mut bytes = crate::matrix::encode(value, policy)
        .or_else(|| crate::oracle::encode(value, policy))
        .or_else(|| super::super::bn254::encode(value, policy))
        .or_else(|| super::super::domains::encode(value, policy))
        .unwrap_or_else(|| {
            if let Value::Groups(v) = value {
                let mut out = Vec::new();
                out.try_reserve_exact(width)
                    .map_err(|_| crate::exhausted("wire-bytes"))?;
                out.extend_from_slice(super::super::MAGIC);
                out.push(67);
                out.extend_from_slice(&(v.len() as u32).to_le_bytes());
                for x in v.iter() {
                    out.extend_from_slice(&x.to_bytes().map_err(crate::ark)?);
                }
                Ok(out)
            } else {
                Err(crate::refused("native-wire-type"))
            }
        })
        .map_err(Error::Backend)?;
    if bytes.len() != width {
        return Err(unsupported());
    }
    bytes[5] = format(&value.physical_type()).ok_or_else(unsupported)?.0;
    let (retained, _, _) = scan(&value.physical_type(), &bytes, policy)?;
    peak(policy, retained, width)?;
    Ok(bytes)
}
fn matrix<S: crate::matrix::Wire>(bytes: &[u8], p: &Policy) -> Result<Value> {
    let rows = u32::from_le_bytes(bytes[6..10].try_into().unwrap()) as usize;
    let cols = u32::from_le_bytes(bytes[10..14].try_into().unwrap()) as usize;
    let n = u32::from_le_bytes(bytes[14..18].try_into().unwrap()) as usize;
    let mut entries = Vec::new();
    entries.try_reserve_exact(n).map_err(|_| Error::Limit)?;
    let mut previous = None;
    for b in bytes[18..].chunks_exact(S::WIDTH + 8) {
        let row = u32::from_le_bytes(b[..4].try_into().unwrap());
        let col = u32::from_le_bytes(b[4..8].try_into().unwrap());
        if row as usize >= rows || col as usize >= cols || previous.is_some_and(|x| x >= (row, col))
        {
            return Err(invalid(DecodeReason::Header));
        }
        let x = S::decode(&b[8..]).map_err(|_| invalid(DecodeReason::Scalar))?;
        if x == S::zero() {
            return Err(invalid(DecodeReason::Scalar));
        }
        entries.push((row, col, x));
        previous = Some((row, col));
    }
    crate::matrix::from_entries(rows, cols, &entries, p)
        .map(S::value)
        .map_err(Error::Backend)
}
pub(super) fn decode(backend: &NativeBackend, ty: &PhysicalType, bytes: &[u8]) -> Result<Value> {
    let value = decode_value(backend, ty, bytes)?;
    backend
        .policy()
        .output(value.retained_bytes(), usize::MAX)
        .map_err(|_| Error::Limit)?;
    Ok(value)
}
fn decode_value(backend: &NativeBackend, ty: &PhysicalType, bytes: &[u8]) -> Result<Value> {
    let (retained, _, _) = scan(ty, bytes, backend.policy())?;
    peak(backend.policy(), retained, bytes.len())?;
    let (tag, _, _) = format(ty).ok_or_else(unsupported)?;
    if ty.kind() == Type::Matrix {
        return match tag {
            23 => matrix::<crate::Scalar>(bytes, backend.policy()),
            45 => matrix::<crate::Bn254Scalar>(bytes, backend.policy()),
            24 => matrix::<crate::RistrettoScalar>(bytes, backend.policy()),
            25 => matrix::<crate::KoalaBear>(bytes, backend.policy()),
            30 => matrix::<crate::KoalaBearExt8>(bytes, backend.policy()),
            _ => Err(unsupported()),
        };
    }
    if matches!(tag, 33..=36) {
        let d = if matches!(tag, 33 | 34) {
            crate::oracle::Domain::Base
        } else {
            crate::oracle::Domain::Extension
        };
        return if ty.kind() == Type::Commitment {
            Ok(Value::OracleRoot(d, bytes[6..].try_into().unwrap()))
        } else {
            let mut hashes = Vec::new();
            hashes
                .try_reserve_exact((bytes.len() - 10) / 32)
                .map_err(|_| Error::Limit)?;
            hashes.extend(bytes[10..].as_chunks::<32>().0.iter().copied());
            Ok(Value::OraclePath(d, hashes.into()))
        };
    }
    macro_rules! values {
        ($width:literal, $decode:expr, $variant:ident, $reason:ident) => {{
            let mut v = Vec::new();
            v.try_reserve_exact((bytes.len() - 10) / $width)
                .map_err(|_| Error::Limit)?;
            for b in bytes[10..].as_chunks::<$width>().0 {
                v.push(($decode)(b).map_err(|_| invalid(DecodeReason::$reason))?);
            }
            Ok(Value::$variant(v.into()))
        }};
    }
    match tag {
        66 => values!(32, zkc_arkworks::decode_scalar, Vector, Scalar),
        41 => values!(32, zkc_arkworks::bn254::decode_scalar, Bn254Vector, Scalar),
        20 => values!(4, crate::plonky3::decode_scalar, KoalaBearVector, Scalar),
        27 => values!(
            32,
            crate::plonky3::decode_extension,
            KoalaBearExt8Vector,
            Scalar
        ),
        14 => values!(
            32,
            |b: &[u8; 32]| Option::<crate::RistrettoScalar>::from(
                crate::RistrettoScalar::from_canonical_bytes(*b)
            )
            .ok_or(()),
            RistrettoVector,
            Scalar
        ),
        67 => values!(48, crate::GroupPoint::from_bytes, Groups, Group),
        47 => values!(32, crate::Bn254G1::from_bytes, Bn254G1Vector, Group),
        49 => values!(64, crate::Bn254G2::from_bytes, Bn254G2Vector, Group),
        17 => values!(
            32,
            |b: &[u8; 32]| curve25519_dalek::ristretto::CompressedRistretto(*b)
                .decompress()
                .filter(|x| x.compress().to_bytes() == *b)
                .ok_or(()),
            RistrettoGroups,
            Group
        ),
        _ => Err(unsupported()),
    }
}
