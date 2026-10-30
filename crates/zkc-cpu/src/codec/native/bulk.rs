//! Typed numeric and row-oracle leaves of the native message grammar.
//! The caller supplies the complete type. Shape/count and peak allocation are
//! checked before any scalar, group, matrix or path payload is allocated.
use super::structured::{add, header, invalid, mul, peak};
use super::{NativeWireError as Error, unsupported};
use crate::{CpuBackend, Policy, Value};
use zkc_runtime::vm::{DecodeReason, Identity, PhysicalType, Type, Value as RuntimeValue};
type Result<T> = std::result::Result<T, Error>;

// Tag, scalar/point wire width, retained element width. Matrix entries add two
// u32 coordinates. Existing BLS native vector tags intentionally remain 66/67.
pub(super) fn format(ty: &PhysicalType) -> Option<(u8, usize, usize)> {
    if crate::operations::halo2curves::is_resident(ty) {
        use zkc_kernels::halo2curves::bn254 as kernel;
        return match (ty.kind(), ty.logical().identity()) {
            (Type::Vector, Identity::Bn254Fr) => {
                Some((41, 32, std::mem::size_of::<kernel::ScalarElement>()))
            }
            (Type::Groups, Identity::Bn254G1) => {
                Some((47, 32, std::mem::size_of::<kernel::G1Element>()))
            }
            (Type::Groups, Identity::Bn254G2) => {
                Some((49, 64, std::mem::size_of::<kernel::G2Element>()))
            }
            _ => Option::None,
        };
    }
    if crate::operations::blst::is_resident(ty) {
        use zkc_kernels::blst::bls12_381 as kernel;
        return match ty.kind() {
            Type::Vector => Some((66, 32, std::mem::size_of::<kernel::Scalar>())),
            Type::Groups if ty.logical().identity() == Identity::Bls12381G1 => {
                Some((67, 48, std::mem::size_of::<kernel::G1>()))
            }
            Type::Groups => Some((52, 96, std::mem::size_of::<kernel::G2>())),
            _ => Option::None,
        };
    }
    if PhysicalType::default_for(ty.logical().clone())
        .ok()
        .as_ref()
        != Some(ty)
    {
        return Option::None;
    }
    use Identity::*;
    use Type::*;
    if crate::fields::contains(ty.logical().identity()) {
        let tags = crate::fields::tags(ty.logical().identity()).ok()?;
        let width = crate::fields::element_width(ty.logical().identity()).ok()?;
        return match ty.kind() {
            Vector => Some((tags[1], width, width)),
            Matrix => Some((
                tags[2],
                width + 8,
                crate::fields::matrix_entry_width(ty.logical().identity()).ok()?,
            )),
            _ => Option::None,
        };
    }
    // Digest-generic Merkle roots and proofs: one tag each for every scheme;
    // the expected type supplies the digest width and encoding.
    if let Some(scheme) = crate::merkle::Scheme::from_identity(ty.logical().identity()) {
        let width = scheme.digest_bytes();
        return match ty.kind() {
            Commitment => Some((71, width, width)),
            Proof => Some((72, width, width)),
            _ => Option::None,
        };
    }
    if let Some(domain) = crate::oracle::Domain::from_identity(ty.logical().identity()) {
        return Some((domain.tag(ty.kind())?, 32, 32));
    }
    Some(match (ty.kind(), ty.logical().identity()) {
        (Vector, Bls12381Fr) => (66, 32, 32),
        (Vector, Bn254Fr) => (41, 32, 32),
        (Vector, Ristretto255Scalar) => (14, 32, 32),
        (Vector, Binary64) => (74, 8, 8),
        (Vector, Binary64Ext3) => (77, 24, 24),
        (Groups, Bls12381G1) => (67, 48, 128),
        (Groups, Bn254G1) => (47, 32, std::mem::size_of::<crate::Bn254G1>()),
        (Groups, Bn254G2) => (49, 64, std::mem::size_of::<crate::Bn254G2>()),
        (Groups, Bls12381G2) => (52, 96, std::mem::size_of::<crate::Bls12381G2>()),
        (Groups, Edwards25519Prime) => (69, 32, std::mem::size_of::<crate::EdwardsPrime>()),
        (Groups, Ristretto255Group) => (17, 32, std::mem::size_of::<crate::RistrettoPoint>()),
        (Matrix, Bls12381Fr) => (23, 40, 40),
        (Matrix, Bn254Fr) => (45, 40, 40),
        (Matrix, Ristretto255Scalar) => (24, 40, 40),
        (Matrix, Binary64) => (75, 16, 16),
        (Matrix, Binary64Ext3) => (78, 32, 32),
        _ => return Option::None,
    })
}
/// Keccak row-oracle paths keep their historical sibling cap; pruned proofs of
/// the digest-generic schemes are bounded by the element ceiling instead.
fn capped(tag: u8) -> bool {
    matches!(tag, 34 | 36 | 80)
}
fn limit(kind: Type, tag: u8, count: usize, memory: usize, p: &Policy) -> Result<()> {
    if kind == Type::Groups {
        if count > p.max_groups.min(32768) {
            return Err(Error::Limit);
        }
        p.output(add(256, mul(count, memory)?)?, usize::MAX)
            .map_err(|_| Error::Limit)?;
    } else {
        p.vector_width(count, memory).map_err(|_| Error::Limit)?;
    }
    if kind == Type::Proof && capped(tag) && count > 24 {
        return Err(invalid(DecodeReason::Length));
    }
    Ok(())
}
fn count(value: &Value) -> Result<usize> {
    if let Some(count) = crate::fields::count(value) {
        return Ok(count);
    }
    Ok(match value {
        Value::BlstVector(v) => v.len(),
        Value::HaloVector(v) => v.len(),
        Value::BlstG1Vector(v) => v.len(),
        Value::HaloG1Vector(v) => v.len(),
        Value::BlstG2Vector(v) => v.len(),
        Value::HaloG2Vector(v) => v.len(),
        Value::Vector(v) => v.len(),
        Value::Bn254Vector(v) => v.len(),
        Value::RistrettoVector(v) => v.len(),

        Value::Binary64Vector(v) => v.len(),
        Value::Binary64Ext3Vector(v) => v.len(),
        Value::Groups(v) => v.len(),
        Value::Bn254G1Vector(v) => v.len(),
        Value::Bn254G2Vector(v) => v.len(),
        Value::Bls12381G2Vector(v) => v.len(),
        Value::RistrettoGroups(v) => v.len(),
        Value::EdwardsGroups(v) => v.len(),
        Value::Matrix(v) => v.entries().len(),
        Value::Bn254Matrix(v) => v.entries().len(),
        Value::RistrettoMatrix(v) => v.entries().len(),

        Value::Binary64Matrix(v) => v.entries().len(),
        Value::Binary64Ext3Matrix(v) => v.entries().len(),
        Value::OracleRoot(..) => 1,
        Value::OraclePath(_, v) => v.len(),
        Value::MerkleDigest(..) => 1,
        Value::MerkleProof(scheme, v) => v.len() / scheme.digest_bytes(),
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
    let (tag, _, memory) = format(&value.physical_type()).ok_or_else(unsupported)?;
    let count = count(value)?;
    limit(value.ty(), tag, count, memory, policy)?;
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
    let (tag, wire, memory) = format(&ty).ok_or_else(unsupported)?;
    let n = count(value)?;
    limit(ty.kind(), tag, n, memory, policy)?;
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
        if bytes.len() != add(6, wire)? {
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
    limit(kind, tag, n, memory, policy)?;
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
    if crate::operations::resident::is_resident(&value.physical_type()) {
        let (tag, _, _) = format(&value.physical_type()).ok_or_else(unsupported)?;
        let mut out = Vec::new();
        out.try_reserve_exact(width).map_err(|_| Error::Limit)?;
        out.extend_from_slice(super::super::MAGIC);
        out.push(tag);
        out.extend_from_slice(
            &u32::try_from(count(value)?)
                .map_err(|_| Error::Limit)?
                .to_le_bytes(),
        );
        match value {
            Value::BlstVector(v) => {
                for s in v.iter() {
                    out.extend_from_slice(&s.to_bytes_le());
                }
            }
            Value::HaloVector(v) => {
                for s in v.iter() {
                    out.extend_from_slice(&s.to_bytes_le());
                }
            }
            Value::BlstG1Vector(v) => {
                for p in v.iter() {
                    out.extend_from_slice(&p.to_bytes());
                }
            }
            Value::HaloG1Vector(v) => {
                for p in v.iter() {
                    out.extend_from_slice(&p.to_bytes());
                }
            }
            Value::BlstG2Vector(v) => {
                for p in v.iter() {
                    out.extend_from_slice(&p.to_bytes());
                }
            }
            Value::HaloG2Vector(v) => {
                for p in v.iter() {
                    out.extend_from_slice(&p.to_bytes());
                }
            }
            _ => return Err(unsupported()),
        }
        return Ok(out);
    }
    if value.ty() == Type::Vector
        && crate::fields::contains(value.physical_type().logical().identity())
    {
        return crate::fields::encode_vector(value, policy).map_err(Error::Backend);
    }
    // Type-owned encoders produce complete canonical frames. Validate their
    // framing against the expected physical type without rewriting it.
    let bytes = crate::matrix::encode(value, policy)
        .or_else(|| crate::oracle::encode(value, policy))
        .or_else(|| crate::merkle::encode(value, policy))
        .or_else(|| super::bn254::encode(value, policy))
        .or_else(|| super::domains::encode(value, policy))
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
    // This generic associated width cannot be a stable Rust array length.
    #[allow(clippy::chunks_exact_to_as_chunks)]
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
pub(super) fn decode(backend: &CpuBackend, ty: &PhysicalType, bytes: &[u8]) -> Result<Value> {
    let value = decode_value(backend, ty, bytes)?;
    backend
        .policy()
        .output(value.retained_bytes(), usize::MAX)
        .map_err(|_| Error::Limit)?;
    Ok(value)
}
fn decode_value(backend: &CpuBackend, ty: &PhysicalType, bytes: &[u8]) -> Result<Value> {
    let (retained, _, _) = scan(ty, bytes, backend.policy())?;
    peak(backend.policy(), retained, bytes.len())?;
    let (tag, _, _) = format(ty).ok_or_else(unsupported)?;
    if crate::fields::contains(ty.logical().identity()) {
        use crate::operations::field::Family;
        return crate::fields::with_residue_or!(ty.logical().identity(), Err(unsupported()), |S| {
            (|| -> Result<Value> {
                if ty.kind() == Type::Matrix {
                    return matrix::<S>(bytes, backend.policy());
                }
                let width = zkc_kernels::plonky3::residue::width::<S>();
                let mut values = Vec::new();
                values
                    .try_reserve_exact((bytes.len() - 10) / width)
                    .map_err(|_| Error::Limit)?;
                for word in bytes[10..].chunks_exact(width) {
                    values.push(
                        zkc_kernels::plonky3::residue::decode::<S>(word)
                            .map_err(|_| invalid(DecodeReason::Scalar))?,
                    );
                }
                Ok(S::vector_value(values))
            })()
        });
    }
    if ty.kind() == Type::Matrix {
        return match tag {
            23 => matrix::<crate::Scalar>(bytes, backend.policy()),
            45 => matrix::<crate::Bn254Scalar>(bytes, backend.policy()),
            24 => matrix::<crate::RistrettoScalar>(bytes, backend.policy()),
            75 => matrix::<crate::Binary64>(bytes, backend.policy()),
            78 => matrix::<crate::Binary64Ext3>(bytes, backend.policy()),
            _ => Err(unsupported()),
        };
    }
    if matches!(tag, 71 | 72) {
        let scheme = crate::merkle::Scheme::from_identity(ty.logical().identity())
            .ok_or_else(unsupported)?;
        let digests = &bytes[if tag == 71 { 6 } else { 10 }..];
        // Canonical digest encodings only; framing alone authenticates nothing.
        if !scheme.valid_digests(digests) {
            return Err(invalid(DecodeReason::Scalar));
        }
        let mut copy = Vec::new();
        copy.try_reserve_exact(digests.len())
            .map_err(|_| Error::Limit)?;
        copy.extend_from_slice(digests);
        return Ok(if tag == 71 {
            Value::MerkleDigest(scheme, copy.into())
        } else {
            Value::MerkleProof(scheme, copy.into())
        });
    }
    if let Some(d) = crate::oracle::Domain::from_identity(ty.logical().identity()) {
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
    if crate::operations::halo2curves::is_resident(ty) {
        use zkc_kernels::halo2curves::bn254 as kernel;
        let decoded = match tag {
            41 => kernel::ScalarVector::from_bytes(&bytes[10..])
                .map(|v| Value::HaloVector(std::sync::Arc::new(v))),
            47 => kernel::G1Vector::from_bytes(&bytes[10..])
                .map(|v| Value::HaloG1Vector(std::sync::Arc::new(v))),
            49 => kernel::G2Vector::from_bytes(&bytes[10..])
                .map(|v| Value::HaloG2Vector(std::sync::Arc::new(v))),
            _ => return Err(unsupported()),
        };
        return decoded.map_err(|e| match e {
            kernel::Error::InvalidEncoding => invalid(if tag == 41 {
                DecodeReason::Scalar
            } else {
                DecodeReason::Group
            }),
            _ => Error::Backend(crate::operations::halo2curves::failure(e)),
        });
    }
    if crate::operations::blst::is_resident(ty) {
        use zkc_kernels::blst::bls12_381 as kernel;
        return match tag {
            66 => kernel::ScalarVector::try_from_fn((bytes.len() - 10) / 32, |i| {
                kernel::decode_scalar(&bytes[10 + i * 32..10 + (i + 1) * 32])
            })
            .map(|v| Value::BlstVector(std::sync::Arc::new(v)))
            .map_err(|e| resident_decode_error(e, DecodeReason::Scalar)),
            67 => kernel::G1Vector::try_from_fn((bytes.len() - 10) / 48, |i| {
                kernel::G1::from_bytes(&bytes[10 + i * 48..10 + (i + 1) * 48])
            })
            .map(|v| Value::BlstG1Vector(std::sync::Arc::new(v)))
            .map_err(|e| resident_decode_error(e, DecodeReason::Group)),
            52 => kernel::G2Vector::try_from_fn((bytes.len() - 10) / 96, |i| {
                kernel::G2::from_bytes(&bytes[10 + i * 96..10 + (i + 1) * 96])
            })
            .map(|v| Value::BlstG2Vector(std::sync::Arc::new(v)))
            .map_err(|e| resident_decode_error(e, DecodeReason::Group)),
            _ => Err(unsupported()),
        };
    }
    match tag {
        66 => values!(
            32,
            zkc_kernels::arkworks::bls12_381::decode_scalar,
            Vector,
            Scalar
        ),
        41 => values!(
            32,
            zkc_kernels::arkworks::bn254::decode_scalar,
            Bn254Vector,
            Scalar
        ),
        74 => values!(
            8,
            zkc_kernels::plonky3::binary::decode,
            Binary64Vector,
            Scalar
        ),
        77 => values!(
            24,
            zkc_kernels::plonky3::binary::decode_ext3,
            Binary64Ext3Vector,
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
        67 => values!(48, crate::G1::from_bytes, Groups, Group),
        47 => values!(32, crate::Bn254G1::from_bytes, Bn254G1Vector, Group),
        49 => values!(64, crate::Bn254G2::from_bytes, Bn254G2Vector, Group),
        52 => values!(96, crate::Bls12381G2::from_bytes, Bls12381G2Vector, Group),
        69 => values!(
            32,
            |b: &[u8; 32]| crate::EdwardsPrime::from_bytes(b).ok_or(()),
            EdwardsGroups,
            Group
        ),
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

fn resident_decode_error(
    error: zkc_kernels::blst::bls12_381::Error,
    reason: DecodeReason,
) -> Error {
    use zkc_kernels::blst::bls12_381::Error as E;
    match error {
        E::Allocation | E::CapacityOverflow => Error::Limit,
        _ => invalid(reason),
    }
}
