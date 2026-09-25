//! First physical matrix representation: immutable canonical sparse COO.
//! The logical matrix contract has no storage layout or backend dependency.
use crate::kernels::arithmetic::{Coefficient, reserve};
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use ark_ff::{BigInt, BigInteger, PrimeField};
use p3_field::{BasedVectorSpace, PrimeField32};
use sha2::{Digest, Sha256};
use std::sync::Arc;
use zkc_runtime::interactive::{Identity, PhysicalType, Type};

/// Canonical mathematical coefficients, independent of Montgomery or wire
/// storage. Prime fields use their least nonnegative decimal representative.
pub(crate) trait CanonicalCoefficient: Coefficient {
    const IDENTITY: Identity;
    fn canonical(self) -> String;
}
impl CanonicalCoefficient for crate::Scalar {
    const IDENTITY: Identity = Identity::Bls12381Fr;
    fn canonical(self) -> String {
        self.into_bigint().to_string()
    }
}
impl CanonicalCoefficient for crate::Bn254Scalar {
    const IDENTITY: Identity = Identity::Bn254Fr;
    fn canonical(self) -> String {
        self.into_bigint().to_string()
    }
}
impl CanonicalCoefficient for crate::RistrettoScalar {
    const IDENTITY: Identity = Identity::Ristretto255Scalar;
    fn canonical(self) -> String {
        let mut limbs = [0; 4];
        for (limb, bytes) in limbs.iter_mut().zip(self.to_bytes().as_chunks::<8>().0) {
            *limb = u64::from_le_bytes(*bytes);
        }
        BigInt::<4>::new(limbs).to_string()
    }
}
impl CanonicalCoefficient for crate::KoalaBear {
    const IDENTITY: Identity = Identity::KoalaBear;
    fn canonical(self) -> String {
        self.as_canonical_u32().to_string()
    }
}
impl CanonicalCoefficient for crate::KoalaBearExt8 {
    const IDENTITY: Identity = Identity::KoalaBearExt8;
    fn canonical(self) -> String {
        // The installed ascending power basis gives the canonical integer
        // sum(c_i * p^i). Its decimal spelling is injective and agrees with
        // prime-field spelling for embedded base elements. p^8 < 2^256.
        let radix = BigInt::<4>::from(crate::plonky3::MODULUS);
        let mut value = BigInt::<4>::default();
        let coordinates: &[crate::KoalaBear] = self.as_basis_coefficients_slice();
        for c in coordinates.iter().rev() {
            value = value.mul_low(&radix);
            value.add_with_carry(&BigInt::from(c.as_canonical_u32()));
        }
        value.to_string()
    }
}

pub const MATRIX_DIMENSION_LIMIT: usize = 1 << 16;
pub const MATRIX_NONZERO_LIMIT: usize = 1 << 20;

/// Entries are unique, nonzero and strictly ordered by (row, column). Only
/// checked constructors can create this representation; clones share backing.
#[derive(Clone, Debug)]
pub struct SparseCoo<S> {
    rows: usize,
    columns: usize,
    entries: Arc<[(u32, u32, S)]>,
}
impl<S> SparseCoo<S> {
    pub fn rows(&self) -> usize {
        self.rows
    }
    pub fn columns(&self) -> usize {
        self.columns
    }
    pub fn entries(&self) -> &[(u32, u32, S)] {
        &self.entries
    }
    pub(crate) fn retained_bytes(&self) -> Result<usize> {
        size(self.entries.len(), std::mem::size_of::<(u32, u32, S)>())
    }
    pub(crate) fn policy(&self, p: &Policy) -> Result<()> {
        preflight::<S>(self.rows, self.columns, self.entries.len(), p)
    }
}
fn preflight<S>(rows: usize, columns: usize, nnz: usize, p: &Policy) -> Result<()> {
    if rows > MATRIX_DIMENSION_LIMIT || columns > MATRIX_DIMENSION_LIMIT {
        return Err(exhausted("matrix-dimension-limit"));
    }
    if nnz > MATRIX_NONZERO_LIMIT {
        return Err(exhausted("matrix-nonzero-limit"));
    }
    let cells = rows
        .checked_mul(columns)
        .ok_or_else(|| exhausted("size-overflow"))?;
    if nnz > cells {
        return Err(refused("matrix-count"));
    }
    p.output(size(nnz, std::mem::size_of::<(u32, u32, S)>())?, usize::MAX)
}
fn entry<S: Coefficient>(
    rows: usize,
    columns: usize,
    previous: Option<(u32, u32)>,
    current: (u32, u32, S),
) -> Result<()> {
    let (r, c, a) = current;
    if r as usize >= rows || c as usize >= columns {
        return Err(refused("matrix-index"));
    }
    if previous.is_some_and(|p| p >= (r, c)) {
        return Err(refused("matrix-order"));
    }
    if a == S::zero() {
        return Err(refused("matrix-zero"));
    }
    Ok(())
}
pub(crate) fn from_entries<S: Coefficient>(
    rows: usize,
    columns: usize,
    entries: &[(u32, u32, S)],
    p: &Policy,
) -> Result<SparseCoo<S>> {
    preflight::<S>(rows, columns, entries.len(), p)?;
    let mut previous = None;
    for &e in entries {
        entry(rows, columns, previous, e)?;
        previous = Some((e.0, e.1));
    }
    let mut owned = reserve(entries.len())?;
    owned.extend_from_slice(entries);
    Ok(SparseCoo {
        rows,
        columns,
        entries: owned.into(),
    })
}

/// Public-data content binding under SHA256, not relation satisfaction or key
/// provenance. Checked constructors already enforce normalized sorted COO.
/// Stream compact JSON without retaining a second copy of the matrix:
/// ["zkc.matrix/1", field, [rowsString, columnsString, [[r,c,coefficient],...]]].
pub(crate) fn identity_check<S: CanonicalCoefficient>(
    m: &SparseCoo<S>,
    attributes: &[String],
) -> Result<bool> {
    let [expected] = attributes else {
        return Err(refused("kernel-attributes"));
    };
    if expected.len() != 64
        || !expected
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(refused("kernel-attributes"));
    }
    let mut hash = Sha256::new();
    hash.update(b"[\"zkc.matrix/1\",\"");
    hash.update(S::IDENTITY.name());
    hash.update(b"\",[\"");
    hash.update(m.rows.to_string());
    hash.update(b"\",\"");
    hash.update(m.columns.to_string());
    hash.update(b"\",[");
    for (i, &(r, c, a)) in m.entries.iter().enumerate() {
        if i != 0 {
            hash.update(b",");
        }
        hash.update(b"[\"");
        hash.update(r.to_string());
        hash.update(b"\",\"");
        hash.update(c.to_string());
        hash.update(b"\",\"");
        hash.update(a.canonical());
        hash.update(b"\"]");
    }
    hash.update(b"]]]");
    Ok(format!("{:x}", hash.finalize()) == *expected)
}

/// Shared algorithms use upstream scalar arithmetic. Exact dimensions are
/// checked before allocating; no dense matrix, cache, file lookup or padding.
pub(crate) fn mul<S: Coefficient>(
    m: &SparseCoo<S>,
    x: &[S],
    transpose: bool,
    p: &Policy,
    available: usize,
) -> Result<Vec<S>> {
    let (input, output) = if transpose {
        (m.rows, m.columns)
    } else {
        (m.columns, m.rows)
    };
    if x.len() != input {
        return Err(refused("matrix-shape"));
    }
    p.vector_width(output, std::mem::size_of::<S>())?;
    p.output(size(output, std::mem::size_of::<S>())?, available)?;
    let mut result = reserve(output)?;
    result.resize(output, S::zero());
    for &(r, c, a) in m.entries.iter() {
        let (i, j) = if transpose {
            (c as usize, r as usize)
        } else {
            (r as usize, c as usize)
        };
        result[i] = result[i] + a * x[j];
    }
    Ok(result)
}
pub(crate) fn bilinear<S: Coefficient>(m: &SparseCoo<S>, y: &[S], x: &[S]) -> Result<S> {
    if y.len() != m.rows || x.len() != m.columns {
        return Err(refused("matrix-shape"));
    }
    Ok(m.entries.iter().fold(S::zero(), |s, &(r, c, a)| {
        s + y[r as usize] * a * x[c as usize]
    }))
}

trait Wire: Coefficient {
    const WIDTH: usize;
    const TAG: u8;
    fn decode(bytes: &[u8]) -> Result<Self>;
    fn encode(self, out: &mut Vec<u8>) -> Result<()>;
    fn value(m: SparseCoo<Self>) -> Value;
}
impl Wire for crate::Bn254Scalar {
    const WIDTH: usize = 32;
    const TAG: u8 = 45;
    fn decode(bytes: &[u8]) -> Result<Self> {
        zkc_arkworks::bn254::decode_scalar(bytes).map_err(crate::ark)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(zkc_arkworks::bn254::encode_scalar(&self).map_err(crate::ark)?);
        Ok(())
    }
    fn value(m: SparseCoo<Self>) -> Value {
        Value::Bn254Matrix(m)
    }
}
impl Wire for crate::Scalar {
    const WIDTH: usize = 32;
    const TAG: u8 = 23;
    fn decode(bytes: &[u8]) -> Result<Self> {
        zkc_arkworks::decode_scalar(bytes).map_err(crate::ark)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(zkc_arkworks::encode_scalar(&self).map_err(crate::ark)?);
        Ok(())
    }
    fn value(m: SparseCoo<Self>) -> Value {
        Value::Matrix(m)
    }
}
impl Wire for crate::RistrettoScalar {
    const WIDTH: usize = 32;
    const TAG: u8 = 24;
    fn decode(bytes: &[u8]) -> Result<Self> {
        let a = bytes.try_into().map_err(|_| refused("wire-length"))?;
        Option::from(Self::from_canonical_bytes(a)).ok_or_else(|| refused("noncanonical-scalar"))
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(self.to_bytes());
        Ok(())
    }
    fn value(m: SparseCoo<Self>) -> Value {
        Value::RistrettoMatrix(m)
    }
}
impl Wire for crate::KoalaBear {
    const WIDTH: usize = 4;
    const TAG: u8 = 25;
    fn decode(bytes: &[u8]) -> Result<Self> {
        crate::plonky3::decode_scalar(bytes)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(crate::plonky3::encode_scalar(self));
        Ok(())
    }
    fn value(m: SparseCoo<Self>) -> Value {
        Value::KoalaBearMatrix(m)
    }
}
impl Wire for crate::KoalaBearExt8 {
    const WIDTH: usize = 32;
    const TAG: u8 = 30;
    fn decode(bytes: &[u8]) -> Result<Self> {
        crate::plonky3::decode_extension(bytes)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(crate::plonky3::encode_extension(self));
        Ok(())
    }
    fn value(m: SparseCoo<Self>) -> Value {
        Value::KoalaBearExt8Matrix(m)
    }
}
fn wire_size<S: Wire>(n: usize) -> Result<usize> {
    n.checked_mul(8 + S::WIDTH)
        .and_then(|n| n.checked_add(18))
        .ok_or_else(|| exhausted("size-overflow"))
}
fn encode_matrix<S: Wire>(m: &SparseCoo<S>, p: &Policy) -> Result<Vec<u8>> {
    m.policy(p)?;
    let length = wire_size::<S>(m.entries.len())?;
    p.wire(length)?;
    let mut out = reserve(length)?;
    out.extend_from_slice(b"ZKCV\x01");
    out.push(S::TAG);
    for n in [m.rows, m.columns, m.entries.len()] {
        out.extend(
            u32::try_from(n)
                .map_err(|_| exhausted("size-overflow"))?
                .to_le_bytes(),
        );
    }
    for &(r, c, a) in m.entries.iter() {
        out.extend(r.to_le_bytes());
        out.extend(c.to_le_bytes());
        a.encode(&mut out)?;
    }
    Ok(out)
}
fn u32le(b: &[u8]) -> Result<u32> {
    Ok(u32::from_le_bytes(
        b.try_into().map_err(|_| refused("wire-length"))?,
    ))
}
#[allow(
    clippy::chunks_exact_to_as_chunks,
    reason = "generic associated scalar widths cannot be array lengths on stable Rust"
)]
fn decode_matrix<S: Wire>(bytes: &[u8], p: &Policy) -> Result<Value> {
    p.wire(bytes.len())?;
    if bytes.len() < 6 || &bytes[..5] != b"ZKCV\x01" || bytes[5] != S::TAG {
        return Err(refused("wire-header"));
    }
    if bytes.len() < 18 {
        return Err(refused("wire-length"));
    }
    let rows = u32le(&bytes[6..10])? as usize;
    let columns = u32le(&bytes[10..14])? as usize;
    let nnz = u32le(&bytes[14..18])? as usize;
    preflight::<S>(rows, columns, nnz, p)?;
    if wire_size::<S>(nnz)? != bytes.len() {
        return Err(refused("wire-length"));
    }
    let decode_entry = |chunk: &[u8]| -> Result<_> {
        Ok((
            u32le(&chunk[..4])?,
            u32le(&chunk[4..8])?,
            S::decode(&chunk[8..])?,
        ))
    };
    // First pass validates every coefficient and coordinate before reserving
    // backing. The second pass decodes the same immutable bytes into storage.
    let mut previous = None;
    for chunk in bytes[18..].chunks_exact(8 + S::WIDTH) {
        let e = decode_entry(chunk)?;
        entry(rows, columns, previous, e)?;
        previous = Some((e.0, e.1));
    }
    let mut entries = reserve(nnz)?;
    for chunk in bytes[18..].chunks_exact(8 + S::WIDTH) {
        entries.push(decode_entry(chunk)?);
    }
    Ok(S::value(SparseCoo {
        rows,
        columns,
        entries: entries.into(),
    }))
}
pub(crate) fn encode(v: &Value, p: &Policy) -> Option<Result<Vec<u8>>> {
    Some(match v {
        Value::Bn254Matrix(m) => encode_matrix(m, p),
        Value::Matrix(m) => encode_matrix(m, p),
        Value::RistrettoMatrix(m) => encode_matrix(m, p),
        Value::KoalaBearMatrix(m) => encode_matrix(m, p),
        Value::KoalaBearExt8Matrix(m) => encode_matrix(m, p),
        _ => return None,
    })
}
pub(crate) fn decode(ty: PhysicalType, bytes: &[u8], p: &Policy) -> Option<Result<Value>> {
    if ty.kind() != Type::Matrix {
        return None;
    }
    Some(match ty.logical().identity() {
        Identity::Bn254Fr => decode_matrix::<crate::Bn254Scalar>(bytes, p),
        Identity::Bls12381Fr => decode_matrix::<crate::Scalar>(bytes, p),
        Identity::Ristretto255Scalar => decode_matrix::<crate::RistrettoScalar>(bytes, p),
        Identity::KoalaBear => decode_matrix::<crate::KoalaBear>(bytes, p),
        Identity::KoalaBearExt8 => decode_matrix::<crate::KoalaBearExt8>(bytes, p),
        _ => Err(refused("wire-type")),
    })
}

macro_rules! constructor {
    ($name:ident, $variant:ident, $s:ty) => {
        impl Value {
            /// Construct a public matrix from already canonical COO entries.
            /// Duplicates, zeros and unsorted inputs are refused, never normalized.
            pub fn $name(
                rows: usize,
                columns: usize,
                entries: &[(u32, u32, $s)],
                p: &Policy,
            ) -> Result<Self> {
                Ok(Self::$variant(from_entries(rows, columns, entries, p)?))
            }
        }
    };
}
constructor!(matrix, Matrix, crate::Scalar);
constructor!(ristretto_matrix, RistrettoMatrix, crate::RistrettoScalar);
constructor!(koala_bear_matrix, KoalaBearMatrix, crate::KoalaBear);
constructor!(
    koala_bear_ext8_matrix,
    KoalaBearExt8Matrix,
    crate::KoalaBearExt8
);

constructor!(bn254_matrix, Bn254Matrix, crate::Bn254Scalar);
