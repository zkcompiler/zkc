//! First physical matrix representation: immutable canonical sparse COO.
//! The logical matrix contract has no storage layout or backend dependency.
use crate::operations::arithmetic::{Coefficient, reserve};
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use ark_ff::{BigInt, BigInteger, PrimeField};
use p3_field::{BasedVectorSpace, PrimeField32};
use sha2::{Digest, Sha256};
use zkc_runtime::vm::Identity;

/// Canonical mathematical coefficients, independent of Montgomery or wire
/// storage. Prime fields use their least nonnegative decimal representative.
pub(crate) trait IdentityCoefficient: Coefficient {
    const IDENTITY: Identity;
    fn canonical(self) -> String;
}
impl IdentityCoefficient for crate::Scalar {
    const IDENTITY: Identity = Identity::Bls12381Fr;
    fn canonical(self) -> String {
        self.into_bigint().to_string()
    }
}
impl IdentityCoefficient for crate::Bn254Scalar {
    const IDENTITY: Identity = Identity::Bn254Fr;
    fn canonical(self) -> String {
        self.into_bigint().to_string()
    }
}
impl IdentityCoefficient for crate::RistrettoScalar {
    const IDENTITY: Identity = Identity::Ristretto255Scalar;
    fn canonical(self) -> String {
        let mut limbs = [0; 4];
        for (limb, bytes) in limbs.iter_mut().zip(self.to_bytes().as_chunks::<8>().0) {
            *limb = u64::from_le_bytes(*bytes);
        }
        BigInt::<4>::new(limbs).to_string()
    }
}
impl IdentityCoefficient for crate::KoalaBear {
    const IDENTITY: Identity = Identity::KoalaBear;
    fn canonical(self) -> String {
        self.as_canonical_u32().to_string()
    }
}
impl IdentityCoefficient for crate::KoalaBearExt4 {
    const IDENTITY: Identity = Identity::KoalaBearExt4;
    fn canonical(self) -> String {
        // As for the octic extension: sum(c_i * p^i) in the ascending basis.
        let radix = BigInt::<4>::from(zkc_kernels::plonky3::MODULUS);
        let mut value = BigInt::<4>::default();
        let coordinates: &[crate::KoalaBear] = self.as_basis_coefficients_slice();
        for c in coordinates.iter().rev() {
            value = value.mul_low(&radix);
            value.add_with_carry(&BigInt::from(c.as_canonical_u32()));
        }
        value.to_string()
    }
}
// A binary field's coefficient is the decimal integer of its bit pattern,
// sum(c_i * 2^i) over its coordinates c_i in GF(2): the extension rule above
// with characteristic two (docs/spec/domains/vectors.md).
impl IdentityCoefficient for crate::Binary64 {
    const IDENTITY: Identity = Identity::Binary64;
    fn canonical(self) -> String {
        zkc_kernels::plonky3::binary::bits(self).to_string()
    }
}
impl IdentityCoefficient for crate::Binary64Ext3 {
    const IDENTITY: Identity = Identity::Binary64Ext3;
    fn canonical(self) -> String {
        BigInt::<3>::new(zkc_kernels::plonky3::binary::ext3_bits(self)).to_string()
    }
}
impl IdentityCoefficient for crate::KoalaBearExt8 {
    const IDENTITY: Identity = Identity::KoalaBearExt8;
    fn canonical(self) -> String {
        // The installed ascending power basis gives the canonical integer
        // sum(c_i * p^i). Its decimal spelling is injective and agrees with
        // prime-field spelling for embedded base elements. p^8 < 2^256.
        let radix = BigInt::<4>::from(zkc_kernels::plonky3::MODULUS);
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

/// Native matrix storage with VM backing identity and policy admission.
#[derive(Clone, Debug)]
pub struct SparseCoo<S> {
    data: zkc_kernels::matrix::SparseCoo<S>,
}
impl<S> SparseCoo<S> {
    pub fn rows(&self) -> usize {
        self.data.rows()
    }
    pub fn columns(&self) -> usize {
        self.data.columns()
    }
    pub fn entries(&self) -> &[(u32, u32, S)] {
        self.data.entries()
    }
    pub(crate) fn retained_bytes(&self) -> Result<usize> {
        size(self.entries().len(), std::mem::size_of::<(u32, u32, S)>())
    }
    pub(crate) fn backing(&self) -> Result<zkc_runtime::vm::Backing> {
        Ok(zkc_runtime::vm::Backing::of(
            self.data.storage(),
            self.retained_bytes()?,
        ))
    }
    pub(crate) fn policy(&self, p: &Policy) -> Result<()> {
        preflight::<S>(self.rows(), self.columns(), self.entries().len(), p)
    }
}
fn failure(error: zkc_kernels::matrix::Error) -> zkc_runtime::vm::BackendError {
    if error == zkc_kernels::matrix::Error::Allocation {
        exhausted(error.code())
    } else {
        refused(error.code())
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

pub(crate) fn get<S: Coefficient>(m: &SparseCoo<S>, row: usize, column: usize) -> Result<S> {
    zkc_kernels::matrix::get(&m.data, row, column).map_err(failure)
}
pub(crate) fn from_entries<S: Coefficient>(
    rows: usize,
    columns: usize,
    entries: &[(u32, u32, S)],
    p: &Policy,
) -> Result<SparseCoo<S>> {
    preflight::<S>(rows, columns, entries.len(), p)?;
    Ok(SparseCoo {
        data: zkc_kernels::matrix::from_entries(rows, columns, entries).map_err(failure)?,
    })
}
/// Public-data content binding under SHA256, not relation satisfaction or key
/// provenance. Checked constructors already enforce normalized sorted COO.
/// Stream compact JSON without retaining a second copy of the matrix:
/// ["zkc.matrix/0", field, [rowsString, columnsString, [[r,c,coefficient],...]]].
pub(crate) fn identity_check<S: IdentityCoefficient>(
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
    hash.update(b"[\"zkc.matrix/0\",\"");
    hash.update(S::IDENTITY.name());
    hash.update(b"\",[\"");
    hash.update(m.rows().to_string());
    hash.update(b"\",\"");
    hash.update(m.columns().to_string());
    hash.update(b"\",[");
    for (i, &(r, c, a)) in m.entries().iter().enumerate() {
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
    Ok(hash
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>()
        == *expected)
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
        (m.rows(), m.columns())
    } else {
        (m.columns(), m.rows())
    };
    if x.len() != input {
        return Err(refused("matrix-shape"));
    }
    p.vector_width(output, std::mem::size_of::<S>())?;
    p.output(size(output, std::mem::size_of::<S>())?, available)?;
    let mut result = reserve(output)?;
    result.resize(output, S::zero());
    zkc_kernels::matrix::mul_into(&m.data, x, transpose, &mut result).map_err(failure)?;
    Ok(result)
}
pub(crate) fn row_dot<S: Coefficient>(m: &SparseCoo<S>, x: &[S], row: usize) -> Result<S> {
    zkc_kernels::matrix::row_dot(&m.data, x, row).map_err(failure)
}
pub(crate) fn column_dot<S: Coefficient>(m: &SparseCoo<S>, x: &[S], column: usize) -> Result<S> {
    zkc_kernels::matrix::column_dot(&m.data, x, column).map_err(failure)
}
pub(crate) fn bilinear<S: Coefficient>(m: &SparseCoo<S>, y: &[S], x: &[S]) -> Result<S> {
    zkc_kernels::matrix::bilinear(&m.data, y, x).map_err(failure)
}

pub(crate) trait Wire: Coefficient {
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
        zkc_kernels::arkworks::bn254::decode_scalar(bytes).map_err(crate::ark)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(zkc_kernels::arkworks::bn254::encode_scalar(&self).map_err(crate::ark)?);
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
        zkc_kernels::arkworks::bls12_381::decode_scalar(bytes).map_err(crate::ark)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(zkc_kernels::arkworks::bls12_381::encode_scalar(&self).map_err(crate::ark)?);
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
        zkc_kernels::plonky3::decode_scalar(bytes).map_err(crate::field_error)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(zkc_kernels::plonky3::encode_scalar(self));
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
        zkc_kernels::plonky3::decode_extension(bytes).map_err(crate::field_error)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(zkc_kernels::plonky3::encode_extension(self));
        Ok(())
    }
    fn value(m: SparseCoo<Self>) -> Value {
        Value::KoalaBearExt8Matrix(m)
    }
}
impl Wire for crate::KoalaBearExt4 {
    const WIDTH: usize = 16;
    const TAG: u8 = 28;
    fn decode(bytes: &[u8]) -> Result<Self> {
        zkc_kernels::plonky3::decode_quartic(bytes).map_err(crate::field_error)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(zkc_kernels::plonky3::encode_quartic(self));
        Ok(())
    }
    fn value(m: SparseCoo<Self>) -> Value {
        Value::KoalaBearExt4Matrix(m)
    }
}
impl Wire for crate::Binary64 {
    const WIDTH: usize = zkc_kernels::plonky3::binary::WIDTH;
    const TAG: u8 = 75;
    fn decode(bytes: &[u8]) -> Result<Self> {
        zkc_kernels::plonky3::binary::decode(bytes).map_err(crate::field_error)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(zkc_kernels::plonky3::binary::encode(self));
        Ok(())
    }
    fn value(m: SparseCoo<Self>) -> Value {
        Value::Binary64Matrix(m)
    }
}
impl Wire for crate::Binary64Ext3 {
    const WIDTH: usize = zkc_kernels::plonky3::binary::EXT3_WIDTH;
    const TAG: u8 = 78;
    fn decode(bytes: &[u8]) -> Result<Self> {
        zkc_kernels::plonky3::binary::decode_ext3(bytes).map_err(crate::field_error)
    }
    fn encode(self, out: &mut Vec<u8>) -> Result<()> {
        out.extend(zkc_kernels::plonky3::binary::encode_ext3(self));
        Ok(())
    }
    fn value(m: SparseCoo<Self>) -> Value {
        Value::Binary64Ext3Matrix(m)
    }
}
fn wire_size<S: Wire>(n: usize) -> Result<usize> {
    n.checked_mul(8 + S::WIDTH)
        .and_then(|n| n.checked_add(18))
        .ok_or_else(|| exhausted("size-overflow"))
}
fn encode_matrix<S: Wire>(m: &SparseCoo<S>, p: &Policy) -> Result<Vec<u8>> {
    m.policy(p)?;
    let length = wire_size::<S>(m.entries().len())?;
    p.wire(length)?;
    let mut out = reserve(length)?;
    out.extend_from_slice(b"ZKCV\x00");
    out.push(S::TAG);
    for n in [m.rows(), m.columns(), m.entries().len()] {
        out.extend(
            u32::try_from(n)
                .map_err(|_| exhausted("size-overflow"))?
                .to_le_bytes(),
        );
    }
    for &(r, c, a) in m.entries().iter() {
        out.extend(r.to_le_bytes());
        out.extend(c.to_le_bytes());
        a.encode(&mut out)?;
    }
    Ok(out)
}

pub(crate) fn encode(v: &Value, p: &Policy) -> Option<Result<Vec<u8>>> {
    Some(match v {
        Value::Bn254Matrix(m) => encode_matrix(m, p),
        Value::Matrix(m) => encode_matrix(m, p),
        Value::RistrettoMatrix(m) => encode_matrix(m, p),
        Value::KoalaBearMatrix(m) => encode_matrix(m, p),
        Value::KoalaBearExt8Matrix(m) => encode_matrix(m, p),
        Value::KoalaBearExt4Matrix(m) => encode_matrix(m, p),
        Value::Binary64Matrix(m) => encode_matrix(m, p),
        Value::Binary64Ext3Matrix(m) => encode_matrix(m, p),
        _ => return None,
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
constructor!(
    koala_bear_ext4_matrix,
    KoalaBearExt4Matrix,
    crate::KoalaBearExt4
);

constructor!(binary64_matrix, Binary64Matrix, crate::Binary64);
constructor!(
    binary64_ext3_matrix,
    Binary64Ext3Matrix,
    crate::Binary64Ext3
);

constructor!(bn254_matrix, Bn254Matrix, crate::Bn254Scalar);

#[cfg(test)]
mod tests;
