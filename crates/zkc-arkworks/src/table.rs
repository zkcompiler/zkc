use crate::{Bounds, Error, SCALAR_BYTES, Scalar, decode_scalar, encode_scalar};
use crate::{bounds::vector, error::same_arity};
use ark_ff::{AdditiveGroup, Field};
use ark_poly::DenseMultilinearExtension;
use std::{fmt, sync::Arc};

/// An immutable MLE table. Clone is O(1) and shares backend storage.
/// No method yields mutable storage. Restriction allocates new scratch, keeping
/// all earlier aliases and committed originals unchanged on success and error.
#[derive(Clone)]
pub struct Table {
    pub(crate) polynomial: Arc<DenseMultilinearExtension<Scalar>>,
}

impl fmt::Debug for Table {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Table")
            .field("arity", &self.arity())
            .finish_non_exhaustive()
    }
}

impl Table {
    /// Validate shape/policy before allocating, then copy and bit-reverse once.
    pub fn from_logical(values: &[Scalar], bounds: &Bounds) -> Result<Self, Error> {
        let n = bounds.table_length(values.len())?;
        let mut owned = vector(values.len())?;
        owned.extend_from_slice(values);
        Ok(Self::permuted(owned, n))
    }

    /// Consume an already allocated logical vector and permute it in place.
    /// Validates before conversion. The caller owns the input allocation cost.
    pub fn from_logical_vec(values: Vec<Scalar>, bounds: &Bounds) -> Result<Self, Error> {
        let n = bounds.table_length(values.len())?;
        Ok(Self::permuted(values, n))
    }

    fn permuted(mut values: Vec<Scalar>, n: usize) -> Self {
        for j in 0..values.len() {
            let i = bit_reverse(j, n);
            if i > j {
                values.swap(i, j);
            }
        }
        Self::backend(values, n)
    }

    fn backend(values: Vec<Scalar>, n: usize) -> Self {
        // Only validated ingress and shape-preserving restriction reach here.
        Self {
            polynomial: Arc::new(DenseMultilinearExtension::from_evaluations_vec(n, values)),
        }
    }

    /// Decode concatenated canonical scalars in logical order. The enclosing
    /// artifact supplies arity; length/bounds are checked before allocation.
    pub fn from_logical_bytes(n: usize, bytes: &[u8], bounds: &Bounds) -> Result<Self, Error> {
        bounds.bytes(bytes.len())?;
        let len = bounds.table(n)?;
        let expected = len
            .checked_mul(SCALAR_BYTES)
            .ok_or(Error::CapacityOverflow)?;
        if bytes.len() != expected {
            return Err(Error::InvalidEncoding);
        }
        let mut values = vector(len)?;
        for chunk in bytes.as_chunks::<SCALAR_BYTES>().0 {
            values.push(decode_scalar(chunk)?);
        }
        Ok(Self::permuted(values, n))
    }

    /// Number of remaining coordinates; constants have arity zero and one cell.
    pub fn arity(&self) -> usize {
        self.polynomial.num_vars
    }

    /// Number of table entries, always `2^arity`.
    pub fn len(&self) -> usize {
        self.polynomial.evaluations.len()
    }

    /// Allocated scalar slots in the immutable backing, including spare capacity.
    /// Hosts use this read-only size for conservative retained-byte accounting.
    pub fn storage_capacity(&self) -> usize {
        self.polynomial.evaluations.capacity()
    }

    /// A valid table is never empty, including at zero arity.
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Copy values into the logical MSB-first order.
    pub fn logical_values(&self) -> Result<Vec<Scalar>, Error> {
        let mut values = vector(self.len())?;
        for i in 0..self.len() {
            values.push(self.polynomial.evaluations[bit_reverse(i, self.arity())]);
        }
        Ok(values)
    }

    /// Serialize in logical order without a second whole-table scalar copy.
    pub fn to_logical_bytes(&self, bounds: &Bounds) -> Result<Vec<u8>, Error> {
        bounds.table(self.arity())?;
        let len = self
            .len()
            .checked_mul(SCALAR_BYTES)
            .ok_or(Error::CapacityOverflow)?;
        bounds.bytes(len)?;
        let mut bytes = vector(len)?;
        for i in 0..self.len() {
            bytes.extend_from_slice(&encode_scalar(
                &self.polynomial.evaluations[bit_reverse(i, self.arity())],
            )?);
        }
        Ok(bytes)
    }

    /// Fix logical coordinate zero. Returns fresh low-bit scratch of arity n-1.
    pub fn restrict_first(&self, r: Scalar) -> Result<Self, Error> {
        if self.arity() == 0 {
            return Err(Error::PositiveArityRequired);
        }
        let mut values = vector(self.len() / 2)?;
        for pair in self.polynomial.evaluations.as_chunks::<2>().0 {
            values.push(pair[0] + r * (pair[1] - pair[0]));
        }
        Ok(Self::backend(values, self.arity() - 1))
    }

    /// Evaluate by the tensor-product definition, independently of restriction
    /// and upstream PCS opening. O(n * 2^n) field operations, no table allocation.
    pub fn evaluate(&self, point: &[Scalar]) -> Result<Scalar, Error> {
        same_arity(self.arity(), point.len())?;
        Ok(self
            .polynomial
            .evaluations
            .iter()
            .enumerate()
            .map(|(j, value)| {
                point.iter().enumerate().fold(*value, |v, (bit, r)| {
                    v * if j >> bit & 1 == 1 {
                        *r
                    } else {
                        Scalar::ONE - r
                    }
                })
            })
            .sum())
    }

    /// Sum the product of two original MLEs on the Boolean cube.
    pub fn product_boolean_sum(&self, other: &Self) -> Result<Scalar, Error> {
        same_arity(self.arity(), other.arity())?;
        Ok(self
            .polynomial
            .evaluations
            .iter()
            .zip(&other.polynomial.evaluations)
            .map(|(a, b)| *a * b)
            .sum())
    }

    /// Coefficients `[constant, linear, quadratic]` of the first-coordinate
    /// product round, summed over all remaining Boolean coordinates.
    /// This is the product of two MLEs, not the MLE of their pointwise product.
    pub fn round_product(&self, other: &Self) -> Result<[Scalar; 3], Error> {
        same_arity(self.arity(), other.arity())?;
        if self.arity() == 0 {
            return Err(Error::PositiveArityRequired);
        }
        let mut q = [Scalar::ZERO; 3];
        for (a, b) in self
            .polynomial
            .evaluations
            .as_chunks::<2>()
            .0
            .iter()
            .zip(other.polynomial.evaluations.as_chunks::<2>().0)
        {
            let da = a[1] - a[0];
            let db = b[1] - b[0];
            q[0] += a[0] * b[0];
            q[1] += da * b[0] + a[0] * db;
            q[2] += da * db;
        }
        Ok(q)
    }

    /// Extract the single value of a fully restricted table.
    pub fn scalar_at_zero_arity(&self) -> Result<Scalar, Error> {
        if self.arity() != 0 {
            return Err(Error::ZeroArityRequired);
        }
        Ok(self.polynomial.evaluations[0])
    }
}

fn bit_reverse(i: usize, n: usize) -> usize {
    if n == 0 {
        0
    } else {
        i.reverse_bits() >> (usize::BITS as usize - n)
    }
}
