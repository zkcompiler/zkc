//! Owned validated upstream buffers; shared ownership belongs to the caller.
use super::{
    Error, G1, G1Element, G2, G2Element, Scalar, ScalarElement, msm_work, msm_workspace_bytes,
    scaling, vector,
};
use crate::field::{Coefficient, Result as FieldResult};
use halo2curves_axiom::{
    group::{Curve, Group},
    msm::msm_serial,
};

macro_rules! owned_vector {
    ($name:ident, $element:ident, $upstream:ty, $decode:path, $encode:ident) => {
        /// Final upstream ABI storage. No hidden copy-on-write or preparation
        /// cache. A failed constructor drops all private partial storage.
        #[derive(Debug, Default, PartialEq, Eq)]
        pub struct $name(Vec<$upstream>);
        impl $name {
            /// Adopt storage after validating every element. No buffer copy;
            /// points are checked even when supplied as upstream affine types.
            pub fn from_elements(mut values: Vec<$upstream>) -> Result<Self, Error> {
                for value in &mut values {
                    *value = Self::validate_element(*value)?.0;
                }
                Ok(Self(values))
            }
            pub fn as_elements(&self) -> &[$upstream] {
                &self.0
            }
            pub fn into_elements(self) -> Vec<$upstream> {
                self.0
            }
            pub fn try_from_fn(
                len: usize,
                mut element: impl FnMut(usize) -> Result<$element, Error>,
            ) -> Result<Self, Error> {
                let mut values = vector(len)?;
                for index in 0..len {
                    values.push(element(index)?.0);
                }
                Ok(Self(values))
            }
            pub fn from_slice(values: &[$element]) -> Result<Self, Error> {
                Self::try_from_fn(values.len(), |index| Ok(values[index]))
            }
            pub fn filled(len: usize, value: $element) -> Result<Self, Error> {
                Self::try_from_fn(len, |_| Ok(value))
            }
            pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
                if !bytes.len().is_multiple_of($element::BYTES) {
                    return Err(Error::InvalidEncoding);
                }
                Self::try_from_fn(bytes.len() / $element::BYTES, |index| {
                    let start = index * $element::BYTES;
                    $decode(&bytes[start..start + $element::BYTES])
                })
            }
            /// Check the whole destination shape before writing any bytes.
            pub fn write_bytes(&self, out: &mut [u8]) -> Result<(), Error> {
                let bytes = self
                    .len()
                    .checked_mul($element::BYTES)
                    .ok_or(Error::CapacityOverflow)?;
                if out.len() != bytes {
                    return Err(Error::LengthMismatch);
                }
                for (element, out) in self.iter().zip(out.chunks_exact_mut($element::BYTES)) {
                    out.copy_from_slice(&element.$encode());
                }
                Ok(())
            }
            pub fn len(&self) -> usize {
                self.0.len()
            }
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }
            /// Capacity payload, excluding the Vec header and allocator metadata.
            pub fn storage_bytes(&self) -> usize {
                self.0.capacity() * size_of::<$upstream>()
            }
            pub fn get(&self, index: usize) -> Option<$element> {
                self.0.get(index).copied().map($element)
            }
            /// Slice-like index semantics; callers check dynamic indices.
            pub fn set(&mut self, index: usize, value: $element) {
                self.0[index] = value.0;
            }
            pub fn iter(
                &self,
            ) -> impl ExactSizeIterator<Item = $element> + DoubleEndedIterator + '_ {
                self.0.iter().copied().map($element)
            }
        }
    };
}
owned_vector!(
    ScalarVector,
    Scalar,
    ScalarElement,
    super::decode_scalar,
    to_bytes_le
);
owned_vector!(G1Vector, G1, G1Element, G1::from_bytes, to_bytes);
owned_vector!(G2Vector, G2, G2Element, G2::from_bytes, to_bytes);

impl ScalarVector {
    fn validate_element(value: ScalarElement) -> Result<Scalar, Error> {
        Ok(Scalar::from_element(value))
    }
    pub fn add_into(&self, rhs: &Self, out: &mut Self) -> FieldResult<()> {
        crate::vector::add(&self.0, &rhs.0, &mut out.0)
    }
    pub fn sub_into(&self, rhs: &Self, out: &mut Self) -> FieldResult<()> {
        crate::vector::sub(&self.0, &rhs.0, &mut out.0)
    }
    pub fn mul_into(&self, rhs: &Self, out: &mut Self) -> FieldResult<()> {
        crate::vector::mul(&self.0, &rhs.0, &mut out.0)
    }
    pub fn neg_into(&self, out: &mut Self) -> FieldResult<()> {
        crate::vector::neg(&self.0, &mut out.0)
    }
    pub fn scale_into(&self, scalar: Scalar, out: &mut Self) -> FieldResult<()> {
        crate::vector::scale(&self.0, scalar.0, &mut out.0)
    }
    pub fn inverse_into(&self, out: &mut Self) -> FieldResult<()> {
        crate::vector::Inversion::new(&self.0)?.write_into(&mut out.0)
    }
    pub fn dot(&self, rhs: &Self) -> FieldResult<Scalar> {
        ScalarElement::dot_product(&self.0, &rhs.0).map(Scalar)
    }
    pub fn sum(&self) -> Scalar {
        Scalar(self.0.iter().fold(ScalarElement::zero(), |a, b| a + b))
    }
    pub fn product(&self) -> Scalar {
        Scalar(self.0.iter().fold(ScalarElement::one(), |a, b| a * b))
    }
    pub fn evaluate(&self, x: Scalar) -> Scalar {
        Scalar(crate::polynomial::evaluate(&self.0, x.0))
    }
}

macro_rules! group_vector {
    ($name:ident, $point:ident, $affine:ty, $projective:ty) => {
        impl $name {
            fn validate_element(value: $affine) -> Result<$point, Error> {
                $point::from_element(value)
            }
            /// Reserve empty affine storage. Only validated points can be
            /// appended; no raw element is admitted through this constructor.
            pub fn with_capacity(capacity: usize) -> Result<Self, Error> {
                crate::allocation::reserve(capacity)
                    .map(Self)
                    .map_err(|_| Error::Allocation)
            }
            /// Append a validated point, reusing reserved affine storage.
            /// Like Vec::push, this may grow the buffer when capacity is full.
            pub fn push(&mut self, point: $point) {
                self.0.push(point.0);
            }
            /// Serial variable-time Pippenger, borrowing resident buffers.
            /// Caller admits timing and public-shape bounds. Upstream allocates
            /// scalar representations and bucket vectors infallibly.
            pub fn msm(&self, scalars: &ScalarVector) -> Result<$point, Error> {
                if self.len() != scalars.len() {
                    return Err(Error::LengthMismatch);
                }
                msm_workspace_bytes(self.len())?;
                msm_work(self.len())?;
                if self.is_empty() {
                    return Ok($point::identity());
                }
                let result = crate::cpu::install(|| {
                    // All-zero coefficients return without writing acc.
                    let mut acc = <$projective>::identity();
                    msm_serial(&scalars.0, &self.0, &mut acc);
                    acc.to_affine()
                });
                Ok($point(result))
            }
            fn map_into(
                &self,
                out: &mut Self,
                element: impl Fn(usize, $point) -> $point + Send + Sync,
            ) -> Result<(), Error> {
                if self.len() != out.len() {
                    return Err(Error::LengthMismatch);
                }
                crate::cpu::chunks_mut(&mut out.0, 32, |offset, chunk| {
                    for (index, out) in chunk.iter_mut().enumerate() {
                        let index = offset + index;
                        *out = element(index, $point(self.0[index])).0;
                    }
                });
                Ok(())
            }
            pub fn add_into(&self, rhs: &Self, out: &mut Self) -> Result<(), Error> {
                if self.len() != rhs.len() {
                    return Err(Error::LengthMismatch);
                }
                self.map_into(out, |i, point| point.add(&$point(rhs.0[i])))
            }
            pub fn neg_into(&self, out: &mut Self) -> Result<(), Error> {
                self.map_into(out, |_, point| point.neg())
            }
            /// Convenience Direct plan, without heap scratch.
            pub fn scale_into(&self, scalar: Scalar, out: &mut Self) -> Result<(), Error> {
                let mut plan = $point::scaling_plan(
                    self.len(),
                    scaling::Selection::Fixed(scaling::Algorithm::Direct),
                )?;
                self.scale_with_plan_into(scalar, out, &mut plan)
            }
            pub fn scale_each_into(
                &self,
                scalars: &ScalarVector,
                out: &mut Self,
            ) -> Result<(), Error> {
                let mut plan = $point::scaling_plan(
                    self.len(),
                    scaling::Selection::Fixed(scaling::Algorithm::Direct),
                )?;
                self.scale_each_with_plan_into(scalars, out, &mut plan)
            }
            pub fn scale_with_plan_into(
                &self,
                scalar: Scalar,
                out: &mut Self,
                plan: &mut scaling::Plan<$affine>,
            ) -> Result<(), Error> {
                plan.scale_into(&self.0, &mut out.0, |_| scalar.0, |p| p, |p| p)
            }
            pub fn scale_each_with_plan_into(
                &self,
                scalars: &ScalarVector,
                out: &mut Self,
                plan: &mut scaling::Plan<$affine>,
            ) -> Result<(), Error> {
                if self.len() != scalars.len() {
                    return Err(Error::LengthMismatch);
                }
                plan.scale_into(&self.0, &mut out.0, |i| scalars.0[i], |p| p, |p| p)
            }
            pub fn sum(&self) -> $point {
                // One final normalization, not one inversion per addition.
                let sum = self.0.iter().fold(<$projective>::identity(), |a, b| a + b);
                $point(sum.to_affine())
            }
        }
    };
}
group_vector!(G1Vector, G1, G1Element, halo2curves_axiom::bn256::G1);
group_vector!(G2Vector, G2, G2Element, halo2curves_axiom::bn256::G2);
