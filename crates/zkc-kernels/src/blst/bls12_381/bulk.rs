//! Typed, owned upstream storage. Wrap in the backend's ordinary shared owner
//! for cheap immutable cloning; no hidden copy-on-write or cached preparation.
use super::{Error, G1, G2, Scalar, msm_workspace_bytes, vector};
use crate::field::{Coefficient, Result as FieldResult};

macro_rules! owned_vector {
    ($name:ident, $element:ident, $upstream:ty, $decode:path, $encode:ident) => {
        /// Owned validated elements in the upstream bulk ABI. Construction is
        /// fallible; scalar extraction copies one value without allocating.
        /// Backends own admission and shared ownership of the finished carrier.
        #[derive(Debug, Default, PartialEq, Eq)]
        pub struct $name(Vec<$upstream>);

        impl $name {
            /// Adopt an owned buffer of trusted mathematical elements without
            /// allocation, copying or validation. Elements obey the same
            /// premises as the wrapper's `from_element`; decode external bytes
            /// with `from_bytes`. Capacity is retained for payload accounting.
            pub fn from_elements(values: Vec<$upstream>) -> Self {
                Self(values)
            }

            /// Borrow the exact upstream ABI for existing typed family kernels.
            pub fn as_elements(&self) -> &[$upstream] {
                &self.0
            }

            /// Transfer ownership of the buffer, with no allocation or copying.
            pub fn into_elements(self) -> Vec<$upstream> {
                self.0
            }

            /// Construct directly into the final upstream buffer. No wrapper
            /// vector is staged. A failed callback drops all private storage.
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

            /// Copy wrapper elements once, for an explicit storage boundary.
            pub fn from_slice(values: &[$element]) -> Result<Self, Error> {
                Self::try_from_fn(values.len(), |index| Ok(values[index]))
            }

            /// Decode concatenated canonical elements directly into resident
            /// storage. A partial final element or invalid encoding refuses.
            pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
                if !bytes.len().is_multiple_of($element::BYTES) {
                    return Err(Error::InvalidEncoding);
                }
                Self::try_from_fn(bytes.len() / $element::BYTES, |index| {
                    let start = index * $element::BYTES;
                    $decode(&bytes[start..start + $element::BYTES])
                })
            }

            /// Write canonical concatenated bytes into a caller-reserved exact
            /// destination, checking its complete extent before any writes.
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

            /// Initialize an owned destination before passing it to a kernel.
            pub fn filled(len: usize, value: $element) -> Result<Self, Error> {
                Self::try_from_fn(len, |_| Ok(value))
            }

            pub fn len(&self) -> usize {
                self.0.len()
            }
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }
            /// Reserved element payload, including spare capacity; excludes the
            /// Vec header, allocator overhead and the backend's shared owner.
            pub fn storage_bytes(&self) -> usize {
                self.0.capacity() * size_of::<$upstream>()
            }
            pub fn get(&self, index: usize) -> Option<$element> {
                self.0.get(index).copied().map($element)
            }
            /// Replace one validated element. Panics if `index >= len()`, like
            /// ordinary slice indexing; adapters validate indices beforehand.
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
    blstrs::Scalar,
    super::decode_scalar,
    to_bytes_le
);
owned_vector!(G1Vector, G1, blstrs::G1Projective, G1::from_bytes, to_bytes);
owned_vector!(G2Vector, G2, blstrs::G2Projective, G2::from_bytes, to_bytes);

impl ScalarVector {
    /// Destination operations reuse the existing shape-bound vector plan.
    /// All extents are checked before writes; no managed workspace is needed.
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
    /// Refuse any zero before writing; empty inversion succeeds.
    pub fn inverse_into(&self, out: &mut Self) -> FieldResult<()> {
        crate::vector::Inversion::new(&self.0)?.write_into(&mut out.0)
    }
    /// Exact equal-length dot product; empty inputs produce zero.
    pub fn dot(&self, rhs: &Self) -> FieldResult<Scalar> {
        blstrs::Scalar::dot_product(&self.0, &rhs.0).map(Scalar)
    }
    pub fn sum(&self) -> Scalar {
        Scalar(self.0.iter().fold(blstrs::Scalar::zero(), |a, b| a + b))
    }
    pub fn product(&self) -> Scalar {
        Scalar(self.0.iter().fold(blstrs::Scalar::one(), |a, b| a * b))
    }
    /// Ascending-degree coefficient evaluation using the shared Horner kernel.
    pub fn evaluate(&self, x: Scalar) -> Scalar {
        Scalar(crate::polynomial::evaluate(&self.0, x.0))
    }
}

macro_rules! group_vector {
    ($name:ident, $point:ident, $upstream:ty) => {
        impl $name {
            /// Equal-length variable-time MSM borrowing both resident buffers.
            /// No wrapper-to-upstream Vec is created. Upstream still allocates
            /// affine points, scalar bytes and Pippenger workspace infallibly.
            /// Explicit trusted timing authorization belongs to the caller.
            pub fn msm(&self, scalars: &ScalarVector) -> Result<$point, Error> {
                if self.len() != scalars.len() {
                    return Err(Error::LengthMismatch);
                }
                // Upstream indexes the first point and truncates mismatches.
                if self.is_empty() {
                    return Ok($point::identity());
                }
                msm_workspace_bytes(self.len())?;
                Ok($point(<$upstream>::multi_exp(&self.0, &scalars.0)))
            }

            fn map_into(
                &self,
                out: &mut Self,
                mut element: impl FnMut(usize, $point) -> $point,
            ) -> Result<(), Error> {
                if self.len() != out.len() {
                    return Err(Error::LengthMismatch);
                }
                for (index, (point, out)) in self.iter().zip(&mut out.0).enumerate() {
                    *out = element(index, point).0;
                }
                Ok(())
            }

            /// Equal-length addition; shape refusal precedes all writes.
            pub fn add_into(&self, rhs: &Self, out: &mut Self) -> Result<(), Error> {
                if self.len() != rhs.len() {
                    return Err(Error::LengthMismatch);
                }
                self.map_into(out, |i, point| point.add(&$point(rhs.0[i])))
            }
            pub fn neg_into(&self, out: &mut Self) -> Result<(), Error> {
                self.map_into(out, |_, point| point.neg())
            }
            /// Shared-scalar multiplication into owned resident storage.
            pub fn scale_into(&self, scalar: Scalar, out: &mut Self) -> Result<(), Error> {
                self.map_into(out, |_, point| point.scale(scalar))
            }
            /// Elementwise multiplication with an exact equal-length scalar vector.
            pub fn scale_each_into(
                &self,
                scalars: &ScalarVector,
                out: &mut Self,
            ) -> Result<(), Error> {
                if self.len() != scalars.len() {
                    return Err(Error::LengthMismatch);
                }
                self.map_into(out, |i, point| point.scale(Scalar(scalars.0[i])))
            }
            pub fn sum(&self) -> $point {
                self.iter().fold($point::identity(), |a, b| a.add(&b))
            }
        }
    };
}
group_vector!(G1Vector, G1, blstrs::G1Projective);
group_vector!(G2Vector, G2, blstrs::G2Projective);
