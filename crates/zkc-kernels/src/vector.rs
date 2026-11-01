//! Destination arithmetic shared by dense kernels and numerical expressions.
//! Provider packing is a physical implementation detail; scalar tails preserve
//! exact field arithmetic. Destinations have checked exact extents; callers own
//! their storage reservations.
use crate::field::{Coefficient, Error, Result};
use std::ops::{Add, Mul, Neg, Sub};

/// A nonempty set of independent field lanes. Arithmetic on `Value` must agree
/// with scalar arithmetic in every lane. `load` and `store` receive exactly
/// `WIDTH` elements; they must preserve lane order without extra storage.
pub trait Packing<S: Coefficient> {
    type Value: Copy
        + Send
        + Sync
        + Add<Output = Self::Value>
        + Sub<Output = Self::Value>
        + Mul<Output = Self::Value>
        + Neg<Output = Self::Value>;
    /// Must be greater than zero, including for the scalar implementation.
    const WIDTH: usize;
    fn broadcast(value: S) -> Self::Value;
    fn load(values: &[S]) -> Self::Value;
    fn store(value: Self::Value, values: &mut [S]);
}

pub struct Scalar;
impl<S: Coefficient> Packing<S> for Scalar {
    type Value = S;
    const WIDTH: usize = 1;
    #[inline]
    fn broadcast(value: S) -> S {
        value
    }
    #[inline]
    fn load(values: &[S]) -> S {
        values[0]
    }
    #[inline]
    fn store(value: S, values: &mut [S]) {
        values[0] = value;
    }
}

type Packed<S> = <<S as Coefficient>::Packing as Packing<S>>::Value;

/// Operands are whole slots in one caller-owned scratch allocation. A result
/// may overwrite either operand: both values are loaded before each write.
#[derive(Clone, Copy, Debug)]
pub enum SlotOperation {
    Add(usize, usize),
    Multiply(usize, usize),
    Negate(usize),
}

/// Existing destination algorithms over one native scalar representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Algorithm {
    Scalar,
    /// Native independent lanes, with the same scalar-order tail and no conversion.
    Packed,
}

/// A shape-bound choice, made without inspecting operand values. No scratch is
/// needed. Reuse requires the same scalar type and exact number of elements.
/// Providers retain their timing behavior; choosing lanes grants no new timing
/// or representation permission to a VM binding.
#[derive(Clone, Copy, Debug)]
pub struct Plan<S> {
    len: usize,
    algorithm: Algorithm,
    output_bytes: usize,
    scalar: std::marker::PhantomData<S>,
}

impl<S: Coefficient> Plan<S> {
    /// Execute independent lanes in an admitted scratch schedule. Exact slot
    /// overlap is safe; partial overlap is not expressible. This checks storage
    /// extents, not the caller's liveness or ownership obligation.
    pub fn apply_slots(
        &self,
        operation: SlotOperation,
        output: usize,
        stride: usize,
        storage: &mut [S],
    ) -> Result<()> {
        if stride < self.len || stride == 0 || !storage.len().is_multiple_of(stride) {
            return Err(Error::LengthMismatch);
        }
        let slots = storage.len() / stride;
        let (a, b) = match operation {
            SlotOperation::Add(a, b) | SlotOperation::Multiply(a, b) => (a, b),
            SlotOperation::Negate(a) => (a, a),
        };
        if [a, b, output].iter().any(|i| *i >= slots) {
            return Err(Error::LengthMismatch);
        }
        // Bounded by the validated allocation length; no products can wrap.
        let (a, b, output) = (a * stride, b * stride, output * stride);
        let width = S::Packing::WIDTH;
        let end = self.packed_end();
        for lane in (0..end).step_by(width) {
            let left = S::Packing::load(&storage[a + lane..a + lane + width]);
            let right = S::Packing::load(&storage[b + lane..b + lane + width]);
            let value = match operation {
                SlotOperation::Add(..) => left + right,
                SlotOperation::Multiply(..) => left * right,
                SlotOperation::Negate(..) => -left,
            };
            S::Packing::store(value, &mut storage[output + lane..output + lane + width]);
        }
        for lane in end..self.len {
            let left = storage[a + lane];
            let right = storage[b + lane];
            storage[output + lane] = match operation {
                SlotOperation::Add(..) => left + right,
                SlotOperation::Multiply(..) => left * right,
                SlotOperation::Negate(..) => -left,
            };
        }
        Ok(())
    }
    /// Make a fixed choice. Unavailable native packing is a refusal, never an
    /// implicit scalar fallback or a conversion to base-coordinate storage.
    pub fn new(len: usize, algorithm: Algorithm) -> Result<Self> {
        let output_bytes = len
            .checked_mul(size_of::<S>())
            .filter(|bytes| *bytes <= isize::MAX as usize)
            .ok_or(Error::CapacityOverflow)?;
        if algorithm == Algorithm::Packed && S::Packing::WIDTH <= 1 {
            return Err(Error::PackingUnavailable);
        }
        Ok(Self {
            len,
            algorithm,
            output_bytes,
            scalar: std::marker::PhantomData,
        })
    }

    /// Use the provider's compile-time native packing only when at least one
    /// full block fits. Portable builds and scalar-only extensions stay scalar.
    pub fn select(len: usize) -> Result<Self> {
        Self::new(
            len,
            if S::Packing::WIDTH > 1 && len >= S::Packing::WIDTH {
                Algorithm::Packed
            } else {
                Algorithm::Scalar
            },
        )
    }
    pub fn algorithm(&self) -> Algorithm {
        self.algorithm
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    pub fn output_bytes(&self) -> usize {
        self.output_bytes
    }
    pub fn workspace_bytes(&self) -> usize {
        0
    }

    #[inline]
    fn packed_end(&self) -> usize {
        match self.algorithm {
            Algorithm::Scalar => 0,
            Algorithm::Packed => self.len / S::Packing::WIDTH * S::Packing::WIDTH,
        }
    }

    #[inline]
    fn binary(
        &self,
        a: &[S],
        b: &[S],
        out: &mut [S],
        scalar: impl Fn(S, S) -> S + Send + Sync,
        packed: impl Fn(Packed<S>, Packed<S>) -> Packed<S> + Send + Sync,
    ) -> Result<()> {
        equal_len(self.len, a.len())?;
        equal_len(self.len, b.len())?;
        equal_len(self.len, out.len())?;
        let end = self.packed_end();
        let width = S::Packing::WIDTH;
        let grain = (4096 / width).max(1) * width;
        crate::cpu::chunks_mut(&mut out[..end], grain, |start, out| {
            for ((a, b), out) in a[start..start + out.len()]
                .chunks_exact(width)
                .zip(b[start..start + out.len()].chunks_exact(width))
                .zip(out.chunks_exact_mut(width))
            {
                S::Packing::store(packed(S::Packing::load(a), S::Packing::load(b)), out);
            }
        });
        crate::cpu::chunks_mut(&mut out[end..], 4096, |start, out| {
            for ((a, b), out) in a[end + start..end + start + out.len()]
                .iter()
                .zip(&b[end + start..end + start + out.len()])
                .zip(out)
            {
                *out = scalar(*a, *b);
            }
        });
        Ok(())
    }
    #[inline]
    fn unary(
        &self,
        a: &[S],
        out: &mut [S],
        scalar: impl Fn(S) -> S + Send + Sync,
        packed: impl Fn(Packed<S>) -> Packed<S> + Send + Sync,
    ) -> Result<()> {
        equal_len(self.len, a.len())?;
        equal_len(self.len, out.len())?;
        let end = self.packed_end();
        let width = S::Packing::WIDTH;
        let grain = (4096 / width).max(1) * width;
        crate::cpu::chunks_mut(&mut out[..end], grain, |start, out| {
            for (a, out) in a[start..start + out.len()]
                .chunks_exact(width)
                .zip(out.chunks_exact_mut(width))
            {
                S::Packing::store(packed(S::Packing::load(a)), out);
            }
        });
        crate::cpu::chunks_mut(&mut out[end..], 4096, |start, out| {
            for (a, out) in a[end + start..end + start + out.len()].iter().zip(out) {
                *out = scalar(*a);
            }
        });
        Ok(())
    }
    #[inline]
    pub fn add(&self, a: &[S], b: &[S], out: &mut [S]) -> Result<()> {
        self.binary(a, b, out, |a, b| a + b, |a, b| a + b)
    }
    #[inline]
    pub fn sub(&self, a: &[S], b: &[S], out: &mut [S]) -> Result<()> {
        self.binary(a, b, out, |a, b| a - b, |a, b| a - b)
    }
    #[inline]
    pub fn mul(&self, a: &[S], b: &[S], out: &mut [S]) -> Result<()> {
        self.binary(a, b, out, |a, b| a * b, |a, b| a * b)
    }
    #[inline]
    pub fn neg(&self, a: &[S], out: &mut [S]) -> Result<()> {
        self.unary(a, out, |a| -a, |a| -a)
    }
    #[inline]
    pub fn scale(&self, a: &[S], scalar: S, out: &mut [S]) -> Result<()> {
        let packed = S::Packing::broadcast(scalar);
        self.unary(a, out, |a| a * scalar, |a| a * packed)
    }
}

// The slice API and reusable plans share one implementation.
#[inline]
pub fn add<S: Coefficient>(a: &[S], b: &[S], out: &mut [S]) -> Result<()> {
    Plan::select(a.len())?.add(a, b, out)
}
#[inline]
pub fn sub<S: Coefficient>(a: &[S], b: &[S], out: &mut [S]) -> Result<()> {
    Plan::select(a.len())?.sub(a, b, out)
}
#[inline]
pub fn mul<S: Coefficient>(a: &[S], b: &[S], out: &mut [S]) -> Result<()> {
    Plan::select(a.len())?.mul(a, b, out)
}
#[inline]
pub fn neg<S: Coefficient>(a: &[S], out: &mut [S]) -> Result<()> {
    Plan::select(a.len())?.neg(a, out)
}
#[inline]
pub fn scale<S: Coefficient>(a: &[S], scalar: S, out: &mut [S]) -> Result<()> {
    Plan::select(a.len())?.scale(a, scalar, out)
}

/// Exact extents; no prefix truncation on a shape mismatch.
pub fn equal_len(a: usize, b: usize) -> Result<()> {
    if a == b {
        Ok(())
    } else {
        Err(Error::LengthMismatch)
    }
}

/// Checked nonzero operands for Montgomery batch inversion. Validation precedes
/// destination allocation; the caller owns initialized unpublished storage.
pub struct Inversion<'a, S> {
    values: &'a [S],
}
impl<'a, S: Coefficient> Inversion<'a, S> {
    pub fn new(values: &'a [S]) -> Result<Self> {
        if values.iter().any(|x| *x == S::zero()) {
            return Err(Error::ZeroInverse);
        }
        Ok(Self { values })
    }
    pub fn write_into(&self, out: &mut [S]) -> Result<()> {
        equal_len(self.values.len(), out.len())?;
        if self.values.is_empty() {
            return Ok(());
        }
        let mut product = S::one();
        for (x, prefix) in self.values.iter().zip(out.iter_mut()) {
            *prefix = product;
            product = product * *x;
        }
        let mut inverse = product.inverse().ok_or(Error::ZeroInverse)?;
        for (x, prefix) in self.values.iter().zip(out.iter_mut()).rev() {
            *prefix = *prefix * inverse;
            inverse = inverse * *x;
        }
        Ok(())
    }
}
