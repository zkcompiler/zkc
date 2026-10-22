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

#[inline]
fn binary<S: Coefficient>(
    a: &[S],
    b: &[S],
    out: &mut [S],
    scalar: impl Fn(S, S) -> S,
    packed: impl Fn(Packed<S>, Packed<S>) -> Packed<S>,
) -> Result<()> {
    equal_len(a.len(), b.len())?;
    equal_len(a.len(), out.len())?;
    let width = S::Packing::WIDTH;
    let end = if width > 1 {
        a.len() / width * width
    } else {
        0
    };
    for ((a, b), out) in a[..end]
        .chunks_exact(width)
        .zip(b[..end].chunks_exact(width))
        .zip(out[..end].chunks_exact_mut(width))
    {
        S::Packing::store(packed(S::Packing::load(a), S::Packing::load(b)), out);
    }
    for ((a, b), out) in a[end..].iter().zip(&b[end..]).zip(&mut out[end..]) {
        *out = scalar(*a, *b);
    }
    Ok(())
}

#[inline]
fn unary<S: Coefficient>(
    a: &[S],
    out: &mut [S],
    scalar: impl Fn(S) -> S,
    packed: impl Fn(Packed<S>) -> Packed<S>,
) -> Result<()> {
    equal_len(a.len(), out.len())?;
    let width = S::Packing::WIDTH;
    let end = if width > 1 {
        a.len() / width * width
    } else {
        0
    };
    for (a, out) in a[..end]
        .chunks_exact(width)
        .zip(out[..end].chunks_exact_mut(width))
    {
        S::Packing::store(packed(S::Packing::load(a)), out);
    }
    for (a, out) in a[end..].iter().zip(&mut out[end..]) {
        *out = scalar(*a);
    }
    Ok(())
}

#[inline]
pub fn add<S: Coefficient>(a: &[S], b: &[S], out: &mut [S]) -> Result<()> {
    binary::<S>(a, b, out, |a, b| a + b, |a, b| a + b)
}
#[inline]
pub fn sub<S: Coefficient>(a: &[S], b: &[S], out: &mut [S]) -> Result<()> {
    binary::<S>(a, b, out, |a, b| a - b, |a, b| a - b)
}
#[inline]
pub fn mul<S: Coefficient>(a: &[S], b: &[S], out: &mut [S]) -> Result<()> {
    binary::<S>(a, b, out, |a, b| a * b, |a, b| a * b)
}
#[inline]
pub fn neg<S: Coefficient>(a: &[S], out: &mut [S]) -> Result<()> {
    unary::<S>(a, out, |a| -a, |a| -a)
}
#[inline]
pub fn scale<S: Coefficient>(a: &[S], scalar: S, out: &mut [S]) -> Result<()> {
    let packed = S::Packing::broadcast(scalar);
    unary::<S>(a, out, |a| a * scalar, |a| a * packed)
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
