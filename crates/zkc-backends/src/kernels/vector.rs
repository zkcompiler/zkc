//! Destination arithmetic shared by dense kernels and numerical expressions.
//! Provider packing is a physical implementation detail; scalar tails preserve
//! exact field arithmetic. Callers own shape checks and storage reservations.
use super::field::{Coefficient, Family};
use p3_field::{ExtensionField, Field, PackedFieldExtension, PackedValue};
use std::{
    marker::PhantomData,
    ops::{Add, Mul, Neg, Sub},
};

pub(crate) trait Packing<S: Coefficient> {
    type Value: Copy
        + Add<Output = Self::Value>
        + Sub<Output = Self::Value>
        + Mul<Output = Self::Value>
        + Neg<Output = Self::Value>;
    const WIDTH: usize;
    fn broadcast(value: S) -> Self::Value;
    fn load(values: &[S]) -> Self::Value;
    fn store(value: Self::Value, values: &mut [S]);
}

pub(crate) struct Scalar;
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

/// Uses the provider's extension packing, including the degree-one base field.
/// Extension coordinates are transposed by provider APIs, never pointer casts.
pub(crate) struct Extension<B>(PhantomData<B>);
impl<B: Field, S: Coefficient + ExtensionField<B>> Packing<S> for Extension<B> {
    type Value = S::ExtensionPacking;
    const WIDTH: usize = B::Packing::WIDTH;
    #[inline]
    fn broadcast(value: S) -> Self::Value {
        value.into()
    }
    #[inline]
    fn load(values: &[S]) -> Self::Value {
        Self::Value::from_ext_slice(values)
    }
    #[inline]
    fn store(value: Self::Value, values: &mut [S]) {
        value.to_ext_slice(values);
    }
}

type Packed<S> = <<S as Family>::Packing as Packing<S>>::Value;

#[inline]
fn binary<S: Family>(
    a: &[S],
    b: &[S],
    out: &mut [S],
    scalar: impl Fn(S, S) -> S,
    packed: impl Fn(Packed<S>, Packed<S>) -> Packed<S>,
) {
    debug_assert_eq!(a.len(), b.len());
    debug_assert_eq!(a.len(), out.len());
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
}

#[inline]
fn unary<S: Family>(
    a: &[S],
    out: &mut [S],
    scalar: impl Fn(S) -> S,
    packed: impl Fn(Packed<S>) -> Packed<S>,
) {
    debug_assert_eq!(a.len(), out.len());
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
}

#[inline]
pub(crate) fn add<S: Family>(a: &[S], b: &[S], out: &mut [S]) {
    binary::<S>(a, b, out, |a, b| a + b, |a, b| a + b);
}
#[inline]
pub(crate) fn sub<S: Family>(a: &[S], b: &[S], out: &mut [S]) {
    binary::<S>(a, b, out, |a, b| a - b, |a, b| a - b);
}
#[inline]
pub(crate) fn mul<S: Family>(a: &[S], b: &[S], out: &mut [S]) {
    binary::<S>(a, b, out, |a, b| a * b, |a, b| a * b);
}
#[inline]
pub(crate) fn neg<S: Family>(a: &[S], out: &mut [S]) {
    unary::<S>(a, out, |a| -a, |a| -a);
}
#[inline]
pub(crate) fn scale<S: Family>(a: &[S], scalar: S, out: &mut [S]) {
    let packed = S::Packing::broadcast(scalar);
    unary::<S>(a, out, |a| a * scalar, |a| a * packed);
}
