//! Field arithmetic independent of VM values and physical identities.
use crate::{
    Binary64, Binary64Ext3, KoalaBear, KoalaBearExt4, KoalaBearExt8, RistrettoScalar, Scalar,
};
use ark_ff::Field;
use std::ops::{Add, Mul, Neg, Sub};

/// Invalid mathematical extents or noncanonical element encodings.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    LengthMismatch,
    NoncanonicalScalar,
    WireLength,
    ZeroInverse,
}
impl Error {
    pub const fn code(self) -> &'static str {
        match self {
            Self::LengthMismatch => "length-mismatch",
            Self::NoncanonicalScalar => "noncanonical-scalar",
            Self::WireLength => "wire-length",
            Self::ZeroInverse => "zero-inverse",
        }
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;

pub trait Coefficient:
    Copy + PartialEq + Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Neg<Output = Self>
{
    type Packing: crate::vector::Packing<Self>;
    const DOT_SETUP_WORK: u64 = 1;
    fn dot_product(a: &[Self], b: &[Self]) -> Result<Self> {
        crate::vector::equal_len(a.len(), b.len())?;
        Ok(a.iter().zip(b).fold(Self::zero(), |s, (a, b)| s + *a * *b))
    }
    fn zero() -> Self;
    fn one() -> Self;
    fn inverse(self) -> Option<Self>;
}
impl Coefficient for crate::Bn254Scalar {
    type Packing = crate::vector::Scalar;

    fn zero() -> Self {
        Self::from(0)
    }
    fn one() -> Self {
        Self::from(1)
    }
    fn inverse(self) -> Option<Self> {
        Field::inverse(&self)
    }
}
impl Coefficient for Scalar {
    type Packing = crate::vector::Scalar;

    fn zero() -> Self {
        Self::from(0)
    }
    fn one() -> Self {
        Self::from(1)
    }
    fn inverse(self) -> Option<Self> {
        Field::inverse(&self)
    }
}
impl Coefficient for RistrettoScalar {
    type Packing = crate::vector::Scalar;

    fn zero() -> Self {
        Self::ZERO
    }
    fn one() -> Self {
        Self::ONE
    }
    fn inverse(self) -> Option<Self> {
        (self != Self::ZERO).then(|| self.invert())
    }
}
pub fn parse_ristretto_decimal(s: &str) -> Result<RistrettoScalar> {
    const MODULUS: &str = crate::RISTRETTO_SCALAR_MODULUS_DECIMAL;
    if s.is_empty()
        || !s.bytes().all(|b| b.is_ascii_digit())
        || (s.len() > 1 && s.starts_with('0'))
        || s.len() > MODULUS.len()
        || (s.len() == MODULUS.len() && s >= MODULUS)
    {
        return Err(Error::NoncanonicalScalar);
    }
    Ok(s.bytes().fold(RistrettoScalar::ZERO, |a, b| {
        a * RistrettoScalar::from(10u64) + RistrettoScalar::from(u64::from(b - b'0'))
    }))
}
impl Coefficient for KoalaBear {
    type Packing = crate::vector::Plonky3;
    const DOT_SETUP_WORK: u64 = 1 + crate::plonky3::PACKING_WIDTH as u64;
    fn dot_product(a: &[Self], b: &[Self]) -> Result<Self> {
        crate::plonky3::dot(a, b)
    }

    fn zero() -> Self {
        <Self as p3_field::PrimeCharacteristicRing>::ZERO
    }
    fn one() -> Self {
        <Self as p3_field::PrimeCharacteristicRing>::ONE
    }
    fn inverse(self) -> Option<Self> {
        p3_field::Field::try_inverse(&self)
    }
}
impl Coefficient for KoalaBearExt8 {
    type Packing = crate::vector::Plonky3;

    fn zero() -> Self {
        <Self as p3_field::PrimeCharacteristicRing>::ZERO
    }
    fn one() -> Self {
        <Self as p3_field::PrimeCharacteristicRing>::ONE
    }
    fn inverse(self) -> Option<Self> {
        p3_field::Field::try_inverse(&self)
    }
}
impl Coefficient for KoalaBearExt4 {
    type Packing = crate::vector::Plonky3;

    fn zero() -> Self {
        <Self as p3_field::PrimeCharacteristicRing>::ZERO
    }
    fn one() -> Self {
        <Self as p3_field::PrimeCharacteristicRing>::ONE
    }
    fn inverse(self) -> Option<Self> {
        p3_field::Field::try_inverse(&self)
    }
}
// Binary fields: addition is exclusive or and every element is its own
// negation. Inversion of zero is refused, as for every installed field.
impl Coefficient for Binary64 {
    type Packing = crate::vector::Plonky3;

    fn zero() -> Self {
        <Self as p3_field::PrimeCharacteristicRing>::ZERO
    }
    fn one() -> Self {
        <Self as p3_field::PrimeCharacteristicRing>::ONE
    }
    fn inverse(self) -> Option<Self> {
        p3_field::Field::try_inverse(&self)
    }
}
impl Coefficient for Binary64Ext3 {
    type Packing = crate::vector::Plonky3;

    fn zero() -> Self {
        <Self as p3_field::PrimeCharacteristicRing>::ZERO
    }
    fn one() -> Self {
        <Self as p3_field::PrimeCharacteristicRing>::ONE
    }
    fn inverse(self) -> Option<Self> {
        p3_field::Field::try_inverse(&self)
    }
}
