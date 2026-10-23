//! Canonical scalars and shared coefficient arithmetic.
use super::{Error, ScalarElement};
use crate::field::Coefficient;
use halo2curves_axiom::ff::{Field, PrimeField};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

pub const MODULUS: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";

/// Prime-field value with private provider coordinates and canonical byte ingress.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Scalar(pub(super) ScalarElement);

impl Scalar {
    pub const ZERO: Self = Self(ScalarElement::ZERO);
    pub const ONE: Self = Self(ScalarElement::ONE);
    pub const BYTES: usize = 32;
    /// Adopt a typed field element. Fabricated raw Montgomery values are
    /// outside the field premises; untrusted bytes use `decode_scalar`.
    pub fn from_element(element: ScalarElement) -> Self {
        Self(element)
    }
    pub fn into_element(self) -> ScalarElement {
        self.0
    }
    pub fn to_bytes_le(self) -> [u8; Self::BYTES] {
        self.0.to_repr()
    }
    /// Euclidean inversion supplies no constant-time guarantee.
    pub fn inverse(self) -> Option<Self> {
        Option::<ScalarElement>::from(self.0.invert()).map(Self)
    }
    /// Public unsigned exponent, including `0^0 = 1`.
    pub fn pow(self, exponent: u64) -> Self {
        Self(self.0.pow_vartime([exponent]))
    }
}
impl From<u64> for Scalar {
    fn from(value: u64) -> Self {
        Self(ScalarElement::from(value))
    }
}
impl Default for Scalar {
    fn default() -> Self {
        Self::ZERO
    }
}
macro_rules! binary {
    ($trait:ident, $method:ident, $assign:ident, $assign_method:ident, $op:tt) => {
        impl $trait for Scalar {
            type Output = Self;
            fn $method(self, rhs: Self) -> Self {
                Self(self.0 $op rhs.0)
            }
        }
        impl $assign for Scalar {
            fn $assign_method(&mut self, rhs: Self) {
                *self = *self $op rhs;
            }
        }
    };
}
binary!(Add, add, AddAssign, add_assign, +);
binary!(Sub, sub, SubAssign, sub_assign, -);
binary!(Mul, mul, MulAssign, mul_assign, *);
impl Neg for Scalar {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}
impl Coefficient for Scalar {
    type Packing = crate::vector::Scalar;
    fn zero() -> Self {
        Self::ZERO
    }
    fn one() -> Self {
        Self::ONE
    }
    fn inverse(self) -> Option<Self> {
        self.inverse()
    }
}
// Owned bulk buffers use exactly Fr's ABI; the shared destination kernels need
// no wrapper vector or conversion for this representation.
impl Coefficient for ScalarElement {
    type Packing = crate::vector::Scalar;
    fn zero() -> Self {
        Self::ZERO
    }
    fn one() -> Self {
        Self::ONE
    }
    fn inverse(self) -> Option<Self> {
        self.invert().into()
    }
}

pub fn encode_scalar(scalar: &Scalar) -> [u8; Scalar::BYTES] {
    scalar.to_bytes_le()
}

/// Exact unflagged 32-byte little-endian integer, strictly below the order.
pub fn decode_scalar(bytes: &[u8]) -> Result<Scalar, Error> {
    let repr = bytes.try_into().map_err(|_| Error::InvalidEncoding)?;
    Option::<ScalarElement>::from(ScalarElement::from_repr(repr))
        .map(Scalar)
        .ok_or(Error::InvalidEncoding)
}

/// Strict unsigned decimal grammar without reduction, signs or leading zeros.
pub fn parse_decimal(text: &str) -> crate::field::Result<Scalar> {
    if text.is_empty()
        || text.len() > MODULUS.len()
        || !text.bytes().all(|b| b.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
        || (text.len() == MODULUS.len() && text >= MODULUS)
    {
        return Err(crate::field::Error::NoncanonicalScalar);
    }
    Ok(text.bytes().fold(Scalar::ZERO, |value, digit| {
        value * Scalar::from(10) + Scalar::from(u64::from(digit - b'0'))
    }))
}
