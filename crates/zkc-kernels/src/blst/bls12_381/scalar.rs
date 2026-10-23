//! Canonical scalar algebra and adapters to the existing coefficient kernels.
use crate::field::Coefficient;
use group::ff::Field;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// Scalar with private Montgomery coordinates and checked byte ingress.
/// Trusted typed values can transfer directly; arithmetic stays in this representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Scalar(pub(super) blstrs::Scalar);

impl From<u64> for Scalar {
    fn from(value: u64) -> Self {
        Self(blstrs::Scalar::from(value))
    }
}

impl Scalar {
    pub const ZERO: Self = Self(blstrs::Scalar::ZERO);
    pub const ONE: Self = Self(blstrs::Scalar::ONE);
    pub const BYTES: usize = 32;

    /// Adopt a trusted upstream field value in O(1), without encoding or
    /// validation. Fabricated raw Montgomery coordinates are outside the field
    /// premises; untrusted input must enter through `decode_scalar` instead.
    pub fn from_element(element: super::ScalarElement) -> Self {
        Self(element)
    }

    /// Move the mathematical element into a trusted family adapter.
    pub fn into_element(self) -> super::ScalarElement {
        self.0
    }

    /// Exact canonical little-endian encoding, without Montgomery coordinates.
    pub fn to_bytes_le(self) -> [u8; Self::BYTES] {
        self.0.to_bytes_le()
    }

    /// Multiplicative inverse, with `None` exactly at zero. The pinned provider
    /// uses Euclidean inversion; this method grants no constant-time guarantee.
    pub fn inverse(self) -> Option<Self> {
        self.0.inverse().map(Self)
    }

    /// Exponentiation by an unsigned integer, including `0^0 = 1`.
    /// The exponent is public: this uses the provider's variable-time powering.
    pub fn pow(self, exponent: u64) -> Self {
        Self(self.0.pow_vartime([exponent]))
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

// Bulk storage has the exact upstream element ABI. Both adapters use the same
// arithmetic; this implementation lets bulk destinations use vector::Plan
// without constructing a temporary vector of zkc scalar wrappers.
impl Coefficient for blstrs::Scalar {
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

/// Parse an unsigned canonical decimal integer in `[0, r)`, never reducing.
/// Reject signs, whitespace, leading zeros (except `"0"`) and the modulus.
pub fn parse_decimal(text: &str) -> crate::field::Result<Scalar> {
    const MODULUS: &str =
        "52435875175126190479447740508185965837690552500527637822603658699938581184513";
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
