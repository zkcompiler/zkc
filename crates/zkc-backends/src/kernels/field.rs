//! Exact native field adapters shared by dense kernels and numerical consumers.
//! Values are matched by nominal field; vectors are borrowed immutable backings.
//! Arithmetic and canonical literals remain delegated to the existing providers.
use super::arithmetic::equal_len;
use crate::{Binary64, Binary64Ext3, KoalaBear, KoalaBearExt4, KoalaBearExt8};
use crate::{Result, RistrettoScalar, Scalar, Value, refused};
use ark_ff::Field;
use std::{
    ops::{Add, Mul, Neg, Sub},
    sync::Arc,
};

pub(crate) trait Coefficient:
    Copy + PartialEq + Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Neg<Output = Self>
{
    fn zero() -> Self;
    fn one() -> Self;
    fn inverse(self) -> Option<Self>;
}
impl Coefficient for crate::Bn254Scalar {
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
        return Err(refused("noncanonical-scalar"));
    }
    Ok(s.bytes().fold(RistrettoScalar::ZERO, |a, b| {
        a * RistrettoScalar::from(10u64) + RistrettoScalar::from(u64::from(b - b'0'))
    }))
}
impl Coefficient for KoalaBear {
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
pub(crate) trait Family: crate::matrix::IdentityCoefficient {
    type Packing: super::vector::Packing<Self>;
    /// Packed dot products also reduce their accumulator lanes, even at length zero.
    const DOT_SETUP_WORK: u64 = 1;
    fn dot(a: &[Self], b: &[Self]) -> Result<Self> {
        equal_len(a.len(), b.len())?;
        Ok(a.iter().zip(b).fold(Self::zero(), |s, (a, b)| s + *a * *b))
    }
    fn product(a: &[Self], b: &[Self], out: &mut [Self]) -> Result<()> {
        equal_len(a.len(), b.len())?;
        equal_len(a.len(), out.len())?;
        super::vector::mul::<Self>(a, b, out);
        Ok(())
    }
    fn field(v: &Value) -> Result<Self>;
    fn matrix(v: &Value) -> Result<&crate::matrix::SparseCoo<Self>>;
    fn vector(v: &Value) -> Result<&Arc<[Self]>>;
    fn polynomial(v: &Value) -> Result<&[Self]>;
    fn round(v: &Value) -> Result<&[Self]>;
    fn field_value(v: Self) -> Value;
    fn vector_value(v: Arc<[Self]>) -> Value;
    fn polynomial_value(v: Arc<[Self]>) -> Value;
    fn decimal(s: &str) -> Result<Self>;
}
macro_rules! family {
    ($s:ty, $packing:ty, $field:ident, $vector:ident, $matrix:ident, $poly:ident, $round:ident, $parse:expr $(, $extra:item)*) => {
        impl Family for $s {
            type Packing = $packing;
            $($extra)*
            fn matrix(v: &Value) -> Result<&crate::matrix::SparseCoo<Self>> {
                if let Value::$matrix(v) = v {Ok(v)} else {Err(refused("kernel-operands"))}
            }
            fn field(v: &Value) -> Result<Self> {
                if let Value::$field(v) = v {
                    Ok(*v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn vector(v: &Value) -> Result<&Arc<[Self]>> {
                if let Value::$vector(v) = v {
                    Ok(v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn polynomial(v: &Value) -> Result<&[Self]> {
                if let Value::$poly(v) = v {
                    Ok(v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn round(v: &Value) -> Result<&[Self]> {
                if let Value::$round(v) = v {
                    Ok(v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn field_value(v: Self) -> Value {
                Value::$field(v)
            }
            fn vector_value(v: Arc<[Self]>) -> Value {
                Value::$vector(v)
            }
            fn polynomial_value(v: Arc<[Self]>) -> Value {
                Value::$poly(v)
            }
            fn decimal(s: &str) -> Result<Self> {
                ($parse)(s)
            }
        }
    };
}
family!(
    crate::Bn254Scalar,
    super::vector::Scalar,
    Bn254Field,
    Bn254Vector,
    Bn254Matrix,
    Bn254Polynomial,
    Bn254Round,
    |s| crate::parse_bn254_decimal(s).map_err(crate::ark)
);
family!(
    Scalar,
    super::vector::Scalar,
    Field,
    Vector,
    Matrix,
    Polynomial,
    Round,
    |s| { zkc_arkworks::parse_decimal(s).map_err(crate::ark) }
);
family!(
    RistrettoScalar,
    super::vector::Scalar,
    RistrettoField,
    RistrettoVector,
    RistrettoMatrix,
    RistrettoPolynomial,
    RistrettoRound,
    parse_ristretto_decimal
);

family!(
    KoalaBear,
    super::vector::Extension<KoalaBear>,
    KoalaBearField,
    KoalaBearVector,
    KoalaBearMatrix,
    KoalaBearPolynomial,
    KoalaBearRound,
    crate::plonky3::parse_decimal,
    const DOT_SETUP_WORK: u64 = 1 + crate::plonky3::PACKING_WIDTH as u64;,
    fn dot(a: &[Self], b: &[Self]) -> Result<Self> {
        crate::plonky3::dot(a, b)
    }
);

family!(
    KoalaBearExt8,
    super::vector::Extension<KoalaBear>,
    KoalaBearExt8Field,
    KoalaBearExt8Vector,
    KoalaBearExt8Matrix,
    KoalaBearExt8Polynomial,
    KoalaBearExt8Round,
    crate::plonky3::parse_extension_decimal
);

family!(
    KoalaBearExt4,
    super::vector::Extension<KoalaBear>,
    KoalaBearExt4Field,
    KoalaBearExt4Vector,
    KoalaBearExt4Matrix,
    KoalaBearExt4Polynomial,
    KoalaBearExt4Round,
    crate::plonky3::parse_quartic_decimal
);

family!(
    Binary64,
    super::vector::Extension<Binary64>,
    Binary64Field,
    Binary64Vector,
    Binary64Matrix,
    Binary64Polynomial,
    Binary64Round,
    crate::plonky3::binary::parse_literal
);

family!(
    Binary64Ext3,
    super::vector::Extension<Binary64>,
    Binary64Ext3Field,
    Binary64Ext3Vector,
    Binary64Ext3Matrix,
    Binary64Ext3Polynomial,
    Binary64Ext3Round,
    crate::plonky3::binary::parse_ext3_literal
);

/// Dispatch once on the exact binding field, then execute over typed operands.
macro_rules! with_field {
    ($identity:expr, |$coefficient:ident| $body:expr) => {
        match $identity {
            zkc_runtime::vm::Identity::Bn254Fr => {
                type $coefficient = $crate::Bn254Scalar;
                $body
            }
            zkc_runtime::vm::Identity::Bls12381Fr => {
                type $coefficient = $crate::Scalar;
                $body
            }
            zkc_runtime::vm::Identity::Ristretto255Scalar => {
                type $coefficient = $crate::RistrettoScalar;
                $body
            }
            zkc_runtime::vm::Identity::KoalaBear => {
                type $coefficient = $crate::KoalaBear;
                $body
            }
            zkc_runtime::vm::Identity::KoalaBearExt4 => {
                type $coefficient = $crate::KoalaBearExt4;
                $body
            }
            zkc_runtime::vm::Identity::KoalaBearExt8 => {
                type $coefficient = $crate::KoalaBearExt8;
                $body
            }
            zkc_runtime::vm::Identity::Binary64 => {
                type $coefficient = $crate::Binary64;
                $body
            }
            zkc_runtime::vm::Identity::Binary64Ext3 => {
                type $coefficient = $crate::Binary64Ext3;
                $body
            }
            _ => Err($crate::refused("kernel-operands")),
        }
    };
}
pub(crate) use with_field;

#[cfg(test)]
mod tests {
    use super::*;

    fn destination_shapes<S: Family>() -> Result<()> {
        let input = [S::one(); 3];
        for (left, right, len) in [(&input[..2], &input[..], 3), (&input[..], &input[..], 2)] {
            let mut output = vec![S::zero(); len];
            assert_eq!(
                S::product(left, right, &mut output).unwrap_err().code,
                "refused:length-mismatch"
            );
            assert!(output.iter().all(|value| *value == S::zero()));
        }
        let mut output = [S::zero(); 3];
        S::product(&input, &input, &mut output)?;
        assert!(output.iter().all(|value| *value == S::one()));
        Ok(())
    }

    #[test]
    fn shared_product_adapter_checks_every_shape_before_writing() {
        for domain in crate::domains::INSTALLED {
            with_field!(domain.field, |S| destination_shapes::<S>()).unwrap();
        }
    }
}
