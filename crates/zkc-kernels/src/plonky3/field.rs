use super::{
    KoalaBear, KoalaBearExt4, KoalaBearExt8,
    binary::{Binary64, Binary64Ext3},
};
use crate::field::{Coefficient, Result};

impl Coefficient for KoalaBear {
    type Packing = super::packing::Native;
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
    type Packing = super::packing::Native;

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
    type Packing = super::packing::Native;

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
    type Packing = super::packing::Native;

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
    type Packing = super::packing::Native;

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
