use crate::field::Coefficient;
use ark_ff::Field;

impl Coefficient for super::Scalar {
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
