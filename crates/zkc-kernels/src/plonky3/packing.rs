//! Native element packing supplied by Plonky3.
use crate::{field::Coefficient, vector::Packing};
use p3_field::{Field, PackedValue};

/// Use the field's declared packing for native element slices. Explicit base-
/// coordinate extension packing has a different layout and conversion cost;
/// its availability alone does not make it suitable for these destinations.
pub struct Native;
impl<S: Coefficient + Field> Packing<S> for Native {
    type Value = <S as Field>::Packing;
    const WIDTH: usize = <<S as Field>::Packing as PackedValue>::WIDTH;
    #[inline]
    fn broadcast(value: S) -> Self::Value {
        value.into()
    }
    #[inline]
    fn load(values: &[S]) -> Self::Value {
        *Self::Value::from_slice(values)
    }
    #[inline]
    fn store(value: Self::Value, values: &mut [S]) {
        values.copy_from_slice(value.as_slice());
    }
}
