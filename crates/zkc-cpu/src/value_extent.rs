//! Pure collection metadata access for common-input admission.
use crate::{Result, Value, refused};
use zkc_runtime::vm::Value as _;

pub(super) fn inspect(value: &Value, axis: usize) -> Result<u64> {
    use crate::operations::field::{Family, StructuredFamily, with_field};
    let ty = value.physical_type();
    let length = if ty.kind() == zkc_runtime::vm::Type::Matrix {
        with_field!(ty.logical().identity(), |S| {
            let matrix = S::matrix(value)?;
            match axis {
                0 => Ok(matrix.rows()),
                1 => Ok(matrix.columns()),
                _ => Err(refused("input-binding-extent-axis")),
            }
        })?
    } else {
        if axis != 0 {
            return Err(refused("input-binding-extent-axis"));
        }
        macro_rules! lengths {
            ($($variant:ident),+ $(,)?) => {
                match value {
                    $(Value::$variant(v) => Some(v.len()),)+
                    _ => None,
                }
            };
        }
        if let Some(length) = lengths!(
            Bytes,
            Indices,
            Sequence,
            FieldArray,
            FixedVector,
            BlstVector,
            HaloVector,
            Groups,
            RistrettoGroups,
            EdwardsGroups,
            Bn254G1Vector,
            Bn254G2Vector,
            Bls12381G2Vector,
            BlstG1Vector,
            BlstG2Vector,
            HaloG1Vector,
            HaloG2Vector,
        ) {
            length
        } else if ty.kind() == zkc_runtime::vm::Type::Vector {
            with_field!(ty.logical().identity(), |S| Ok(S::vector(value)?.len()))?
        } else {
            return Err(refused("input-binding-extent-unsupported"));
        }
    };
    u64::try_from(length).map_err(|_| refused("input-binding-extent-limit"))
}
