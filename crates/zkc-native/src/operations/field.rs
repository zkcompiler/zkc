//! Exact native field adapters shared by dense kernels and numerical consumers.
//! Values are matched by nominal field; vectors are borrowed immutable backings.
//! Arithmetic and canonical literals remain delegated to the existing providers.
use crate::{Binary64, Binary64Ext3, KoalaBear, KoalaBearExt4, KoalaBearExt8};
use crate::{Result, RistrettoScalar, Scalar, Value, refused};
use std::sync::Arc;
pub(crate) use zkc_kernels::fields::Coefficient;

pub(crate) trait Family: crate::matrix::IdentityCoefficient {
    fn dot(a: &[Self], b: &[Self]) -> Result<Self> {
        Self::dot_product(a, b).map_err(crate::field_error)
    }
    fn product(a: &[Self], b: &[Self], out: &mut [Self]) -> Result<()> {
        zkc_kernels::vector::mul::<Self>(a, b, out).map_err(crate::field_error)
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
    ($s:ty, $field:ident, $vector:ident, $matrix:ident, $poly:ident, $round:ident, $parse:expr $(, $extra:item)*) => {
        impl Family for $s {
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
                #[cfg(test)]
                LITERAL_DECODES.with(|count| count.set(count.get() + 1));
                ($parse)(s)
            }
        }
    };
}
family!(
    crate::Bn254Scalar,
    Bn254Field,
    Bn254Vector,
    Bn254Matrix,
    Bn254Polynomial,
    Bn254Round,
    |s| zkc_kernels::bn254::parse_decimal(s).map_err(crate::ark)
);
family!(Scalar, Field, Vector, Matrix, Polynomial, Round, |s| {
    zkc_kernels::parse_decimal(s).map_err(crate::ark)
});
family!(
    RistrettoScalar,
    RistrettoField,
    RistrettoVector,
    RistrettoMatrix,
    RistrettoPolynomial,
    RistrettoRound,
    |s| zkc_kernels::fields::parse_ristretto_decimal(s).map_err(crate::field_error)
);

family!(
    KoalaBear,
    KoalaBearField,
    KoalaBearVector,
    KoalaBearMatrix,
    KoalaBearPolynomial,
    KoalaBearRound,
    |s| zkc_kernels::plonky3::parse_decimal(s).map_err(crate::field_error)
);

family!(
    KoalaBearExt8,
    KoalaBearExt8Field,
    KoalaBearExt8Vector,
    KoalaBearExt8Matrix,
    KoalaBearExt8Polynomial,
    KoalaBearExt8Round,
    |s| zkc_kernels::plonky3::parse_extension_decimal(s).map_err(crate::field_error)
);

family!(
    KoalaBearExt4,
    KoalaBearExt4Field,
    KoalaBearExt4Vector,
    KoalaBearExt4Matrix,
    KoalaBearExt4Polynomial,
    KoalaBearExt4Round,
    |s| zkc_kernels::plonky3::parse_quartic_decimal(s).map_err(crate::field_error)
);

family!(
    Binary64,
    Binary64Field,
    Binary64Vector,
    Binary64Matrix,
    Binary64Polynomial,
    Binary64Round,
    |s| zkc_kernels::plonky3::binary::parse_literal(s).map_err(crate::field_error)
);

family!(
    Binary64Ext3,
    Binary64Ext3Field,
    Binary64Ext3Vector,
    Binary64Ext3Matrix,
    Binary64Ext3Polynomial,
    Binary64Ext3Round,
    |s| zkc_kernels::plonky3::binary::parse_ext3_literal(s).map_err(crate::field_error)
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

// Count actual decoder entries, including validation and ordinary execution.
// Thread-local storage keeps parallel tests independent without production cost.
#[cfg(test)]
thread_local! {
    pub(crate) static LITERAL_DECODES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(crate) fn literal<S: Family>(attributes: &[String]) -> Result<Value> {
    let [text] = attributes else {
        return Err(refused("kernel-attributes"));
    };
    Ok(S::field_value(S::decimal(text)?))
}

pub(crate) fn decode_literal(
    field: zkc_runtime::vm::Identity,
    attributes: &[String],
) -> Result<Value> {
    with_field!(field, |S| literal::<S>(attributes))
}

pub(crate) fn publish_literal(
    value: &Value,
    i: &zkc_runtime::vm::Invocation<'_>,
    policy: &crate::Policy,
) -> Result<Vec<Value>> {
    // These are inline scalars: every result retains its ordinary fresh charge.
    policy.output(512, i.max_output_bytes)?;
    Ok(vec![value.clone()])
}

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
