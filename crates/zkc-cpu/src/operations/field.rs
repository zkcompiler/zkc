//! Exact native field adapters shared by dense kernels and numerical consumers.
//! Values are matched by nominal field; vectors are borrowed immutable backings.
//! Arithmetic and canonical literals remain delegated to the existing providers.
use crate::{Binary64, Binary64Ext3};
use crate::{Result, RistrettoScalar, Scalar, Value, refused};
pub(crate) use zkc_kernels::field::Coefficient;

/// Scalar/vector adaptation requires only the provider's coefficient algebra.
pub(crate) trait Family: Coefficient {
    /// Owned provider bulk buffers freeze without another element allocation.
    const RESIDENT_STORAGE: bool = false;
    fn dot(a: &[Self], b: &[Self]) -> Result<Self> {
        Self::dot_product(a, b).map_err(crate::field_error)
    }
    fn field(v: &Value) -> Result<Self>;
    fn vector(v: &Value) -> Result<&[Self]>;
    fn field_value(v: Self) -> Value;
    fn vector_value(v: Vec<Self>) -> Value;
    fn decimal(s: &str) -> Result<Self>;
}

/// Structured consumers additionally require canonical matrix coefficients and
/// actual matrix, polynomial and round payloads in the Native value inventory.
pub(crate) trait StructuredFamily: Family + crate::matrix::IdentityCoefficient {
    fn matrix(v: &Value) -> Result<&crate::matrix::SparseCoo<Self>>;
    fn polynomial(v: &Value) -> Result<&[Self]>;
    fn round(v: &Value) -> Result<&[Self]>;
    fn polynomial_value(v: crate::Buffer<Self>) -> Result<Value>;
}
macro_rules! family {
    ($s:ty, $field:ident, $vector:ident, $matrix:ident, $poly:ident, $round:ident, $parse:expr $(, $extra:item)*) => {
        impl Family for $s {
            $($extra)*
            fn field(v: &Value) -> Result<Self> {
                if let Value::$field(v) = v {
                    Ok(*v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn vector(v: &Value) -> Result<&[Self]> {
                if let Value::$vector(v) = v {
                    Ok(v)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn field_value(v: Self) -> Value {
                Value::$field(v)
            }
            fn vector_value(v: Vec<Self>) -> Value {
                Value::$vector(v.into())
            }
            fn decimal(s: &str) -> Result<Self> {
                #[cfg(test)]
                LITERAL_DECODES.with(|count| count.set(count.get() + 1));
                ($parse)(s)
            }
        }
        impl StructuredFamily for $s {
            fn matrix(v: &Value) -> Result<&crate::matrix::SparseCoo<Self>> {
                if let Value::$matrix(v) = v {Ok(v)} else {Err(refused("kernel-operands"))}
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
                    Ok(v.as_slice())
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn polynomial_value(v: crate::Buffer<Self>) -> Result<Value> {
                Ok(Value::$poly(v))
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
    |s| zkc_kernels::arkworks::bn254::parse_decimal(s).map_err(crate::ark)
);
family!(Scalar, Field, Vector, Matrix, Polynomial, Round, |s| {
    zkc_kernels::arkworks::bls12_381::parse_decimal(s).map_err(crate::ark)
});
family!(
    RistrettoScalar,
    RistrettoField,
    RistrettoVector,
    RistrettoMatrix,
    RistrettoPolynomial,
    RistrettoRound,
    |s| zkc_kernels::dalek::ristretto255::parse_decimal(s).map_err(crate::field_error)
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
            identity if crate::fields::contains(identity) => {
                $crate::fields::with_residue!(identity, |$coefficient| $body)
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
    policy.output(crate::VALUE_SLOT_BYTES, i.max_output_bytes)?;
    Ok(vec![value.clone()])
}
