//! One native typed registration for every Plonky3 residue field.
use crate::{Result, Value, refused};
use p3_field::{BasedVectorSpace, PrimeField64};
use zkc_kernels::plonky3::residue::{PrimeWord, Residue};
use zkc_runtime::vm::{Identity, LogicalType, PhysicalType, Representation, Type};

macro_rules! inventory {
    ([$($callback:tt)+], $context:tt) => {
        $($callback)+! { $context;
            (crate::KoalaBear, KoalaBear, KoalaBear, KoalaBearField, KoalaBearVector, KoalaBearMatrix, KoalaBearPolynomial, KoalaBearRound, KoalaBearSparseCoo, 19, 20, 25),
            (crate::KoalaBearExt4, KoalaBearExt4, KoalaBear, KoalaBearExt4Field, KoalaBearExt4Vector, KoalaBearExt4Matrix, KoalaBearExt4Polynomial, KoalaBearExt4Round, KoalaBearExt4SparseCoo, 21, 22, 28),
            (crate::KoalaBearExt8, KoalaBearExt8, KoalaBear, KoalaBearExt8Field, KoalaBearExt8Vector, KoalaBearExt8Matrix, KoalaBearExt8Polynomial, KoalaBearExt8Round, KoalaBearExt8SparseCoo, 26, 27, 30),
            (crate::BabyBear, BabyBear, BabyBear, BabyBearField, BabyBearVector, BabyBearMatrix, BabyBearPolynomial, BabyBearRound, BabyBearSparseCoo, 90, 91, 92),
            (crate::BabyBearExt4, BabyBearExt4, BabyBear, BabyBearExt4Field, BabyBearExt4Vector, BabyBearExt4Matrix, BabyBearExt4Polynomial, BabyBearExt4Round, BabyBearExt4SparseCoo, 93, 94, 95),
            (crate::Goldilocks, Goldilocks, Goldilocks, GoldilocksField, GoldilocksVector, GoldilocksMatrix, GoldilocksPolynomial, GoldilocksRound, GoldilocksSparseCoo, 96, 97, 98),
            (crate::GoldilocksExt2, GoldilocksExt2, Goldilocks, GoldilocksExt2Field, GoldilocksExt2Vector, GoldilocksExt2Matrix, GoldilocksExt2Polynomial, GoldilocksExt2Round, GoldilocksExt2SparseCoo, 99, 100, 101),
        }
    };
}
pub(crate) use inventory;

pub(crate) trait Registered: Residue + crate::operations::field::StructuredFamily {
    const TAGS: [u8; 3];
    fn representation(kind: Type) -> Option<Representation>;
}
macro_rules! register {
    ((); $(($s:ty, $id:ident, $base:ident, $f:ident, $v:ident, $m:ident, $p:ident, $r:ident, $sparse:ident, $ft:literal, $vt:literal, $mt:literal),)*) => { $(
        impl crate::operations::field::Family for $s {
            fn field(v: &Value) -> Result<Self> { if let Value::$f(x) = v { Ok(*x) } else { Err(refused("kernel-operands")) } }
            fn vector(v: &Value) -> Result<&[Self]> { if let Value::$v(x) = v { Ok(x) } else { Err(refused("kernel-operands")) } }
            fn field_value(v: Self) -> Value { Value::$f(v) }
            fn vector_value(v: Vec<Self>) -> Value { Value::$v(v.into()) }
            fn decimal(s: &str) -> Result<Self> {
                #[cfg(test)]
                crate::operations::field::LITERAL_DECODES.with(|n| n.set(n.get() + 1));
                zkc_kernels::plonky3::residue::parse_decimal(s).map_err(crate::field_error)
            }
        }
        impl crate::operations::field::StructuredFamily for $s {
            fn matrix(v: &Value) -> Result<&crate::matrix::SparseCoo<Self>> { if let Value::$m(x) = v { Ok(x) } else { Err(refused("kernel-operands")) } }
            fn polynomial(v: &Value) -> Result<&[Self]> { if let Value::$p(x) = v { Ok(x) } else { Err(refused("kernel-operands")) } }
            fn round(v: &Value) -> Result<&[Self]> { if let Value::$r(x) = v { Ok(x.as_slice()) } else { Err(refused("kernel-operands")) } }
            fn polynomial_value(v: crate::Buffer<Self>) -> Result<Value> { Ok(Value::$p(v)) }
        }
        impl crate::matrix::Wire for $s {
            const WIDTH: usize = <$s as Residue>::Base::WORD_BYTES * <$s as BasedVectorSpace<crate::$base>>::DIMENSION;
            const TAG: u8 = $mt;
            fn decode(bytes: &[u8]) -> Result<Self> { zkc_kernels::plonky3::residue::decode(bytes).map_err(crate::field_error) }
            fn encode(self, out: &mut Vec<u8>) -> Result<()> { zkc_kernels::plonky3::residue::encode_into(&self, out); Ok(()) }
            fn value(m: crate::matrix::SparseCoo<Self>) -> Value { Value::$m(m) }
        }
        impl Registered for $s {
            const TAGS: [u8; 3] = [$ft, $vt, $mt];
            fn representation(kind: Type) -> Option<Representation> {
                Some(match kind {
                    Type::Field => Representation::$id,
                    Type::Vector => Representation::$v,
                    Type::Polynomial => Representation::$p,
                    Type::Round => Representation::$r,
                    Type::Matrix => Representation::$sparse,
                    _ => return None,
                })
            }
        }
        impl From<[$s; 3]> for Value {
            fn from(value: [$s; 3]) -> Self { Value::$r(value.into()) }
        }
        impl From<crate::matrix::SparseCoo<$s>> for Value {
            fn from(value: crate::matrix::SparseCoo<$s>) -> Self { Value::$m(value) }
        }
        impl crate::matrix::IdentityCoefficient for $s {
            const IDENTITY: Identity = Identity::$id;
            fn canonical(self) -> String { canonical(self) }
        }
        impl crate::ring::sealed::Sealed for $s {}
        impl crate::ring::Carrier for $s { const IDENTITY: Identity = Identity::$id; }
    )*
        pub(crate) fn count(value: &Value) -> Option<usize> {
            match value {
                $(Value::$f(_) => Some(1),
                  Value::$v(v) | Value::$p(v) => Some(v.len()),
                  Value::$m(v) => Some(v.entries().len()),
                  Value::$r(_) => Some(3),)*
                _ => None,
            }
        }

        /// Collection checks only; callers retain common byte and capability
        /// checks. In particular, element policy precedes normalization.
        pub(crate) fn validate_collection(value: &Value, policy: &crate::Policy) -> Option<Result<()>> {
            Some(match value {
                $(Value::$v(v) => policy.vector_width(v.len(), std::mem::size_of::<$s>()),
                  Value::$p(v) => policy.vector_width(v.len(), std::mem::size_of::<$s>()).and_then(|()| {
                      if zkc_kernels::polynomial::normalized(v) {
                          Ok(())
                      } else {
                          Err(refused("polynomial-normalization"))
                      }
                  }),
                  Value::$m(m) => m.policy(policy),)*
                _ => return None,
            })
        }

        /// Dense buffers retain spare capacity; COO storage owns its entry
        /// charge. Inline scalars and rounds keep their conservative charge.
        pub(crate) fn collection_retained_bytes(value: &Value) -> Option<Result<usize>> {
            Some(match value {
                $(Value::$v(v) | Value::$p(v) => crate::value::size(v.storage_capacity(), std::mem::size_of::<$s>()),
                  Value::$m(m) => m.retained_bytes(),)*
                _ => return None,
            })
        }

        /// Preserve the immutable owner across vector/polynomial aliases and
        /// matrix clones, including owners of empty dense buffers.
        pub(crate) fn collection_backing(value: &Value, bytes: usize) -> Option<zkc_runtime::vm::Backing> {
            Some(match value {
                $(Value::$v(v) | Value::$p(v) => v.backing(bytes),
                  Value::$m(m) => m.backing().ok()?,)*
                _ => return None,
            })
        }
    };
}
inventory!([register], ());

fn canonical<S: Residue>(value: S) -> String {
    use ark_ff::{BigInt, BigInteger};
    let radix = BigInt::<4>::from(S::Base::ORDER_U64);
    let mut result = BigInt::<4>::default();
    for c in value.as_basis_coefficients_slice().iter().rev() {
        result = result.mul_low(&radix);
        result.add_with_carry(&BigInt::from(c.as_canonical_u64()));
    }
    result.to_string()
}
macro_rules! dispatch {
    (($identity:expr, $s:ident, $body:expr); $(($t:ty, $id:ident, $base:ident, $f:ident, $v:ident, $m:ident, $p:ident, $r:ident, $sparse:ident, $ft:literal, $vt:literal, $mt:literal),)*) => {
        match $identity { $(zkc_runtime::vm::Identity::$id => { type $s = $t; $body })* _ => Err($crate::refused("kernel-operands")) }
    };
}
pub(crate) use dispatch;
macro_rules! with_residue {
    ($identity:expr, |$s:ident| $body:expr) => {
        $crate::fields::inventory!([$crate::fields::dispatch], ($identity, $s, $body))
    };
}
pub(crate) use with_residue;

pub(crate) fn scalar_bytes<S: Residue>(value: &S) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(zkc_kernels::plonky3::residue::width::<S>());
    zkc_kernels::plonky3::residue::encode_into(value, &mut bytes);
    bytes
}
pub(crate) fn contains(identity: Identity) -> bool {
    element_width(identity).is_ok()
}
pub(crate) fn montgomery(identity: Identity) -> bool {
    crate::fields::with_residue_or!(identity, false, |S| {
        <<S as Residue>::Base as PrimeWord>::MONTGOMERY_INVERSE.is_some()
    })
}
pub(crate) fn element_width(identity: Identity) -> Result<usize> {
    with_residue!(
        identity,
        |S| Ok(zkc_kernels::plonky3::residue::width::<S>())
    )
}
pub(crate) fn matrix_entry_width(identity: Identity) -> Result<usize> {
    with_residue!(identity, |S| Ok(std::mem::size_of::<(u32, u32, S)>()))
}

pub(crate) fn tags(identity: Identity) -> Result<[u8; 3]> {
    with_residue!(identity, |S| Ok(S::TAGS))
}
pub(crate) fn decode_scalar(identity: Identity, bytes: &[u8]) -> Result<Value> {
    use crate::operations::field::Family;
    with_residue!(identity, |S| Ok(S::field_value(
        zkc_kernels::plonky3::residue::decode::<S>(bytes).map_err(crate::field_error)?
    )))
}
pub(crate) fn encode_scalar(value: &Value, out: &mut Vec<u8>) -> Result<()> {
    use crate::operations::field::Family;
    use zkc_runtime::vm::Value as _;
    with_residue!(value.physical_type().logical().identity(), |S| {
        zkc_kernels::plonky3::residue::encode_into(&S::field(value)?, out);
        Ok(())
    })
}
pub(crate) fn encode_vector(value: &Value, policy: &crate::Policy) -> Result<Vec<u8>> {
    use crate::operations::field::Family;
    use zkc_runtime::vm::Value as _;
    with_residue!(value.physical_type().logical().identity(), |S| {
        let values = S::vector(value)?;
        let width = zkc_kernels::plonky3::residue::width::<S>();
        policy.vector_width(values.len(), std::mem::size_of::<S>())?;
        let length = values
            .len()
            .checked_mul(width)
            .and_then(|n| n.checked_add(10))
            .ok_or_else(|| crate::exhausted("wire-bytes"))?;
        policy.wire(length)?;
        let mut out = crate::operations::arithmetic::reserve(length)?;
        out.extend_from_slice(b"ZKCV\x00");
        out.push(S::TAGS[1]);
        out.extend_from_slice(
            &u32::try_from(values.len())
                .map_err(|_| crate::exhausted("element-limit"))?
                .to_le_bytes(),
        );
        for value in values {
            zkc_kernels::plonky3::residue::encode_into(value, &mut out);
        }
        Ok(out)
    })
}

macro_rules! dispatch_or {
    (($identity:expr, $fallback:expr, $s:ident, $body:expr); $(($t:ty, $id:ident, $base:ident, $f:ident, $v:ident, $m:ident, $p:ident, $r:ident, $sparse:ident, $ft:literal, $vt:literal, $mt:literal),)*) => {
        match $identity { $(zkc_runtime::vm::Identity::$id => { type $s = $t; $body })* _ => $fallback }
    };
}
pub(crate) use dispatch_or;
macro_rules! with_residue_or {
    ($identity:expr, $fallback:expr, |$s:ident| $body:expr) => {
        $crate::fields::inventory!(
            [$crate::fields::dispatch_or],
            ($identity, $fallback, $s, $body)
        )
    };
}
pub(crate) use with_residue_or;

/// Native's installed storage facts come from the same typed registration as
/// its value adapters. Runtime admission keeps its independent catalogue.
pub(crate) fn physical(identity: Identity, kind: Type) -> Option<PhysicalType> {
    with_residue_or!(identity, None, |S| {
        let representation = S::representation(kind)?;
        PhysicalType::new(LogicalType::new(kind, identity).ok()?, representation).ok()
    })
}
