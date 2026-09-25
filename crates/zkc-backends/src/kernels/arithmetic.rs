//! Shared dense scalar/vector/coefficient arithmetic. Mathematical meanings do
//! not depend on physical layout. Callers preflight sizes before allocating.
use crate::{KoalaBear, KoalaBearExt8};
use crate::{Policy, Result, RistrettoScalar, Scalar, Value, exhausted, refused, value::size};
use ark_ff::Field;
use std::{
    ops::{Add, Mul, Neg, Sub},
    sync::Arc,
};
use zkc_runtime::interactive::{Identity, Invocation};

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
/// Montgomery batch inversion. The caller supplies the checked allocation;
/// zero inputs are refused before any output is materialized. Scalar inversion
/// remains delegated to the selected field library.
fn invert_nonzero<S: Coefficient>(values: &[S], out: &mut Vec<S>) -> Result<()> {
    if values.iter().any(|x| *x == S::zero()) {
        return Err(refused("zero-inverse"));
    }
    if values.is_empty() {
        return Ok(());
    }
    let mut product = S::one();
    for x in values {
        out.push(product);
        product = product * *x;
    }
    let mut inverse = product.inverse().ok_or_else(|| refused("zero-inverse"))?;
    for (x, prefix) in values.iter().zip(out.iter_mut()).rev() {
        *prefix = *prefix * inverse;
        inverse = inverse * *x;
    }
    Ok(())
}

pub(crate) fn evaluate<S: Coefficient>(coefficients: &[S], x: S) -> S {
    coefficients.iter().rev().fold(S::zero(), |a, c| a * x + *c)
}
pub(crate) fn boundary<S: Coefficient>(coefficients: &[S]) -> S {
    coefficients.first().copied().unwrap_or_else(S::zero)
        + coefficients.iter().fold(S::zero(), |a, c| a + *c)
}
pub(crate) fn normalized<S: Coefficient>(coefficients: &[S]) -> bool {
    coefficients.last().is_none_or(|c| *c != S::zero())
}
pub(crate) fn reserve<T>(n: usize) -> Result<Vec<T>> {
    let mut v = Vec::new();
    v.try_reserve_exact(n)
        .map_err(|_| exhausted("allocation"))?;
    Ok(v)
}
pub(crate) fn equal_len(a: usize, b: usize) -> Result<()> {
    if a != b {
        Err(refused("length-mismatch"))
    } else {
        Ok(())
    }
}
pub(crate) fn split_len(n: usize) -> Result<usize> {
    if n == 0 || !n.is_multiple_of(2) {
        Err(refused("split-length"))
    } else {
        Ok(n / 2)
    }
}
pub(crate) fn natural(attrs: &[String], i: usize) -> Result<usize> {
    attrs
        .get(i)
        .and_then(|a| zkc_runtime::logical::natural_index(a).ok())
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| refused("kernel-attributes"))
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
trait Family: crate::matrix::CanonicalCoefficient {
    fn dot(a: &[Self], b: &[Self]) -> Result<Self> {
        equal_len(a.len(), b.len())?;
        Ok(a.iter().zip(b).fold(Self::zero(), |s, (a, b)| s + *a * *b))
    }
    fn product(a: &[Self], b: &[Self], out: &mut Vec<Self>) -> Result<()> {
        equal_len(a.len(), b.len())?;
        out.extend(a.iter().zip(b).map(|(a, b)| *a * *b));
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
    |s| crate::parse_bn254_decimal(s).map_err(crate::ark)
);
family!(Scalar, Field, Vector, Matrix, Polynomial, Round, |s| {
    zkc_arkworks::parse_decimal(s).map_err(crate::ark)
});
family!(
    RistrettoScalar,
    RistrettoField,
    RistrettoVector,
    RistrettoMatrix,
    RistrettoPolynomial,
    RistrettoRound,
    parse_ristretto_decimal
);

family!(
    KoalaBear,
    KoalaBearField,
    KoalaBearVector,
    KoalaBearMatrix,
    KoalaBearPolynomial,
    KoalaBearRound,
    crate::plonky3::parse_decimal,
    fn dot(a: &[Self], b: &[Self]) -> Result<Self> {
        crate::plonky3::dot(a, b)
    },
    fn product(a: &[Self], b: &[Self], out: &mut Vec<Self>) -> Result<()> {
        out.resize(a.len(), <Self as Coefficient>::zero());
        crate::plonky3::mul_into(a, b, out)
    }
);

family!(
    KoalaBearExt8,
    KoalaBearExt8Field,
    KoalaBearExt8Vector,
    KoalaBearExt8Matrix,
    KoalaBearExt8Polynomial,
    KoalaBearExt8Round,
    crate::plonky3::parse_extension_decimal
);

pub(crate) fn apply(
    name: &str,
    field: Option<Identity>,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Option<Result<Vec<Value>>> {
    if !(name.starts_with("field.")
        || name.starts_with("matrix.")
        || name.starts_with("vector.")
        || matches!(
            name,
            "poly.from_coefficients"
                | "poly.divide_opening"
                | "poly.coefficients"
                | "poly.coefficient_count"
                | "poly.degree_check"
                | "poly.univariate_evaluate"
                | "poly.univariate_boundary"
                | "poly.boundary"
                | "poly.round_evaluate"
        ))
    {
        return None;
    }
    if matches!(
        name,
        "vector.from_point" | "vector.to_point" | "vector.from_table" | "vector.to_table"
    ) {
        return None;
    }
    if name == "vector.embed" {
        return Some((|| {
            let [Value::KoalaBearVector(xs)] = args else {
                return Err(refused("kernel-operands"));
            };
            p.vector_width(xs.len(), 32)?;
            p.output(size(xs.len(), 32)?, i.max_output_bytes)?;
            let mut out = reserve(xs.len())?;
            out.extend(xs.iter().copied().map(KoalaBearExt8::from));
            Ok(vec![Value::KoalaBearExt8Vector(out.into())])
        })());
    }
    if name == "field.embed" {
        return Some((|| {
            p.output(512, i.max_output_bytes)?;
            match (
                i.binding
                    .signature()
                    .outputs
                    .first()
                    .map(|t| t.logical().identity()),
                args,
            ) {
                (Some(Identity::KoalaBearExt8), [Value::KoalaBearField(x)]) => {
                    Ok(vec![Value::KoalaBearExt8Field((*x).into())])
                }
                _ => Err(refused("kernel-operands")),
            }
        })());
    }
    Some(match field {
        Some(Identity::Bn254Fr) => dense::<crate::Bn254Scalar>(name, args, i, p),
        Some(Identity::Bls12381Fr) => dense::<Scalar>(name, args, i, p),
        Some(Identity::Ristretto255Scalar) => dense::<RistrettoScalar>(name, args, i, p),
        Some(Identity::KoalaBearExt8) => dense::<KoalaBearExt8>(name, args, i, p),
        Some(Identity::KoalaBear) => dense::<KoalaBear>(name, args, i, p),
        _ => Err(refused("kernel-operands")),
    })
}
fn dense<S: Family>(
    name: &str,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Result<Vec<Value>> {
    let arg = |j| args.get(j).ok_or_else(|| refused("kernel-operands"));
    let f = |j| S::field(arg(j)?);
    let v = |j| S::vector(arg(j)?);
    let index = |j| match arg(j)? {
        Value::Index(n) => usize::try_from(*n).map_err(|_| refused("index-bounds")),
        _ => Err(refused("kernel-operands")),
    };
    let scalar = |s| Ok(vec![S::field_value(s)]);
    let boolean = |b| Ok(vec![Value::Bool(b)]);
    let width = std::mem::size_of::<S>();
    let allocation = |n| {
        p.vector_width(n, width)?;
        p.output(size(n, width)?, i.max_output_bytes)?;
        reserve::<S>(n)
    };
    // Scalar results (including Boolean checks) reserve before arithmetic.
    if i.binding.signature().outputs.iter().all(|t| {
        matches!(
            t.kind(),
            zkc_runtime::interactive::Type::Field | zkc_runtime::interactive::Type::Bool
        )
    }) {
        p.output(512, i.max_output_bytes)?;
    }
    match name {
        "field.constant" => scalar(S::decimal(&i.attributes[0])?),
        "field.add" => scalar(f(0)? + f(1)?),
        "field.sub" => scalar(f(0)? - f(1)?),
        "field.mul" => scalar(f(0)? * f(1)?),
        "field.neg" => scalar(-f(0)?),
        "field.inverse" => scalar(f(0)?.inverse().ok_or_else(|| refused("zero-inverse"))?),
        "field.equal" => boolean(f(0)? == f(1)?),
        "poly.univariate_evaluate" => scalar(evaluate(S::polynomial(arg(0)?)?, f(1)?)),
        "poly.univariate_boundary" => scalar(boundary(S::polynomial(arg(0)?)?)),
        "poly.boundary" => scalar(boundary(S::round(arg(0)?)?)),
        "poly.round_evaluate" => scalar(evaluate(S::round(arg(0)?)?, f(1)?)),
        "poly.degree_check" => {
            boolean(S::polynomial(arg(0)?)?.len().saturating_sub(1) <= natural(i.attributes, 0)?)
        }
        "poly.from_coefficients" => {
            let a = v(0)?;
            let n = a.iter().rposition(|s| *s != S::zero()).map_or(0, |i| i + 1);
            let mut out = allocation(n)?;
            out.extend_from_slice(&a[..n]);
            Ok(vec![S::polynomial_value(out.into())])
        }
        "poly.coefficients" => {
            let a = S::polynomial(arg(0)?)?;
            let mut out = allocation(a.len())?;
            out.extend_from_slice(a);
            Ok(vec![S::vector_value(out.into())])
        }
        "matrix.mul_vector" | "matrix.transpose_mul_vector" => {
            let m = S::matrix(arg(0)?)?;
            Ok(vec![S::vector_value(
                crate::matrix::mul(
                    m,
                    v(1)?,
                    name == "matrix.transpose_mul_vector",
                    p,
                    i.max_output_bytes,
                )?
                .into(),
            )])
        }
        "matrix.bilinear" => scalar(crate::matrix::bilinear(S::matrix(arg(0)?)?, v(1)?, v(2)?)?),
        "matrix.shape_check" => {
            let m = S::matrix(arg(0)?)?;
            boolean(
                m.rows() == natural(i.attributes, 0)? && m.columns() == natural(i.attributes, 1)?,
            )
        }
        "matrix.identity_check" => boolean(crate::matrix::identity_check(
            S::matrix(arg(0)?)?,
            i.attributes,
        )?),
        "vector.constant" => {
            let mut out = allocation(i.attributes.len())?;
            for literal in i.attributes {
                out.push(S::decimal(literal)?);
            }
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.scatter_sum" => {
            let a = v(0)?;
            let n = natural(i.attributes, 0)?;
            equal_len(a.len(), i.attributes.len() - 1)?;
            // Check all indices before allocating the zero-filled output. A late
            // bad index must not be masked by an output-allocation failure.
            for j in 1..i.attributes.len() {
                if natural(i.attributes, j)? >= n {
                    return Err(refused("vector-index"));
                }
            }
            let mut out = allocation(n)?;
            out.resize(n, S::zero());
            for (j, value) in a.iter().enumerate() {
                let index = natural(i.attributes, j + 1)?;
                out[index] = out[index] + *value;
            }
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.empty" => {
            p.output(size(0, width)?, i.max_output_bytes)?;
            Ok(vec![S::vector_value(Arc::from([]))])
        }
        "vector.sum" => scalar(v(0)?.iter().fold(S::zero(), |s, x| s + *x)),
        "vector.dot" => {
            let (a, b) = (v(0)?, v(1)?);
            equal_len(a.len(), b.len())?;
            scalar(S::dot(a, b)?)
        }
        "field.from_index" => {
            let Value::Index(mut n) = *arg(0)? else {
                return Err(refused("kernel-operands"));
            };
            let (mut sum, mut bit) = (S::zero(), S::one());
            while n != 0 {
                if n & 1 == 1 {
                    sum = sum + bit;
                }
                n >>= 1;
                bit = bit + bit;
            }
            scalar(sum)
        }
        "vector.length" => Ok(vec![Value::Index(
            u64::try_from(v(0)?.len()).map_err(|_| exhausted("size-overflow"))?,
        )]),
        "poly.divide_opening" => {
            let cs = S::polynomial(arg(0)?)?;
            let (point, value) = (f(1)?, f(2)?);
            if cs.is_empty() {
                return if value == S::zero() {
                    Ok(vec![S::polynomial_value(Arc::from([]))])
                } else {
                    Err(refused("polynomial-opening-value"))
                };
            }
            let mut out = allocation(cs.len() - 1)?;
            out.resize(cs.len() - 1, S::zero());
            let mut remainder = *cs.last().expect("nonempty polynomial");
            for j in (1..cs.len()).rev() {
                out[j - 1] = remainder;
                remainder = cs[j - 1] + point * remainder;
            }
            if remainder != value {
                return Err(refused("polynomial-opening-value"));
            }
            while out.last().is_some_and(|x| *x == S::zero()) {
                out.pop();
            }
            Ok(vec![S::polynomial_value(out.into())])
        }
        "poly.coefficient_count" => Ok(vec![Value::Index(
            u64::try_from(S::polynomial(arg(0)?)?.len()).map_err(|_| exhausted("size-overflow"))?,
        )]),
        "vector.get" => scalar(
            *v(0)?
                .get(index(1)?)
                .ok_or_else(|| refused("vector-index"))?,
        ),
        "vector.slice" => {
            let a = v(0)?;
            let start = index(1)?;
            let length = index(2)?;
            let end = start
                .checked_add(length)
                .ok_or_else(|| refused("vector-slice"))?;
            let slice = a.get(start..end).ok_or_else(|| refused("vector-slice"))?;
            let mut out = allocation(length)?;
            out.extend_from_slice(slice);
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.rotate" => {
            let a = v(0)?;
            let k = index(1)?;
            if a.is_empty() || k >= a.len() {
                return Err(refused("vector-rotation"));
            }
            let mut out = allocation(a.len())?;
            out.extend_from_slice(&a[k..]);
            out.extend_from_slice(&a[..k]);
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.interleave" => {
            let (a, b) = (v(0)?, v(1)?);
            equal_len(a.len(), b.len())?;
            let mut out = allocation(
                a.len()
                    .checked_mul(2)
                    .ok_or_else(|| exhausted("size-overflow"))?,
            )?;
            for (x, y) in a.iter().zip(b.iter()) {
                out.push(*x);
                out.push(*y);
            }
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.prefix_product" | "vector.prefix_sum" | "vector.inverse" => {
            let a = v(0)?;
            if name == "vector.inverse" && a.iter().any(|x| *x == S::zero()) {
                return Err(refused("zero-inverse"));
            }
            let mut out = allocation(a.len())?;
            if name == "vector.inverse" {
                invert_nonzero(a, &mut out)?;
                return Ok(vec![S::vector_value(out.into())]);
            }
            let mut acc = if name == "vector.prefix_product" {
                S::one()
            } else {
                S::zero()
            };
            for x in a.iter() {
                acc = match name {
                    "vector.prefix_product" => acc * *x,
                    _ => acc + *x,
                };
                out.push(acc);
            }
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.fill" | "vector.geometric" => {
            let x = f(0)?;
            let n = index(1)?;
            let mut out = allocation(n)?;
            let mut power = S::one();
            for _ in 0..n {
                out.push(if name == "vector.fill" { x } else { power });
                power = power * x;
            }
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.at" => scalar(
            *v(0)?
                .get(natural(i.attributes, 0)?)
                .ok_or_else(|| refused("vector-index"))?,
        ),
        "vector.length_check" => boolean(v(0)?.len() == natural(i.attributes, 0)?),
        "vector.split" => {
            let a = v(0)?;
            let half = split_len(a.len())?;
            p.output(
                size(half, width)?
                    .checked_mul(2)
                    .ok_or_else(|| exhausted("size-overflow"))?,
                i.max_output_bytes,
            )?;
            let mut left = allocation(half)?;
            let mut right = allocation(half)?;
            left.extend_from_slice(&a[..half]);
            right.extend_from_slice(&a[half..]);
            Ok(vec![
                S::vector_value(left.into()),
                S::vector_value(right.into()),
            ])
        }
        "vector.splat" | "vector.powers" => {
            let n = natural(i.attributes, 0)?;
            let x = f(0)?;
            let mut out = allocation(n)?;
            let mut power = S::one();
            for _ in 0..n {
                out.push(if name == "vector.splat" { x } else { power });
                if name == "vector.powers" {
                    power = power * x;
                }
            }
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.append" | "vector.scale" => {
            let a = v(0)?;
            let x = f(1)?;
            let n = a
                .len()
                .checked_add(usize::from(name == "vector.append"))
                .ok_or_else(|| exhausted("size-overflow"))?;
            let mut out = allocation(n)?;
            if name == "vector.append" {
                out.extend_from_slice(a);
                out.push(x);
            } else {
                out.extend(a.iter().map(|a| *a * x));
            }
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.gather" => {
            let a = v(0)?;
            // Validate every index before allocating or copying any element.
            for j in 0..i.attributes.len() {
                if natural(i.attributes, j)? >= a.len() {
                    return Err(refused("vector-index"));
                }
            }
            let mut out = allocation(i.attributes.len())?;
            for j in 0..i.attributes.len() {
                out.push(a[natural(i.attributes, j)?]);
            }
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.add" | "vector.sub" | "vector.mul" | "vector.concat" | "vector.kronecker" => {
            let (a, b) = (v(0)?, v(1)?);
            let n = match name {
                "vector.concat" => a
                    .len()
                    .checked_add(b.len())
                    .ok_or_else(|| exhausted("size-overflow"))?,
                "vector.kronecker" => a
                    .len()
                    .checked_mul(b.len())
                    .ok_or_else(|| exhausted("size-overflow"))?,
                _ => {
                    equal_len(a.len(), b.len())?;
                    a.len()
                }
            };
            let mut out = allocation(n)?;
            match name {
                "vector.mul" => S::product(a, b, &mut out)?,
                "vector.concat" => {
                    out.extend_from_slice(a);
                    out.extend_from_slice(b);
                }
                "vector.kronecker" => {
                    for x in a.iter() {
                        for y in b.iter() {
                            out.push(*x * *y);
                        }
                    }
                }
                _ => out.extend(a.iter().zip(b.iter()).map(|(a, b)| match name {
                    "vector.add" => *a + *b,
                    "vector.sub" => *a - *b,
                    _ => *a * *b,
                })),
            }
            Ok(vec![S::vector_value(out.into())])
        }
        "vector.matvec" => {
            let (a, b) = (v(0)?, v(1)?);
            let (rows, cols, transpose) = (
                natural(i.attributes, 0)?,
                natural(i.attributes, 1)?,
                natural(i.attributes, 2)?,
            );
            if transpose > 1 {
                return Err(refused("matrix-shape"));
            }
            equal_len(
                a.len(),
                rows.checked_mul(cols)
                    .ok_or_else(|| exhausted("size-overflow"))?,
            )?;
            let (inner, outer) = if transpose == 0 {
                (cols, rows)
            } else {
                (rows, cols)
            };
            equal_len(b.len(), inner)?;
            let mut out = allocation(outer)?;
            for j in 0..outer {
                let mut sum = S::zero();
                for k in 0..inner {
                    let index = if transpose == 0 {
                        j * cols + k
                    } else {
                        k * cols + j
                    };
                    sum = sum + a[index] * b[k];
                }
                out.push(sum);
            }
            Ok(vec![S::vector_value(out.into())])
        }
        _ => Err(refused("kernel-operands")),
    }
}

impl Value {
    /// Bounded host construction of canonical BN254 vector backing.
    pub fn bn254_vector(values: &[crate::Bn254Scalar], policy: &Policy) -> Result<Self> {
        policy.vector(values.len())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::Bn254Vector(v.into()))
    }
    /// Bounded vector of validated BN254 G1 points.
    pub fn bn254_g1_vector(values: &[crate::Bn254G1], policy: &Policy) -> Result<Self> {
        policy.bn254_groups::<crate::Bn254G1>(values.len())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::Bn254G1Vector(v.into()))
    }
    /// Bounded vector of validated BN254 G2 points.
    pub fn bn254_g2_vector(values: &[crate::Bn254G2], policy: &Policy) -> Result<Self> {
        policy.bn254_groups::<crate::Bn254G2>(values.len())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::Bn254G2Vector(v.into()))
    }
    pub fn koala_bear_ext8_vector(values: &[KoalaBearExt8], policy: &Policy) -> Result<Self> {
        policy.vector_width(values.len(), std::mem::size_of::<KoalaBearExt8>())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::KoalaBearExt8Vector(v.into()))
    }
    pub fn koala_bear_vector(values: &[KoalaBear], policy: &Policy) -> Result<Self> {
        policy.vector_width(values.len(), std::mem::size_of::<KoalaBear>())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::KoalaBearVector(v.into()))
    }
    pub fn vector(values: &[Scalar], policy: &Policy) -> Result<Self> {
        policy.vector(values.len())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::Vector(v.into()))
    }
    pub fn ristretto_vector(values: &[RistrettoScalar], policy: &Policy) -> Result<Self> {
        policy.vector(values.len())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::RistrettoVector(v.into()))
    }
    pub fn ristretto_groups(values: &[crate::RistrettoPoint], policy: &Policy) -> Result<Self> {
        policy.ristretto_groups(values.len())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::RistrettoGroups(v.into()))
    }
}

#[cfg(test)]
mod batch_inversion_tests {
    use super::*;

    fn check<S: Coefficient>() {
        for n in [0, 1, 2, 17, 257] {
            let mut x = S::one();
            let values: Vec<_> = (0..n)
                .map(|_| {
                    x = x + S::one();
                    x
                })
                .collect();
            let mut output = Vec::with_capacity(n);
            invert_nonzero(&values, &mut output).unwrap();
            assert_eq!(output.len(), n);
            assert!(values.iter().zip(&output).all(|(x, y)| *x * *y == S::one()));
            for index in [0, n / 2, n.saturating_sub(1)] {
                if n == 0 {
                    continue;
                }
                let mut with_zero = values.clone();
                with_zero[index] = S::zero();
                output.clear();
                assert!(invert_nonzero(&with_zero, &mut output).is_err());
                assert!(output.is_empty());
            }
        }
    }

    #[test]
    fn agrees_with_field_inversion_and_preserves_zero_refusal() {
        check::<Scalar>();
        check::<crate::Bn254Scalar>();
        check::<RistrettoScalar>();
        check::<KoalaBear>();
        check::<KoalaBearExt8>();
    }
}
