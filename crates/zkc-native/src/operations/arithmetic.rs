//! Shared dense scalar/vector/coefficient arithmetic. Mathematical meanings do
//! not depend on physical layout. Callers preflight sizes before allocating.
pub(crate) use super::field::Coefficient;
use super::field::{Family, StructuredFamily, with_field};
use crate::{Binary64, Binary64Ext3, KoalaBear, KoalaBearExt4, KoalaBearExt8};
use crate::{Policy, Result, RistrettoScalar, Scalar, Value, exhausted, refused, value::size};
use std::sync::Arc;
use zkc_kernels::{
    polynomial::{boundary, evaluate},
    vector::Plan,
};
use zkc_runtime::vm::{Identity, Invocation, Value as _};

/// Montgomery batch inversion. The caller supplies the checked allocation;
/// zero inputs are refused before any output is materialized. Scalar inversion
/// remains delegated to the selected field library.
fn invert_nonzero<S: Coefficient>(
    values: &[S],
    allocate: impl FnOnce() -> Result<Vec<S>>,
) -> Result<Vec<S>> {
    let operation = zkc_kernels::vector::Inversion::new(values).map_err(crate::field_error)?;
    let mut out = allocate()?;
    out.resize(values.len(), S::zero());
    operation.write_into(&mut out).map_err(crate::field_error)?;
    Ok(out)
}

fn find_last<S: Coefficient>(
    values: &[S],
    needle: S,
    policy: &Policy,
    available: usize,
) -> Result<Value> {
    policy.vector_width(values.len(), std::mem::size_of::<S>())?;
    let retained = Value::Index(0).retained_bytes();
    policy.output(retained, available)?;
    let call = crate::numerical::Call::new(policy, available);
    call.work_items(values.len(), 1, 1)?;
    let output = call.scalar(retained)?;
    // Visit the complete ordered vector; no mask or value cache is needed.
    let mut found = values.len();
    for (position, value) in values.iter().enumerate() {
        if *value == needle {
            found = position;
        }
    }
    let found = u64::try_from(found).map_err(|_| exhausted("size-overflow"))?;
    output.finish(|| Ok(Value::Index(found)))
}

pub(crate) fn reserve<T>(n: usize) -> Result<Vec<T>> {
    zkc_kernels::allocation::reserve(n).map_err(|_| exhausted("allocation"))
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
pub(crate) fn apply(
    name: &str,
    field: Option<Identity>,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Result<Vec<Value>> {
    // The binding's output port names the extension; its declared base field
    // supplies the operand.
    let target = i
        .binding
        .signature()
        .outputs
        .first()
        .map(|t| t.logical().identity());
    if name == "vector.embed" {
        fn embed<B: Copy, E: From<B>>(
            xs: &[B],
            p: &Policy,
            i: &Invocation<'_>,
            value: fn(Arc<[E]>) -> Value,
        ) -> Result<Vec<Value>> {
            let width = std::mem::size_of::<E>();
            p.vector_width(xs.len(), width)?;
            p.output(size(xs.len(), width)?, i.max_output_bytes)?;
            let mut out = reserve(xs.len())?;
            out.extend(xs.iter().copied().map(E::from));
            Ok(vec![value(out.into())])
        }
        return match (target, args) {
            (Some(Identity::KoalaBearExt8), [Value::KoalaBearVector(xs)]) => {
                embed::<KoalaBear, KoalaBearExt8>(xs, p, i, Value::KoalaBearExt8Vector)
            }
            (Some(Identity::KoalaBearExt4), [Value::KoalaBearVector(xs)]) => {
                embed::<KoalaBear, KoalaBearExt4>(xs, p, i, Value::KoalaBearExt4Vector)
            }
            (Some(Identity::Binary64Ext3), [Value::Binary64Vector(xs)]) => {
                embed::<Binary64, Binary64Ext3>(xs, p, i, Value::Binary64Ext3Vector)
            }
            _ => Err(refused("kernel-operands")),
        };
    }
    if name == "field.embed" {
        p.output(512, i.max_output_bytes)?;
        return match (target, args) {
            (Some(Identity::KoalaBearExt8), [Value::KoalaBearField(x)]) => {
                Ok(vec![Value::KoalaBearExt8Field((*x).into())])
            }
            (Some(Identity::KoalaBearExt4), [Value::KoalaBearField(x)]) => {
                Ok(vec![Value::KoalaBearExt4Field((*x).into())])
            }
            (Some(Identity::Binary64Ext3), [Value::Binary64Field(x)]) => {
                Ok(vec![Value::Binary64Ext3Field((*x).into())])
            }
            _ => Err(refused("kernel-operands")),
        };
    }
    with_field!(field.ok_or_else(|| refused("kernel-operands"))?, |S| {
        structured::<S>(name, args, i, p)
    })
}
fn preflight_scalar_output(i: &Invocation<'_>, p: &Policy) -> Result<()> {
    // Scalar results (including Boolean checks) reserve before arithmetic.
    if i.binding.signature().outputs.iter().all(|t| {
        matches!(
            t.kind(),
            zkc_runtime::vm::Type::Field | zkc_runtime::vm::Type::Bool
        )
    }) {
        p.output(512, i.max_output_bytes)?;
    }
    Ok(())
}

/// Structured payloads are available only through their dedicated adapter.
/// Other operations use the same scalar/vector family as resident providers.
fn structured<S: StructuredFamily>(
    name: &str,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Result<Vec<Value>> {
    if !name.starts_with("poly.") && !name.starts_with("matrix.") {
        return dense::<S>(name, args, i, p);
    }
    let arg = |j| args.get(j).ok_or_else(|| refused("kernel-operands"));
    let f = |j| S::field(arg(j)?);
    let v = |j| S::vector(arg(j)?);
    let index = |j| match arg(j)? {
        Value::Index(n) => usize::try_from(*n).map_err(|_| refused("index-bounds")),
        _ => Err(refused("kernel-operands")),
    };
    let scalar = |s| Ok(vec![S::field_value(s)]);
    let boolean = |b| Ok(vec![Value::Bool(b)]);
    let allocation = |n| {
        p.vector_width(n, std::mem::size_of::<S>())?;
        p.output(size(n, std::mem::size_of::<S>())?, i.max_output_bytes)?;
        reserve::<S>(n)
    };
    preflight_scalar_output(i, p)?;
    match name {
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
            Ok(vec![S::polynomial_value(out.into())?])
        }
        "poly.coefficients" => {
            let a = S::polynomial(arg(0)?)?;
            let mut out = allocation(a.len())?;
            out.extend_from_slice(a);
            Ok(vec![S::vector_value(out)])
        }
        "matrix.mul_vector" | "matrix.transpose_mul_vector" => {
            let m = S::matrix(arg(0)?)?;
            Ok(vec![S::vector_value(crate::matrix::mul(
                m,
                v(1)?,
                name == "matrix.transpose_mul_vector",
                p,
                i.max_output_bytes,
            )?)])
        }
        "matrix.bilinear" => scalar(crate::matrix::bilinear(S::matrix(arg(0)?)?, v(1)?, v(2)?)?),
        "matrix.row_dot" => scalar(crate::matrix::row_dot(
            S::matrix(arg(0)?)?,
            v(1)?,
            index(2)?,
        )?),
        "matrix.column_dot" => scalar(crate::matrix::column_dot(
            S::matrix(arg(0)?)?,
            v(1)?,
            index(2)?,
        )?),
        "matrix.get" => scalar(crate::matrix::get(
            S::matrix(arg(0)?)?,
            index(1)?,
            index(2)?,
        )?),
        "matrix.dimension" => {
            let matrix = S::matrix(arg(0)?)?;
            let dimension = match natural(i.attributes, 0)? {
                0 => matrix.rows(),
                1 => matrix.columns(),
                _ => return Err(refused("matrix-axis")),
            };
            Ok(vec![Value::Index(
                u64::try_from(dimension).map_err(|_| exhausted("size-overflow"))?,
            )])
        }
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
        "poly.divide_opening" => {
            let cs = S::polynomial(arg(0)?)?;
            let (point, value) = (f(1)?, f(2)?);
            if cs.is_empty() {
                return if value == S::zero() {
                    Ok(vec![S::polynomial_value(Arc::from([]))?])
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
            Ok(vec![S::polynomial_value(out.into())?])
        }
        "poly.coefficient_count" => Ok(vec![Value::Index(
            u64::try_from(S::polynomial(arg(0)?)?.len()).map_err(|_| exhausted("size-overflow"))?,
        )]),
        _ => Err(refused("kernel-operands")),
    }
}

pub(super) fn dense<S: Family>(
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
    let call = crate::numerical::Call::new(p, i.max_output_bytes);
    // At most two outputs occur in this family. Plain resident construction
    // retains its reservation until publication; dense destinations below use
    // their existing Output reservations instead.
    let reservations = std::cell::RefCell::new([None, None]);
    let allocation = |n| {
        p.vector_width(n, width)?;
        let bytes = size(n, width)?;
        p.output(bytes, i.max_output_bytes)?;
        if S::RESIDENT_STORAGE {
            let reservation = call.reserve_workspace::<u8>(bytes)?;
            *reservations
                .borrow_mut()
                .iter_mut()
                .find(|slot| slot.is_none())
                .ok_or_else(|| refused("kernel-output-count"))? = Some(reservation);
        }
        reserve::<S>(n)
    };
    let destination = |n, initial, per_element| {
        // Preserve element/output preflights before numerical work and storage.
        p.vector_width(n, width)?;
        let bytes = size(n, width)?;
        p.output(bytes, i.max_output_bytes)?;
        call.work_items(n, per_element, 1)?;
        call.output(n, initial, bytes)
    };
    preflight_scalar_output(i, p)?;
    match name {
        "field.constant" => {
            super::field::publish_literal(&super::field::literal::<S>(i.attributes)?, i, p)
        }
        "field.add" => scalar(f(0)? + f(1)?),
        "field.sub" => scalar(f(0)? - f(1)?),
        "field.mul" => scalar(f(0)? * f(1)?),
        "field.neg" => scalar(-f(0)?),
        "field.inverse" => scalar(f(0)?.inverse().ok_or_else(|| refused("zero-inverse"))?),
        "field.equal" => boolean(f(0)? == f(1)?),
        "vector.constant" => {
            let mut out = allocation(i.attributes.len())?;
            for literal in i.attributes {
                out.push(S::decimal(literal)?);
            }
            Ok(vec![S::vector_value(out)])
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
            Ok(vec![S::vector_value(out)])
        }
        "vector.empty" => Ok(vec![S::vector_value(allocation(0)?)]),
        "vector.sum" | "vector.product" => {
            let a = v(0)?;
            // One load and one accumulator operation per element, plus setup.
            call.work_items(a.len(), 2, 1)?;
            let result = call.scalar(512)?;
            Ok(vec![result.finish(|| {
                let value = if name == "vector.sum" {
                    a.iter().fold(S::zero(), |sum, x| sum + *x)
                } else {
                    a.iter().fold(S::one(), |product, x| product * *x)
                };
                Ok(S::field_value(value))
            })?])
        }
        "vector.dot" => {
            let (a, b) = (v(0)?, v(1)?);
            equal_len(a.len(), b.len())?;
            // Two loads, multiply/add, and any provider accumulator-lane reduction.
            call.work_items(a.len(), 4, S::DOT_SETUP_WORK)?;
            let result = call.scalar(512)?;
            Ok(vec![result.finish(|| Ok(S::field_value(S::dot(a, b)?)))?])
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
            Ok(vec![S::vector_value(out)])
        }
        "vector.transpose" => {
            let input = v(0)?;
            let rows = index(1)?;
            let columns = index(2)?;
            let count = rows
                .checked_mul(columns)
                .ok_or_else(|| refused("vector-shape"))?;
            if input.len() != count {
                return Err(refused("vector-shape"));
            }
            let mut out = allocation(count)?;
            // A zero extent may accompany a huge other extent. Do not loop
            // over it when there are no coordinates to visit.
            if count != 0 {
                for column in 0..columns {
                    for row in 0..rows {
                        out.push(input[row * columns + column]);
                    }
                }
            }
            Ok(vec![S::vector_value(out)])
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
            Ok(vec![S::vector_value(out)])
        }
        "vector.bit_reverse" | "vector.bit_reverse_rows" => {
            let a = v(0)?;
            let width = if name == "vector.bit_reverse" {
                1
            } else {
                index(1)?
            };
            if width == 0 || !a.len().is_multiple_of(width) {
                return Err(refused("vector-shape"));
            }
            let height = a.len() / width;
            if !height.is_power_of_two() {
                return Err(refused("vector-bit-reversal"));
            }
            let mut out = allocation(a.len())?;
            for row in 0..height {
                let source = zkc_kernels::polynomial::reverse_bits(row, height)
                    .ok_or_else(|| refused("vector-bit-reversal"))?;
                out.extend_from_slice(&a[source * width..(source + 1) * width]);
            }
            Ok(vec![S::vector_value(out)])
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
            Ok(vec![S::vector_value(out)])
        }
        "vector.prefix_product" | "vector.prefix_sum" | "vector.inverse" => {
            let a = v(0)?;
            if name == "vector.inverse" {
                let out = invert_nonzero(a, || allocation(a.len()))?;
                return Ok(vec![S::vector_value(out)]);
            }
            let mut out = allocation(a.len())?;
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
            Ok(vec![S::vector_value(out)])
        }
        "vector.fill" | "vector.geometric" | "vector.splat" | "vector.powers" => {
            // Attribute-sized forms historically read the length before the scalar.
            let (x, n) = if matches!(name, "vector.splat" | "vector.powers") {
                let n = natural(i.attributes, 0)?;
                (f(0)?, n)
            } else {
                (f(0)?, index(1)?)
            };
            let constant = matches!(name, "vector.fill" | "vector.splat");
            // Constant initialization and freezing need no field multiplication.
            // Geometric construction also counts each power update and write.
            let mut out = destination(
                n,
                if constant { x } else { S::zero() },
                if constant { 2 } else { 4 },
            )?;
            if !constant {
                let mut power = S::one();
                for value in out.as_mut_slice() {
                    *value = power;
                    power = power * x;
                }
            }
            Ok(vec![out.finish(|values| Ok(S::vector_value(values)))?])
        }
        "vector.at" => scalar(
            *v(0)?
                .get(natural(i.attributes, 0)?)
                .ok_or_else(|| refused("vector-index"))?,
        ),
        "vector.equal" => boolean(v(0)? == v(1)?),
        "vector.find_last" => Ok(vec![find_last(v(0)?, f(1)?, p, i.max_output_bytes)?]),
        "vector.length_check" => boolean(v(0)?.len() == natural(i.attributes, 0)?),
        "vector.split" => {
            let a = v(0)?;
            let half = split_len(a.len())?;
            let bytes = size(half, width)?;
            p.output(
                bytes
                    .checked_mul(2)
                    .ok_or_else(|| exhausted("size-overflow"))?,
                i.max_output_bytes,
            )?;
            p.vector_width(half, width)?;
            let call = crate::numerical::Call::new(p, i.max_output_bytes);
            call.work(
                (a.len() as u64)
                    .checked_mul(2)
                    .ok_or_else(|| exhausted("numerical-work"))?,
            )?;
            let mut left = call.output(half, S::zero(), bytes)?;
            let mut right = call.output(half, S::zero(), bytes)?;
            left.as_mut_slice().copy_from_slice(&a[..half]);
            right.as_mut_slice().copy_from_slice(&a[half..]);
            Ok(vec![
                left.finish(|values| Ok(S::vector_value(values)))?,
                right.finish(|values| Ok(S::vector_value(values)))?,
            ])
        }
        "vector.scale" => {
            let a = v(0)?;
            let x = f(1)?;
            // Load, multiply, initialize/write the destination, then freeze it.
            let mut out = destination(a.len(), S::zero(), 5)?;
            let plan = Plan::select(a.len()).map_err(crate::field_error)?;
            plan.scale(a, x, out.as_mut_slice())
                .map_err(crate::field_error)?;
            Ok(vec![out.finish(|values| Ok(S::vector_value(values)))?])
        }
        "vector.append" => {
            let a = v(0)?;
            let x = f(1)?;
            let n = a
                .len()
                .checked_add(1)
                .ok_or_else(|| exhausted("size-overflow"))?;
            let mut out = allocation(n)?;
            out.extend_from_slice(a);
            out.push(x);
            Ok(vec![S::vector_value(out)])
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
            Ok(vec![S::vector_value(out)])
        }
        "vector.add" | "vector.sub" | "vector.mul" => {
            let (a, b) = (v(0)?, v(1)?);
            equal_len(a.len(), b.len())?;
            // Two loads, arithmetic, initialized write, and freezing copy.
            let mut out = destination(a.len(), S::zero(), 6)?;
            let plan = Plan::select(a.len()).map_err(crate::field_error)?;
            if name == "vector.mul" {
                plan.mul(a, b, out.as_mut_slice())
                    .map_err(crate::field_error)?;
            } else if name == "vector.add" {
                plan.add(a, b, out.as_mut_slice())
                    .map_err(crate::field_error)?;
            } else {
                plan.sub(a, b, out.as_mut_slice())
                    .map_err(crate::field_error)?;
            }
            Ok(vec![out.finish(|values| Ok(S::vector_value(values)))?])
        }
        "vector.concat" | "vector.kronecker" => {
            let (a, b) = (v(0)?, v(1)?);
            let n = if name == "vector.concat" {
                a.len()
                    .checked_add(b.len())
                    .ok_or_else(|| exhausted("size-overflow"))?
            } else {
                a.len()
                    .checked_mul(b.len())
                    .ok_or_else(|| exhausted("size-overflow"))?
            };
            let mut out = allocation(n)?;
            if name == "vector.concat" {
                out.extend_from_slice(a);
                out.extend_from_slice(b);
            } else {
                for x in a.iter() {
                    for y in b.iter() {
                        out.push(*x * *y);
                    }
                }
            }
            Ok(vec![S::vector_value(out)])
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
            rows.checked_mul(cols)
                .ok_or_else(|| exhausted("size-overflow"))?;
            let matrix = zkc_kernels::matrix::RowMajor::new(a, rows, cols)
                .ok_or_else(|| refused("length-mismatch"))?;
            let (inner, outer) = if transpose == 0 {
                (matrix.cols(), matrix.rows())
            } else {
                (matrix.rows(), matrix.cols())
            };
            equal_len(b.len(), inner)?;
            // Keep the existing shape and output refusals ahead of the new
            // per-call bounds. Matrix elements stay in their exact field type;
            // transposition changes indexing without materializing a copy.
            p.vector_width(outer, width)?;
            let bytes = size(outer, width)?;
            p.output(bytes, i.max_output_bytes)?;
            let call = crate::numerical::Call::new(p, i.max_output_bytes);
            let work = (a.len() as u64)
                .checked_mul(2)
                .and_then(|n| n.checked_add(outer as u64))
                .ok_or_else(|| exhausted("numerical-work"))?;
            call.work(work)?;
            let mut out = call.output(outer, S::zero(), bytes)?;
            for (j, destination) in out.as_mut_slice().iter_mut().enumerate() {
                let mut sum = S::zero();
                if transpose == 0 {
                    for (a, b) in matrix
                        .row(j)
                        .expect("checked matrix row")
                        .iter()
                        .zip(b.iter())
                    {
                        sum = sum + *a * *b;
                    }
                } else {
                    for (k, b) in b.iter().enumerate() {
                        let a = matrix.transpose(j, k).expect("checked matrix coordinates");
                        sum = sum + *a * *b;
                    }
                }
                *destination = sum;
            }
            Ok(vec![out.finish(|values| Ok(S::vector_value(values)))?])
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
        policy.typed_groups::<crate::Bn254G1>(values.len())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::Bn254G1Vector(v.into()))
    }
    /// Bounded vector of validated BN254 G2 points.
    pub fn bn254_g2_vector(values: &[crate::Bn254G2], policy: &Policy) -> Result<Self> {
        policy.typed_groups::<crate::Bn254G2>(values.len())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::Bn254G2Vector(v.into()))
    }
    /// Bounded vector of validated BLS12-381 G2 points.
    pub fn bls12381_g2_vector(values: &[crate::Bls12381G2], policy: &Policy) -> Result<Self> {
        policy.typed_groups::<crate::Bls12381G2>(values.len())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::Bls12381G2Vector(v.into()))
    }
    pub fn koala_bear_ext8_vector(values: &[KoalaBearExt8], policy: &Policy) -> Result<Self> {
        policy.vector_width(values.len(), std::mem::size_of::<KoalaBearExt8>())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::KoalaBearExt8Vector(v.into()))
    }
    pub fn koala_bear_ext4_vector(values: &[KoalaBearExt4], policy: &Policy) -> Result<Self> {
        policy.vector_width(values.len(), std::mem::size_of::<KoalaBearExt4>())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::KoalaBearExt4Vector(v.into()))
    }
    pub fn binary64_vector(values: &[Binary64], policy: &Policy) -> Result<Self> {
        policy.vector_width(values.len(), std::mem::size_of::<Binary64>())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::Binary64Vector(v.into()))
    }
    pub fn binary64_ext3_vector(values: &[Binary64Ext3], policy: &Policy) -> Result<Self> {
        policy.vector_width(values.len(), std::mem::size_of::<Binary64Ext3>())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::Binary64Ext3Vector(v.into()))
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
        policy.dalek_groups(values.len())?;
        let mut v = reserve(values.len())?;
        v.extend_from_slice(values);
        Ok(Self::RistrettoGroups(v.into()))
    }
}

/// Independent native port facts, also used for exact implementation assembly.
pub(crate) const CONTRACTS: &[crate::bindings::Contract] = {
    use crate::bindings::{field, poly};
    use zkc_runtime::vm::{AttributeRule, Type::*};
    &[
        field::operation("field.constant", &[], &[Field], AttributeRule::FieldDecimal)
            .implemented_by(&[
                "arkworks/field.constant",
                "dalek/field.constant",
                "plonky3/field.constant",
            ]),
        field::operation("field.add", &[Field, Field], &[Field], AttributeRule::None)
            .implemented_by(&["arkworks/field.add", "dalek/field.add", "plonky3/field.add"]),
        field::operation("field.mul", &[Field, Field], &[Field], AttributeRule::None)
            .implemented_by(&["arkworks/field.mul", "dalek/field.mul", "plonky3/field.mul"]),
        field::operation("field.equal", &[Field, Field], &[Bool], AttributeRule::None)
            .implemented_by(&[
                "arkworks/field.equal",
                "dalek/field.equal",
                "plonky3/field.equal",
            ]),
        poly::operation("poly.boundary", &[Round], &[Field], AttributeRule::None).implemented_by(
            &[
                "arkworks/poly.boundary",
                "dalek/poly.boundary",
                "plonky3/poly.boundary",
            ],
        ),
        poly::operation(
            "poly.round_evaluate",
            &[Round, Field],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.round_evaluate",
            "dalek/poly.round_evaluate",
            "plonky3/poly.round_evaluate",
        ]),
        field::operation(
            "vector.get",
            &[Vector, Index],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.get",
            "dalek/vector.get",
            "plonky3/vector.get",
        ]),
        field::operation(
            "vector.slice",
            &[Vector, Index, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.slice",
            "dalek/vector.slice",
            "plonky3/vector.slice",
        ]),
        field::operation(
            "vector.transpose",
            &[Vector, Index, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.transpose",
            "dalek/vector.transpose",
            "plonky3/vector.transpose",
        ]),
        field::operation(
            "vector.find_last",
            &[Vector, Field],
            &[Index],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.find_last",
            "dalek/vector.find_last",
            "plonky3/vector.find_last",
        ]),
        field::operation("vector.length", &[Vector], &[Index], AttributeRule::None).implemented_by(
            &[
                "arkworks/vector.length",
                "dalek/vector.length",
                "plonky3/vector.length",
            ],
        ),
        field::operation(
            "vector.rotate",
            &[Vector, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.rotate",
            "dalek/vector.rotate",
            "plonky3/vector.rotate",
        ]),
        field::operation(
            "vector.bit_reverse",
            &[Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.bit_reverse",
            "dalek/vector.bit_reverse",
            "plonky3/vector.bit_reverse",
        ]),
        field::operation(
            "vector.bit_reverse_rows",
            &[Vector, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.bit_reverse_rows",
            "dalek/vector.bit_reverse_rows",
            "plonky3/vector.bit_reverse_rows",
        ]),
        field::operation(
            "vector.interleave",
            &[Vector, Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.interleave",
            "dalek/vector.interleave",
            "plonky3/vector.interleave",
        ]),
        field::operation(
            "vector.prefix_product",
            &[Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.prefix_product",
            "dalek/vector.prefix_product",
            "plonky3/vector.prefix_product",
        ]),
        field::operation(
            "vector.prefix_sum",
            &[Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.prefix_sum",
            "dalek/vector.prefix_sum",
            "plonky3/vector.prefix_sum",
        ]),
        field::operation("vector.inverse", &[Vector], &[Vector], AttributeRule::None)
            .implemented_by(&[
                "arkworks/vector.inverse",
                "dalek/vector.inverse",
                "plonky3/vector.inverse",
            ]),
        field::embedding("vector.embed", &[Vector], &[Vector], AttributeRule::None)
            .implemented_by(&["plonky3/vector.embed"]),
        field::operation(
            "vector.fill",
            &[Field, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.fill",
            "dalek/vector.fill",
            "plonky3/vector.fill",
        ]),
        field::operation(
            "vector.geometric",
            &[Field, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.geometric",
            "dalek/vector.geometric",
            "plonky3/vector.geometric",
        ]),
        field::operation("field.from_index", &[Index], &[Field], AttributeRule::None)
            .implemented_by(&[
                "arkworks/field.from_index",
                "dalek/field.from_index",
                "plonky3/field.from_index",
            ]),
        poly::operation(
            "poly.coefficient_count",
            &[Polynomial],
            &[Index],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.coefficient_count",
            "dalek/poly.coefficient_count",
            "plonky3/poly.coefficient_count",
        ]),
        poly::operation(
            "poly.divide_opening",
            &[Polynomial, Field, Field],
            &[Polynomial],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.divide_opening",
            "dalek/poly.divide_opening",
            "plonky3/poly.divide_opening",
        ]),
        field::operation("field.sub", &[Field, Field], &[Field], AttributeRule::None)
            .implemented_by(&["arkworks/field.sub", "dalek/field.sub", "plonky3/field.sub"]),
        field::operation("field.neg", &[Field], &[Field], AttributeRule::None).implemented_by(&[
            "arkworks/field.neg",
            "dalek/field.neg",
            "plonky3/field.neg",
        ]),
        field::operation("field.inverse", &[Field], &[Field], AttributeRule::None).implemented_by(
            &[
                "arkworks/field.inverse",
                "dalek/field.inverse",
                "plonky3/field.inverse",
            ],
        ),
        field::operation(
            "matrix.mul_vector",
            &[Matrix, Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/matrix.mul_vector",
            "dalek/matrix.mul_vector",
            "plonky3/matrix.mul_vector",
        ]),
        field::operation(
            "matrix.transpose_mul_vector",
            &[Matrix, Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/matrix.transpose_mul_vector",
            "dalek/matrix.transpose_mul_vector",
            "plonky3/matrix.transpose_mul_vector",
        ]),
        field::operation(
            "matrix.bilinear",
            &[Matrix, Vector, Vector],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/matrix.bilinear",
            "dalek/matrix.bilinear",
            "plonky3/matrix.bilinear",
        ]),
        field::operation(
            "matrix.row_dot",
            &[Matrix, Vector, Index],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/matrix.row_dot",
            "dalek/matrix.row_dot",
            "plonky3/matrix.row_dot",
        ]),
        field::operation(
            "matrix.column_dot",
            &[Matrix, Vector, Index],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/matrix.column_dot",
            "dalek/matrix.column_dot",
            "plonky3/matrix.column_dot",
        ]),
        field::operation(
            "matrix.get",
            &[Matrix, Index, Index],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/matrix.get",
            "dalek/matrix.get",
            "plonky3/matrix.get",
        ]),
        field::operation(
            "matrix.dimension",
            &[Matrix],
            &[Index],
            AttributeRule::Unsigned64,
        )
        .implemented_by(&[
            "arkworks/matrix.dimension",
            "dalek/matrix.dimension",
            "plonky3/matrix.dimension",
        ]),
        field::operation(
            "matrix.shape_check",
            &[Matrix],
            &[Bool],
            AttributeRule::MatrixDimensions,
        )
        .implemented_by(&[
            "arkworks/matrix.shape_check",
            "dalek/matrix.shape_check",
            "plonky3/matrix.shape_check",
        ]),
        field::operation(
            "matrix.identity_check",
            &[Matrix],
            &[Bool],
            AttributeRule::MatrixIdentity,
        )
        .implemented_by(&[
            "arkworks/matrix.identity_check",
            "dalek/matrix.identity_check",
            "plonky3/matrix.identity_check",
        ]),
        field::operation(
            "vector.constant",
            &[],
            &[Vector],
            AttributeRule::FieldDecimals,
        )
        .implemented_by(&[
            "arkworks/vector.constant",
            "dalek/vector.constant",
            "plonky3/vector.constant",
        ]),
        field::operation(
            "vector.scatter_sum",
            &[Vector],
            &[Vector],
            AttributeRule::ScatterShape,
        )
        .implemented_by(&[
            "arkworks/vector.scatter_sum",
            "dalek/vector.scatter_sum",
            "plonky3/vector.scatter_sum",
        ]),
        field::operation("vector.empty", &[], &[Vector], AttributeRule::None).implemented_by(&[
            "arkworks/vector.empty",
            "dalek/vector.empty",
            "plonky3/vector.empty",
        ]),
        field::operation(
            "vector.append",
            &[Vector, Field],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.append",
            "dalek/vector.append",
            "plonky3/vector.append",
        ]),
        field::operation(
            "vector.splat",
            &[Field],
            &[Vector],
            AttributeRule::NaturalIndex,
        )
        .implemented_by(&[
            "arkworks/vector.splat",
            "dalek/vector.splat",
            "plonky3/vector.splat",
        ]),
        field::operation(
            "vector.powers",
            &[Field],
            &[Vector],
            AttributeRule::NaturalIndex,
        )
        .implemented_by(&[
            "arkworks/vector.powers",
            "dalek/vector.powers",
            "plonky3/vector.powers",
        ]),
        field::operation(
            "vector.equal",
            &[Vector, Vector],
            &[Bool],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.equal",
            "dalek/vector.equal",
            "plonky3/vector.equal",
        ]),
        field::operation(
            "vector.add",
            &[Vector, Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.add",
            "dalek/vector.add",
            "plonky3/vector.add",
        ]),
        field::operation(
            "vector.sub",
            &[Vector, Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.sub",
            "dalek/vector.sub",
            "plonky3/vector.sub",
        ]),
        field::operation(
            "vector.mul",
            &[Vector, Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.mul",
            "dalek/vector.mul",
            "plonky3/vector.mul",
        ]),
        field::operation(
            "vector.scale",
            &[Vector, Field],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.scale",
            "dalek/vector.scale",
            "plonky3/vector.scale",
        ]),
        field::operation("vector.sum", &[Vector], &[Field], AttributeRule::None).implemented_by(&[
            "arkworks/vector.sum",
            "dalek/vector.sum",
            "plonky3/vector.sum",
        ]),
        field::operation("vector.product", &[Vector], &[Field], AttributeRule::None)
            .implemented_by(&[
                "arkworks/vector.product",
                "dalek/vector.product",
                "plonky3/vector.product",
            ]),
        field::operation(
            "vector.dot",
            &[Vector, Vector],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.dot",
            "dalek/vector.dot",
            "plonky3/vector.dot",
        ]),
        field::operation(
            "vector.split",
            &[Vector],
            &[Vector, Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.split",
            "dalek/vector.split",
            "plonky3/vector.split",
        ]),
        field::operation(
            "vector.concat",
            &[Vector, Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.concat",
            "dalek/vector.concat",
            "plonky3/vector.concat",
        ]),
        field::operation(
            "vector.at",
            &[Vector],
            &[Field],
            AttributeRule::NaturalIndex,
        )
        .implemented_by(&["arkworks/vector.at", "dalek/vector.at", "plonky3/vector.at"]),
        field::operation(
            "vector.length_check",
            &[Vector],
            &[Bool],
            AttributeRule::NaturalIndex,
        )
        .implemented_by(&[
            "arkworks/vector.length_check",
            "dalek/vector.length_check",
            "plonky3/vector.length_check",
        ]),
        field::operation(
            "vector.gather",
            &[Vector],
            &[Vector],
            AttributeRule::NaturalIndices,
        )
        .implemented_by(&[
            "arkworks/vector.gather",
            "dalek/vector.gather",
            "plonky3/vector.gather",
        ]),
        field::operation(
            "vector.kronecker",
            &[Vector, Vector],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/vector.kronecker",
            "dalek/vector.kronecker",
            "plonky3/vector.kronecker",
        ]),
        field::operation(
            "vector.matvec",
            &[Vector, Vector],
            &[Vector],
            AttributeRule::MatrixShape,
        )
        .implemented_by(&[
            "arkworks/vector.matvec",
            "dalek/vector.matvec",
            "plonky3/vector.matvec",
        ]),
        poly::operation(
            "poly.from_coefficients",
            &[Vector],
            &[Polynomial],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.from_coefficients",
            "dalek/poly.from_coefficients",
            "plonky3/poly.from_coefficients",
        ]),
        poly::operation(
            "poly.coefficients",
            &[Polynomial],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.coefficients",
            "dalek/poly.coefficients",
            "plonky3/poly.coefficients",
        ]),
        poly::operation(
            "poly.degree_check",
            &[Polynomial],
            &[Bool],
            AttributeRule::NaturalIndex,
        )
        .implemented_by(&[
            "arkworks/poly.degree_check",
            "dalek/poly.degree_check",
            "plonky3/poly.degree_check",
        ]),
        poly::operation(
            "poly.univariate_evaluate",
            &[Polynomial, Field],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.univariate_evaluate",
            "dalek/poly.univariate_evaluate",
            "plonky3/poly.univariate_evaluate",
        ]),
        poly::operation(
            "poly.univariate_boundary",
            &[Polynomial],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.univariate_boundary",
            "dalek/poly.univariate_boundary",
            "plonky3/poly.univariate_boundary",
        ]),
    ]
};
pub(crate) const EMBEDDINGS: &[crate::bindings::Contract] = &[crate::bindings::field::embedding(
    "field.embed",
    &[zkc_runtime::vm::Type::Field],
    &[zkc_runtime::vm::Type::Field],
    zkc_runtime::vm::AttributeRule::None,
)
.implemented_by(&["plonky3/field.embed"])];

#[cfg(test)]
mod batch_inversion_tests {
    use super::*;

    /// Distinct nonzero values: successive sums of one in odd characteristic.
    fn check<S: Coefficient>() {
        let mut x = S::one();
        check_values(|_| {
            x = x + S::one();
            x
        });
    }
    fn check_values<S: Coefficient>(mut element: impl FnMut(usize) -> S) {
        for n in [0, 1, 2, 17, 257] {
            let values: Vec<_> = (0..n).map(&mut element).collect();
            let output = invert_nonzero(&values, || Ok(Vec::with_capacity(n))).unwrap();
            assert_eq!(output.len(), n);
            assert!(values.iter().zip(&output).all(|(x, y)| *x * *y == S::one()));
            for index in [0, n / 2, n.saturating_sub(1)] {
                if n == 0 {
                    continue;
                }
                let mut with_zero = values.clone();
                with_zero[index] = S::zero();
                assert_eq!(
                    invert_nonzero(&with_zero, || panic!("zero must precede allocation"))
                        .err()
                        .unwrap()
                        .code,
                    "refused:zero-inverse"
                );
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
        check::<KoalaBearExt4>();
        // In characteristic two, one plus one is zero: use bit patterns instead.
        check_values(|k| zkc_kernels::plonky3::binary::from_bits(k as u64 + 2));
        check_values(|k| zkc_kernels::plonky3::binary::ext3_from_bits([3, k as u64, 5]));
    }
}

#[cfg(test)]
mod search_tests {
    use super::*;

    #[test]
    fn ordered_search_obeys_exact_result_work_and_memory_floors() {
        let values = [Scalar::from(3), Scalar::from(7), Scalar::from(3)];
        let policy = Policy {
            max_numerical_work: 4,
            max_numerical_bytes: 512,
            ..Policy::default()
        };
        assert!(matches!(
            find_last(&values, values[0], &policy, 512).unwrap(),
            Value::Index(2)
        ));
        for (limited, available, code) in [
            (
                Policy {
                    max_numerical_work: 3,
                    ..policy
                },
                512,
                "exhausted:numerical-work",
            ),
            (
                Policy {
                    max_numerical_bytes: 511,
                    ..policy
                },
                512,
                "exhausted:numerical-bytes",
            ),
            (policy, 511, "exhausted:output-bytes"),
            (
                Policy {
                    max_table_elements: 2,
                    ..policy
                },
                512,
                "exhausted:element-limit",
            ),
        ] {
            assert_eq!(
                find_last(&values, values[0], &limited, available)
                    .unwrap_err()
                    .code,
                code
            );
        }
        assert!(matches!(
            find_last(&[], Scalar::from(9), &policy, 512).unwrap(),
            Value::Index(0)
        ));
        assert!(matches!(
            find_last(&values, Scalar::from(9), &policy, 512).unwrap(),
            Value::Index(3)
        ));
        assert_eq!(values, [Scalar::from(3), Scalar::from(7), Scalar::from(3)]);
    }
}
