//! Arkworks radix-two FFTs in natural order shift * omega^i.
use crate::{
    Bn254Scalar as F, Policy, Result, Value, exhausted, kernels::arithmetic::reserve, refused,
    value::size,
};
use ark_ff::{FftField, Field, One, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use zkc_runtime::interactive::{Identity, Invocation};
fn domain(n: usize, shift: F, p: &Policy) -> Result<Radix2EvaluationDomain<F>> {
    if !n.is_power_of_two() || n.trailing_zeros() > F::TWO_ADICITY {
        return Err(refused("coset-size"));
    }
    if n > p.max_table_elements.min(1 << 20) {
        return Err(refused("coset-element-limit"));
    }
    if shift.is_zero() {
        return Err(refused("coset-zero-shift"));
    }
    Radix2EvaluationDomain::<F>::new(n)
        .and_then(|d| d.get_coset(shift))
        .ok_or_else(|| refused("coset-size"))
}
pub(crate) fn apply(
    name: &str,
    field: Option<Identity>,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Option<Result<Vec<Value>>> {
    if field != Some(Identity::Bn254Fr)
        || !matches!(
            name,
            "poly.coset_evaluate"
                | "poly.coset_interpolate"
                | "poly.domain_point"
                | "poly.domain_root"
                | "poly.domain_points"
                | "poly.even_odd_fold"
                | "poly.opening_quotient"
        )
    {
        return None;
    }
    Some(execute(name, args, i, p))
}
fn execute(name: &str, args: &[Value], i: &Invocation<'_>, p: &Policy) -> Result<Vec<Value>> {
    let arg = |n| args.get(n).ok_or_else(|| refused("kernel-operands"));
    let f = |n| match arg(n)? {
        Value::Bn254Field(v) => Ok(*v),
        _ => Err(refused("kernel-operands")),
    };
    let v = |n| match arg(n)? {
        Value::Bn254Vector(v) => Ok(v.as_ref()),
        _ => Err(refused("kernel-operands")),
    };
    let ix = |n| match arg(n)? {
        Value::Index(v) => usize::try_from(*v).map_err(|_| refused("index-bounds")),
        _ => Err(refused("kernel-operands")),
    };
    let alloc = |n: usize| -> Result<Vec<F>> {
        p.vector(n)?;
        p.output(size(n, 32)?, i.max_output_bytes)?;
        p.output(
            size(n, 32)?
                .checked_mul(8)
                .ok_or_else(|| exhausted("size-overflow"))?,
            usize::MAX,
        )?;
        reserve(n)
    };
    let result = match name {
        "poly.domain_root" => {
            p.output(512, i.max_output_bytes)?;
            Value::Bn254Field(domain(ix(0)?, F::one(), p)?.group_gen)
        }
        "poly.domain_point" => {
            p.output(512, i.max_output_bytes)?;
            let d = domain(ix(1)?, f(0)?, p)?;
            let j = ix(2)?;
            if j >= d.size() {
                return Err(refused("coset-coordinate"));
            }
            Value::Bn254Field(d.element(j))
        }
        "poly.domain_points" => {
            let d = domain(ix(1)?, f(0)?, p)?;
            let mut out = alloc(d.size())?;
            out.extend(d.elements());
            Value::Bn254Vector(out.into())
        }
        "poly.coset_evaluate" => {
            let Value::Bn254Polynomial(coeff) = arg(0)? else {
                return Err(refused("kernel-operands"));
            };
            let d = domain(ix(2)?, f(1)?, p)?;
            if coeff.len() > d.size() {
                return Err(refused("coset-coefficient-count"));
            }
            let mut out = alloc(d.size())?;
            out.extend_from_slice(coeff);
            d.fft_in_place(&mut out);
            Value::Bn254Vector(out.into())
        }
        "poly.coset_interpolate" => {
            let values = v(0)?;
            let d = domain(values.len(), f(1)?, p)?;
            let mut out = alloc(d.size())?;
            out.extend_from_slice(values);
            d.ifft_in_place(&mut out);
            while out.last() == Some(&F::zero()) {
                out.pop();
            }
            Value::Bn254Polynomial(out.into())
        }
        "poly.even_odd_fold" => {
            let values = v(0)?;
            let d = domain(values.len(), f(1)?, p)?;
            let half = d.size() / 2;
            if half == 0 {
                return Err(refused("coset-fold-size"));
            }
            let mut out = alloc(half)?;
            let inv2 = F::from(2).inverse().unwrap();
            let c = f(2)?;
            let mut invx = d.offset_inv;
            let invg = d.group_gen_inv;
            for (a, b) in values[..half].iter().zip(&values[half..]) {
                out.push((*a + *b) * inv2 + c * (*a - *b) * inv2 * invx);
                invx *= invg;
            }
            Value::Bn254Vector(out.into())
        }
        "poly.opening_quotient" => {
            let values = v(0)?;
            let d = domain(values.len(), f(1)?, p)?;
            let point = f(2)?;
            let value = f(3)?;
            if d.evaluate_vanishing_polynomial(point).is_zero() {
                return Err(refused("coset-opening-point"));
            }
            let mut out = alloc(d.size())?;
            out.extend(d.elements().map(|x| x - point));
            ark_ff::batch_inversion(&mut out);
            for (x, y) in out.iter_mut().zip(values) {
                *x *= *y - value;
            }
            Value::Bn254Vector(out.into())
        }
        _ => return Err(refused("coset-operation")),
    };
    Ok(vec![result])
}
