//! Arkworks radix-two FFTs in natural order shift * omega^i.
use crate::{
    Bn254Scalar as F, Policy, Result, Value, exhausted,
    kernels::arithmetic::reserve,
    numerical::{Call, transform::CosetBatch},
    refused,
    value::size,
};
use ark_ff::{FftField, Field, One, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use zkc_runtime::vm::{Identity, Invocation};
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
) -> Result<Vec<Value>> {
    if field != Some(Identity::Bn254Fr)
        || !matches!(
            name,
            "poly.coset_evaluate"
                | "poly.coset_extend"
                | "poly.coset_interpolate"
                | "poly.domain_point"
                | "poly.domain_root"
                | "poly.domain_points"
                | "poly.even_odd_fold"
                | "poly.opening_quotient"
        )
    {
        return Err(refused("kernel-operands"));
    }
    execute(name, args, i.max_output_bytes, p)
}
fn execute(name: &str, args: &[Value], available: usize, p: &Policy) -> Result<Vec<Value>> {
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
        p.output(size(n, 32)?, available)?;
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
            p.output(512, available)?;
            Value::Bn254Field(domain(ix(0)?, F::one(), p)?.group_gen)
        }
        "poly.domain_point" => {
            p.output(512, available)?;
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
        "poly.coset_extend" => {
            let values = v(0)?;
            let shape = CosetBatch::new(values.len(), ix(1)?, ix(2)?, ix(5)?)?;
            let domains = if shape.width == 0 {
                None
            } else {
                let input = domain(shape.height, f(3)?, p)?;
                let output = domain(shape.size, f(4)?, p)?;
                Some((input, output))
            };
            p.vector(shape.input_len)?;
            p.vector(shape.output_len)?;
            let retained = size(shape.output_len, 32)?;
            p.output(retained, available)?;
            let call = Call::new(p, available);
            call.work(shape.work(1)?)?;
            // One capacity-preserving Vec serves both transforms per column.
            // Internal Arkworks twiddle/work allocations are provider-owned.
            let workspace = if domains.is_some() {
                shape.height.max(shape.size)
            } else {
                0
            };
            let _workspace = call.transform_workspace::<F>(workspace)?;
            let mut output = call.output(shape.output_len, F::zero(), retained)?;
            if let Some((input_domain, output_domain)) = domains {
                let mut scratch = reserve(workspace)?;
                for (column, destination) in values
                    .chunks_exact(shape.height)
                    .zip(output.as_mut_slice().chunks_exact_mut(shape.size))
                {
                    scratch.clear();
                    scratch.extend_from_slice(column);
                    input_domain.ifft_in_place(&mut scratch);
                    if scratch
                        .get(shape.size..)
                        .is_some_and(|tail| tail.iter().any(|c| !c.is_zero()))
                    {
                        return Err(refused("coset-coefficient-count"));
                    }
                    scratch.resize(shape.size, F::zero());
                    output_domain.fft_in_place(&mut scratch);
                    destination.copy_from_slice(&scratch);
                }
            }
            output.finish(|values| Ok(Value::Bn254Vector(values.into())))?
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

#[cfg(test)]
mod tests {
    use super::*;

    fn args(values: Vec<F>, width: u64, height: u64, size: u64) -> Vec<Value> {
        vec![
            Value::Bn254Vector(values.into()),
            Value::Index(width),
            Value::Index(height),
            Value::Bn254Field(F::from(7)),
            Value::Bn254Field(F::from(11)),
            Value::Index(size),
        ]
    }

    fn vector(value: &Value) -> &[F] {
        let Value::Bn254Vector(values) = value else {
            panic!("expected vector")
        };
        values
    }

    fn run(args: &[Value], policy: &Policy, available: usize) -> Result<Vec<Value>> {
        execute("poly.coset_extend", args, available, policy)
    }

    #[test]
    fn batch_extension_matches_existing_per_column_operations() {
        let policy = Policy::default();
        for width in [1, 4, 16] {
            for (height, size) in [(1, 1), (1, 4), (4, 1), (4, 2), (4, 8), (8, 4), (8, 16)] {
                let input = domain(height, F::from(7), &policy).unwrap();
                let output = domain(size, F::from(11), &policy).unwrap();
                let mut values = Vec::new();
                let mut expected = Vec::new();
                for column in 0..width {
                    let coefficients: Vec<_> = (0..(column % (height.min(size) + 1)))
                        .map(|j| F::from((17 * column + 5 * j + 1) as u64))
                        .collect();
                    let column_values: Vec<_> = input
                        .elements()
                        .map(|x| coefficients.iter().rev().fold(F::zero(), |v, c| v * x + c))
                        .collect();
                    let interpolated = execute(
                        "poly.coset_interpolate",
                        &[
                            Value::Bn254Vector(column_values.clone().into()),
                            Value::Bn254Field(F::from(7)),
                        ],
                        usize::MAX,
                        &policy,
                    )
                    .unwrap()
                    .remove(0);
                    let evaluated = execute(
                        "poly.coset_evaluate",
                        &[
                            interpolated,
                            Value::Bn254Field(F::from(11)),
                            Value::Index(size as u64),
                        ],
                        usize::MAX,
                        &policy,
                    )
                    .unwrap()
                    .remove(0);
                    let horner: Vec<_> = output
                        .elements()
                        .map(|x| coefficients.iter().rev().fold(F::zero(), |v, c| v * x + c))
                        .collect();
                    assert_eq!(vector(&evaluated), horner);
                    expected.extend_from_slice(vector(&evaluated));
                    values.extend(column_values);
                }
                let args = args(values.clone(), width as u64, height as u64, size as u64);
                let alias = args[0].clone();
                let result = run(&args, &policy, usize::MAX).unwrap();
                assert_eq!(vector(&result[0]), expected);
                assert_eq!(vector(&alias), values);
                assert_ne!(vector(&result[0]).as_ptr(), vector(&alias).as_ptr());
            }
        }
    }

    #[test]
    fn shrinking_accepts_actual_low_degree_and_refuses_any_high_column() {
        let policy = Policy::default();
        let input = domain(4, F::from(7), &policy).unwrap();
        for coefficients in [vec![], vec![F::one()], vec![F::one(), F::one()]] {
            let mut values = coefficients.clone();
            input.fft_in_place(&mut values);
            assert!(run(&args(values, 1, 4, 2), &policy, usize::MAX).is_ok());
        }
        let low = vec![F::one(); 4];
        let mut high = vec![F::zero(), F::zero(), F::one()];
        input.fft_in_place(&mut high);
        for values in [high.clone(), [low, high].concat()] {
            let args = args(values.clone(), (values.len() / 4) as u64, 4, 2);
            let alias = args[0].clone();
            assert_eq!(
                run(&args, &policy, usize::MAX).unwrap_err().code,
                "refused:coset-coefficient-count"
            );
            assert_eq!(vector(&alias), values);
        }
    }

    #[test]
    fn batch_preflight_checks_resources_and_preserves_aliases() {
        let policy = Policy::default();
        let values = vec![F::one(); 16];
        let args = args(values.clone(), 4, 4, 8);
        let shape = CosetBatch::new(16, 4, 4, 8).unwrap();
        let retained = size(32, 32).unwrap();
        let managed = retained + (32 + 8) * std::mem::size_of::<F>();
        let work = shape.work(1).unwrap();
        for (policy, available, expected) in [
            (
                Policy {
                    max_numerical_work: work - 1,
                    ..policy
                },
                retained,
                "exhausted:numerical-work",
            ),
            (
                Policy {
                    max_numerical_bytes: managed - 1,
                    ..policy
                },
                retained,
                "exhausted:numerical-bytes",
            ),
            (
                Policy {
                    max_numerical_work: 0,
                    ..policy
                },
                retained - 1,
                "exhausted:output-bytes",
            ),
            (
                Policy {
                    max_table_elements: 4,
                    ..policy
                },
                retained,
                "refused:coset-element-limit",
            ),
            (
                Policy {
                    max_table_elements: 16,
                    ..policy
                },
                retained,
                "exhausted:element-limit",
            ),
        ] {
            let alias = args[0].clone();
            assert_eq!(run(&args, &policy, available).unwrap_err().code, expected);
            assert_eq!(vector(&alias), values);
        }
        let exact = Policy {
            max_numerical_work: work,
            max_numerical_bytes: managed,
            ..policy
        };
        assert!(run(&args, &exact, retained).is_ok());
    }

    #[test]
    fn batch_shape_empty_and_domain_refusals() {
        let policy = Policy::default();
        for (values, width, height, size, expected) in [
            (vec![F::one()], 0, 0, 0, "refused:coset-batch-shape"),
            (vec![F::one(); 3], 1, 4, 2, "refused:coset-batch-shape"),
            (vec![F::one(); 5], 1, 4, 2, "refused:coset-batch-shape"),
            (vec![], u64::MAX, 2, 2, "exhausted:size-overflow"),
            (vec![], u64::MAX, 0, 2, "exhausted:size-overflow"),
            (vec![], 1, 0, 0, "refused:coset-size"),
            (vec![F::one(); 4], 1, 4, 3, "refused:coset-size"),
        ] {
            assert_eq!(
                run(&args(values, width, height, size), &policy, usize::MAX)
                    .unwrap_err()
                    .code,
                expected
            );
        }
        let mut empty = args(vec![], 0, u64::MAX, u64::MAX);
        empty[3] = Value::Bn254Field(F::zero());
        empty[4] = Value::Bn254Field(F::zero());
        assert!(vector(&run(&empty, &policy, usize::MAX).unwrap()[0]).is_empty());
        let mut arguments = args(vec![F::one(); 4], 1, 4, 3);
        arguments[3] = Value::Bn254Field(F::zero());
        assert_eq!(
            run(&arguments, &policy, usize::MAX).unwrap_err().code,
            "refused:coset-zero-shift"
        );
        arguments[3] = Value::Bn254Field(F::one());
        arguments[4] = Value::Bn254Field(F::zero());
        arguments[5] = Value::Index(4);
        assert_eq!(
            run(&arguments, &policy, usize::MAX).unwrap_err().code,
            "refused:coset-zero-shift"
        );
    }
}
