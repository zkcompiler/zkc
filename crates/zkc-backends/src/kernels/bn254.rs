//! Arkworks radix-two FFTs in natural order shift * omega^i.
use crate::{
    Bn254Scalar as F, Policy, Result, Value, exhausted,
    kernels::arithmetic::reserve,
    numerical::opening::{OpeningQuotientSumShape, column_index},
    numerical::{Call, coset::CosetBatchShape},
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
                | "poly.coset_evaluate_at"
                | "poly.coset_extend"
                | "poly.coset_interpolate"
                | "poly.domain_point"
                | "poly.domain_root"
                | "poly.domain_points"
                | "poly.even_odd_fold"
                | "poly.opening_quotient"
                | "poly.opening_quotient_sum"
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
        "poly.coset_evaluate_at" => {
            let values = v(0)?;
            let shape = CosetBatchShape::new(values.len(), ix(1)?, ix(2)?, 1)?;
            let domain = if shape.width == 0 {
                None
            } else {
                Some(domain(shape.height, f(3)?, p)?)
            };
            let retained = shape.admit(p, 32, available)?;
            let call = Call::new(p, available);
            // The explicit serial provider routine uses one inversion, so
            // admission is independent of the caller's Rayon thread pool.
            call.work(shape.evaluation_work(1, 1)?)?;
            let mut output = call.output(shape.output_len, F::zero(), retained)?;
            if let Some(domain) = domain {
                let point = f(4)?;
                let mut weights = call.scratch(shape.height, F::zero())?;
                // Only the adapter-owned weights are managed. Arkworks 0.6.0
                // allocates height * 32 payload bytes for prefix products
                // internally, scoped to this call and outside managed storage.
                coset_evaluate_at_into(
                    values,
                    domain,
                    point,
                    weights.as_mut(),
                    output.as_mut_slice(),
                );
            }
            output.finish(|values| Ok(Value::Bn254Vector(values.into())))?
        }
        "poly.coset_extend" => {
            let values = v(0)?;
            let shape = CosetBatchShape::new(values.len(), ix(1)?, ix(2)?, ix(5)?)?;
            let domains = if shape.width == 0 {
                None
            } else {
                let input = domain(shape.height, f(3)?, p)?;
                let output = domain(shape.output_height, f(4)?, p)?;
                Some((input, output))
            };
            let retained = shape.admit(p, 32, available)?;
            let call = Call::new(p, available);
            call.work(shape.extension_work(1)?)?;
            // One capacity-preserving Vec serves both transforms per column.
            // Internal Arkworks twiddle/work allocations are provider-owned.
            let workspace = if domains.is_some() {
                shape.height.max(shape.output_height)
            } else {
                0
            };
            let _workspace = call.reserve_workspace::<F>(workspace)?;
            let mut output = call.output(shape.output_len, F::zero(), retained)?;
            if let Some((input_domain, output_domain)) = domains {
                let mut scratch = reserve(workspace)?;
                for (column, destination) in values
                    .chunks_exact(shape.height)
                    .zip(output.as_mut_slice().chunks_exact_mut(shape.output_height))
                {
                    scratch.clear();
                    scratch.extend_from_slice(column);
                    input_domain.ifft_in_place(&mut scratch);
                    if scratch
                        .get(shape.output_height..)
                        .is_some_and(|tail| tail.iter().any(|c| !c.is_zero()))
                    {
                        return Err(refused("coset-coefficient-count"));
                    }
                    scratch.resize(shape.output_height, F::zero());
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
        "poly.opening_quotient_sum" => opening_quotient_sum(args, available, p)?,
        _ => return Err(refused("coset-operation")),
    };
    Ok(vec![result])
}

fn opening_quotient_sum(args: &[Value], available: usize, policy: &Policy) -> Result<Value> {
    let [
        Value::Bn254Vector(values),
        Value::Index(width),
        Value::Index(height),
        Value::Bn254Field(shift),
        Value::Indices(columns),
        Value::Bn254Vector(points),
        Value::Bn254Vector(claims),
        Value::Bn254Vector(weights),
        Value::Bn254Vector(initial),
    ] = args
    else {
        return Err(refused("kernel-operands"));
    };
    let shape = OpeningQuotientSumShape::new(
        values.len(),
        usize::try_from(*width).map_err(|_| exhausted("size-overflow"))?,
        usize::try_from(*height).map_err(|_| exhausted("size-overflow"))?,
        columns.len(),
        [points.len(), claims.len(), weights.len()],
        initial.len(),
    )?;
    shape.admit_inputs(policy, std::mem::size_of::<F>())?;
    let domain = if columns.is_empty() {
        None
    } else {
        let domain = domain(shape.height, *shift, policy)?;
        for (&column, &point) in columns.iter().zip(points.iter()) {
            column_index(column, shape.width).ok_or_else(|| refused("coset-coordinate"))?;
            if domain.evaluate_vanishing_polynomial(point).is_zero() {
                return Err(refused("coset-opening-point"));
            }
        }
        Some(domain)
    };
    let retained = shape.admit(policy, std::mem::size_of::<F>(), available)?;
    let call = Call::new(policy, available);
    call.work(shape.work()?)?;
    let mut output = call.output(shape.height, F::zero(), retained)?;
    if let Some(domain) = domain {
        let mut denominators = call.scratch(shape.height, F::zero())?;
        let mut prefixes = call.scratch(shape.height, F::zero())?;
        output.as_mut_slice().copy_from_slice(initial);
        let mut previous_point = None;
        for (j, &column) in columns.iter().enumerate() {
            let column = usize::try_from(column).map_err(|_| refused("coset-coordinate"))?;
            let offset = column
                .checked_mul(shape.height)
                .ok_or_else(|| exhausted("size-overflow"))?;
            let end = offset
                .checked_add(shape.height)
                .ok_or_else(|| exhausted("size-overflow"))?;
            let selected = &values[offset..end];
            if previous_point == Some(points[j]) {
                for (row, &inverse) in prefixes.as_ref().iter().enumerate() {
                    output.as_mut_slice()[row] +=
                        weights[j] * (selected[row] - claims[j]) * inverse;
                }
                continue;
            }
            for (denominator, x) in denominators.as_mut().iter_mut().zip(domain.elements()) {
                *denominator = x - points[j];
            }
            serial_batch_inverse_into(denominators.as_ref(), prefixes.as_mut(), |row, inverse| {
                output.as_mut_slice()[row] += weights[j] * (selected[row] - claims[j]) * inverse;
            })?;
            previous_point = Some(points[j]);
        }
    } else {
        output.as_mut_slice().copy_from_slice(initial);
    }
    output.finish(|values| Ok(Value::Bn254Vector(values.into())))
}

/// Serial Montgomery inversion with explicitly supplied prefix storage. Unlike
/// Arkworks' allocating convenience routine, both arrays belong to Call and
/// remain accounted for. No provider-private Vec or Rayon scratch is involved.
fn serial_batch_inverse_into(
    denominators: &[F],
    prefixes: &mut [F],
    mut finish: impl FnMut(usize, F),
) -> Result<()> {
    debug_assert_eq!(denominators.len(), prefixes.len());
    let mut product = F::one();
    for (prefix, denominator) in prefixes.iter_mut().zip(denominators) {
        *prefix = product;
        product *= denominator;
    }
    let mut inverse = product
        .inverse()
        .ok_or_else(|| refused("coset-opening-point"))?;
    for (row, (prefix, denominator)) in prefixes.iter_mut().zip(denominators).enumerate().rev() {
        let denominator_inverse = *prefix * inverse;
        inverse *= denominator;
        finish(row, denominator_inverse);
        *prefix = denominator_inverse;
    }
    Ok(())
}

/// Provider arithmetic only; the native adapter has checked geometry and owns
/// the admitted private destination and scoped weights. No transform is used.
fn coset_evaluate_at_into(
    values: &[F],
    domain: Radix2EvaluationDomain<F>,
    point: F,
    weights: &mut [F],
    destination: &mut [F],
) {
    for (row, (x, denominator)) in domain.elements().zip(weights.iter_mut()).enumerate() {
        if point == x {
            for (column, result) in values.chunks_exact(domain.size()).zip(destination) {
                *result = column[row];
            }
            return;
        }
        *denominator = point - x;
    }
    ark_ff::serial_batch_inversion_and_mul(weights, &F::one());
    let scale = domain.evaluate_vanishing_polynomial(point)
        * domain.size_inv
        * domain.offset_inv.pow([domain.size() as u64]);
    for (inverse, x) in weights.iter_mut().zip(domain.elements()) {
        *inverse *= scale * x;
    }
    for (column, result) in values.chunks_exact(domain.size()).zip(destination) {
        *result = column
            .iter()
            .zip(weights.iter())
            .fold(F::zero(), |sum, (value, weight)| sum + *value * *weight);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn opening_args(height: usize) -> Vec<Value> {
        vec![
            Value::Bn254Vector(
                (0..3 * height)
                    .map(|i| F::from((11 * i + 1) as u64))
                    .collect(),
            ),
            Value::Index(3),
            Value::Index(height as u64),
            Value::Bn254Field(F::from(7)),
            Value::Indices(vec![2, 0, 2, 1].into()),
            Value::Bn254Vector(vec![F::zero(), F::from(19), F::from(19), F::zero()].into()),
            Value::Bn254Vector(vec![F::from(5), F::from(9), F::from(15), F::from(13)].into()),
            Value::Bn254Vector(vec![F::from(7), F::zero(), F::from(11), F::from(17)].into()),
            Value::Bn254Vector((0..height).map(|i| F::from((41 + i) as u64)).collect()),
        ]
    }

    fn run_opening(args: &[Value], policy: &Policy, available: usize) -> Result<Vec<Value>> {
        execute("poly.opening_quotient_sum", args, available, policy)
    }

    #[test]
    fn opening_sum_matches_scalar_divisions_and_exact_managed_limits() {
        for (height, repeated) in [1, 4, 16].into_iter().flat_map(|h| [(h, false), (h, true)]) {
            let mut args = opening_args(height);
            if repeated {
                args[5] = Value::Bn254Vector(vec![F::zero(); 4].into());
            }
            let aliases = args.clone();
            let snapshots = [0, 5, 6, 7, 8].map(|i| vector(&args[i]).to_vec());
            let d = domain(height, F::from(7), &Policy::default()).unwrap();
            let values = vector(&args[0]);
            let points = vector(&args[5]);
            let claims = vector(&args[6]);
            let weights = vector(&args[7]);
            let initial = vector(&args[8]);
            let expected: Vec<_> = (0..height)
                .map(|row| {
                    [2, 0, 2, 1]
                        .iter()
                        .enumerate()
                        .fold(initial[row], |sum, (j, column)| {
                            sum + weights[j] * (values[column * height + row] - claims[j])
                                / (d.element(row) - points[j])
                        })
                })
                .collect();
            let shape =
                OpeningQuotientSumShape::new(3 * height, 3, height, 4, [4; 3], height).unwrap();
            let retained = size(height, 32).unwrap();
            let managed = shape.managed_bytes(32).unwrap();
            let work = shape.work().unwrap();
            let exact = Policy {
                max_numerical_work: work,
                max_numerical_bytes: managed,
                ..Policy::default()
            };
            let result = run_opening(&args, &exact, retained).unwrap();
            assert_eq!(result.len(), 1);
            assert_eq!(vector(&result[0]), expected);
            assert_ne!(vector(&result[0]).as_ptr(), initial.as_ptr());
            for (limited, available, expected) in [
                (
                    Policy {
                        max_numerical_work: work - 1,
                        ..exact
                    },
                    retained,
                    "exhausted:numerical-work",
                ),
                (
                    Policy {
                        max_numerical_bytes: managed - 1,
                        ..exact
                    },
                    retained,
                    "exhausted:numerical-bytes",
                ),
                (exact, retained - 1, "exhausted:output-bytes"),
            ] {
                assert_eq!(
                    run_opening(&args, &limited, available).unwrap_err().code,
                    expected
                );
            }
            for (i, snapshot) in [0, 5, 6, 7, 8].into_iter().zip(snapshots) {
                assert_eq!(vector(&args[i]), snapshot);
                assert_eq!(vector(&aliases[i]), snapshot);
            }
        }
    }

    #[test]
    fn opening_sum_validates_every_descriptor_before_admission_or_mutation() {
        let original = opening_args(4);
        let snapshots = [0, 6, 8].map(|i| vector(&original[i]).to_vec());
        let on_domain = domain(4, F::from(7), &Policy::default())
            .unwrap()
            .element(3);
        let policy = Policy {
            max_numerical_work: 0,
            max_numerical_bytes: 0,
            ..Policy::default()
        };
        for (columns, points, expected) in [
            (
                vec![2, 0, 2, 3],
                vec![F::zero(); 4],
                "refused:coset-coordinate",
            ),
            (
                vec![2, 0, 2, 1],
                vec![F::zero(), F::zero(), F::zero(), on_domain],
                "refused:coset-opening-point",
            ),
            (
                vec![2, 0, 2, 3],
                vec![on_domain, F::zero(), F::zero(), F::zero()],
                "refused:coset-opening-point",
            ),
        ] {
            let mut args = original.clone();
            args[4] = Value::Indices(columns.into());
            args[5] = Value::Bn254Vector(points.into());
            args[7] = Value::Bn254Vector(vec![F::zero(); 4].into());
            assert_eq!(run_opening(&args, &policy, 0).unwrap_err().code, expected);
            for (i, snapshot) in [0, 6, 8].into_iter().zip(&snapshots) {
                assert_eq!(vector(&args[i]), snapshot.as_slice());
            }
        }
    }

    #[test]
    fn opening_sum_checks_exact_operands_shapes_and_empty_domains() {
        let policy = Policy::default();
        let original = opening_args(4);
        let mut extra = original.clone();
        extra.push(Value::Index(0));
        for args in [&original[..8], extra.as_slice()] {
            assert_eq!(
                run_opening(args, &policy, usize::MAX).unwrap_err().code,
                "refused:kernel-operands"
            );
        }
        for i in 0..9 {
            let mut args = original.clone();
            args[i] = Value::KoalaBearField(crate::KoalaBear::default());
            assert_eq!(
                run_opening(&args, &policy, usize::MAX).unwrap_err().code,
                "refused:kernel-operands"
            );
        }
        for (index, replacement, expected) in [
            (
                0,
                Value::Bn254Vector(vec![F::one(); 11].into()),
                "refused:coset-batch-shape",
            ),
            (
                5,
                Value::Bn254Vector(vec![F::zero(); 3].into()),
                "refused:coset-opening-shape",
            ),
            (
                6,
                Value::Bn254Vector(vec![F::zero(); 3].into()),
                "refused:coset-opening-shape",
            ),
            (
                7,
                Value::Bn254Vector(vec![F::zero(); 3].into()),
                "refused:coset-opening-shape",
            ),
            (
                8,
                Value::Bn254Vector(vec![F::zero(); 3].into()),
                "refused:coset-opening-shape",
            ),
            (1, Value::Index(u64::MAX), "exhausted:size-overflow"),
            (3, Value::Bn254Field(F::zero()), "refused:coset-zero-shift"),
        ] {
            let mut args = original.clone();
            args[index] = replacement;
            assert_eq!(
                run_opening(&args, &policy, usize::MAX).unwrap_err().code,
                expected
            );
        }
        for (width, height) in [(0, 0), (usize::MAX, 0), (0, 3), (2, 3)] {
            let mut args = vec![
                Value::Bn254Vector(vec![F::one(); width * height].into()),
                Value::Index(width as u64),
                Value::Index(height as u64),
                Value::Bn254Field(F::zero()),
                Value::Indices(vec![].into()),
                Value::Bn254Vector(vec![].into()),
                Value::Bn254Vector(vec![].into()),
                Value::Bn254Vector(vec![].into()),
                Value::Bn254Vector(vec![F::from(7); height].into()),
            ];
            let result = run_opening(&args, &policy, usize::MAX).unwrap();
            assert_eq!(vector(&result[0]), vec![F::from(7); height]);
            if height > 0 {
                assert_ne!(vector(&result[0]).as_ptr(), vector(&args[8]).as_ptr());
            }
            args[8] = Value::Bn254Vector(vec![F::one(); height + 1].into());
            assert_eq!(
                run_opening(&args, &policy, usize::MAX).unwrap_err().code,
                "refused:coset-opening-shape"
            );
        }
        for height in [0, 3] {
            let mut args = original.clone();
            args[0] = Value::Bn254Vector(vec![F::one(); 3 * height].into());
            args[2] = Value::Index(height as u64);
            args[8] = Value::Bn254Vector(vec![F::one(); height].into());
            assert_eq!(
                run_opening(&args, &policy, usize::MAX).unwrap_err().code,
                "refused:coset-size"
            );
        }
        let mut no_columns = original.clone();
        no_columns[0] = Value::Bn254Vector(vec![].into());
        no_columns[1] = Value::Index(0);
        assert_eq!(
            run_opening(&no_columns, &policy, usize::MAX)
                .unwrap_err()
                .code,
            "refused:coset-coordinate"
        );
        let mut args = original;
        args[0] = args[8].clone();
        args[1] = Value::Index(1);
        args[4] = Value::Indices(vec![0; 4].into());
        let snapshot = vector(&args[8]).to_vec();
        assert!(run_opening(&args, &policy, usize::MAX).is_ok());
        assert_eq!(vector(&args[0]), snapshot);
        assert_eq!(vector(&args[8]), snapshot);
    }

    fn point_args(values: Vec<F>, width: u64, height: u64, shift: F, point: F) -> Vec<Value> {
        vec![
            Value::Bn254Vector(values.into()),
            Value::Index(width),
            Value::Index(height),
            Value::Bn254Field(shift),
            Value::Bn254Field(point),
        ]
    }

    fn run_point(args: &[Value], policy: &Policy, available: usize) -> Result<Vec<Value>> {
        execute("poly.coset_evaluate_at", args, available, policy)
    }

    fn horner(coefficients: &[F], point: F) -> F {
        coefficients
            .iter()
            .rev()
            .fold(F::zero(), |sum, c| sum * point + c)
    }

    #[test]
    fn direct_coset_points_match_horner_and_arbitrary_word_interpolants() {
        let policy = Policy::default();
        let shift = F::from(7);
        for width in [0, 1, 4, 16] {
            for height in [1, 2, 8, 32] {
                let domain = domain(height, shift, &policy).unwrap();
                assert!(!domain.evaluate_vanishing_polynomial(F::from(19)).is_zero());
                let points: Vec<_> = [F::zero(), F::from(19)]
                    .into_iter()
                    .chain(domain.elements())
                    .collect();
                for kind in 0..4 {
                    let mut values = Vec::new();
                    let mut coefficients = Vec::new();
                    for col in 0..width {
                        let count = match kind {
                            0 => 0,
                            1 => 1,
                            _ => height,
                        };
                        let coeff: Vec<_> = (0..count)
                            .map(|j| F::from((17 * col + 5 * j + 1) as u64))
                            .collect();
                        let column: Vec<_> = domain
                            .elements()
                            .enumerate()
                            .map(|(row, x)| {
                                if kind == 3 {
                                    F::from((23 * col + row * row + 5 * row + 1) as u64)
                                } else {
                                    horner(&coeff, x)
                                }
                            })
                            .collect();
                        let recovered = execute(
                            "poly.coset_interpolate",
                            &[
                                Value::Bn254Vector(column.clone().into()),
                                Value::Bn254Field(shift),
                            ],
                            usize::MAX,
                            &policy,
                        )
                        .unwrap();
                        let Value::Bn254Polynomial(recovered) = &recovered[0] else {
                            panic!("expected polynomial")
                        };
                        if kind != 3 {
                            assert_eq!(recovered.as_ref(), coeff);
                        }
                        coefficients.push(recovered.to_vec());
                        values.extend(column);
                    }
                    for point in points.iter().copied() {
                        let args =
                            point_args(values.clone(), width as u64, height as u64, shift, point);
                        let alias = args[0].clone();
                        let result = run_point(&args, &policy, usize::MAX).unwrap();
                        let actual = vector(&result[0]);
                        let expected: Vec<_> =
                            coefficients.iter().map(|c| horner(c, point)).collect();
                        assert_eq!(
                            actual, expected,
                            "width={width}, height={height}, kind={kind}"
                        );
                        for row in 0..height {
                            if point == domain.element(row) {
                                for (col, result) in actual.iter().enumerate() {
                                    assert_eq!(*result, values[col * height + row]);
                                }
                            }
                        }
                        if kind == 3 {
                            // Independent Lagrange products check arbitrary words
                            // without using an inverse FFT as the sole oracle.
                            for (column, result) in values.chunks_exact(height).zip(actual) {
                                let mut expected = F::zero();
                                for (row, value) in column.iter().enumerate() {
                                    let x = domain.element(row);
                                    let (mut numerator, mut denominator) = (F::one(), F::one());
                                    for other in 0..height {
                                        if other != row {
                                            let y = domain.element(other);
                                            numerator *= point - y;
                                            denominator *= x - y;
                                        }
                                    }
                                    expected += *value * numerator / denominator;
                                }
                                assert_eq!(*result, expected);
                            }
                        }
                        assert_eq!(vector(&alias), values);
                        if width != 0 {
                            assert_ne!(actual.as_ptr(), vector(&alias).as_ptr());
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn direct_coset_point_managed_limits_and_aliases() {
        let policy = Policy::default();
        let values = vec![F::from(5); 32];
        let args = point_args(values.clone(), 4, 8, F::from(7), F::zero());
        let shape = CosetBatchShape::new(32, 4, 8, 1).unwrap();
        let retained = size(4, 32).unwrap();
        // Adapter weights and result staging, plus reserved final storage.
        // Arkworks' hidden prefix products are outside the managed facade.
        let managed = retained + (4 + 8) * std::mem::size_of::<F>();
        let work = shape.evaluation_work(1, 1).unwrap();
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
            assert_eq!(
                run_point(&args, &policy, available).unwrap_err().code,
                expected
            );
            assert_eq!(vector(&alias), values);
        }
        let exact = Policy {
            max_numerical_work: work,
            max_numerical_bytes: managed,
            ..policy
        };
        assert!(run_point(&args, &exact, retained).is_ok());
        let mut on_domain = args.clone();
        on_domain[4] = Value::Bn254Field(domain(8, F::from(7), &policy).unwrap().element(7));
        assert!(run_point(&on_domain, &exact, retained).is_ok());
    }

    #[test]
    fn direct_coset_point_shape_domain_and_empty_precedence() {
        let policy = Policy::default();
        for (len, width, height, shift, expected) in [
            (1, 0, 0, F::zero(), "refused:coset-batch-shape"),
            (3, 1, 4, F::zero(), "refused:coset-batch-shape"),
            (5, 1, 4, F::one(), "refused:coset-batch-shape"),
            (0, u64::MAX, 2, F::zero(), "exhausted:size-overflow"),
            (0, u64::MAX, 0, F::zero(), "refused:coset-size"),
            (0, 1, 0, F::zero(), "refused:coset-size"),
            (3, 1, 3, F::one(), "refused:coset-size"),
            (2, 1, 2, F::zero(), "refused:coset-zero-shift"),
        ] {
            let args = point_args(vec![F::one(); len], width, height, shift, F::zero());
            let alias = args[0].clone();
            assert_eq!(
                run_point(&args, &policy, usize::MAX).unwrap_err().code,
                expected
            );
            assert_eq!(vector(&alias), vec![F::one(); len]);
            if width == 1 && len as u64 == height {
                let old = execute(
                    "poly.coset_interpolate",
                    &[args[0].clone(), args[3].clone()],
                    usize::MAX,
                    &policy,
                );
                assert_eq!(old.unwrap_err().code, expected);
            }
        }
        for height in [0, 3, u64::MAX] {
            let args = point_args(vec![], 0, height, F::zero(), F::zero());
            let exact = Policy {
                max_numerical_work: 1,
                max_numerical_bytes: 256,
                ..policy
            };
            assert!(vector(&run_point(&args, &exact, 256).unwrap()[0]).is_empty());
            assert_eq!(
                run_point(
                    &args,
                    &Policy {
                        max_numerical_work: 0,
                        ..exact
                    },
                    256
                )
                .unwrap_err()
                .code,
                "exhausted:numerical-work"
            );
            assert_eq!(
                run_point(
                    &args,
                    &Policy {
                        max_numerical_bytes: 255,
                        ..exact
                    },
                    256
                )
                .unwrap_err()
                .code,
                "exhausted:numerical-bytes"
            );
            assert_eq!(
                run_point(&args, &exact, 255).unwrap_err().code,
                "exhausted:output-bytes"
            );
        }
    }

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
    fn direct_large_word_fits_default_admission_with_one_inversion() {
        let policy = Policy::default();
        let args = point_args(vec![F::from(11); 16384], 1, 16384, F::from(7), F::from(19));
        let result = run_point(&args, &policy, usize::MAX).unwrap();
        assert_eq!(vector(&result[0]), &[F::from(11)]);
    }

    #[test]
    fn batch_preflight_checks_resources_and_preserves_aliases() {
        let policy = Policy::default();
        let values = vec![F::one(); 16];
        let args = args(values.clone(), 4, 4, 8);
        let shape = CosetBatchShape::new(16, 4, 4, 8).unwrap();
        let retained = size(32, 32).unwrap();
        let managed = retained + (32 + 8) * std::mem::size_of::<F>();
        let work = shape.extension_work(1).unwrap();
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
