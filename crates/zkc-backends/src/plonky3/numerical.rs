//! Checked native installation of coset kernels. Each backend owns its DFT
//! preparation; no protocol value or transcript state lives in this cache.
use super::polynomial::{self, Domain, Error, Kernels};
use crate::numerical::coset::CosetBatchShape;
use crate::numerical::opening::OpeningQuotientSumShape;
use crate::{
    KoalaBear, KoalaBearExt4, KoalaBearExt8, Policy, Result, Value, exhausted, numerical::Call,
    refused, value::size,
};
use p3_field::ExtensionField;
use zkc_runtime::vm::{Identity, Invocation};

fn failure(error: Error) -> zkc_runtime::vm::BackendError {
    match error {
        Error::SizeOverflow => return exhausted("size-overflow"),
        Error::Allocation => return exhausted("allocation"),
        _ => {}
    }
    refused(match error {
        Error::DomainSize => "coset-size",
        Error::ElementLimit => "coset-element-limit",
        Error::ZeroShift => "coset-zero-shift",
        Error::CoefficientCount => "coset-coefficient-count",
        Error::EvaluationCount => "coset-evaluation-count",
        Error::Coordinate => "coset-coordinate",
        Error::FoldSize => "coset-fold-size",
        Error::PointOnDomain => "coset-opening-point",
        Error::OpeningValue => "polynomial-opening-value",
        Error::BatchShape => "coset-batch-shape",
        Error::OpeningShape => "coset-opening-shape",
        Error::SizeOverflow | Error::Allocation => unreachable!(),
    })
}
trait Family: ExtensionField<KoalaBear> {
    fn field(v: &Value) -> Result<Self>;
    fn vector(v: &Value) -> Result<&[Self]>;
    fn polynomial(v: &Value) -> Result<&[Self]>;
    fn field_value(v: Self) -> Value;
    fn vector_value(v: Vec<Self>) -> Value;
    fn polynomial_value(v: Vec<Self>) -> Value;
}
macro_rules! family {
    ($t:ty, $f:ident, $v:ident, $p:ident) => {
        impl Family for $t {
            fn field(v: &Value) -> Result<Self> {
                if let Value::$f(x) = v {
                    Ok(*x)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn vector(v: &Value) -> Result<&[Self]> {
                if let Value::$v(x) = v {
                    Ok(x)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn polynomial(v: &Value) -> Result<&[Self]> {
                if let Value::$p(x) = v {
                    Ok(x)
                } else {
                    Err(refused("kernel-operands"))
                }
            }
            fn field_value(v: Self) -> Value {
                Value::$f(v)
            }
            fn vector_value(v: Vec<Self>) -> Value {
                Value::$v(v.into())
            }
            fn polynomial_value(v: Vec<Self>) -> Value {
                Value::$p(v.into())
            }
        }
    };
}
family!(
    KoalaBear,
    KoalaBearField,
    KoalaBearVector,
    KoalaBearPolynomial
);
family!(
    KoalaBearExt8,
    KoalaBearExt8Field,
    KoalaBearExt8Vector,
    KoalaBearExt8Polynomial
);
family!(
    KoalaBearExt4,
    KoalaBearExt4Field,
    KoalaBearExt4Vector,
    KoalaBearExt4Polynomial
);

pub(crate) fn apply(
    name: &str,
    field: Option<Identity>,
    args: &[Value],
    invocation: &Invocation<'_>,
    policy: &Policy,
    kernels: &Kernels,
) -> Result<Vec<Value>> {
    if !matches!(
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
    ) {
        return Err(refused("kernel-operands"));
    }
    match field {
        Some(Identity::KoalaBear) => {
            execute::<KoalaBear>(name, args, policy, invocation.max_output_bytes, kernels)
        }
        Some(Identity::KoalaBearExt8) => {
            execute::<KoalaBearExt8>(name, args, policy, invocation.max_output_bytes, kernels)
        }
        Some(Identity::KoalaBearExt4) => {
            execute::<KoalaBearExt4>(name, args, policy, invocation.max_output_bytes, kernels)
        }
        _ => Err(refused("coset-field")),
    }
}
fn execute<E: Family>(
    name: &str,
    args: &[Value],
    policy: &Policy,
    available: usize,
    kernels: &Kernels,
) -> Result<Vec<Value>> {
    let arg = |i| args.get(i).ok_or_else(|| refused("kernel-operands"));
    let field = |i| E::field(arg(i)?);
    let vector = |i| E::vector(arg(i)?);
    let index = |i| match arg(i)? {
        Value::Index(n) => usize::try_from(*n).map_err(|_| refused("index-bounds")),
        _ => Err(refused("kernel-operands")),
    };
    let width = std::mem::size_of::<E>();
    let domain =
        |n, shift| Domain::new(n, shift, policy.max_table_elements.min(1 << 20)).map_err(failure);
    let allocation = |n: usize| -> Result<()> {
        policy.vector_width(n, width)?;
        policy.output(size(n, width)?, available)?;
        // Conservative DFT/batch-inversion temporary budget, including extension coordinates.
        policy.output(
            size(n, width)?
                .checked_mul(8)
                .ok_or_else(|| exhausted("size-overflow"))?,
            usize::MAX,
        )
    };
    let output = match name {
        "poly.domain_root" => {
            policy.output(512, available)?;
            E::field_value(domain(index(0)?, E::ONE)?.generator())
        }
        "poly.domain_point" => {
            policy.output(512, available)?;
            E::field_value(
                domain(index(1)?, field(0)?)?
                    .point(index(2)?)
                    .map_err(failure)?,
            )
        }
        "poly.domain_points" => {
            let d = domain(index(1)?, field(0)?)?;
            allocation(d.size())?;
            let mut out = crate::kernels::arithmetic::reserve(d.size())?;
            let mut x = d.shift();
            for _ in 0..d.size() {
                out.push(x);
                x *= d.base_generator();
            }
            E::vector_value(out)
        }
        "poly.coset_evaluate" => {
            let p = E::polynomial(arg(0)?)?;
            let d = domain(index(2)?, field(1)?)?;
            if p.len() > d.size() {
                return Err(failure(Error::CoefficientCount));
            }
            allocation(d.size())?;
            E::vector_value(kernels.evaluate(p, d).map_err(failure)?)
        }
        "poly.coset_interpolate" => {
            let v = vector(0)?;
            let d = domain(v.len(), field(1)?)?;
            allocation(v.len())?;
            E::polynomial_value(kernels.interpolate(v, d).map_err(failure)?)
        }
        "poly.coset_evaluate_at" => {
            let values = vector(0)?;
            let shape = CosetBatchShape::new(values.len(), index(1)?, index(2)?, 1)?;
            let domain = if shape.width == 0 {
                None
            } else {
                Some(domain(shape.height, field(3)?)?)
            };
            let retained = shape.admit(policy, width, available)?;
            let call = Call::new(policy, available);
            call.work(shape.evaluation_work(E::DIMENSION, 2)?)?;
            let mut output = call.output(shape.output_len, E::ZERO, retained)?;
            if let Some(domain) = domain {
                let point = field(4)?;
                let mut denominators = call.scratch(shape.height, E::ZERO)?;
                let mut weights = call.scratch(shape.height, E::ZERO)?;
                polynomial::coset_evaluate_at_into(
                    values,
                    domain,
                    point,
                    denominators.as_mut(),
                    weights.as_mut(),
                    output.as_mut_slice(),
                )
                .map_err(failure)?;
            }
            output.finish(|values| Ok(E::vector_value(values)))?
        }
        "poly.coset_extend" => {
            let values = vector(0)?;
            let shape = CosetBatchShape::new(values.len(), index(1)?, index(2)?, index(5)?)?;
            // Empty batches do not inspect unused shifts or domains.
            let domains = if shape.width == 0 {
                None
            } else {
                let input = domain(shape.height, field(3)?)?;
                let output = domain(shape.output_height, field(4)?)?;
                Some((input, output))
            };
            let retained = shape.admit(policy, width, available)?;
            let call = Call::new(policy, available);
            call.work(shape.extension_work(E::DIMENSION)?)?;
            // Admit every adapter-owned Vec before allocating even the result.
            // The pinned P3 transforms reuse their owned dense matrices; input
            // coefficients overlap with output scaling. Twiddle caches are
            // provider-owned and outside this payload scope.
            let workspace = if domains.is_some() {
                shape
                    .input_len
                    .checked_add(shape.output_len)
                    .ok_or_else(|| exhausted("size-overflow"))?
            } else {
                0
            };
            let _workspace = call.reserve_workspace::<E>(workspace)?;
            let mut output = call.output(shape.output_len, E::ZERO, retained)?;
            if let Some((input_domain, output_domain)) = domains {
                kernels
                    .coset_extend_into(
                        values,
                        shape.width,
                        input_domain,
                        output_domain,
                        output.as_mut_slice(),
                    )
                    .map_err(failure)?;
            }
            output.finish(|values| Ok(E::vector_value(values)))?
        }
        "poly.even_odd_fold" => {
            let v = vector(0)?;
            let d = domain(v.len(), field(1)?)?;
            d.folded().map_err(failure)?;
            allocation(v.len() / 2)?;
            E::vector_value(polynomial::fold(v, d, field(2)?).map_err(failure)?)
        }
        "poly.opening_quotient" => {
            let v = vector(0)?;
            let d = domain(v.len(), field(1)?)?;
            allocation(v.len())?;
            let point = field(2)?;
            let value = field(3)?;
            let quotient = polynomial::OpeningQuotient::new(v, d, point, value).map_err(failure)?;
            let call = Call::new(policy, available);
            call.work(opening_quotient_work(v.len())?)?;
            let mut output = call.output(v.len(), E::ZERO, size(v.len(), width)?)?;
            {
                let mut denominators = call.scratch(v.len(), E::ZERO)?;
                quotient
                    .write_into(denominators.as_mut(), output.as_mut_slice())
                    .map_err(failure)?;
            }
            output.finish(|values| Ok(E::vector_value(values)))?
        }
        "poly.opening_quotient_sum" => opening_quotient_sum::<E>(args, policy, available)?,
        _ => return Err(refused("coset-operation")),
    };
    Ok(vec![output])
}

fn opening_quotient_sum<E: Family>(
    args: &[Value],
    policy: &Policy,
    available: usize,
) -> Result<Value> {
    let [
        values,
        Value::Index(width),
        Value::Index(height),
        shift,
        Value::Indices(columns),
        points,
        claims,
        weights,
        initial,
    ] = args
    else {
        return Err(refused("kernel-operands"));
    };
    // All operands retain their exact nominal field, including an unused shift.
    let values = E::vector(values)?;
    let shift = E::field(shift)?;
    let points = E::vector(points)?;
    let claims = E::vector(claims)?;
    let weights = E::vector(weights)?;
    let initial = E::vector(initial)?;
    let shape = OpeningQuotientSumShape::new(
        values.len(),
        usize::try_from(*width).map_err(|_| exhausted("size-overflow"))?,
        usize::try_from(*height).map_err(|_| exhausted("size-overflow"))?,
        columns.len(),
        [points.len(), claims.len(), weights.len()],
        initial.len(),
    )?;
    shape.admit_inputs(policy, std::mem::size_of::<E>())?;
    let quotient = if columns.is_empty() {
        None
    } else {
        let domain = Domain::new(shape.height, shift, policy.max_table_elements.min(1 << 20))
            .map_err(failure)?;
        Some(
            polynomial::OpeningQuotientSum::new(
                values,
                shape.width,
                domain,
                columns,
                points,
                claims,
                weights,
            )
            .map_err(failure)?,
        )
    };
    // The complete descriptor list is valid before charging execution work,
    // allocating any result/workspace, or copying initial.
    let retained = shape.admit(policy, std::mem::size_of::<E>(), available)?;
    let call = Call::new(policy, available);
    call.work(shape.work()?)?;
    let mut output = call.output(shape.height, E::ZERO, retained)?;
    if let Some(quotient) = quotient {
        let mut denominators = call.scratch(shape.height, E::ZERO)?;
        let mut prefixes = call.scratch(shape.height, E::ZERO)?;
        quotient
            .write_into(
                initial,
                denominators.as_mut(),
                prefixes.as_mut(),
                output.as_mut_slice(),
            )
            .map_err(failure)?;
    } else {
        output.as_mut_slice().copy_from_slice(initial);
    }
    output.finish(|values| Ok(E::vector_value(values)))
}

fn opening_quotient_work(len: usize) -> Result<u64> {
    // Sixteen units per element cover initialized output/scratch, denominator
    // generation, prefix products, and the reverse quotient
    // pass. A unit is one native field operation or bounded scalar-loop step.
    // The fixed allowance covers two <=64-bit membership powers (<=256 field
    // operations) and the pinned KoalaBear degree-1/4/8 inversion routines:
    // finite quartic/octic formulas and the base field's bounded 31-bit GCD.
    // This is a work bound, not elapsed time or a constant-time guarantee.
    u64::try_from(len)
        .ok()
        .and_then(|n| n.checked_mul(16))
        .and_then(|n| n.checked_add(4096))
        .ok_or_else(|| exhausted("numerical-work"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    fn opening_args<E: Family>() -> Vec<Value> {
        let element =
            |i: usize| E::from_basis_coefficients_fn(|j| KoalaBear::from_usize(11 * i + 7 * j + 1));
        vec![
            E::vector_value((0..12).map(element).collect()),
            Value::Index(3),
            Value::Index(4),
            E::field_value(element(3)),
            Value::Indices(vec![2, 0, 2].into()),
            E::vector_value(vec![E::ZERO, element(19), E::ZERO]),
            E::vector_value(vec![element(5), element(9), element(15)]),
            E::vector_value(vec![element(7), E::ZERO, element(11)]),
            E::vector_value((0..4).map(|i| element(41 + i)).collect()),
        ]
    }

    fn run_opening<E: Family>(
        args: &[Value],
        policy: &Policy,
        available: usize,
    ) -> Result<Vec<Value>> {
        execute::<E>(
            "poly.opening_quotient_sum",
            args,
            policy,
            available,
            &Kernels::default(),
        )
    }

    fn opening_native_checks<E: Family>(repeated: bool) {
        let mut args = opening_args::<E>();
        if repeated {
            args[5] = E::vector_value(vec![E::ZERO; 3]);
        }
        let aliases = args.clone();
        let snapshots = [0, 5, 6, 7, 8].map(|i| E::vector(&args[i]).unwrap().to_vec());
        let values = E::vector(&args[0]).unwrap();
        let points = E::vector(&args[5]).unwrap();
        let claims = E::vector(&args[6]).unwrap();
        let weights = E::vector(&args[7]).unwrap();
        let initial = E::vector(&args[8]).unwrap();
        let domain = Domain::new(4, E::field(&args[3]).unwrap(), 4).unwrap();
        let expected: Vec<_> = (0..4)
            .map(|row| {
                [2, 0, 2]
                    .iter()
                    .enumerate()
                    .fold(initial[row], |sum, (j, column)| {
                        sum + weights[j] * (values[column * 4 + row] - claims[j])
                            / (domain.point(row).unwrap() - points[j])
                    })
            })
            .collect();
        let shape = OpeningQuotientSumShape::new(12, 3, 4, 3, [3; 3], 4).unwrap();
        let bytes = std::mem::size_of::<E>();
        let retained = size(4, bytes).unwrap();
        let managed = shape.managed_bytes(bytes).unwrap();
        let work = shape.work().unwrap();
        let policy = Policy {
            max_numerical_work: work,
            max_numerical_bytes: managed,
            ..Policy::default()
        };
        let result = run_opening::<E>(&args, &policy, retained).unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(E::vector(&result[0]).unwrap(), expected);
        assert_ne!(E::vector(&result[0]).unwrap().as_ptr(), initial.as_ptr());
        for (limited, available, expected) in [
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
            (policy, retained - 1, "exhausted:output-bytes"),
            (
                Policy {
                    max_table_elements: 11,
                    ..policy
                },
                retained,
                "exhausted:element-limit",
            ),
        ] {
            assert_eq!(
                run_opening::<E>(&args, &limited, available)
                    .unwrap_err()
                    .code,
                expected
            );
        }
        for (i, snapshot) in [0, 5, 6, 7, 8].into_iter().zip(snapshots) {
            assert_eq!(E::vector(&args[i]).unwrap(), snapshot);
            assert_eq!(E::vector(&aliases[i]).unwrap(), snapshot);
        }
    }

    #[test]
    fn native_opening_sums_preserve_coordinates_aliases_and_exact_limits() {
        for repeated in [false, true] {
            opening_native_checks::<KoalaBear>(repeated);
            opening_native_checks::<KoalaBearExt4>(repeated);
            opening_native_checks::<KoalaBearExt8>(repeated);
        }
    }

    #[test]
    fn native_opening_sum_validates_the_final_descriptor_before_admission() {
        let policy = Policy {
            max_numerical_work: 0,
            max_numerical_bytes: 0,
            ..Policy::default()
        };
        let original = opening_args::<KoalaBearExt8>();
        let snapshots = [0, 6, 8].map(|i| KoalaBearExt8::vector(&original[i]).unwrap().to_vec());
        let domain = Domain::new(4, KoalaBearExt8::field(&original[3]).unwrap(), 4).unwrap();
        for (columns, points, expected) in [
            (
                vec![2, 0, 3],
                vec![KoalaBearExt8::ZERO; 3],
                "refused:coset-coordinate",
            ),
            (
                vec![2, 0, 2],
                vec![
                    KoalaBearExt8::ZERO,
                    KoalaBearExt8::ZERO,
                    domain.point(3).unwrap(),
                ],
                "refused:coset-opening-point",
            ),
            (
                vec![2, 0, 3],
                vec![
                    domain.point(0).unwrap(),
                    KoalaBearExt8::ZERO,
                    KoalaBearExt8::ZERO,
                ],
                "refused:coset-opening-point",
            ),
        ] {
            let mut args = original.clone();
            args[4] = Value::Indices(columns.into());
            args[5] = KoalaBearExt8::vector_value(points);
            args[7] = KoalaBearExt8::vector_value(vec![KoalaBearExt8::ZERO; 3]);
            assert_eq!(
                run_opening::<KoalaBearExt8>(&args, &policy, 0)
                    .unwrap_err()
                    .code,
                expected
            );
            for (i, snapshot) in [0, 6, 8].into_iter().zip(&snapshots) {
                assert_eq!(
                    KoalaBearExt8::vector(&args[i]).unwrap(),
                    snapshot.as_slice()
                );
            }
        }
    }

    #[test]
    fn native_opening_sum_exact_operands_shapes_and_empty_semantics() {
        let policy = Policy::default();
        let original = opening_args::<KoalaBear>();
        let mut extra = original.clone();
        extra.push(Value::Index(0));
        for args in [&original[..8], extra.as_slice()] {
            assert_eq!(
                run_opening::<KoalaBear>(args, &policy, usize::MAX)
                    .unwrap_err()
                    .code,
                "refused:kernel-operands"
            );
        }
        for i in 0..9 {
            let mut args = original.clone();
            args[i] = Value::Bn254Field(crate::Bn254Scalar::from(1));
            assert_eq!(
                run_opening::<KoalaBear>(&args, &policy, usize::MAX)
                    .unwrap_err()
                    .code,
                "refused:kernel-operands"
            );
        }
        for (index, replacement, expected) in [
            (
                0,
                KoalaBear::vector_value(vec![KoalaBear::ONE; 11]),
                "refused:coset-batch-shape",
            ),
            (
                5,
                KoalaBear::vector_value(vec![KoalaBear::ZERO; 2]),
                "refused:coset-opening-shape",
            ),
            (
                6,
                KoalaBear::vector_value(vec![KoalaBear::ZERO; 2]),
                "refused:coset-opening-shape",
            ),
            (
                7,
                KoalaBear::vector_value(vec![KoalaBear::ZERO; 2]),
                "refused:coset-opening-shape",
            ),
            (
                8,
                KoalaBear::vector_value(vec![KoalaBear::ZERO; 3]),
                "refused:coset-opening-shape",
            ),
            (1, Value::Index(u64::MAX), "exhausted:size-overflow"),
            (
                3,
                KoalaBear::field_value(KoalaBear::ZERO),
                "refused:coset-zero-shift",
            ),
        ] {
            let mut args = original.clone();
            args[index] = replacement;
            assert_eq!(
                run_opening::<KoalaBear>(&args, &policy, usize::MAX)
                    .unwrap_err()
                    .code,
                expected
            );
        }
        for (width, height) in [(0, 0), (usize::MAX, 0), (0, 3), (2, 3)] {
            let initial = vec![KoalaBear::from_usize(7); height];
            let mut args = vec![
                KoalaBear::vector_value(vec![KoalaBear::ONE; width * height]),
                Value::Index(width as u64),
                Value::Index(height as u64),
                KoalaBear::field_value(KoalaBear::ZERO),
                Value::Indices(vec![].into()),
                KoalaBear::vector_value(vec![]),
                KoalaBear::vector_value(vec![]),
                KoalaBear::vector_value(vec![]),
                KoalaBear::vector_value(initial.clone()),
            ];
            let result = run_opening::<KoalaBear>(&args, &policy, usize::MAX).unwrap();
            assert_eq!(KoalaBear::vector(&result[0]).unwrap(), initial);
            if height > 0 {
                assert_ne!(
                    KoalaBear::vector(&result[0]).unwrap().as_ptr(),
                    KoalaBear::vector(&args[8]).unwrap().as_ptr()
                );
            }
            args[8] = KoalaBear::vector_value(vec![KoalaBear::ONE; height + 1]);
            assert_eq!(
                run_opening::<KoalaBear>(&args, &policy, usize::MAX)
                    .unwrap_err()
                    .code,
                "refused:coset-opening-shape"
            );
        }
        // A nonempty descriptor list still needs a nonempty valid domain.
        for height in [0, 3] {
            let mut args = original.clone();
            args[0] = KoalaBear::vector_value(vec![KoalaBear::ONE; 3 * height]);
            args[2] = Value::Index(height as u64);
            args[8] = KoalaBear::vector_value(vec![KoalaBear::ONE; height]);
            assert_eq!(
                run_opening::<KoalaBear>(&args, &policy, usize::MAX)
                    .unwrap_err()
                    .code,
                "refused:coset-size"
            );
        }
        let mut no_columns = original.clone();
        no_columns[0] = KoalaBear::vector_value(vec![]);
        no_columns[1] = Value::Index(0);
        assert_eq!(
            run_opening::<KoalaBear>(&no_columns, &policy, usize::MAX)
                .unwrap_err()
                .code,
            "refused:coset-coordinate"
        );
        // The same immutable owner may supply both values and initial.
        let mut args = original;
        args[0] = args[8].clone();
        args[1] = Value::Index(1);
        args[4] = Value::Indices(vec![0, 0, 0].into());
        let snapshot = KoalaBear::vector(&args[8]).unwrap().to_vec();
        assert!(run_opening::<KoalaBear>(&args, &policy, usize::MAX).is_ok());
        assert_eq!(KoalaBear::vector(&args[0]).unwrap(), snapshot);
        assert_eq!(KoalaBear::vector(&args[8]).unwrap(), snapshot);
    }

    fn point_args<E: Family>(
        values: Vec<E>,
        width: u64,
        height: u64,
        shift: E,
        point: E,
    ) -> Vec<Value> {
        vec![
            E::vector_value(values),
            Value::Index(width),
            Value::Index(height),
            E::field_value(shift),
            E::field_value(point),
        ]
    }

    fn run_point<E: Family>(
        args: &[Value],
        policy: &Policy,
        available: usize,
    ) -> Result<Vec<Value>> {
        execute::<E>(
            "poly.coset_evaluate_at",
            args,
            policy,
            available,
            &Kernels::default(),
        )
    }

    fn point_evaluation_checks<E: Family>() {
        let policy = Policy::default();
        let element =
            |i: usize| E::from_basis_coefficients_fn(|j| KoalaBear::from_usize(11 * i + 7 * j + 1));
        let shift = element(3);
        for width in [0, 1, 4, 16] {
            for height in [1, 2, 8, 32] {
                let domain = Domain::new(height, shift, 32).unwrap();
                assert!(!domain.contains(element(19)));
                let points: Vec<_> = [E::ZERO, element(19)]
                    .into_iter()
                    .chain((0..height).map(|row| domain.point(row).unwrap()))
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
                        let coeff: Vec<_> = (0..count).map(|j| element(17 * col + j)).collect();
                        // Known coefficients use direct Horner evaluation, with
                        // no FFT in either the input construction or oracle.
                        let column: Vec<_> = (0..height)
                            .map(|row| {
                                if kind == 3 {
                                    element(23 * col + row * row + 5 * row)
                                } else {
                                    polynomial::evaluate_at(&coeff, domain.point(row).unwrap())
                                }
                            })
                            .collect();
                        let recovered = execute::<E>(
                            "poly.coset_interpolate",
                            &[E::vector_value(column.clone()), E::field_value(shift)],
                            &policy,
                            usize::MAX,
                            &Kernels::default(),
                        )
                        .unwrap();
                        let recovered = E::polynomial(&recovered[0]).unwrap().to_vec();
                        if kind != 3 {
                            assert_eq!(recovered, coeff);
                        }
                        coefficients.push(recovered);
                        values.extend(column);
                    }
                    for point in points.iter().copied() {
                        let args =
                            point_args(values.clone(), width as u64, height as u64, shift, point);
                        let alias = args[0].clone();
                        let result = run_point::<E>(&args, &policy, usize::MAX).unwrap();
                        let actual = E::vector(&result[0]).unwrap();
                        let expected: Vec<_> = coefficients
                            .iter()
                            .map(|coeff| polynomial::evaluate_at(coeff, point))
                            .collect();
                        assert_eq!(
                            actual, expected,
                            "width={width}, height={height}, kind={kind}"
                        );
                        for row in 0..height {
                            if point == domain.point(row).unwrap() {
                                for (col, result) in actual.iter().enumerate() {
                                    assert_eq!(*result, values[col * height + row]);
                                }
                            }
                        }
                        if kind == 3 {
                            // Independent Lagrange products also check arbitrary
                            // words without relying on provider interpolation.
                            for (column, result) in values.chunks_exact(height).zip(actual) {
                                let mut expected = E::ZERO;
                                for (row, value) in column.iter().enumerate() {
                                    let x = domain.point(row).unwrap();
                                    let (mut numerator, mut denominator) = (E::ONE, E::ONE);
                                    for other in 0..height {
                                        if other != row {
                                            let y = domain.point(other).unwrap();
                                            numerator *= point - y;
                                            denominator *= x - y;
                                        }
                                    }
                                    expected += *value * numerator / denominator;
                                }
                                assert_eq!(*result, expected);
                            }
                        }
                        assert_eq!(E::vector(&alias).unwrap(), values);
                        if width != 0 {
                            assert_ne!(actual.as_ptr(), E::vector(&alias).unwrap().as_ptr());
                        }
                    }
                }
            }
        }

        // A trace with 1,024 rows and blowup four reaches a 4,096-point
        // opening domain. It must fit default work admission, including Ext8.
        for width in [1, 4] {
            let values = vec![element(5); 4096 * width];
            let args = point_args(values, width as u64, 4096, shift, element(19));
            let result = run_point::<E>(&args, &policy, usize::MAX).unwrap();
            assert_eq!(E::vector(&result[0]).unwrap(), vec![element(5); width]);
        }

        let values = vec![element(5); 32];
        let args = point_args(values.clone(), 4, 8, shift, E::ZERO);
        let element_bytes = std::mem::size_of::<E>();
        let retained = size(4, element_bytes).unwrap();
        let managed = retained + (4 + 2 * 8) * element_bytes;
        let shape = CosetBatchShape::new(32, 4, 8, 1).unwrap();
        let work = shape.evaluation_work(E::DIMENSION, 2).unwrap();
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
                run_point::<E>(&args, &policy, available).unwrap_err().code,
                expected
            );
            assert_eq!(E::vector(&alias).unwrap(), values);
        }
        let exact = Policy {
            max_numerical_work: work,
            max_numerical_bytes: managed,
            ..policy
        };
        assert!(run_point::<E>(&args, &exact, retained).is_ok());
        let mut on_domain = args.clone();
        on_domain[4] = E::field_value(Domain::new(8, shift, 8).unwrap().point(7).unwrap());
        assert!(run_point::<E>(&on_domain, &exact, retained).is_ok());
    }

    #[test]
    fn direct_coset_points_match_horner_and_arbitrary_word_interpolants() {
        point_evaluation_checks::<KoalaBear>();
        point_evaluation_checks::<KoalaBearExt4>();
        point_evaluation_checks::<KoalaBearExt8>();
    }

    fn point_refusal_checks<E: Family>() {
        let policy = Policy::default();
        for (len, width, height, shift, expected) in [
            (1, 0, 0, E::ZERO, "refused:coset-batch-shape"),
            (3, 1, 4, E::ZERO, "refused:coset-batch-shape"),
            (5, 1, 4, E::ONE, "refused:coset-batch-shape"),
            (0, u64::MAX, 2, E::ZERO, "exhausted:size-overflow"),
            (0, u64::MAX, 0, E::ZERO, "refused:coset-size"),
            (0, 1, 0, E::ZERO, "refused:coset-size"),
            (3, 1, 3, E::ONE, "refused:coset-size"),
            (2, 1, 2, E::ZERO, "refused:coset-zero-shift"),
        ] {
            let args = point_args(vec![E::ONE; len], width, height, shift, E::ZERO);
            let alias = args[0].clone();
            assert_eq!(
                run_point::<E>(&args, &policy, usize::MAX).unwrap_err().code,
                expected
            );
            assert_eq!(E::vector(&alias).unwrap(), vec![E::ONE; len]);
            if width == 1 && len as u64 == height {
                let old = execute::<E>(
                    "poly.coset_interpolate",
                    &[args[0].clone(), args[3].clone()],
                    &policy,
                    usize::MAX,
                    &Kernels::default(),
                );
                assert_eq!(old.unwrap_err().code, expected);
            }
        }
        for height in [0, 3, u64::MAX] {
            let args = point_args::<E>(vec![], 0, height, E::ZERO, E::ZERO);
            let exact = Policy {
                max_numerical_work: 1,
                max_numerical_bytes: 256,
                ..policy
            };
            assert!(
                E::vector(&run_point::<E>(&args, &exact, 256).unwrap()[0])
                    .unwrap()
                    .is_empty()
            );
            assert_eq!(
                run_point::<E>(
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
                run_point::<E>(
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
                run_point::<E>(&args, &exact, 255).unwrap_err().code,
                "exhausted:output-bytes"
            );
        }
    }

    #[test]
    fn direct_coset_point_shape_domain_and_empty_precedence() {
        point_refusal_checks::<KoalaBear>();
        point_refusal_checks::<KoalaBearExt4>();
        point_refusal_checks::<KoalaBearExt8>();
    }

    fn batch_args<E: Family>(values: Vec<E>, width: u64, height: u64, size: u64) -> Vec<Value> {
        vec![
            E::vector_value(values),
            Value::Index(width),
            Value::Index(height),
            E::field_value(E::from_basis_coefficients_fn(|j| {
                KoalaBear::from_usize(3 + j)
            })),
            E::field_value(E::from_basis_coefficients_fn(|j| {
                KoalaBear::from_usize(7 + 2 * j)
            })),
            Value::Index(size),
        ]
    }

    fn run<E: Family>(args: &[Value], policy: &Policy, available: usize) -> Result<Vec<Value>> {
        execute::<E>(
            "poly.coset_extend",
            args,
            policy,
            available,
            &Kernels::default(),
        )
    }

    fn native_batch_checks<E: Family>() {
        let policy = Policy::default();
        let kernels = Kernels::default();
        let args = batch_args::<E>(vec![], 1, 4, 2);
        let input = Domain::new(4, E::field(&args[3]).unwrap(), 16).unwrap();
        let output = Domain::new(2, E::field(&args[4]).unwrap(), 16).unwrap();
        for coefficients in [vec![], vec![E::ONE], vec![E::ONE, E::ONE]] {
            let values = kernels.evaluate(&coefficients, input).unwrap();
            let args = batch_args(values.clone(), 1, 4, 2);
            let alias = args[0].clone();
            let result = run::<E>(&args, &policy, usize::MAX).unwrap();
            assert_eq!(
                E::vector(&result[0]).unwrap(),
                kernels.evaluate(&coefficients, output).unwrap()
            );
            assert_eq!(E::vector(&alias).unwrap(), values);
            assert_ne!(
                E::vector(&result[0]).unwrap().as_ptr(),
                E::vector(&alias).unwrap().as_ptr()
            );
        }

        let low = kernels.evaluate(&[E::ONE, E::ONE], input).unwrap();
        let high = kernels
            .evaluate(&[E::ZERO, E::ZERO, E::ONE], input)
            .unwrap();
        for values in [high.clone(), [low.clone(), high].concat()] {
            let args = batch_args(values.clone(), (values.len() / 4) as u64, 4, 2);
            let alias = args[0].clone();
            assert_eq!(
                run::<E>(&args, &policy, usize::MAX).unwrap_err().code,
                "refused:coset-coefficient-count"
            );
            assert_eq!(E::vector(&alias).unwrap(), values);
        }

        // Managed limits include final Arc overlap and provider-consumed Vecs.
        let args = batch_args(low.clone(), 1, 4, 8);
        let shape = CosetBatchShape::new(4, 1, 4, 8).unwrap();
        let retained = size(8, std::mem::size_of::<E>()).unwrap();
        let managed =
            retained + (8 + shape.input_len + shape.output_len) * std::mem::size_of::<E>();
        let work = shape.extension_work(E::DIMENSION).unwrap();
        for (policy, available, expected) in [
            (
                Policy {
                    max_numerical_work: 0,
                    ..policy
                },
                retained,
                "exhausted:numerical-work",
            ),
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
        ] {
            let alias = args[0].clone();
            assert_eq!(
                run::<E>(&args, &policy, available).unwrap_err().code,
                expected
            );
            assert_eq!(E::vector(&alias).unwrap(), low);
        }
        let exact = Policy {
            max_numerical_bytes: managed,
            max_numerical_work: work,
            ..policy
        };
        assert!(run::<E>(&args, &exact, retained).is_ok());

        // Individual domains fit, but the whole input/output vector must fit too.
        for (height, size) in [(4, 2), (2, 4)] {
            let args = batch_args(vec![E::ZERO; 4 * height], 4, height as u64, size as u64);
            let small = Policy {
                max_table_elements: 8,
                ..policy
            };
            assert_eq!(
                run::<E>(&args, &small, usize::MAX).unwrap_err().code,
                "exhausted:element-limit"
            );
        }
    }

    #[test]
    fn native_batch_scopes_preserve_all_installed_coordinates_and_aliases() {
        native_batch_checks::<KoalaBear>();
        native_batch_checks::<KoalaBearExt4>();
        native_batch_checks::<KoalaBearExt8>();
    }

    #[test]
    fn native_batch_shape_empty_and_domain_refusal_precedence() {
        let policy = Policy::default();
        for (values, width, height, size, expected) in [
            (vec![KoalaBear::ONE], 0, 0, 0, "refused:coset-batch-shape"),
            (
                vec![KoalaBear::ONE; 3],
                1,
                4,
                2,
                "refused:coset-batch-shape",
            ),
            (
                vec![KoalaBear::ONE; 5],
                1,
                4,
                2,
                "refused:coset-batch-shape",
            ),
            (vec![], u64::MAX, 2, 2, "exhausted:size-overflow"),
            (vec![], u64::MAX, 0, 2, "exhausted:size-overflow"),
            (vec![], 1, 0, 0, "refused:coset-size"),
            (vec![KoalaBear::ONE; 4], 1, 4, 3, "refused:coset-size"),
        ] {
            let args = batch_args(values, width, height, size);
            assert_eq!(
                run::<KoalaBear>(&args, &policy, usize::MAX)
                    .unwrap_err()
                    .code,
                expected
            );
        }
        let mut empty = batch_args::<KoalaBear>(vec![], 0, u64::MAX, u64::MAX);
        empty[3] = Value::KoalaBearField(KoalaBear::ZERO);
        empty[4] = Value::KoalaBearField(KoalaBear::ZERO);
        assert!(
            KoalaBear::vector(&run::<KoalaBear>(&empty, &policy, usize::MAX).unwrap()[0])
                .unwrap()
                .is_empty()
        );

        let mut args = batch_args(vec![KoalaBear::ONE; 4], 1, 4, 3);
        args[3] = Value::KoalaBearField(KoalaBear::ZERO);
        assert_eq!(
            run::<KoalaBear>(&args, &policy, usize::MAX)
                .unwrap_err()
                .code,
            "refused:coset-zero-shift"
        );
        args[3] = Value::KoalaBearField(KoalaBear::ONE);
        args[5] = Value::Index(4);
        args[4] = Value::KoalaBearField(KoalaBear::ZERO);
        assert_eq!(
            run::<KoalaBear>(&args, &policy, usize::MAX)
                .unwrap_err()
                .code,
            "refused:coset-zero-shift"
        );
    }
}
