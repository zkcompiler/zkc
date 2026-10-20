//! Checked native installation of coset kernels. Each backend owns its DFT
//! preparation; no protocol value or transcript state lives in this cache.
use super::polynomial::{self, Domain, Error, Kernels};
use crate::numerical::transform::CosetBatch;
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
            | "poly.coset_extend"
            | "poly.coset_interpolate"
            | "poly.domain_point"
            | "poly.domain_root"
            | "poly.domain_points"
            | "poly.even_odd_fold"
            | "poly.opening_quotient"
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
        "poly.coset_extend" => {
            let values = vector(0)?;
            let shape = CosetBatch::new(values.len(), index(1)?, index(2)?, index(5)?)?;
            // Empty batches do not inspect unused shifts or domains.
            let domains = if shape.width == 0 {
                None
            } else {
                let input = domain(shape.height, field(3)?)?;
                let output = domain(shape.size, field(4)?)?;
                Some((input, output))
            };
            policy.vector_width(shape.input_len, width)?;
            policy.vector_width(shape.output_len, width)?;
            let retained = size(shape.output_len, width)?;
            policy.output(retained, available)?;
            let call = Call::new(policy, available);
            call.work(shape.work(E::DIMENSION)?)?;
            // Admit every adapter-owned Vec before allocating even the result.
            // P3's internal cached twiddles are outside this payload scope.
            let workspace = if domains.is_some() {
                shape.p3_workspace()?
            } else {
                0
            };
            let _workspace = call.transform_workspace::<E>(workspace)?;
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
        _ => return Err(refused("coset-operation")),
    };
    Ok(vec![output])
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

/// Independent native port facts, also used for exact implementation assembly.
pub(crate) const CONTRACTS: &[crate::bindings::Contract] = {
    use crate::bindings::poly;
    use zkc_runtime::vm::{AttributeRule, Type::*};
    &[
        poly::operation(
            "poly.coset_extend",
            &[Vector, Index, Index, Field, Field, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/poly.coset_extend", "plonky3/poly.coset_extend"]),
        poly::operation(
            "poly.coset_evaluate",
            &[Polynomial, Field, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.coset_evaluate",
            "plonky3/poly.coset_evaluate",
        ]),
        poly::operation(
            "poly.coset_interpolate",
            &[Vector, Field],
            &[Polynomial],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.coset_interpolate",
            "plonky3/poly.coset_interpolate",
        ]),
        poly::operation(
            "poly.domain_point",
            &[Field, Index, Index],
            &[Field],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/poly.domain_point", "plonky3/poly.domain_point"]),
        poly::operation("poly.domain_root", &[Index], &[Field], AttributeRule::None)
            .implemented_by(&["arkworks/poly.domain_root", "plonky3/poly.domain_root"]),
        poly::operation(
            "poly.domain_points",
            &[Field, Index],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/poly.domain_points", "plonky3/poly.domain_points"]),
        poly::operation(
            "poly.even_odd_fold",
            &[Vector, Field, Field],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&["arkworks/poly.even_odd_fold", "plonky3/poly.even_odd_fold"]),
        poly::operation(
            "poly.opening_quotient",
            &[Vector, Field, Field, Field],
            &[Vector],
            AttributeRule::None,
        )
        .implemented_by(&[
            "arkworks/poly.opening_quotient",
            "plonky3/poly.opening_quotient",
        ]),
    ]
};

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

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
        let shape = CosetBatch::new(4, 1, 4, 8).unwrap();
        let retained = size(8, std::mem::size_of::<E>()).unwrap();
        let managed = retained + (8 + shape.p3_workspace().unwrap()) * std::mem::size_of::<E>();
        let work = shape.work(E::DIMENSION).unwrap();
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
