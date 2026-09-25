//! Checked native installation of coset kernels. Each backend owns its DFT
//! preparation; no protocol value or transcript state lives in this cache.
use super::polynomial::{self, Domain, Error, Kernels};
use crate::{KoalaBear, KoalaBearExt8, Policy, Result, Value, exhausted, refused, value::size};
use p3_field::ExtensionField;
use zkc_runtime::interactive::{Identity, Invocation};

fn failure(error: Error) -> zkc_runtime::interactive::BackendError {
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

pub(crate) fn apply(
    name: &str,
    field: Option<Identity>,
    args: &[Value],
    invocation: &Invocation<'_>,
    policy: &Policy,
    kernels: &Kernels,
) -> Option<Result<Vec<Value>>> {
    if !matches!(
        name,
        "poly.coset_evaluate"
            | "poly.coset_interpolate"
            | "poly.domain_point"
            | "poly.domain_root"
            | "poly.domain_points"
            | "poly.even_odd_fold"
            | "poly.opening_quotient"
    ) {
        return None;
    }
    Some(match field {
        Some(Identity::KoalaBear) => {
            execute::<KoalaBear>(name, args, policy, invocation.max_output_bytes, kernels)
        }
        Some(Identity::KoalaBearExt8) => {
            execute::<KoalaBearExt8>(name, args, policy, invocation.max_output_bytes, kernels)
        }
        _ => Err(refused("coset-field")),
    })
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
                x *= d.generator();
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
            E::vector_value(
                polynomial::opening_quotient(v, d, field(2)?, field(3)?).map_err(failure)?,
            )
        }
        _ => return Err(refused("coset-operation")),
    };
    Ok(vec![output])
}
