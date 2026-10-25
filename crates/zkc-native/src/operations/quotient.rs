//! Native admission and publication for canonical quotient-ring coefficients.
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use zkc_kernels::polynomial::quotient::{self, Operands, Ring};
use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, LogicalType, OperationBinding, OperationSignature,
    PhysicalType, Type, Value as _,
};

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use Type::{Bool, Index, Indices};
    if !binding.arguments.is_empty()
        || binding.implementation != format!("native/{}", binding.contract)
    {
        return None;
    }
    // Authored independently of runtime admission and compiler declarations.
    let (inputs, outputs): (&[Type], &[Type]) = match binding.contract.as_str() {
        "quotient.add" | "quotient.subtract" | "quotient.multiply" | "quotient.pointwise" => {
            (&[Indices, Indices, Index], &[Indices])
        }
        "quotient.project" | "quotient.ntt" | "quotient.intt" => {
            (&[Indices, Index, Index], &[Indices])
        }
        "quotient.norm_within" => (&[Indices, Indices, Index, Index], &[Bool]),
        _ => return None,
    };
    let physical =
        |kind| PhysicalType::default_for(LogicalType::new(kind, Identity::None).ok()?).ok();
    Some(OperationSignature {
        inputs: inputs
            .iter()
            .copied()
            .map(physical)
            .collect::<Option<_>>()?,
        outputs: outputs
            .iter()
            .copied()
            .map(physical)
            .collect::<Option<_>>()?,
        attributes: AttributeRule::None,
    })
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    policy: &Policy,
    available: usize,
) -> Result<Vec<Value>> {
    use Value::{Index, Indices};
    if matches!(name, "quotient.project" | "quotient.ntt" | "quotient.intt") {
        return apply_unary(name, args, policy, available);
    }
    let (left, right, modulus, bound) = match (name, args) {
        (
            "quotient.add" | "quotient.subtract" | "quotient.multiply" | "quotient.pointwise",
            [Indices(a), Indices(b), Index(q)],
        ) => (a, b, *q, None),
        ("quotient.norm_within", [Indices(a), Indices(b), Index(q), Index(bound)]) => {
            (a, b, *q, Some(*bound))
        }
        _ => return Err(refused("quotient-operands")),
    };
    policy.vector_width(left.len(), 8)?;
    policy.vector_width(right.len(), 8)?;
    let failure = |e: quotient::Error| refused(e.code());
    let ring = Ring::new(modulus, left.len()).map_err(failure)?;
    let operands = Operands::new(
        ring.polynomial(left).map_err(failure)?,
        ring.polynomial(right).map_err(failure)?,
    )
    .map_err(failure)?;
    let call = crate::numerical::Call::new(policy, available);
    let linear_work =
        || quotient::linear_work(ring.degree()).ok_or_else(|| exhausted("numerical-work"));
    let result = if let Some(bound) = bound {
        let retained = Value::Bool(false).retained_bytes();
        policy.output(retained, available)?;
        call.work(linear_work()?)?;
        call.scalar(retained)?
            .finish(|| Ok(Value::Bool(operands.norm_within(bound))))?
    } else {
        let retained = size(ring.degree(), 8)?;
        policy.output(retained, available)?;
        let work = if name == "quotient.multiply" {
            quotient::product_work(ring.degree()).ok_or_else(|| exhausted("numerical-work"))?
        } else {
            linear_work()?
        };
        call.work(work)?;
        let mut output = call.output(ring.degree(), 0u64, retained)?;
        match name {
            "quotient.add" => operands.add_into(output.as_mut_slice()),
            "quotient.subtract" => operands.subtract_into(output.as_mut_slice()),
            "quotient.multiply" => operands.multiply_into(output.as_mut_slice()),
            "quotient.pointwise" => operands.pointwise_into(output.as_mut_slice()),
            _ => unreachable!("operation was admitted above"),
        }
        .map_err(failure)?;
        output.finish(|values| Ok(Value::Indices(values.into())))?
    };
    Ok(vec![result])
}

fn apply_unary(
    name: &str,
    args: &[Value],
    policy: &Policy,
    available: usize,
) -> Result<Vec<Value>> {
    let [
        Value::Indices(input),
        Value::Index(q),
        Value::Index(parameter),
    ] = args
    else {
        return Err(refused("quotient-operands"));
    };
    policy.vector_width(input.len(), 8)?;
    let failure = |error: quotient::Error| refused(error.code());
    let degree = if name == "quotient.project" {
        usize::try_from(*parameter).map_err(|_| refused("quotient-degree"))?
    } else {
        input.len()
    };
    let ring = Ring::new(*q, degree).map_err(failure)?;
    policy.vector_width(degree, 8)?;
    let transform = if name != "quotient.project" {
        Some(quotient::transform::Transform::new(ring, *parameter).map_err(failure)?)
    } else {
        None
    };
    // Projection deliberately accepts arbitrary residues and input lengths.
    let canonical = if transform.is_some() {
        Some(ring.polynomial(input).map_err(failure)?)
    } else {
        None
    };
    let work = if transform.is_some() {
        quotient::transform::work(degree)
    } else {
        quotient::projection_work(input.len(), degree)
    }
    .ok_or_else(|| exhausted("numerical-work"))?;
    let retained = size(degree, 8)?;
    policy.output(retained, available)?;
    let call = crate::numerical::Call::new(policy, available);
    call.work(work)?;
    let mut output = call.output(degree, 0u64, retained)?;
    match (transform, canonical) {
        (Some(plan), Some(input)) if name == "quotient.ntt" => {
            plan.forward_into(input, output.as_mut_slice())
        }
        (Some(plan), Some(_)) => plan.inverse_into(
            plan.evaluations(input).map_err(failure)?,
            output.as_mut_slice(),
        ),
        _ => ring.project_into(input, output.as_mut_slice()),
    }
    .map_err(failure)?;
    Ok(vec![
        output.finish(|values| Ok(Value::Indices(values.into())))?,
    ])
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("native/quotient.add", "quotient.add"),
    ("native/quotient.subtract", "quotient.subtract"),
    ("native/quotient.multiply", "quotient.multiply"),
    ("native/quotient.norm_within", "quotient.norm_within"),
    ("native/quotient.project", "quotient.project"),
    ("native/quotient.ntt", "quotient.ntt"),
    ("native/quotient.intt", "quotient.intt"),
    ("native/quotient.pointwise", "quotient.pointwise"),
];

#[cfg(test)]
mod tests {
    use super::*;
    fn values(xs: &[u64]) -> Value {
        Value::Indices(xs.to_vec().into())
    }
    fn run(name: &str, args: &[Value]) -> Result<Vec<Value>> {
        apply(name, args, &Policy::default(), usize::MAX)
    }

    #[test]
    fn arithmetic_reaches_the_exact_negacyclic_contract() {
        let args = [values(&[1, 2]), values(&[3, 4]), Value::Index(17)];
        let result = run("quotient.multiply", &args).unwrap();
        assert!(matches!(&result[0], Value::Indices(xs) if xs.as_ref() == [12, 10]));
        assert!(matches!(&args[0], Value::Indices(xs) if xs.as_ref() == [1, 2]));
        let pointwise = run("quotient.pointwise", &args).unwrap();
        assert!(matches!(&pointwise[0], Value::Indices(xs) if xs.as_ref() == [3, 8]));
        let projected = run(
            "quotient.project",
            &[values(&[1, 2, 3, 4, 5]), Value::Index(17), Value::Index(2)],
        )
        .unwrap();
        assert!(matches!(&projected[0], Value::Indices(xs) if xs.as_ref() == [3, 15]));
    }

    #[test]
    fn inverse_uses_the_same_forward_basis_parameter() {
        let forward = run(
            "quotient.ntt",
            &[values(&[1, 2, 3, 4]), Value::Index(17), Value::Index(2)],
        )
        .unwrap();
        let restored = run(
            "quotient.intt",
            &[forward[0].clone(), Value::Index(17), Value::Index(2)],
        )
        .unwrap();
        assert!(matches!(&restored[0], Value::Indices(xs) if xs.as_ref() == [1, 2, 3, 4]));
    }

    #[test]
    fn raw_inputs_are_admitted_without_a_source_wrapper() {
        for (left, right, modulus, reason) in [
            (vec![0], vec![0], 1, "quotient-modulus"),
            (vec![], vec![], 17, "quotient-degree"),
            (vec![0], vec![], 17, "quotient-shape"),
            (vec![17], vec![0], 17, "quotient-residue"),
            (vec![0], vec![17], 17, "quotient-residue"),
        ] {
            assert_eq!(
                run(
                    "quotient.multiply",
                    &[values(&left), values(&right), Value::Index(modulus)]
                )
                .unwrap_err(),
                refused(reason)
            );
        }
        assert_eq!(
            run("quotient.multiply", &[Value::Bool(false)]).unwrap_err(),
            refused("quotient-operands")
        );
        assert_eq!(
            run(
                "quotient.ntt",
                &[values(&[0; 4]), Value::Index(17), Value::Index(1)]
            )
            .unwrap_err(),
            refused("quotient-transform-root")
        );
    }

    #[test]
    fn norm_threshold_is_an_integer_predicate() {
        for (bound, expected) in [(24, false), (25, true), (26, true)] {
            let result = run(
                "quotient.norm_within",
                &[
                    values(&[14]),
                    values(&[4]),
                    Value::Index(17),
                    Value::Index(bound),
                ],
            )
            .unwrap();
            assert!(matches!(result[0], Value::Bool(actual) if actual == expected));
        }
    }

    #[test]
    fn construction_work_memory_and_publication_limits_are_reached() {
        let args = [values(&[1, 2]), values(&[3, 4]), Value::Index(17)];
        for (policy, reason) in [
            (
                Policy {
                    max_numerical_work: 0,
                    ..Policy::default()
                },
                "numerical-work",
            ),
            (
                Policy {
                    max_numerical_bytes: 0,
                    ..Policy::default()
                },
                "numerical-bytes",
            ),
        ] {
            assert_eq!(
                apply("quotient.multiply", &args, &policy, usize::MAX).unwrap_err(),
                exhausted(reason)
            );
        }
        assert_eq!(
            apply("quotient.multiply", &args, &Policy::default(), 0).unwrap_err(),
            exhausted("output-bytes")
        );
        assert!(matches!(&args[0], Value::Indices(xs) if xs.as_ref() == [1, 2]));
    }
}
