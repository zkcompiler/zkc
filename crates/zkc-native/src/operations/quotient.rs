//! Native admission and publication for canonical quotient-ring coefficients.
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use zkc_kernels::polynomial::quotient::{self, Operands, Ring};
use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, LogicalType, OperationBinding, OperationSignature,
    PhysicalType, Type, Value as _,
};

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use Type::{Bool, Index, Indices, QuotientMatrix};
    if !binding.arguments.is_empty()
        || binding.implementation != format!("native/{}", binding.contract)
    {
        return None;
    }
    // Authored independently of runtime admission and compiler declarations.
    let (inputs, outputs): (&[Type], &[Type]) = match binding.contract.as_str() {
        "quotient.prepare_matrix" => (
            &[Indices, Index, Index, Index, Index, Index],
            &[QuotientMatrix],
        ),
        "quotient.matvec" => (&[QuotientMatrix, Indices], &[Indices]),
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
    if matches!(name, "quotient.prepare_matrix" | "quotient.matvec") {
        return apply_matrix(name, args, policy, available);
    }
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
        (Some(plan), Some(input)) => plan.inverse_into(input, output.as_mut_slice()),
        _ => ring.project_into(input, output.as_mut_slice()),
    }
    .map_err(failure)?;
    Ok(vec![
        output.finish(|values| Ok(Value::Indices(values.into())))?,
    ])
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("native/quotient.prepare_matrix", "quotient.prepare_matrix"),
    ("native/quotient.matvec", "quotient.matvec"),
    ("native/quotient.add", "quotient.add"),
    ("native/quotient.subtract", "quotient.subtract"),
    ("native/quotient.multiply", "quotient.multiply"),
    ("native/quotient.norm_within", "quotient.norm_within"),
    ("native/quotient.project", "quotient.project"),
    ("native/quotient.ntt", "quotient.ntt"),
    ("native/quotient.intt", "quotient.intt"),
    ("native/quotient.pointwise", "quotient.pointwise"),
];

fn apply_matrix(
    name: &str,
    args: &[Value],
    policy: &Policy,
    available: usize,
) -> Result<Vec<Value>> {
    use quotient::rns::{Matrix, PreparedMatrix};
    use std::sync::Arc;
    let failure = |e: quotient::Error| refused(e.code());
    let call = crate::numerical::Call::new(policy, available);
    let output = match (name, args) {
        (
            "quotient.prepare_matrix",
            [
                Value::Indices(coefficients),
                Value::Index(q),
                Value::Index(n),
                Value::Index(rows),
                Value::Index(columns),
                Value::Index(bound),
            ],
        ) => {
            policy.vector_width(coefficients.len(), 8)?;
            let dimension = |value| usize::try_from(value).map_err(|_| refused("quotient-shape"));
            let matrix = Matrix::new(
                coefficients,
                *q,
                dimension(*n)?,
                dimension(*rows)?,
                dimension(*columns)?,
                *bound,
            )
            .map_err(failure)?;
            let len = matrix.storage_elements();
            policy.vector_width(len, 8)?;
            let retained = len
                .checked_mul(8)
                .and_then(|v| v.checked_add(PreparedMatrix::RETAINED_OVERHEAD))
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.output(retained, available)?;
            call.work(matrix.work().ok_or_else(|| exhausted("numerical-work"))?)?;
            let mut scratch = call.scratch(matrix.scratch_elements(), 0u64)?;
            let output = call.output(len, 0u64, retained)?;
            output.finish(|storage| {
                Ok(Value::QuotientMatrix(Arc::new(
                    matrix.prepare(storage, scratch.as_mut()).map_err(failure)?,
                )))
            })?
        }
        ("quotient.matvec", [Value::QuotientMatrix(matrix), Value::Indices(input)]) => {
            policy.vector_width(input.len(), 8)?;
            let product = matrix.digits(input).map_err(failure)?;
            let len = matrix.output_elements();
            policy.vector_width(len, 8)?;
            let retained = size(len, 8)?;
            policy.output(retained, available)?;
            call.work(matrix.work().ok_or_else(|| exhausted("numerical-work"))?)?;
            let mut scratch = call.scratch(
                matrix
                    .scratch_elements()
                    .ok_or_else(|| exhausted("size-overflow"))?,
                0u64,
            )?;
            let mut output = call.output(len, 0u64, retained)?;
            product
                .evaluate(output.as_mut_slice(), scratch.as_mut())
                .map_err(failure)?;
            output.finish(|values| Ok(Value::Indices(values.into())))?
        }
        _ => return Err(refused("quotient-operands")),
    };
    Ok(vec![output])
}

#[cfg(test)]
mod tests;
