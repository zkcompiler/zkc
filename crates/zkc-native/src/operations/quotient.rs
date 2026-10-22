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
        "quotient.add" | "quotient.subtract" | "quotient.multiply" => {
            (&[Indices, Indices, Index], &[Indices])
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
    let (left, right, modulus, bound) = match (name, args) {
        (
            "quotient.add" | "quotient.subtract" | "quotient.multiply",
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
            _ => unreachable!("operation was admitted above"),
        }
        .map_err(failure)?;
        output.finish(|values| Ok(Value::Indices(values.into())))?
    };
    Ok(vec![result])
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("native/quotient.add", "quotient.add"),
    ("native/quotient.subtract", "quotient.subtract"),
    ("native/quotient.multiply", "quotient.multiply"),
    ("native/quotient.norm_within", "quotient.norm_within"),
];

#[cfg(test)]
mod tests;
