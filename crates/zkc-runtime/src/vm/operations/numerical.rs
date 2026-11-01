//! Closed compiler-generated numerical expression calls. This owner does not
//! consult native advertisements or interpret expressions with field arithmetic.
use super::*;
use crate::numerical::Plan;

pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: &[
        Installation::new("numerical.map").implemented_by(&[
            "arkworks/numerical.map",
            "dalek/numerical.map",
            "plonky3/numerical.map",
        ]),
        Installation::new("numerical.sum").implemented_by(&[
            "arkworks/numerical.sum",
            "dalek/numerical.sum",
            "plonky3/numerical.sum",
        ]),
        Installation::new("numerical.product").implemented_by(&[
            "arkworks/numerical.product",
            "dalek/numerical.product",
            "plonky3/numerical.product",
        ]),
    ],

    select: support::select_nominal,
    alternatives: &[],
    physical_error: "uninstalled numerical expression binding",
};

fn arguments(binding: &OperationBinding) -> Result<(Identity, &str)> {
    let [field, mask] = binding.arguments.as_slice() else {
        return Err(support::failure());
    };
    let field = Identity::parse(field).map_err(|_| support::failure())?;
    if field.field_characteristic().is_none()
        || mask.len() > 1023
        || !mask.bytes().all(|b| matches!(b, b'0' | b'1'))
    {
        return Err(support::failure());
    }
    Ok((field, mask))
}

pub(super) fn signature(
    binding: &OperationBinding,
    result: zkc_catalog::NumericalResult,
) -> Result<OperationSignature<LogicalType>> {
    let (field, mask) = arguments(binding)?;
    let mut inputs = Vec::with_capacity(mask.len() + 1);
    inputs.push(LogicalType::new(Type::Index, Identity::None)?);
    for bit in mask.bytes() {
        inputs.push(LogicalType::new(
            if bit == b'0' {
                Type::Field
            } else {
                Type::Vector
            },
            field,
        )?);
    }
    let output = match result {
        zkc_catalog::NumericalResult::Map => Type::Vector,
        zkc_catalog::NumericalResult::Sum | zkc_catalog::NumericalResult::Product => Type::Field,
    };
    Ok(OperationSignature {
        inputs,
        outputs: vec![LogicalType::new(output, field)?],
        attributes: AttributeRule::NumericalExpression,
    })
}

/// Check parameters while admitting every static Local body, including dormant
/// branches. Native direct callers independently repeat these obligations when
/// reached; neither path can supply the other's signature or admission result.
pub(crate) fn parameters(binding: &OperationBinding, attributes: &[String]) -> Result<()> {
    let (field, mask) = arguments(binding)?;
    let failure = || AdmissionError::new(ErrorCode::Attributes, "numerical-expression");
    let [body] = attributes else {
        return Err(failure());
    };
    Plan::parse(body, field, mask.as_bytes()).map_err(|e| {
        AdmissionError::new(
            if e.0 == "numerical-plan-bytes" {
                ErrorCode::Limit
            } else {
                ErrorCode::Attributes
            },
            e.0,
        )
    })?;
    Ok(())
}

#[cfg(test)]
mod tests;
