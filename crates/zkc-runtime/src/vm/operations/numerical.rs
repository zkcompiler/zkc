//! Closed compiler-generated numerical expression calls. This owner does not
//! consult native advertisements or interpret expressions with field arithmetic.
use super::*;
use crate::ring::{Expression, Node};

pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: &[
        Contract::custom("numerical.map").implemented_by(&[
            "arkworks/numerical.map",
            "dalek/numerical.map",
            "plonky3/numerical.map",
        ]),
        Contract::custom("numerical.sum").implemented_by(&[
            "arkworks/numerical.sum",
            "dalek/numerical.sum",
            "plonky3/numerical.sum",
        ]),
        Contract::custom("numerical.product").implemented_by(&[
            "arkworks/numerical.product",
            "dalek/numerical.product",
            "plonky3/numerical.product",
        ]),
    ],
    resolve,
    select: support::select_nominal,
    alternatives: &[],
    physical_error: "uninstalled numerical expression binding",
    physical_only: false,
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

fn resolve(binding: &OperationBinding, _: &Contract) -> Result<OperationSignature<LogicalType>> {
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
    let output = match binding.contract.as_str() {
        "numerical.map" => Type::Vector,
        "numerical.sum" | "numerical.product" => Type::Field,
        _ => return Err(support::failure()),
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
    if body.len() > 4096 {
        return Err(AdmissionError::new(
            ErrorCode::Limit,
            "numerical-expression-bytes",
        ));
    }
    let expression = Expression::parse(body).map_err(|_| failure())?;
    if expression.canonical() != *body
        || expression.inputs().len() != mask.len()
        || expression.outputs().len() != 1
        || expression.inputs().iter().any(|f| *f != field)
        || expression.facts().iter().any(|f| f.field != field)
        || expression
            .nodes()
            .iter()
            .any(|n| matches!(n, Node::Embed(..)))
    {
        return Err(failure());
    }
    Ok(())
}

#[cfg(test)]
mod tests;
