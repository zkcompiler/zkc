//! Logical field-vector contracts. This layer selects no cryptographic code.
use super::{
    AdmissionError, ArgumentKind, AttributeRule, ErrorCode, KernelSignature, LogicalType,
    OperationBinding, Type, TypeArgument,
};

const PARAMETERS: &[ArgumentKind] = &[ArgumentKind::FieldDomain, ArgumentKind::Nat];
pub(super) fn signature(
    binding: &OperationBinding,
) -> Result<KernelSignature<LogicalType>, AdmissionError> {
    let values: Vec<_> = binding.arguments.iter().map(String::as_str).collect();
    let args = super::structural::arguments(
        &values,
        PARAMETERS,
        0,
        &mut super::structural::ParseBudget::new(),
    )?;
    let [TypeArgument::Domain(field), TypeArgument::Nat(length)] = args.as_slice() else {
        return Err(AdmissionError::new(
            ErrorCode::Signature,
            "fixed-vector-arguments",
        ));
    };
    let scalar = LogicalType::new(Type::Field, *field)?;
    let vector = LogicalType::new(Type::Vector, *field)?;
    let fixed = LogicalType::fixed_vector(scalar.clone(), *length)?;
    let (inputs, outputs) = match binding.contract.as_str() {
        "fixed_vector.from_vector" => (vec![vector], vec![fixed]),
        "fixed_vector.to_vector" => (vec![fixed], vec![vector]),
        "fixed_vector.dot" => (vec![fixed.clone(), fixed], vec![scalar]),
        _ => {
            return Err(AdmissionError::new(
                ErrorCode::Signature,
                "uninstalled operation binding",
            ));
        }
    };
    Ok(KernelSignature {
        inputs,
        outputs,
        attributes: AttributeRule::None,
    })
}

use super::operations::{Contract, Contribution};
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "binding-implementation",
    physical_only: false,

    contracts: &[
        Contract::custom("fixed_vector.from_vector")
            .implemented_by(&["plonky3/fixed_vector.from_vector"]),
        Contract::custom("fixed_vector.to_vector")
            .implemented_by(&["plonky3/fixed_vector.to_vector"]),
        Contract::custom("fixed_vector.dot").implemented_by(&["plonky3/fixed_vector.dot"]),
    ],
    resolve: |binding, _| signature(binding),
    select: super::operations::default_ports,
};
