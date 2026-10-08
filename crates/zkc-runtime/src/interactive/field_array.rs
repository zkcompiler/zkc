//! Logical fixed-length public field-array contracts. This layer selects no cryptographic code.
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
            "field-array-arguments",
        ));
    };
    let scalar = LogicalType::new(Type::Field, *field)?;
    let vector = LogicalType::new(Type::Vector, *field)?;
    let fixed = LogicalType::field_array(*field, *length)?;
    let (inputs, outputs) = match binding.contract.as_str() {
        "field_array.from_vector" => (vec![vector], vec![fixed]),
        "field_array.at" => (vec![fixed], vec![scalar]),
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
        attributes: if binding.contract == "field_array.at" {
            AttributeRule::Unsigned64
        } else {
            AttributeRule::None
        },
    })
}

use super::operations::{Contract, Contribution};
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "binding-implementation",
    physical_only: false,

    contracts: &[
        Contract::custom("field_array.from_vector"),
        Contract::custom("field_array.at"),
    ],
    resolve: |binding, _| signature(binding),
    providers: &["arkworks"],
    select: super::operations::default_ports,
};
