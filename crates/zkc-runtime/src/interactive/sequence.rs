//! Logical sequence contracts, independent of physical storage and codecs.
use super::operations::{Contract, Contribution};
use super::{
    AdmissionError, AttributeRule, ErrorCode, KernelSignature, LogicalType, OperationBinding,
};

fn signature(binding: &OperationBinding) -> Result<KernelSignature<LogicalType>, AdmissionError> {
    let invalid = || AdmissionError::new(ErrorCode::Signature, "sequence-contract");
    let [element] = binding.arguments.as_slice() else {
        return Err(invalid());
    };
    let element = LogicalType::parse(element)?;
    let sequence = LogicalType::sequence(element.clone())?;
    let index = LogicalType::parse("index")?;
    let (inputs, outputs) = match binding.contract.as_str() {
        "sequence.empty" => (vec![], vec![sequence]),
        "sequence.append" => (vec![sequence.clone(), element], vec![sequence]),
        "sequence.length" => (vec![sequence], vec![index]),
        "sequence.at" => (vec![sequence, index], vec![element]),
        _ => return Err(invalid()),
    };
    Ok(KernelSignature {
        inputs,
        outputs,
        attributes: AttributeRule::None,
    })
}
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "binding-implementation",
    physical_only: false,
    contracts: &[
        Contract::custom("sequence.empty"),
        Contract::custom("sequence.append"),
        Contract::custom("sequence.length"),
        Contract::custom("sequence.at"),
    ],
    resolve: |binding, _| signature(binding),
    providers: &["native"],
    select: super::operations::default_ports,
};
