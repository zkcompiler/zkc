//! A direct physical conversion preserves one exact logical value. No default
//! realization exists: trusted composition must contribute each ordered pair.
use super::*;
const CONTRACTS: &[Installation] = &[Installation::new("representation.convert")];
pub(super) const CONTRIBUTION: Contribution = Contribution {
    contracts: CONTRACTS,

    select: default_ports,
    alternatives: &[],
    physical_error: "uninstalled conversion binding",
    adapter: Some(erase),
};
fn erase(binding: &OperationBinding) -> Result<OperationSignature<LogicalType>> {
    let [logical] = binding.arguments.as_slice() else {
        return Err(AdmissionError::new(
            ErrorCode::Signature,
            "conversion-arguments",
        ));
    };
    let logical = LogicalType::parse(logical)?;
    Ok(OperationSignature {
        inputs: vec![logical.clone()],
        outputs: vec![logical],
        attributes: AttributeRule::None,
    })
}
