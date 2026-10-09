//! Closed, exact nominal slots. No wire payload, provider, or evidence.
use super::{AdmissionError, ErrorCode};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ResourceDomain {
    bytes: [u8; 128],
    len: u8,
}
impl ResourceDomain {
    pub fn parse(name: &str) -> Result<Self, AdmissionError> {
        if name.is_empty()
            || name.len() > 128
            || !name.as_bytes()[0].is_ascii_alphabetic()
            || !name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-' | b'.'))
        {
            return Err(AdmissionError::new(ErrorCode::Type, "resource-unit-domain"));
        }
        let mut bytes = [0; 128];
        bytes[..name.len()].copy_from_slice(name.as_bytes());
        Ok(Self {
            bytes,
            len: name.len() as u8,
        })
    }
    pub fn name(&self) -> &str {
        std::str::from_utf8(&self.bytes[..usize::from(self.len)]).expect("validated ASCII slot")
    }
}

use super::operations::{Contract, Contribution};
use super::{AttributeRule, KernelSignature, LogicalType, OperationBinding};
fn signature(
    binding: &OperationBinding,
    _: &Contract,
) -> Result<KernelSignature<LogicalType>, AdmissionError> {
    if binding.arguments.len() != 1 {
        return Err(AdmissionError::new(
            ErrorCode::Signature,
            "binding-resource-unit-domain",
        ));
    }
    let domain = ResourceDomain::parse(&binding.arguments[0])
        .map_err(|_| AdmissionError::new(ErrorCode::Type, "binding-resource-unit-domain"))?;
    let ty = LogicalType::resource_unit(domain);
    Ok(KernelSignature {
        inputs: if binding.contract == "resource_unit.create" {
            vec![]
        } else {
            vec![ty.clone()]
        },
        outputs: if binding.contract == "resource_unit.consume" {
            vec![]
        } else {
            vec![ty]
        },
        attributes: AttributeRule::None,
    })
}
pub(super) const CONTRIBUTION: Contribution = Contribution {
    alternatives: &[],
    physical_error: "binding-implementation",
    physical_only: false,

    contracts: &[
        Contract::custom("resource_unit.create").implemented_by(&["logical/resource_unit.create"]),
        Contract::custom("resource_unit.pass").implemented_by(&["logical/resource_unit.pass"]),
        Contract::custom("resource_unit.consume")
            .implemented_by(&["logical/resource_unit.consume"]),
    ],
    resolve: signature,
    select: super::operations::default_ports,
};
