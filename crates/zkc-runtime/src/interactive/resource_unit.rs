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
