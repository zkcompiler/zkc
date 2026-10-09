//! Refusals carry a stable identifier and free-form detail.

use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Refusal {
    pub id: &'static str,
    pub detail: String,
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.id, self.detail)
    }
}

impl std::error::Error for Refusal {}

pub type Result<T> = std::result::Result<T, Refusal>;

pub fn refuse<T>(id: &'static str, detail: impl Into<String>) -> Result<T> {
    Err(Refusal {
        id,
        detail: detail.into(),
    })
}

pub fn ensure(condition: bool, id: &'static str, detail: impl FnOnce() -> String) -> Result<()> {
    if condition {
        Ok(())
    } else {
        refuse(id, detail())
    }
}
