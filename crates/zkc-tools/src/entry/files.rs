//! Explicit file capabilities and transport for schema-directed Entry inputs.
use super::{NamedValues, SetupAuthority, Value};
use crate::host::inputs::digest;
use serde::Deserialize;
use std::collections::BTreeMap;
type Result<T> = std::result::Result<T, String>;
pub const MAX_REQUEST_BYTES: usize = 16 * 1024 * 1024;

#[derive(Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
struct Authority {
    format: String,
    keys: BTreeMap<String, String>,
}
super::decode::objects!(Authority);

fn document<T: for<'de> Deserialize<'de>>(bytes: &[u8]) -> Result<T> {
    let value = crate::host::document::read(bytes, MAX_REQUEST_BYTES)?;
    serde_json::from_value(value).map_err(|_| "entry-request-format".into())
}
/// Parse independently authorized setup pins; input material confers no authority.
pub fn authority(bytes: &[u8]) -> Result<SetupAuthority> {
    if bytes.len() > 64 * 1024 {
        return Err("entry-request-limit".into());
    }
    let value: Authority = document(bytes)?;
    if value.format != "zkc.entry-setups/0" {
        return Err("entry-request-format".into());
    }
    Ok(SetupAuthority {
        keys: value
            .keys
            .into_iter()
            .map(|(k, v)| Ok((k, digest(&v)?)))
            .collect::<Result<_>>()?,
    })
}
mod output;
pub use output::{output_setups, proof_outputs, run_outputs};

pub(crate) use output::output_setups_with;

mod resolver;
pub use resolver::Documents;
