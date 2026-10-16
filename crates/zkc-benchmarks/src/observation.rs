//! Observations collected outside the SDK timer, serialized after measurement.
use serde::Serialize;

#[derive(Clone, Debug, Default, Serialize)]
pub struct Preparation {
    pub entries: usize,
    pub retained_bytes: usize,
    pub hits: u64,
}

#[derive(Serialize)]
pub struct Call {
    pub input_index: usize,
    pub decode_ns: u128,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub execution_counts: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub preparation: Option<Preparation>,
}
impl Call {
    pub fn decoded(input_index: usize, decode_ns: u128) -> Self {
        Self {
            input_index,
            decode_ns,
            execution_counts: None,
            preparation: None,
        }
    }
}

#[derive(Serialize)]
pub struct Lifecycle {
    pub preparation_limits: Option<Limits>,
    pub capture_ns: u128,
    pub admit_ns: u128,
    pub calls: Vec<Call>,
    pub diagnostics_ns: u128,
    pub peak_rss_before_diagnostics: Option<u64>,
    pub peak_rss_after_diagnostics: Option<u64>,
}

#[derive(Serialize)]
pub struct Limits {
    pub default_entries: usize,
    pub default_bytes: usize,
    pub entries: usize,
    pub bytes: usize,
}
