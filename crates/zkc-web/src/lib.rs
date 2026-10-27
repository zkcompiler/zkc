//! In-memory browser boundary over the ordinary SDK. Package authentication,
//! schema decoding, setup authority and execution remain SDK responsibilities.
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use wasm_bindgen::prelude::*;
use zkc::{
    entry::{self, BindingPolicy, Package, ProofEntry, ProofOperation, ProofOptions, ProofRequest},
    execution::Capacity,
};

type Result<T> = std::result::Result<T, String>;

#[derive(Default, Deserialize)]
#[serde(default, deny_unknown_fields)]
struct Options {
    capacity: Option<Json>,
    package_bytes: Option<usize>,
    allow_authored: bool,
    operation: Operation,
    external_work: Option<u64>,
}
#[derive(Default, Deserialize)]
#[serde(rename_all = "snake_case")]
enum Operation {
    #[default]
    Both,
    Prove,
    Verify,
}

/// A Worker-owned admitted deployment. Pins and authority must come from the
/// application independently of downloaded package, statement and proof bytes.
/// `dispose` invalidates the handle; generated `free` releases the Wasm object.
#[wasm_bindgen]
pub struct ProofSession {
    entry: Option<ProofEntry>,
    capacity: Capacity,
    setups: BTreeMap<String, Vec<u8>>,
}
#[wasm_bindgen]
impl ProofSession {
    /// Options are bounded JSON, not a new package or proof format. `capacity`
    /// uses the SDK's existing capacity record. Empty authority means no setups.
    #[wasm_bindgen(constructor)]
    pub fn new(package: &[u8], pin: &[u8], options: &str, authority: &[u8]) -> Result<Self> {
        if options.len() > 64 * 1024 {
            return Err("web-options-limit".into());
        }
        let options: Options = serde_json::from_str(options).map_err(|_| "web-options")?;
        let capacity = options.capacity.map_or_else(
            || Ok(Capacity::default()),
            |v| Capacity::parse(v.to_string().as_bytes()),
        )?;
        let pin = pin.try_into().map_err(|_| "entry-package-pin")?;
        let package = Package::capture(
            package,
            pin,
            options.package_bytes.unwrap_or(Package::MAX_BYTES),
        )
        .map_err(|e| e.to_string())?;
        let authority = if authority.is_empty() {
            Default::default()
        } else {
            entry::files::authority(authority)?
        };
        let mut settings = ProofOptions {
            capacity,
            binding: if options.allow_authored {
                BindingPolicy::AllowAuthored
            } else {
                BindingPolicy::TranscriptRequired
            },
            ..Default::default()
        };
        if let Some(work) = options.external_work {
            settings = settings.with_external_work(work)?;
        }
        let entry = match options.operation {
            Operation::Both => ProofEntry::admit(package, settings, authority),
            Operation::Prove => {
                ProofEntry::admit_operation(package, settings, authority, ProofOperation::Prove)
            }
            Operation::Verify => {
                ProofEntry::admit_operation(package, settings, authority, ProofOperation::Verify)
            }
        }
        .map_err(|e| e.to_string())?;
        Ok(Self {
            entry: Some(entry),
            capacity,
            setups: BTreeMap::new(),
        })
    }

    pub fn describe(&self) -> Result<String> {
        Ok(self.active()?.interface().describe().to_string())
    }

    /// Supply material for an independently pinned slot. SDK preflight checks
    /// its authority before execution. Persistent copies have an aggregate cap.
    #[wasm_bindgen(js_name = setSetup)]
    pub fn set_setup(&mut self, slot: &str, material: &[u8]) -> Result<()> {
        let entry = self.active()?;
        if !entry.interface().setup_names().any(|name| name == slot) {
            return Err("web-setup-slot".into());
        }
        let mut total = material.len();
        for (name, value) in &self.setups {
            if name != slot {
                total = total.checked_add(value.len()).ok_or("web-setup-limit")?;
            }
        }
        if material.len() > self.capacity.wire_bytes || total > self.capacity.values.total_bytes {
            return Err("web-setup-limit".into());
        }
        self.setups.insert(slot.into(), material.into());
        Ok(())
    }

    /// Documents use the same schema and readable values as the native SDK.
    /// File references are refused. Context is an application-owned byte string.
    pub fn prove(
        &self,
        public: &[u8],
        witness: &[u8],
        context: &[u8],
        transcript_budget: Option<u64>,
    ) -> Result<ProofResult> {
        self.execute(public, Some(witness), context, transcript_budget, None)
    }

    pub fn verify(
        &self,
        public: &[u8],
        proof: &[u8],
        context: &[u8],
        transcript_budget: Option<u64>,
    ) -> Result<ProofResult> {
        self.execute(public, None, context, transcript_budget, Some(proof))
    }

    pub fn dispose(&mut self) {
        self.entry = None;
        self.setups.clear();
    }
}
impl ProofSession {
    fn active(&self) -> Result<&ProofEntry> {
        self.entry
            .as_ref()
            .ok_or_else(|| "web-session-disposed".into())
    }
    fn execute(
        &self,
        public: &[u8],
        witness: Option<&[u8]>,
        context: &[u8],
        transcript_budget: Option<u64>,
        proof: Option<&[u8]>,
    ) -> Result<ProofResult> {
        let entry = self.active()?;
        let mut decoder = entry::inputs::Decoder::new(self.capacity)?;
        let mut request = ProofRequest {
            context: context.into(),
            transcript_budget,
            setups: self.setups.clone(),
            ..Default::default()
        };
        for group in entry.interface().input_groups() {
            match group.name() {
                "public" => {
                    request.public = decoder
                        .decode(&group, public, None)
                        .map_err(|e| format!("{}: {}", e.code, e.path))?
                }
                "witness" => {
                    if let Some(bytes) = witness {
                        request.private.inputs = decoder
                            .decode(&group, bytes, None)
                            .map_err(|e| format!("{}: {}", e.code, e.path))?;
                    }
                }
                _ => return Err("entry-job-kind".into()),
            }
        }
        let operation = if proof.is_some() {
            ProofOperation::Verify
        } else {
            ProofOperation::Prove
        };
        let result = entry
            .preflight_file_call(operation, request, None, true)
            .map_err(|e| e.to_string())?
            .execute(proof)
            .map_err(|e| e.to_string())?;
        let report = &result.report;
        let (outputs, encoding_error) = if report.is_success() {
            match result.encode_results() {
                Ok(value) => (value, None),
                Err(error) => (None, Some(error)),
            }
        } else {
            (None, None)
        };
        let success = report.is_success() && encoding_error.is_none();
        let accepted = if encoding_error.is_none() {
            report.verification_result()
        } else {
            None
        };
        // Never publish a partial proof or outputs from an unsuccessful attempt.
        let bytes = if success && proof.is_none() {
            report
                .native
                .outcome
                .as_ref()
                .map_err(|e| e.to_string())?
                .clone()
        } else {
            Vec::new()
        };
        Ok(ProofResult {
            proof: bytes,
            report: json!({"success":success,"accepted":accepted,
                "error":report.native.outcome.as_ref().err(),
                "diagnostics":report.native.diagnostics(),
                "output_error":report.output_error.as_ref().or(encoding_error.as_ref())})
            .to_string(),
            outputs,
        })
    }
}

/// Returned byte arrays are copies. Absence of `accepted` is not acceptance.
#[wasm_bindgen]
pub struct ProofResult {
    proof: Vec<u8>,
    report: String,
    outputs: Option<Vec<u8>>,
}
#[wasm_bindgen]
impl ProofResult {
    #[wasm_bindgen(getter)]
    pub fn proof(&self) -> Vec<u8> {
        self.proof.clone()
    }
    #[wasm_bindgen(getter)]
    pub fn report(&self) -> String {
        self.report.clone()
    }
    #[wasm_bindgen(getter)]
    pub fn outputs(&self) -> Option<Vec<u8>> {
        self.outputs.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn options_reject_unknown_duplicate_invalid_and_oversized_configuration() {
        for text in [
            r#"{"unknown":true}"#,
            r#"{"operation":"run"}"#,
            r#"{"allow_authored":true,"allow_authored":false}"#,
            "{",
        ] {
            assert_eq!(
                ProofSession::new(&[], &[0; 32], text, &[]).err().unwrap(),
                "web-options"
            );
        }
        assert_eq!(
            ProofSession::new(&[], &[0; 32], &" ".repeat(65537), &[])
                .err()
                .unwrap(),
            "web-options-limit"
        );
        assert_eq!(
            ProofSession::new(&[], &[0; 31], "{}", &[]).err().unwrap(),
            "entry-package-pin"
        );
    }
}
