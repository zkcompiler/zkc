//! In-memory browser boundary over the ordinary SDK. Package authentication,
//! schema decoding, setup authority and execution remain SDK responsibilities.
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, sync::Arc};
use wasm_bindgen::prelude::*;
use zkc::{
    entry::{
        self, BindingPolicy, Package, ProofEntry, ProofOperation, ProofOptions,
        memory::ProofCallOptions,
    },
    execution::{Capacity, CpuInstallation, providers::Provider},
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
    providers: Option<Vec<Provider>>,
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
    inputs: BTreeMap<String, Arc<Vec<u8>>>,
    timings: String,
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
        let installation = match options.providers {
            None => CpuInstallation::standard(),
            Some(providers) => {
                let unique: std::collections::BTreeSet<_> = providers.iter().copied().collect();
                if providers.len() > 5 || unique.len() != providers.len() {
                    return Err("web-options".into());
                }
                providers
                    .into_iter()
                    .fold(CpuInstallation::builder(), |builder, provider| {
                        builder.include(provider)
                    })
                    .finish()
            }
        }
        .map_err(|e| e.to_string())?;
        let capacity = options.capacity.map_or_else(
            || Ok(Capacity::default()),
            |v| Capacity::parse(v.to_string().as_bytes()),
        )?;
        let pin = pin.try_into().map_err(|_| "entry-package-pin")?;
        let capture_started = now();
        let package = Package::capture(
            package,
            pin,
            options.package_bytes.unwrap_or(Package::MAX_BYTES),
        )
        .map_err(|e| e.to_string())?;
        let package_capture_ms = now() - capture_started;
        let authority = if authority.is_empty() {
            Default::default()
        } else {
            entry::SetupAuthority::from_bytes(authority)?
        };
        let mut settings = ProofOptions {
            capacity,
            installation,
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
        let admit_started = now();
        let entry = match options.operation {
            Operation::Both => ProofEntry::admit(package, settings, authority),
            Operation::Prove => {
                ProofEntry::admit_operation(package, settings, authority, ProofOperation::Prove)
            }
            Operation::Verify => {
                ProofEntry::admit_operation(package, settings, authority, ProofOperation::Verify)
            }
        }
        .map_err(entry_refusal)?;
        Ok(Self {
            entry: Some(entry),
            capacity,
            setups: BTreeMap::new(),
            inputs: BTreeMap::new(),
            timings: json!({"package_capture_ms": package_capture_ms,
                "package_admit_ms": now() - admit_started})
            .to_string(),
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
        entry.invalidate_setup(slot)?;
        self.setups.remove(slot);
        self.check_material_capacity(material.len())?;
        self.setups.insert(slot.into(), material.into());
        Ok(())
    }

    /// Bind immutable opaque bytes for an existing SDK input reference. This
    /// grants no file access, material identity or setup authority.
    #[wasm_bindgen(js_name = setInput)]
    pub fn set_input(&mut self, name: &str, bytes: &[u8]) -> Result<()> {
        self.active()?.invalidate_prover_inputs()?;
        self.inputs.remove(name);
        if name.is_empty() || name.len() > 4096 || self.inputs.len() >= 1024 {
            return Err("web-input-name".into());
        }
        self.check_material_capacity(bytes.len())?;
        self.inputs.insert(name.into(), Arc::new(bytes.into()));
        Ok(())
    }

    /// Separate capture and admission intervals; neither includes module loading.
    #[wasm_bindgen(getter)]
    pub fn timings(&self) -> String {
        self.timings.clone()
    }

    /// Documents use the same schema and readable values as the native SDK.
    /// References resolve only explicit named bytes. Context belongs to the application.
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
        self.inputs.clear();
    }
}
impl ProofSession {
    fn active(&self) -> Result<&ProofEntry> {
        self.entry
            .as_ref()
            .ok_or_else(|| "web-session-disposed".into())
    }
    fn check_material_capacity(&self, incoming: usize) -> Result<()> {
        let total = self
            .setups
            .values()
            .map(Vec::len)
            .chain(self.inputs.values().map(|value| value.len()))
            .try_fold(incoming, |total, len| total.checked_add(len))
            .ok_or("web-setup-limit")?;
        if incoming > self.capacity.wire_bytes || total > self.capacity.values.total_bytes {
            return Err("web-setup-limit".into());
        }
        Ok(())
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
        let operation = if proof.is_some() {
            ProofOperation::Verify
        } else {
            ProofOperation::Prove
        };
        let started = now();
        let call = entry
            .preflight_memory_call(
                operation,
                Some(public),
                witness,
                &self.inputs,
                ProofCallOptions {
                    context: context.into(),
                    transcript_budget,
                    setups: self.setups.clone(),
                    ..Default::default()
                },
                None,
                true,
            )
            .map_err(entry_refusal)?;
        let memory_preflight_ms = now() - started;
        let started = now();
        let result = Arc::new(call.execute(proof).map_err(entry_refusal)?);
        let execute_cleanup_ms = now() - started;
        let started = now();
        let report = &result.report;
        let (outputs, encoding_error) = if report.is_success() {
            match result.encode_results_owned() {
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
        let output_encode_ms = now() - started;
        let started = now();
        let diagnostics = report.native.diagnostics();
        let diagnostics_ms = now() - started;
        let text = json!({"success":success,"accepted":accepted,
            "error":report.native.outcome.as_ref().err(), "diagnostics":diagnostics,
            "output_error":report.output_error.as_ref().or(encoding_error.as_ref()),
            "timings": { "memory_preflight_ms": memory_preflight_ms,
                "execute_cleanup_ms": execute_cleanup_ms, "output_encode_ms": output_encode_ms,
                "diagnostics_ms": diagnostics_ms }})
        .to_string();
        Ok(ProofResult {
            result,
            publish_proof: success && proof.is_none(),
            report: text,
            outputs,
        })
    }
}

fn entry_refusal(error: entry::EntryError) -> String {
    json!({"sdk_refusal": {"code": error.code(),
        "phase": format!("{:?}", error.phase).to_ascii_lowercase(),
        "path": error.path()}})
    .to_string()
}

/// Returned byte arrays are copies. Absence of `accepted` is not acceptance.
#[wasm_bindgen]
pub struct ProofResult {
    // Custody lasts through getter copies and Worker publication, until free.
    result: Arc<entry::ProofResult>,
    publish_proof: bool,
    report: String,
    outputs: Option<entry::OwnedEncodedResults>,
}
#[wasm_bindgen]
impl ProofResult {
    #[wasm_bindgen(getter)]
    pub fn proof(&self) -> Vec<u8> {
        if self.publish_proof {
            self.result
                .report
                .native
                .outcome
                .as_ref()
                .expect("successful proof")
                .clone()
        } else {
            Vec::new()
        }
    }
    #[wasm_bindgen(getter)]
    pub fn report(&self) -> String {
        self.report.clone()
    }
    #[wasm_bindgen(getter)]
    pub fn outputs(&self) -> Option<Vec<u8>> {
        self.outputs.as_ref().map(|bytes| bytes.as_bytes().to_vec())
    }
}

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = performance, js_name = now)]
    fn now() -> f64;
}
#[cfg(not(target_arch = "wasm32"))]
fn now() -> f64 {
    static START: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
    START
        .get_or_init(std::time::Instant::now)
        .elapsed()
        .as_secs_f64()
        * 1000.
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn options_reject_unknown_duplicate_invalid_and_oversized_configuration() {
        for text in [
            r#"{"unknown":true}"#,
            r#"{"providers":["arkworks","arkworks"]}"#,
            r#"{"providers":["unknown"]}"#,
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
