//! In-memory browser boundary over the ordinary SDK. Package authentication,
//! schema decoding, setup authority and execution remain SDK responsibilities.
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, sync::Arc};
use wasm_bindgen::prelude::*;
use zkc::{
    entry::{
        self, BindingPolicy, InterfaceLimits, Package, ProofEntry, ProofOperation, ProofOptions,
        memory::ProofCallOptions,
    },
    execution::{Capacity, CpuInstallation, providers::Provider},
};

type Result<T> = std::result::Result<T, String>;

#[derive(Default, Deserialize)]
#[serde(default, deny_unknown_fields)]
struct Options {
    capacity: Option<Json>,
    interface_limits: Option<Json>,
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
    /// uses the SDK's existing capacity record and `interface_limits` its
    /// interface allowance record. Empty authority means no setups.
    #[wasm_bindgen(constructor)]
    pub fn new(package: &[u8], pin: &[u8], options: &str, authority: &[u8]) -> Result<Self> {
        if options.len() > 64 * 1024 {
            return Err("web-options-limit".into());
        }
        let options: Options = serde_json::from_str(options).map_err(|_| "web-options")?;
        let installation = match options.providers {
            None => CpuInstallation::standard(),
            Some(providers) => {
                // Each element names an installed provider; uniqueness alone
                // bounds the selection by the installed set.
                let unique: std::collections::BTreeSet<_> = providers.iter().copied().collect();
                if unique.len() != providers.len() {
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
        // Admission reads the package's interface under this selection. A
        // selection above a maximum refuses with that allowance's code before
        // any package byte is read.
        let interface = options.interface_limits.map_or_else(
            || Ok(InterfaceLimits::DEFAULT),
            |v| InterfaceLimits::parse(v.to_string().as_bytes()),
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
            interface,
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
    /// its authority before execution. Each call supplies every persistent
    /// copy, so together they are bounded by one call's setup material
    /// allowance.
    #[wasm_bindgen(js_name = setSetup)]
    pub fn set_setup(&mut self, slot: &str, material: &[u8]) -> Result<()> {
        let entry = self.active()?;
        if !entry.interface().setup_names().any(|name| name == slot) {
            return Err("web-setup-slot".into());
        }
        let allowance = entry.material_limits().setup_bytes;
        entry.invalidate_setup(slot)?;
        self.setups.remove(slot);
        check_material(
            material.len(),
            self.setups.values().map(Vec::len),
            self.capacity.wire_bytes,
            allowance,
        )?;
        self.setups.insert(slot.into(), material.into());
        Ok(())
    }

    /// Bind immutable opaque bytes for an existing SDK input reference. This
    /// grants no file access, material identity or setup authority.
    #[wasm_bindgen(js_name = setInput)]
    pub fn set_input(&mut self, name: &str, bytes: &[u8]) -> Result<()> {
        let entry = self.active()?;
        let allowance = entry.material_limits().reference_bytes;
        entry.invalidate_input(name)?;
        self.inputs.remove(name);
        if name.is_empty() || name.len() > 4096 || self.inputs.len() >= 1024 {
            return Err("web-input-name".into());
        }
        check_material(
            bytes.len(),
            self.inputs.values().map(|value| value.len()),
            self.capacity.wire_bytes,
            allowance,
        )?;
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
        let render = |diagnostics: Json| {
            json!({"success":success,"accepted":accepted,
                "error":report.native.outcome.as_ref().err(), "diagnostics":diagnostics,
                "output_error":report.output_error.as_ref().or(encoding_error.as_ref()),
                "timings": { "memory_preflight_ms": memory_preflight_ms,
                    "execute_cleanup_ms": execute_cleanup_ms, "output_encode_ms": output_encode_ms,
                    "diagnostics_ms": diagnostics_ms }})
            .to_string()
        };
        // The retained report text is charged to the call's invocation root.
        // When its diagnostics do not fit, the report keeps the outcome and
        // marks the omitted diagnostics instead.
        let mut text = render(diagnostics);
        let retention = match result.retain_bytes(text.len()) {
            Ok(retention) => retention,
            Err(_) => {
                text = render(json!({"omitted": "entry-output-limit"}));
                result.retain_bytes(text.len())?
            }
        };
        Ok(ProofResult {
            result,
            publish_proof: success && proof.is_none(),
            report: text,
            outputs,
            _report: retention,
        })
    }
}

/// Each persistent copy is one wire frame, and the copies of one kind together
/// stay within the allowance every call binds them under: setups within the
/// setup material allowance, named inputs within the named reference
/// allowance. Neither derives from the runner's capacity.
fn check_material(
    incoming: usize,
    mut held: impl Iterator<Item = usize>,
    wire_bytes: usize,
    allowance: usize,
) -> Result<()> {
    let total = held
        .try_fold(incoming, |total, len| total.checked_add(len))
        .ok_or("web-setup-limit")?;
    if incoming > wire_bytes || total > allowance {
        return Err("web-setup-limit".into());
    }
    Ok(())
}

fn entry_refusal(error: entry::EntryError) -> String {
    json!({"sdk_refusal": {"code": error.code(),
        "phase": format!("{:?}", error.phase).to_ascii_lowercase(),
        "path": error.path()}})
    .to_string()
}

/// Returned byte arrays are copies. Absence of `accepted` is not acceptance.
/// Every getter call takes a new copy: it is charged to the call's invocation
/// root before copying, and a getter refuses with `entry-output-limit` once
/// the root cannot afford another copy.
#[wasm_bindgen]
pub struct ProofResult {
    // Custody lasts through getter copies and Worker publication, until free.
    result: Arc<entry::ProofResult>,
    publish_proof: bool,
    report: String,
    outputs: Option<entry::OwnedEncodedResults>,
    // The retained report text's live allowance in the invocation root.
    _report: entry::ResultRetention,
}
#[wasm_bindgen]
impl ProofResult {
    #[wasm_bindgen(getter)]
    pub fn proof(&self) -> Result<Vec<u8>> {
        if self.publish_proof {
            self.result.copy_proof()
        } else {
            Ok(Vec::new())
        }
    }
    #[wasm_bindgen(getter)]
    pub fn report(&self) -> Result<String> {
        let copy = self.result.copy_bytes(self.report.as_bytes())?;
        Ok(String::from_utf8(copy).expect("copy of UTF-8 text"))
    }
    #[wasm_bindgen(getter)]
    pub fn outputs(&self) -> Result<Option<Vec<u8>>> {
        self.outputs
            .as_ref()
            .map(entry::OwnedEncodedResults::copy)
            .transpose()
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
    #[test]
    fn provider_selections_range_over_the_installed_providers() {
        let installed = serde_json::to_value(CpuInstallation::standard().unwrap().target())
            .unwrap()["providers"]
            .clone();
        let installed: Vec<Provider> = serde_json::from_value(installed).unwrap();
        assert!(!installed.is_empty());
        let selections = installed
            .iter()
            .map(|provider| vec![*provider])
            .chain([installed.clone(), installed.iter().rev().copied().collect()]);
        for selection in selections {
            let options = json!({ "providers": selection }).to_string();
            // The selection is admitted; the unpinned package refuses next.
            assert_eq!(
                ProofSession::new(&[], &[0; 32], &options, &[])
                    .err()
                    .unwrap(),
                "entry-package-identity",
                "{options}"
            );
        }
        let mut repeated = installed.clone();
        repeated.push(installed[0]);
        let options = json!({ "providers": repeated }).to_string();
        assert_eq!(
            ProofSession::new(&[], &[0; 32], &options, &[])
                .err()
                .unwrap(),
            "web-options"
        );
    }
    #[test]
    fn persistent_material_stays_within_the_allowance_each_call_binds_it_under() {
        let limits = zkc::execution::MaterialLimits::DEFAULT;
        let wire = Capacity::default().wire_bytes;
        for allowance in [limits.setup_bytes, limits.reference_bytes] {
            // Copies of one kind together fill the allowance and no more.
            let frames = allowance / wire;
            let held = || std::iter::repeat_n(wire, frames - 1).chain([1]);
            let room = allowance - (frames - 1) * wire - 1;
            assert!(room < wire);
            check_material(room, held(), wire, allowance).unwrap();
            assert_eq!(
                check_material(room + 1, held(), wire, allowance).unwrap_err(),
                "web-setup-limit"
            );
        }
        // Each copy is still one wire frame.
        assert_eq!(
            check_material(wire + 1, std::iter::empty(), wire, usize::MAX).unwrap_err(),
            "web-setup-limit"
        );
        // Setups and named inputs have separate allowances.
        assert_ne!(limits.setup_bytes, limits.reference_bytes);
    }
    #[test]
    fn interface_selections_refuse_above_their_maxima_before_any_package() {
        let admit = |record: &Json| {
            let options = json!({ "interface_limits": record }).to_string();
            ProofSession::new(&[], &[0; 32], &options, &[])
                .err()
                .unwrap()
        };
        // A lowered and a raised selection are accepted; the unpinned package
        // refuses next.
        let lowered = InterfaceLimits {
            work: 64,
            descriptor_bytes: 64,
        };
        for selection in [lowered, InterfaceLimits::MAXIMUM] {
            assert_eq!(admit(&selection.record()), "entry-package-identity");
        }
        // One above a maximum refuses with that allowance's own code.
        for (field, code) in [
            (1, "entry-interface-work-limit"),
            (2, "entry-interface-descriptor-bytes-limit"),
        ] {
            let mut record = InterfaceLimits::MAXIMUM.record();
            let maximum: u64 = record[field].as_str().unwrap().parse().unwrap();
            record[field] = json!((maximum + 1).to_string());
            assert_eq!(admit(&record), code);
        }
        let mut other = InterfaceLimits::DEFAULT.record();
        other[0] = json!("zkc.material-limits/0");
        assert_eq!(admit(&other), "interface-limits-format");
    }
    /// The browser transport forwards both records as opaque JSON; the session
    /// is their only reader and refuses a malformed one with the SDK's code.
    #[test]
    fn malformed_capacity_and_interface_records_refuse_with_the_sdk_codes() {
        let admit = |options: Json| {
            ProofSession::new(&[], &[0; 32], &options.to_string(), &[])
                .err()
                .unwrap()
        };
        let mut capacity = Capacity::default().record();
        capacity[0] = json!("zkc.material-limits/0");
        assert_eq!(
            admit(json!({ "capacity": capacity })),
            "native-capacity-format"
        );
        assert_eq!(
            admit(json!({ "capacity": ["zkc.native-capacity/0", "1"] })),
            "artifact-record"
        );
        let mut limits = InterfaceLimits::DEFAULT.record();
        limits[1] = json!(1);
        assert_eq!(admit(json!({ "interface_limits": limits })), "tree-kind");
        assert_eq!(
            admit(json!({ "interface_limits": ["zkc.interface-limits/0", "1"] })),
            "artifact-record"
        );
        assert_eq!(
            admit(json!({ "interface_limits": { "tag": "zkc.interface-limits/0" } })),
            "artifact-json-kind"
        );
    }
    /// Admission reads the package's interface under the selected
    /// allowances: a lowered selection refuses what the default admits, and a
    /// raised one admits what the default refuses.
    #[cfg(feature = "test-utils")]
    #[test]
    fn interface_selections_bound_the_admitted_interface_read() {
        use zkc::entry::testing;
        let (interface, artifact) = testing::authored_proof();
        let admit = |interface: &Json, selection: Option<InterfaceLimits>| {
            let (package, pin) = testing::package(interface, &artifact);
            let mut options = json!({ "allow_authored": true });
            if let Some(selection) = selection {
                options["interface_limits"] = selection.record();
            }
            ProofSession::new(&package, &pin, &options.to_string(), &[])
                .map(drop)
                .map_err(|error| {
                    let refusal: Json = serde_json::from_str(&error).unwrap();
                    let text =
                        |field: &str| refusal["sdk_refusal"][field].as_str().unwrap().to_owned();
                    (text("phase"), text("code"))
                })
        };
        let refused = |code: &str| Err(("interface".to_owned(), code.to_owned()));
        let work = |work| InterfaceLimits {
            work,
            ..InterfaceLimits::DEFAULT
        };
        assert_eq!(admit(&interface, None), Ok(()));
        assert_eq!(
            admit(&interface, Some(work(64))),
            refused("entry-interface-work-limit")
        );
        assert_eq!(
            admit(
                &interface,
                Some(InterfaceLimits {
                    descriptor_bytes: 64,
                    ..InterfaceLimits::DEFAULT
                })
            ),
            refused("entry-interface-descriptor-bytes-limit")
        );
        // Schema validation charges each port's display type twice, once for
        // the port and once for its schema. Take the shortest display type
        // at the fixture's four ports that the default work allowance
        // refuses, then the least work selection that admits it.
        let least = |mut low: usize, mut high: usize, admits: &dyn Fn(usize) -> bool| {
            while low < high {
                let middle = low + (high - low) / 2;
                if admits(middle) {
                    high = middle;
                } else {
                    low = middle + 1;
                }
            }
            low
        };
        let padded = |length: usize| {
            let mut padded = interface.clone();
            let display = json!("t".repeat(length));
            for direction in ["inputs", "outputs"] {
                for port in padded["protocols"][0][direction].as_array_mut().unwrap() {
                    port["type"] = display.clone();
                    port["schema"]["type"] = display.clone();
                }
            }
            padded
        };
        let length = least(1, 256 * 1024, &|length| {
            admit(&padded(length), None).is_err()
        });
        assert_eq!(admit(&padded(length - 1), None), Ok(()));
        let padded = padded(length);
        assert_eq!(admit(&padded, None), refused("entry-interface-work-limit"));
        // The least admitting selection is honored exactly, neither clamped
        // to the default nor rounded.
        let needed = least(
            InterfaceLimits::DEFAULT.work + 1,
            InterfaceLimits::MAXIMUM.work,
            &|selected| admit(&padded, Some(work(selected))).is_ok(),
        );
        assert_eq!(admit(&padded, Some(work(needed))), Ok(()));
        assert_eq!(
            admit(&padded, Some(work(needed - 1))),
            refused("entry-interface-work-limit")
        );
    }
}
