//! Sequential prepared execution under caller-managed installation custody.
//!
//! A prepared artifact retains a checked program and bounded, validated key
//! material only. Each call rebinds its actual context, statement, configuration
//! and budgets, constructs a NEW NativeBackend, and owns a new transcript,
//! RNG/nonce authority, runner and proof reader/writer. No backend is cloned.
//!
//! CheckedBundle establishes the existing construction/projection/profile
//! admission, NOT law truth or external caller requirements. An application
//! wrapper may attach authenticated caller requirements with `with_requirements`,
//! check their applicability to each request, and retire both together. Nothing
//! here authenticates a caller contract or proves its trusted laws implicitly.
use super::{
    ArtifactReport, CacheLimits, CacheUsage, CheckedBundle, InputLimits, Observed, TraceMode,
    inputs::BoundInputs, io, material::MaterialCache,
};
use serde_json::Value as Json;
use std::{
    path::Path,
    sync::Arc,
    time::{Duration, Instant},
};
use zkc_backends::{NativeBackend, Value};
use zkc_runtime::interactive::{Runner, Usage, ValueBudget};

/// Named file boundary for source/descriptor/construction/physical custody.
/// The files are captured and checked by CheckedBundle::load, once.
pub struct ArtifactPaths<'a> {
    pub source: &'a str,
    pub descriptor: &'a str,
    pub construction: &'a str,
    pub participants: &'a str,
}

struct Installation {
    compiler: String,
    lean: String,
}

/// Opaque, process-local caller installation epoch. Clones share an epoch;
/// `new` always creates a different one, even for the same executable paths.
/// Paths launch checkers; they are NOT content identity or change detection.
///
/// The caller must keep actual checkers, their dependencies, backend build,
/// admission policy and application requirements fixed for the epoch. Create a
/// new epoch and re-admit when any changes. Calls compare epoch authority only:
/// they neither reopen checkers nor hash binaries, watch paths, or attest a
/// deployment. This is not a persistent/cross-installation admission cache.
#[derive(Clone)]
pub struct CheckerInstallation(Arc<Installation>);
impl CheckerInstallation {
    pub fn new(compiler: impl Into<String>, lean: impl Into<String>) -> Self {
        Self(Arc::new(Installation {
            compiler: compiler.into(),
            lean: lean.into(),
        }))
    }
    pub fn prepare(
        &self,
        paths: ArtifactPaths<'_>,
        limits: CacheLimits,
    ) -> Result<PreparedArtifact, String> {
        let checked = CheckedBundle::load(
            paths.source,
            paths.descriptor,
            paths.construction,
            paths.participants,
            &self.0.compiler,
            &self.0.lean,
        )?;
        Ok(self.prepare_checked(checked, limits))
    }
    /// Transfer an already immutable CheckedBundle without rerunning admission.
    /// The caller attests that it was checked under THIS installation's actual
    /// checker/backend/policy. CheckedBundle does not carry installation identity;
    /// this association cannot be recovered or verified from its contents.
    pub fn prepare_checked(&self, checked: CheckedBundle, limits: CacheLimits) -> PreparedArtifact {
        PreparedArtifact {
            checked,
            installation: self.clone(),
            cache: MaterialCache::new(limits),
            requirements: None,
        }
    }
}

/// Bounded JSON ingress. This may contain secret witness data; it belongs to the
/// caller, is borrowed for a single call, and is NEVER retained by preparation.
/// Parsing checks structural limits only; each invocation performs binding.
pub struct InvocationInputs(Json);
impl InvocationInputs {
    pub fn from_slice(bytes: &[u8]) -> Result<Self, String> {
        io::parse(bytes, io::INPUT_LIMIT).map(Self)
    }
    pub fn read(path: impl AsRef<Path>) -> Result<Self, String> {
        Self::from_slice(&io::read(path, io::INPUT_LIMIT)?)
    }
    pub fn document(&self) -> &Json {
        &self.0
    }
}

/// Per-invocation limits are enforced on hits and misses. Native backend and
/// individual-value and structural hard limits remain unchanged. Value budgets
/// are caller policy, not part of the proof or selectable by source code.
/// Trace disabling has the same diagnostic
/// (not trace-equivalence) contract as the CLI's `--trace=none`.
#[derive(Clone, Copy, Debug)]
pub struct InvocationOptions {
    pub transcript_budget: u64,
    pub input_limits: InputLimits,
    pub trace: TraceMode,
    pub value_budget: ValueBudget,
}
impl InvocationOptions {
    pub fn new(transcript_budget: u64) -> Self {
        Self {
            transcript_budget,
            input_limits: InputLimits::default(),
            trace: TraceMode::Full,
            value_budget: ValueBudget::default(),
        }
    }
}

#[derive(Debug)]
pub enum InvocationError {
    InstallationMismatch,
    Binding(String),
    Runtime(String),
}
impl std::fmt::Display for InvocationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InstallationMismatch => f.write_str("prepared artifact installation mismatch"),
            Self::Binding(s) | Self::Runtime(s) => f.write_str(s),
        }
    }
}
impl std::error::Error for InvocationError {}

/// Execution result, including failed runs. Runner outputs and capabilities are
/// dropped. Proof bytes and events carry the protocol's public observations;
/// this does not assert zero knowledge or secrecy. Durations exclude admission;
/// execution time includes dropping the runner, backend and wire decoder.
pub struct PreparedReport<T> {
    pub execution: ArtifactReport<T>,
    pub binding: [u8; 32],
    pub usage: Usage,
    pub events: Option<Vec<Json>>,
    pub bind_time: Duration,
    pub run_time: Duration,
}

/// One immutable program, one caller installation, bounded key reuse. Methods
/// take `&mut self` to serialize calls; parallel execution is not provided.
/// The key cache starts empty and is populated by invocation binding.
/// A failed call may retain keys already fully validated, never partially
/// imported keys or execution state. Drop/clear releases this cache's holdings.
/// Prover-key files are captured afresh on every call, including hits: digest,
/// material fingerprint AND full verifier bytes select an authenticated import.
/// Ordinary wire decoding and proof point validation are never cached here.
///
/// This handle does not establish law truth. `with_requirements` checks and
/// retains an authenticated caller contract against this exact candidate; the
/// application still authorizes each request. Changing requirements requires
/// a new admission.
///
/// ```no_run
/// use zkc_tools::artifact::{ArtifactPaths, CacheLimits, CheckerInstallation,
///     InvocationInputs, InvocationOptions};
/// let installation = CheckerInstallation::new("/installed/zkc-compile", "/installed/interactive-protocol");
/// let mut prepared = installation.prepare(ArtifactPaths {
///     source: "source.json", descriptor: "descriptor.json",
///     construction: "construction.json", participants: "physical.json",
/// }, CacheLimits::default()).unwrap();
/// // If the wrapper already has a CheckedBundle admitted under this epoch:
/// // let mut prepared = installation.prepare_checked(checked, CacheLimits::default());
/// let producer = InvocationInputs::read("producer.json").unwrap();
/// let validator = InvocationInputs::read("validator.json").unwrap();
/// let options = InvocationOptions::new(10_000);
/// for _ in 0..3 {
///     let proof = prepared.produce(&installation, &producer, options)
///         .unwrap().execution.outcome.unwrap();
///     prepared.validate(&installation, &validator, &proof, options)
///         .unwrap().execution.outcome.unwrap();
/// }
/// ```
pub struct PreparedArtifact {
    checked: CheckedBundle,
    installation: CheckerInstallation,
    cache: MaterialCache,
    requirements: Option<super::requirements::CheckedRequirements>,
}
impl PreparedArtifact {
    /// Bind authenticated caller requirements to this exact captured source and
    /// candidate under the installation that checked the artifact. This consumes
    /// the handle: a refused check cannot return an accidentally usable handle.
    /// Replacing requirements requires a new installation/admission, not mutation.
    /// The caller still checks per-invocation ledger/context authorization.
    pub fn with_requirements(
        mut self,
        installation: &CheckerInstallation,
        requirements: super::ClaimRequirements,
        choices: super::PhysicalChoices,
    ) -> Result<Self, String> {
        if !Arc::ptr_eq(&self.installation.0, &installation.0) {
            return Err(InvocationError::InstallationMismatch.to_string());
        }
        if self.requirements.is_some() {
            return Err("artifact-requirements-already-checked".into());
        }
        self.requirements = Some(super::requirements::check(
            &self.checked,
            &installation.0.compiler,
            requirements,
            choices,
        )?);
        Ok(self)
    }
    pub fn checked_requirements(&self) -> Option<&super::ClaimRequirements> {
        self.requirements.as_ref().map(|r| &r.requirements)
    }
    pub fn checked_choices(&self) -> Option<&super::PhysicalChoices> {
        self.requirements.as_ref().map(|r| &r.choices)
    }
    pub fn cache_usage(&self) -> CacheUsage {
        self.cache.usage()
    }
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }

    fn bind(
        &mut self,
        installation: &CheckerInstallation,
        input: &InvocationInputs,
        options: InvocationOptions,
        producer: bool,
    ) -> Result<BoundInputs, InvocationError> {
        if !Arc::ptr_eq(&self.installation.0, &installation.0) {
            return Err(InvocationError::InstallationMismatch);
        }
        let role = self
            .checked
            .role(producer)
            .map_err(InvocationError::Binding)?;
        self.checked
            .bind_cached(
                &input.0,
                &role,
                options.transcript_budget,
                options.input_limits,
                &mut self.cache,
            )
            .map_err(InvocationError::Binding)
    }

    pub fn produce(
        &mut self,
        installation: &CheckerInstallation,
        input: &InvocationInputs,
        options: InvocationOptions,
    ) -> Result<PreparedReport<Vec<u8>>, InvocationError> {
        self.execute(installation, input, options, None)
    }

    pub fn validate(
        &mut self,
        installation: &CheckerInstallation,
        input: &InvocationInputs,
        proof: &[u8],
        options: InvocationOptions,
    ) -> Result<PreparedReport<()>, InvocationError> {
        let report = self.execute(installation, input, options, Some(proof))?;
        Ok(PreparedReport {
            execution: ArtifactReport {
                outcome: report.execution.outcome.map(|_| ()),
                bytes: report.execution.bytes,
                messages: report.execution.messages,
                cancelled: report.execution.cancelled,
            },
            binding: report.binding,
            usage: report.usage,
            events: report.events,
            bind_time: report.bind_time,
            run_time: report.run_time,
        })
    }

    fn execute(
        &mut self,
        installation: &CheckerInstallation,
        input: &InvocationInputs,
        options: InvocationOptions,
        proof: Option<&[u8]>,
    ) -> Result<PreparedReport<Vec<u8>>, InvocationError> {
        let start = Instant::now();
        let bound = self.bind(installation, input, options, proof.is_none())?;
        let bind_time = start.elapsed();
        let start = Instant::now();
        let backend = Observed::new(bound.backend, &self.checked, options.trace)
            .map_err(InvocationError::Runtime)?;
        let role = if proof.is_none() {
            &self.checked.producer
        } else {
            &self.checked.validator
        };
        let mut runner: Runner<Observed<NativeBackend>> = Runner::new_with_value_budget(
            &self.checked.admitted,
            &self.checked.entry,
            role,
            "artifact",
            backend,
            bound.values,
            options.value_budget,
        )
        .map_err(|e| InvocationError::Runtime(e.error.to_string()))?;
        let execution = match proof {
            None => {
                let report = super::produce(&mut runner, &bound.binding);
                ArtifactReport {
                    outcome: report.outcome.map(|p| p.proof),
                    messages: report.messages,
                    bytes: report.bytes,
                    cancelled: report.cancelled,
                }
            }
            Some(proof) => {
                let report = super::validate_with_decoder(
                    &mut runner,
                    proof,
                    &bound.binding,
                    self.checked.acceptance,
                    |v| {
                        if let Value::Bool(b) = v {
                            Some(*b)
                        } else {
                            None
                        }
                    },
                    &bound.decoder,
                );
                ArtifactReport {
                    outcome: report.outcome.map(|_| Vec::new()),
                    messages: report.messages,
                    bytes: report.bytes,
                    cancelled: report.cancelled,
                }
            }
        };
        let usage = runner.usage();
        let events = (options.trace == TraceMode::Full).then(|| runner.backend().events().to_vec());
        // Include per-invocation teardown in lifecycle measurements. Only the
        // public report and the explicitly bounded key cache survive this call.
        drop(runner);
        drop(bound.decoder);
        drop(bound.resources);
        Ok(PreparedReport {
            execution,
            binding: bound.binding,
            usage,
            events,
            bind_time,
            run_time: start.elapsed(),
        })
    }
}

#[cfg(test)]
mod tests;
