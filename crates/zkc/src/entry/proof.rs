//! Independent named proof calls over the admitted common native deployment.
use super::errors::{EntryError as E, EntryPhase as P, EntryResult};
use super::{
    EntryAssets, Interface, NamedValues, Package, RoleInputs, SetupAuthority, arguments, setups,
    value,
};
use crate::execution::Capacity;
use crate::proof::{AttemptPolicy, NativeDeployment, NativeProofReport, ProofInputs};
use std::collections::BTreeMap;
use zkc_cpu::CpuBackend;

type Result<T> = std::result::Result<T, String>;

/// Require Host absorption of the authorized invocation at managed transcript
/// initialization, or explicitly permit a library-owned binding policy.
/// Neither choice establishes that message handlers or samplers are secure.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum BindingPolicy {
    #[default]
    TranscriptRequired,
    AllowAuthored,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingScope {
    Transcript,
    HeaderOnly,
    /// Binding is entirely defined by the authored protocol; there is no Host header.
    Authored,
}
#[derive(Clone, Debug)]
pub struct ProofOptions {
    pub installation: zkc_cpu::CpuInstallation,
    pub capacity: Capacity,
    pub external_work: u64,
    pub binding: BindingPolicy,
}
impl Default for ProofOptions {
    fn default() -> Self {
        Self {
            capacity: Capacity::default(),
            external_work: CpuBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
            binding: BindingPolicy::default(),
            installation: Default::default(),
        }
    }
}
impl ProofOptions {
    /// Select the frozen CPU support view before proof admission.
    pub fn with_installation(mut self, installation: zkc_cpu::CpuInstallation) -> Self {
        self.installation = installation;
        self
    }
}
/// Explicit retry authorization. Count defaults to one; all cumulative work
/// and payload ceilings remain those of the admitted ProofOptions.capacity.
#[derive(Clone, Copy, Debug)]
pub struct AttemptOptions {
    pub count: u64,
    pub proof_bytes: usize,
}
impl Default for AttemptOptions {
    fn default() -> Self {
        Self {
            count: 1,
            proof_bytes: zkc_runtime::host::wire::MAX_PROOF_BYTES,
        }
    }
}
/// Select the input side independently of the presence of a witness file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofOperation {
    Prove,
    Verify,
}

/// Public values are the application's independently authorized statement. The
/// private map supplies only the invoked role's nonpublic inputs. The adapter
/// assembles shared operands and native admission checks canonical agreement.
#[derive(Debug, Default)]
pub struct ProofRequest {
    pub public: NamedValues,
    pub private: RoleInputs,
    pub context: Vec<u8>,
    /// None uses the operational default for derivation and zero for authored jobs.
    pub transcript_budget: Option<u64>,
    pub setups: BTreeMap<String, Vec<u8>>,
}
/// An authenticated package, checked interface, admitted deployment and the
/// package's admitted expression assets, which are the deployment's only
/// evaluator source.
pub struct ProofEntry {
    package: Package,
    interface: super::BoundInterface,
    assets: EntryAssets,
    native: NativeDeployment,
    scope: BindingScope,
    completion: Option<usize>,
    setup_authority: SetupAuthority,
    roles: (usize, usize),
    material: std::sync::Arc<std::sync::Mutex<zkc_cpu::material::VerifierMaterials>>,
}
/// The outer call result distinguishes preparation refusal. This report must
/// still be checked for execution success, including rejection and cleanup.
#[must_use = "check is_success() or into_result(); invocation preparation is not proof acceptance"]
pub struct ProofReport {
    pub native: NativeProofReport,
    pub outputs: Option<NamedValues>,
    pub output_error: Option<String>,
    pub binding_scope: BindingScope,
}
impl ProofReport {
    /// Distinguish normal semantic rejection from execution, cleanup, or output
    /// reconstruction failure. A successful producer has no verifier decision.
    pub fn verification_result(&self) -> Option<bool> {
        if self.output_error.is_some() {
            return None;
        }
        match self.native.verification_result()? {
            true if self.outputs.is_some() => Some(true),
            false => Some(false),
            _ => None,
        }
    }

    /// For verification, true means the selected acceptance result was true and
    /// complete cleanup/result reconstruction succeeded. Production succeeds
    /// when the complete unpublished proof and its outputs are available.
    #[must_use]
    pub fn is_success(&self) -> bool {
        self.native.outcome.is_ok()
            && self.native.cleanup_errors.is_empty()
            && self.output_error.is_none()
            && self.outputs.is_some()
    }
    /// Preserve the complete report on either branch, including failure usage
    /// and cleanup. Preparation errors remain the outer call's separate result.
    pub fn into_result(self) -> std::result::Result<Self, Box<Self>> {
        if self.is_success() {
            Ok(self)
        } else {
            Err(Box::new(self))
        }
    }
}
impl ProofEntry {
    pub fn with_cpu(mut self, cpu: crate::execution::CpuExecution) -> Self {
        self.native = self.native.with_cpu(cpu);
        self
    }
    pub fn installation(&self) -> &zkc_cpu::CpuInstallation {
        self.native.installation()
    }
    pub fn cpu(&self) -> &crate::execution::CpuExecution {
        self.native.cpu()
    }
    /// Set deployment-owned public computation storage. Zero limits disable it.
    pub fn with_preparation_limits(mut self, limits: zkc_runtime::vm::PreparationLimits) -> Self {
        self.native = self.native.with_preparation_limits(limits);
        self
    }
    pub fn preparation_stats(&self) -> zkc_runtime::vm::PreparationStats {
        self.native.preparation_stats()
    }

    pub fn with_ring_work_limit(mut self, limit: u64) -> Result<Self> {
        self.native = self.native.with_ring_work_limit(limit)?;
        Ok(self)
    }
    pub fn admit(
        package: Package,
        options: ProofOptions,
        setups: SetupAuthority,
    ) -> EntryResult<Self> {
        Self::admit_with_cpu(
            package,
            options,
            setups,
            crate::execution::CpuExecution::serial().map_err(|e| E::new(P::Admission, e))?,
        )
    }
    /// Supply CPU ownership before admitting any proof backend.
    pub fn admit_with_cpu(
        package: Package,
        options: ProofOptions,
        setups: SetupAuthority,
        cpu: crate::execution::CpuExecution,
    ) -> EntryResult<Self> {
        Self::admit_inner(package, options, setups, None, false, cpu)
    }
    /// Admit only the selected operation's executable installation and input plan.
    pub fn admit_operation(
        package: Package,
        options: ProofOptions,
        setups: SetupAuthority,
        operation: ProofOperation,
    ) -> EntryResult<Self> {
        Self::admit_operation_with_cpu(
            package,
            options,
            setups,
            operation,
            crate::execution::CpuExecution::serial().map_err(|e| E::new(P::Admission, e))?,
        )
    }
    /// Admit one operation with an application-owned CPU context.
    pub fn admit_operation_with_cpu(
        package: Package,
        options: ProofOptions,
        setups: SetupAuthority,
        operation: ProofOperation,
        cpu: crate::execution::CpuExecution,
    ) -> EntryResult<Self> {
        Self::admit_inner(package, options, setups, Some(operation), false, cpu)
    }
    pub(crate) fn admit_host_operation(
        package: Package,
        options: ProofOptions,
        setups: SetupAuthority,
        operation: ProofOperation,
        cpu: crate::execution::CpuExecution,
    ) -> EntryResult<Self> {
        Self::admit_inner(package, options, setups, Some(operation), true, cpu)
    }
    fn admit_inner(
        package: Package,
        options: ProofOptions,
        setups: SetupAuthority,
        operation: Option<ProofOperation>,
        retained_inputs: bool,
        cpu: crate::execution::CpuExecution,
    ) -> EntryResult<Self> {
        let interface =
            crate::entry::BoundInterface::read(&package).map_err(|e| E::new(P::Interface, e))?;
        let proof = interface
            .proof()
            .ok_or_else(|| E::new(P::Admission, "entry-job-kind"))?;
        let roles = (proof.prover, proof.verifier);
        let completion = proof.completion;
        let scope = if proof.suite.is_some() {
            BindingScope::Transcript
        } else if proof.format == zkc_runtime::host::wire::ProofFormat::Native {
            BindingScope::HeaderOnly
        } else {
            BindingScope::Authored
        };
        if scope != BindingScope::Transcript && options.binding == BindingPolicy::TranscriptRequired
        {
            return Err(E::new(P::Admission, "entry-proof-binding-policy"));
        }
        if retained_inputs {
            arguments::check_host_ports(&interface, operation)
                .map_err(|e| E::new(P::Interface, e))?;
        } else if let Some(operation) = operation {
            arguments::check_proof_ports(&interface, operation)
                .map_err(|e| E::new(P::Interface, e))?;
        } else {
            arguments::check_ports(&interface).map_err(|e| E::new(P::Interface, e))?;
        }
        let setup_authority = setups.clone();
        let mut authority =
            setups::proof_authority(&interface, setups).map_err(|e| E::new(P::Authority, e))?;
        if let Some(operation) = operation {
            let role = &interface.roles()[if operation == ProofOperation::Prove {
                roles.0
            } else {
                roles.1
            }];
            let selected = interface
                .input_ports(role)
                .flat_map(|p| p.definition.native.iter().map(|i| *i as usize))
                .collect::<std::collections::BTreeSet<_>>();
            authority.inputs.retain(|i, _| selected.contains(i));
        }
        let native = match operation {
            Some(op) if retained_inputs => NativeDeployment::admit_host_operation(
                &package.authenticated_artifact(),
                authority,
                op == ProofOperation::Prove,
                cpu,
                options.installation.clone(),
            ),
            Some(op) => NativeDeployment::admit_artifact_operation(
                &package.authenticated_artifact(),
                authority,
                Some(op == ProofOperation::Prove),
                cpu,
                options.installation.clone(),
            ),
            None => NativeDeployment::admit_artifact(
                &package.authenticated_artifact(),
                authority,
                cpu,
                options.installation.clone(),
            ),
        }
        .and_then(|n| n.with_capacity(options.capacity))
        .and_then(|n| n.with_external_work_limit(options.external_work))
        .map_err(|e| E::new(P::Admission, e))?;
        interface
            .check_proof(&native)
            .map_err(|e| E::new(P::Binding, e))?;
        let assets = if let Some(operation) = operation {
            EntryAssets::admit_role(
                &package,
                &interface,
                native.entry().admitted(),
                native.entry().entry(),
                if operation == ProofOperation::Prove {
                    native.entry().producer_role()
                } else {
                    native.entry().validator_role()
                },
            )
        } else {
            EntryAssets::admit(
                &package,
                &interface,
                native.entry().admitted(),
                native.entry().entry(),
            )
        }
        .map_err(|e| E::new(P::Assets, e))?;
        let native = native
            .with_ring_assets(assets.registry().clone())
            .with_relation_assets(assets.relation_registry().clone());
        let material = std::sync::Arc::new(std::sync::Mutex::new(
            zkc_cpu::material::VerifierMaterials::new(
                native.capacity().backend().ark_bounds(),
                native.installation().clone(),
                native
                    .capacity()
                    .values
                    .live_bytes
                    .min(native.capacity().values.total_bytes),
            ),
        ));
        Ok(Self {
            material,
            completion,
            setup_authority,
            roles,
            package,
            interface,
            assets,
            native,
            scope,
        })
    }
    /// Invalidate a material slot when an adapter replaces its stored raw bytes,
    /// even if the replacement is malformed or rejected before the next call.
    pub fn invalidate_setup(&self, slot: &str) -> Result<()> {
        let pin = self
            .setup_authority
            .keys
            .get(slot)
            .ok_or("entry-setup-material")?;
        self.material
            .lock()
            .map_err(|_| "native-setup-material")?
            .invalidate(pin);
        Ok(())
    }
    /// Invalidate persistent prover imports before an adapter replaces a named
    /// input, including replacements rejected before document decoding. Sources
    /// do not yet identify a setup pin, so all prover imports are cleared while
    /// verifier imports and already checked calls retain their own custody.
    pub fn invalidate_prover_inputs(&self) -> Result<()> {
        self.material
            .lock()
            .map_err(|_| "native-setup-material")?
            .invalidate_provers();
        Ok(())
    }
    pub(super) fn observe_setups(&self, setups: &BTreeMap<String, Vec<u8>>) {
        if let Ok(mut material) = self.material.lock() {
            for (slot, pin) in &self.setup_authority.keys {
                material.observe_replacement(pin, setups.get(slot).map(Vec::as_slice));
            }
        }
    }
    pub fn capacity(&self) -> Capacity {
        self.native.capacity()
    }
    pub fn package(&self) -> &Package {
        &self.package
    }
    pub fn interface(&self) -> &Interface {
        &self.interface
    }
    pub fn assets(&self) -> &EntryAssets {
        &self.assets
    }
    pub fn binding_scope(&self) -> BindingScope {
        self.scope
    }
    pub(crate) fn output_types(
        &self,
        operation: ProofOperation,
    ) -> &[zkc_runtime::vm::PhysicalType] {
        let role = match operation {
            ProofOperation::Prove => self.native.entry().producer(),
            ProofOperation::Verify => self.native.entry().validator(),
        };
        let Some(role) = role else { return &[] };
        // The admitted map covers original outputs, excluding any transcript
        // state added by derivation. Only original outputs reach file encoding.
        let count = self.native.source_interface().roles[&role.role]
            .outputs
            .len();
        &role.outputs[..count]
    }
    pub fn prove(&self, request: ProofRequest) -> EntryResult<ProofReport> {
        self.execute(request, None, None)
    }
    pub fn verify(&self, request: ProofRequest, proof: &[u8]) -> EntryResult<ProofReport> {
        self.execute(request, Some(proof), None)
    }
    /// Use the Entry's completion result with explicit application authorization.
    /// The native controller retains actual providers and cumulative work.
    pub fn prove_attempts(
        &self,
        request: ProofRequest,
        options: AttemptOptions,
    ) -> EntryResult<ProofReport> {
        self.execute(request, None, Some(options))
    }
    fn execute(
        &self,
        request: ProofRequest,
        proof: Option<&[u8]>,
        attempts: Option<AttemptOptions>,
    ) -> EntryResult<ProofReport> {
        let mut imports = crate::host::setups::VerifierKeys::new(
            self.native.capacity().backend().ark_bounds(),
            self.installation().clone(),
        )
        .with_material(self.material.clone());
        self.execute_with(request, proof, attempts, &mut imports)
    }
    pub(crate) fn execute_with(
        &self,
        request: ProofRequest,
        proof: Option<&[u8]>,
        attempts: Option<AttemptOptions>,
        imports: &mut crate::host::setups::VerifierKeys,
    ) -> EntryResult<ProofReport> {
        self.observe_setups(&request.setups);
        let producer = proof.is_none();
        let attempts = self.attempt_policy(producer, attempts, self.native.capacity())?;
        let inputs = self
            .inputs(request, producer, self.native.capacity())
            .map_err(|e| E::new(P::Request, e))?;
        Ok(self.report(
            self.native
                .execute_prepared(
                    &inputs,
                    attempts.as_ref().map_or_else(
                        || crate::proof::Invocation::one_shot(proof),
                        crate::proof::Invocation::Attempts,
                    ),
                    imports,
                )
                .map_err(|e| E::new(P::Preparation, e))?,
            producer,
        ))
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn execute_shared(
        &self,
        request: ProofRequest,
        proof: Option<&[u8]>,
        capacity: Capacity,
        external: u64,
        ring: u64,
        sequence: u64,
        proof_bytes: usize,
        ledger: zkc_runtime::vm::ExecutionLedger,
    ) -> EntryResult<ProofReport> {
        let producer = proof.is_none();
        let attempts = self.attempt_policy(producer, None, capacity)?;
        // Public binding owns one wire copy per verifier-key port. Reserve all
        // copies before argument construction, under the effective child limit.
        let key_bytes = setups::material_bytes(&self.interface, &request.setups, capacity)
            .map_err(|e| E::new(P::Request, e))?;
        let _keys_live = zkc_runtime::host::wire::reserve_allocation(Some(&ledger), key_bytes)
            .map_err(|e| E::new(P::Preparation, e))?;
        let inputs = self
            .inputs(request, producer, capacity)
            .map_err(|e| E::new(P::Request, e))?;
        let native = self
            .native
            .clone()
            .with_invocation_limits(capacity, external, ring, sequence, proof_bytes)
            .with_shared_ledger(ledger);
        Ok(self.report(
            native
                .execute(
                    &inputs,
                    attempts.as_ref().map_or_else(
                        || crate::proof::Invocation::one_shot(proof),
                        crate::proof::Invocation::Attempts,
                    ),
                )
                .map_err(|e| E::new(P::Preparation, e))?,
            producer,
        ))
    }
    /// Validate and load inputs under the same setup, shape and capacity rules
    /// as execution. No randomness, transcript or proof parsing occurs here.
    pub fn check_inputs(
        &self,
        request: ProofRequest,
        operation: ProofOperation,
        attempts: Option<AttemptOptions>,
    ) -> EntryResult<()> {
        let producer = operation == ProofOperation::Prove;
        if !producer && attempts.is_some() {
            return Err(E::new(P::Request, "entry-attempt-operation"));
        }
        let attempts = self.attempt_policy(producer, attempts, self.native.capacity())?;
        let inputs = self
            .inputs(request, producer, self.native.capacity())
            .map_err(|e| E::new(P::Request, e))?;
        let invocation = attempts.as_ref().map_or_else(
            || {
                if producer {
                    crate::proof::Invocation::Prove
                } else {
                    crate::proof::Invocation::Verify(&[])
                }
            },
            crate::proof::Invocation::Attempts,
        );
        self.native
            .check_inputs(&inputs, invocation)
            .map_err(|e| E::new(P::Preparation, e))
    }
    fn attempt_policy(
        &self,
        producer: bool,
        attempts: Option<AttemptOptions>,
        capacity: Capacity,
    ) -> EntryResult<Option<AttemptPolicy>> {
        Ok(
            if producer && (attempts.is_some() || self.completion.is_some()) {
                let options = attempts.unwrap_or_default();
                let completion = self
                    .completion
                    .ok_or_else(|| E::new(P::Request, "entry-attempt-completion"))?;
                Some(AttemptPolicy {
                    completion,
                    // Source randomness enters through managed services; no affine RNG ports.
                    rng: Vec::new(),
                    limits: zkc_runtime::attempt::Limits {
                        attempts: options.count,
                        proof_bytes: options.proof_bytes,
                    },
                    work: capacity.work,
                    values: capacity.values,
                })
            } else {
                None
            },
        )
    }
    fn inputs(
        &self,
        request: ProofRequest,
        producer: bool,
        capacity: Capacity,
    ) -> Result<ProofInputs> {
        let role = &self.interface.roles()[if producer { self.roles.0 } else { self.roles.1 }];
        let managed = self.native.entry().transcript().is_some();
        let keys = setups::public_keys(&self.interface, &request.setups, capacity)?;
        let public = arguments::values(self.interface.public_ports(), request.public, Some(&keys))?;
        let inputs = arguments::proof_inputs(
            &self.interface,
            role,
            &public,
            self.native.public_types(),
            request.private.inputs,
            capacity,
            self.installation(),
        )?;
        Ok(ProofInputs {
            public,
            inputs,
            services: arguments::services(self.interface.services(role), request.private.services)?,
            context: request.context,
            transcript_budget: request.transcript_budget.unwrap_or(if managed {
                super::DEFAULT_DRAW_BUDGET
            } else {
                0
            }),
        })
    }
    fn report(&self, native: NativeProofReport, producer: bool) -> ProofReport {
        let mut report = ProofReport {
            native,
            outputs: None,
            output_error: None,
            binding_scope: self.scope,
        };
        if report.native.outcome.is_err() || !report.native.cleanup_errors.is_empty() {
            return report;
        }
        if let Some(outputs) = &report.native.outputs {
            let role = &self.interface.roles()[if producer { self.roles.0 } else { self.roles.1 }];
            let result = (|| -> Result<NamedValues> {
                let mut leaves = outputs.clone();
                let mut values = NamedValues::new();
                for port in self.interface.output_ports(role) {
                    let selected = port
                        .native
                        .iter()
                        .map(|i| leaves.remove(&(*i as usize)).ok_or("entry-output-shape"))
                        .collect::<std::result::Result<Vec<_>, _>>()?;
                    let mut selected = selected.into_iter();
                    values.insert(
                        port.name.clone(),
                        value::collect(&port.schema, &mut selected)?,
                    );
                    if selected.next().is_some() {
                        return Err("entry-output-shape".into());
                    }
                }
                if !leaves.is_empty() {
                    return Err("entry-output-shape".into());
                }
                Ok(values)
            })();
            match result {
                Ok(values) => report.outputs = Some(values),
                Err(code) => report.output_error = Some(code),
            }
        }
        report
    }
}

/// One call retains setup imports from output preflight through execution.
/// Candidate proof bytes are supplied only after this preflight succeeds.
pub struct ProofCall<'a> {
    host: &'a ProofEntry,
    operation: ProofOperation,
    request: ProofRequest,
    attempts: Option<AttemptOptions>,
    imports: crate::host::setups::VerifierKeys,
    output_setups: zkc_cpu::SetupRegistry,
    encode_results: bool,
}
impl ProofEntry {
    /// Check requested result codecs before input loading or execution.
    pub fn check_result_encoding(&self, operation: ProofOperation) -> Result<()> {
        if self
            .output_types(operation)
            .iter()
            .all(|ty| self.installation().supports_wire(ty))
        {
            Ok(())
        } else {
            Err("entry-output-codec".into())
        }
    }
    /// Check selected result codecs and authenticate setup material before
    /// reading candidate proof bytes.
    /// Request validation and execution preparation take place in `execute`.
    /// This does not issue resources or execute a proof.
    pub fn preflight_call(
        &self,
        operation: ProofOperation,
        request: ProofRequest,
        attempts: Option<AttemptOptions>,
        encode_results: bool,
    ) -> EntryResult<ProofCall<'_>> {
        self.observe_setups(&request.setups);
        if operation == ProofOperation::Verify && attempts.is_some() {
            return Err(E::new(P::Request, "entry-attempt-operation"));
        }
        if encode_results {
            self.check_result_encoding(operation)
                .map_err(|e| E::new(P::Request, e))?;
        }
        let capacity = self.native.capacity();
        let mut imports = crate::host::setups::VerifierKeys::new(
            capacity.backend().ark_bounds(),
            self.installation().clone(),
        )
        .with_material(self.material.clone());
        let output_setups = if encode_results {
            // Reconstruct logical setup pins from the checked deployment, rather
            // than accepting result-encoding authority from candidate data.
            self.cpu()
                .enter(|| {
                    crate::entry::outputs::output_setups_with(
                        &request.setups,
                        &self.setup_authority,
                        capacity,
                        &mut imports,
                        self.installation(),
                    )
                })
                .map_err(|e| E::new(P::Preparation, e))?
        } else {
            Default::default()
        };
        Ok(ProofCall {
            host: self,
            operation,
            request,
            attempts,
            imports,
            output_setups,
            encode_results,
        })
    }
}
impl ProofCall<'_> {
    /// Validate the assembled inputs without executing or issuing resources.
    pub fn check_inputs(self) -> EntryResult<()> {
        self.host
            .check_inputs(self.request, self.operation, self.attempts)
    }
    pub fn execute(mut self, proof: Option<&[u8]>) -> EntryResult<ProofResult> {
        if (self.operation == ProofOperation::Verify) != proof.is_some() {
            return Err(E::new(P::Request, "entry-proof-operation"));
        }
        let report =
            self.host
                .execute_with(self.request, proof, self.attempts, &mut self.imports)?;
        Ok(ProofResult {
            installation: self.host.installation().clone(),
            report,
            cpu: self.host.cpu().clone(),
            capacity: self.host.native.capacity(),
            output_setups: self.output_setups,
            encode_results: self.encode_results,
            _imports: self.imports,
            encoding: std::sync::OnceLock::new(),
        })
    }
}
/// Execution observations survive later result encoding failures.
pub struct ProofResult {
    installation: zkc_cpu::CpuInstallation,
    pub report: ProofReport,
    cpu: crate::execution::CpuExecution,
    capacity: Capacity,
    output_setups: zkc_cpu::SetupRegistry,
    encode_results: bool,
    // Keep charged canonical snapshots and imported keys alive with results.
    _imports: crate::host::setups::VerifierKeys,
    encoding: std::sync::OnceLock<Result<OutputAllowance>>,
}
struct OutputAllowance {
    ledger: zkc_runtime::vm::ExecutionLedger,
    _live: zkc_runtime::vm::LiveReservation,
}
/// Encoded output borrows the pending result, retaining both its original
/// reservations and the new buffer's allowance through publication/handoff.
#[must_use = "retain the encoded envelope through publication or transport copy"]
pub struct EncodedResults<'a> {
    buffer: super::outputs::EncodedBuffer,
    _result: &'a ProofResult,
}
/// A stored transport result owns its pending report as well as its encoded
/// buffer. Getter copies can outlive the original caller's result handle.
#[must_use = "retain the encoded owner through publication or transport copy"]
pub struct OwnedEncodedResults {
    buffer: super::outputs::EncodedBuffer,
    _result: std::sync::Arc<ProofResult>,
}
impl EncodedResults<'_> {
    pub fn as_bytes(&self) -> &[u8] {
        &self.buffer.bytes
    }
}
impl AsRef<[u8]> for EncodedResults<'_> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}
impl std::ops::Deref for EncodedResults<'_> {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        self.as_bytes()
    }
}
impl OwnedEncodedResults {
    pub fn as_bytes(&self) -> &[u8] {
        &self.buffer.bytes
    }
}
impl AsRef<[u8]> for OwnedEncodedResults {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}
impl std::ops::Deref for OwnedEncodedResults {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        self.as_bytes()
    }
}
impl ProofResult {
    pub fn encode_results(&self) -> Result<Option<EncodedResults<'_>>> {
        Ok(self.encode_results_buffer()?.map(|buffer| EncodedResults {
            buffer,
            _result: self,
        }))
    }
    /// Retain original invocation custody when an adapter stores encoded bytes
    /// beyond this method, including deferred Wasm getters and publication.
    pub fn encode_results_owned(
        self: &std::sync::Arc<Self>,
    ) -> Result<Option<OwnedEncodedResults>> {
        Ok(self
            .encode_results_buffer()?
            .map(|buffer| OwnedEncodedResults {
                buffer,
                _result: self.clone(),
            }))
    }
    fn encode_results_buffer(&self) -> Result<Option<super::outputs::EncodedBuffer>> {
        if !self.encode_results {
            return Ok(None);
        }
        let values = self
            .report
            .outputs
            .as_ref()
            .ok_or("entry-proof-incomplete")?;
        let allowance = self
            .encoding
            .get_or_init(|| {
                let ledger =
                    zkc_runtime::vm::ExecutionLedger::new(self.capacity.values, self.capacity.work);
                // Replay already produced payloads into the publication allowance.
                // Original report/import guards remain in place; this accounts for
                // coexistence with one or several encoded buffers, without issuing
                // or reusing an invocation reservation from the material cache.
                let material = self._imports.retained_bytes();
                let proof = self.report.native.outcome.as_ref().map_or(0, Vec::len);
                let live = self
                    .report
                    .native
                    .usage
                    .live_value_bytes
                    .checked_add(material)
                    .and_then(|n| n.checked_add(proof))
                    .ok_or("entry-output-limit")?;
                let fresh = self
                    .report
                    .native
                    .usage
                    .total_value_bytes
                    .checked_add(material)
                    .and_then(|n| n.checked_add(proof))
                    .ok_or("entry-output-limit")?;
                ledger
                    .charge(
                        zkc_runtime::vm::WorkBudget {
                            instructions: 0,
                            iterations: 0,
                            logical_bytes: self.report.native.usage.logical_bytes,
                        },
                        fresh,
                    )
                    .map_err(|_| "entry-output-limit")?;
                let held = ledger
                    .reserve_live(live)
                    .map_err(|_| "entry-output-limit")?;
                Ok(OutputAllowance {
                    ledger,
                    _live: held,
                })
            })
            .as_ref()
            .map_err(Clone::clone)?;
        let buffer = crate::entry::outputs::proof_outputs_reserved(
            values,
            self.capacity,
            self.output_setups.clone(),
            self.cpu.clone(),
            self.installation.clone(),
            Some(allowance.ledger.clone()),
        )?;
        Ok(Some(buffer))
    }
}

impl ProofOptions {
    pub fn with_external_work(mut self, work: u64) -> Result<Self> {
        if work > CpuBackend::DEFAULT_EXTERNAL_WORK_LIMIT {
            return Err("native-proof-external-work-limit".into());
        }
        self.external_work = work;
        Ok(self)
    }
}

#[cfg(test)]
mod publication_tests {
    use super::*;
    use sha2::{Digest, Sha256};
    #[test]
    fn encoded_envelopes_hold_result_and_buffer_allowances_until_handoff() {
        let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
        let frame=serde_json::json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true}}).to_string();
        let package = Package::capture(
            frame.as_bytes(),
            &Sha256::digest(frame.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap();
        let host = ProofEntry::admit(
            package,
            ProofOptions {
                binding: BindingPolicy::AllowAuthored,
                ..Default::default()
            },
            Default::default(),
        )
        .unwrap();
        let result = std::sync::Arc::new(
            host.preflight_memory_call(
                ProofOperation::Prove,
                Some(r#"{"公開":true}"#.as_bytes()),
                Some(r#"{"秘密":false}"#.as_bytes()),
                &Default::default(),
                Default::default(),
                None,
                true,
            )
            .unwrap()
            .execute(None)
            .unwrap(),
        );
        let first = result.encode_results().unwrap().unwrap();
        let allowance = result.encoding.get().unwrap().as_ref().unwrap();
        let ledger = allowance.ledger.clone();
        let one = ledger.snapshot();
        assert!(one.live_reserved_bytes > 0);
        let second = result.encode_results().unwrap().unwrap();
        let two = ledger.snapshot();
        assert_eq!(first.as_bytes(), second.as_bytes());
        assert!(two.live_reserved_bytes > one.live_reserved_bytes);
        drop(second);
        assert_eq!(
            ledger.snapshot().live_reserved_bytes,
            one.live_reserved_bytes
        );
        let publication =
            |bytes: &[u8]| serde_json::from_slice::<serde_json::Value>(bytes).unwrap();
        assert_eq!(publication(first.as_bytes())["values"]["結果"], false);
        drop(first);
        assert!(ledger.snapshot().live_reserved_bytes > 0);
        let stored = result.encode_results_owned().unwrap().unwrap();
        let weak = std::sync::Arc::downgrade(&result);
        drop(result);
        assert!(weak.upgrade().is_some());
        assert_eq!(publication(stored.as_bytes())["values"]["結果"], false);
        assert!(ledger.snapshot().live_reserved_bytes > 0);
        let fresh = ledger.snapshot().total_value_bytes;
        drop(stored);
        assert!(weak.upgrade().is_none());
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
        assert_eq!(ledger.snapshot().total_value_bytes, fresh);
    }
}

#[cfg(test)]
mod material_tests {
    use super::*;
    use crate::entry::memory::ProofCallOptions;
    use sha2::{Digest, Sha256};
    use std::sync::Arc;
    use zkc_kernels::arkworks::bls12_381::Keys;

    fn host(capacity: Capacity) -> ProofEntry {
        let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
        let frame = serde_json::json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true}}).to_string();
        let package = Package::capture(
            frame.as_bytes(),
            &Sha256::digest(frame.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap();
        ProofEntry::admit(
            package,
            ProofOptions {
                capacity,
                binding: BindingPolicy::AllowAuthored,
                ..Default::default()
            },
            Default::default(),
        )
        .unwrap()
    }
    fn keys(host: &ProofEntry) -> Keys {
        Keys::setup_with_rng(
            1,
            &mut ark_std::rand::thread_rng(),
            &host.capacity().backend().ark_bounds(),
        )
        .unwrap()
    }
    #[test]
    fn admitted_material_retention_uses_the_smaller_live_and_total_ceiling() {
        for (live, total) in [(0, 65536), (65536, 0), (65536, 65536)] {
            let mut capacity = Capacity::default();
            capacity.values.live_bytes = live;
            capacity.values.total_bytes = total;
            let host = host(capacity);
            let keys = keys(&host);
            let bounds = capacity.backend().ark_bounds();
            let bytes = keys.verifier_key().to_bytes(&bounds).unwrap();
            let pin = keys.verifier_key().metadata().key_id();
            let mut material = host.material.lock().unwrap();
            let first = material.import(&bytes, pin, bounds).unwrap();
            let second = material.import(&bytes, pin, bounds).unwrap();
            assert_eq!(Arc::ptr_eq(&first, &second), live.min(total) > 0);
        }
    }
    #[test]
    fn named_input_invalidation_preserves_vk_and_checked_calls_after_early_failures() {
        let host = host(Default::default());
        let keys = keys(&host);
        let bounds = host.capacity().backend().ark_bounds();
        let vk = keys.verifier_key().to_bytes(&bounds).unwrap();
        let pk = keys.prover_key().to_bytes(&bounds).unwrap();
        let pin = keys.verifier_key().metadata().key_id();
        let fingerprint = keys.prover_key().material_fingerprint();
        let mut call = host
            .preflight_memory_call(
                ProofOperation::Prove,
                Some(r#"{"公開":true}"#.as_bytes()),
                Some(r#"{"秘密":false}"#.as_bytes()),
                &Default::default(),
                ProofCallOptions::default(),
                None,
                false,
            )
            .unwrap();
        let checked_vk = call.imports.import(&vk, pin).unwrap();
        // Seed numerical imports separately from the Boolean protocol, so this
        // test isolates replacement and document-failure ordering.
        let old = host
            .material
            .lock()
            .unwrap()
            .import_prover(&pk, fingerprint, keys.verifier_key(), bounds)
            .unwrap();
        host.invalidate_prover_inputs().unwrap();
        // The adapter hook precedes even an invalid named binding or malformed
        // public document; the SDK need not resolve that name to a setup pin.
        let error = host
            .preflight_memory_call(
                ProofOperation::Prove,
                Some(b"malformed public"),
                Some(b"malformed witness"),
                &[(
                    "unknown replacement".into(),
                    Arc::new(b"malformed key".to_vec()),
                )]
                .into(),
                ProofCallOptions::default(),
                None,
                false,
            )
            .err()
            .unwrap();
        assert_eq!(error.code(), "entry-request-format");
        assert_eq!(error.path(), Some("public"));
        let mut material = host.material.lock().unwrap();
        let fresh = material
            .import_prover(&pk, fingerprint, keys.verifier_key(), bounds)
            .unwrap();
        assert!(!Arc::ptr_eq(&old, &fresh));
        assert!(Arc::ptr_eq(
            &checked_vk,
            &material.import(&vk, pin, bounds).unwrap()
        ));
        drop(material);
        assert_eq!(old.material_fingerprint(), fingerprint);
        assert!(Arc::ptr_eq(
            &checked_vk,
            &call.imports.import(&vk, pin).unwrap()
        ));
        assert!(call.execute(None).unwrap().report.is_success());
    }
    #[test]
    fn memory_setup_replacement_is_observed_before_malformed_public() {
        let mut host = host(Default::default());
        let keys = keys(&host);
        let bounds = host.capacity().backend().ark_bounds();
        let vk = keys.verifier_key().to_bytes(&bounds).unwrap();
        let pk = keys.prover_key().to_bytes(&bounds).unwrap();
        let pin = keys.verifier_key().metadata().key_id();
        let fingerprint = keys.prover_key().material_fingerprint();
        // Install only the observer slot: numerical imports are independent of
        // the Boolean protocol used to exercise transport failure ordering.
        host.setup_authority.keys.insert("setup".into(), pin);
        for replacement in [Some(b"malformed setup".to_vec()), None] {
            let old_vk = host
                .material
                .lock()
                .unwrap()
                .import(&vk, pin, bounds)
                .unwrap();
            let old_pk = host
                .material
                .lock()
                .unwrap()
                .import_prover(&pk, fingerprint, keys.verifier_key(), bounds)
                .unwrap();
            let options = ProofCallOptions {
                setups: replacement
                    .map(|bytes| [("setup".into(), bytes)].into())
                    .unwrap_or_default(),
                ..Default::default()
            };
            let error = host
                .preflight_memory_call(
                    ProofOperation::Prove,
                    Some(b"malformed public"),
                    None,
                    &Default::default(),
                    options,
                    None,
                    false,
                )
                .err()
                .unwrap();
            assert_eq!(error.code(), "entry-request-format");
            assert_eq!(error.path(), Some("public"));
            let mut material = host.material.lock().unwrap();
            assert!(!Arc::ptr_eq(
                &old_vk,
                &material.import(&vk, pin, bounds).unwrap()
            ));
            assert!(!Arc::ptr_eq(
                &old_pk,
                &material
                    .import_prover(&pk, fingerprint, keys.verifier_key(), bounds)
                    .unwrap()
            ));
        }
    }
    #[cfg(feature = "files")]
    #[test]
    fn file_setup_replacement_is_observed_before_missing_public_file() {
        let mut host = host(Default::default());
        let keys = keys(&host);
        let bounds = host.capacity().backend().ark_bounds();
        let vk = keys.verifier_key().to_bytes(&bounds).unwrap();
        let pk = keys.prover_key().to_bytes(&bounds).unwrap();
        let pin = keys.verifier_key().metadata().key_id();
        let fingerprint = keys.prover_key().material_fingerprint();
        host.setup_authority.keys.insert("setup".into(), pin);
        let old_vk = host
            .material
            .lock()
            .unwrap()
            .import(&vk, pin, bounds)
            .unwrap();
        let old_pk = host
            .material
            .lock()
            .unwrap()
            .import_prover(&pk, fingerprint, keys.verifier_key(), bounds)
            .unwrap();
        let directory = tempfile::tempdir().unwrap();
        let paths = [("public".into(), directory.path().join("missing.json"))].into();
        let error = crate::entry::files::Documents::new(host.capacity())
            .unwrap()
            .preflight_call(
                &host,
                ProofOperation::Prove,
                &paths,
                ProofCallOptions {
                    setups: [("setup".into(), b"malformed setup".to_vec())].into(),
                    ..Default::default()
                },
                None,
                false,
            )
            .err()
            .unwrap();
        assert_eq!(error.code(), "entry-input-document");
        assert_eq!(error.path(), Some("public"));
        let mut material = host.material.lock().unwrap();
        assert!(!Arc::ptr_eq(
            &old_vk,
            &material.import(&vk, pin, bounds).unwrap()
        ));
        assert!(!Arc::ptr_eq(
            &old_pk,
            &material
                .import_prover(&pk, fingerprint, keys.verifier_key(), bounds)
                .unwrap()
        ));
    }
}
