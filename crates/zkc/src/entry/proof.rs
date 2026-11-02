//! Independent named proof calls over the admitted common native deployment.
use super::errors::{EntryError as E, EntryPhase as P, EntryResult};
use super::{
    EntryAssets, Interface, NamedValues, Package, RoleInputs, SetupAuthority, arguments, setups,
    value,
};
use crate::execution::Capacity;
use crate::host::capacity::Allowances;
use crate::proof::{AttemptPolicy, NativeDeployment, NativeProofReport, ProofInputs};
use std::collections::BTreeMap;

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
/// Proof policy. External, Ring and sequence work and interface admission are
/// the same Host allowances a run admits, with defaults and maxima from
/// [`Allowances`](crate::host::capacity::Allowances).
#[derive(Clone, Debug)]
pub struct ProofOptions {
    pub installation: zkc_cpu::CpuInstallation,
    /// The selected role's runner, cumulative across its attempts.
    pub capacity: Capacity,
    pub external_work: u64,
    pub ring_work: u64,
    pub sequence_work: u64,
    pub interface: super::InterfaceLimits,
    /// Each call's invocation root, separate from the runner's capacity.
    pub invocation: crate::execution::InvocationLimits,
    /// Each input loading's work ([`Allowances::LOADING_WORK`]).
    pub loading_work: u64,
    /// The public statement, named references and setup material of each
    /// call, and the setup imports retained across calls.
    pub material: crate::execution::MaterialLimits,
    pub binding: BindingPolicy,
}
impl Default for ProofOptions {
    fn default() -> Self {
        Self {
            capacity: Capacity::default(),
            external_work: Allowances::EXTERNAL_WORK.default,
            ring_work: Allowances::RING_WORK.default,
            sequence_work: Allowances::SEQUENCE_WORK.default,
            interface: super::InterfaceLimits::DEFAULT,
            invocation: crate::execution::InvocationLimits::DEFAULT,
            loading_work: Allowances::LOADING_WORK.default,
            material: crate::execution::MaterialLimits::DEFAULT,
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
    /// Refuse a selection above an installed maximum, without clamping it.
    pub fn validate(&self) -> Result<()> {
        self.capacity.validate()?;
        if !Allowances::EXTERNAL_WORK.admits(self.external_work) {
            return Err("native-proof-external-work-limit".into());
        }
        if !Allowances::RING_WORK.admits(self.ring_work) {
            return Err("native-proof-ring-work-limit".into());
        }
        if !Allowances::SEQUENCE_WORK.admits(self.sequence_work) {
            return Err("native-proof-sequence-work-limit".into());
        }
        if !Allowances::LOADING_WORK.admits(self.loading_work) {
            return Err("native-proof-loading-work-limit".into());
        }
        self.invocation.validate()?;
        self.material.validate()?;
        self.interface.validate().map_err(|e| e.to_string())
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
            proof_bytes: zkc_format::proof::MAX_PROOF_BYTES,
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
    /// The admitted allowances over supplied material.
    material_limits: crate::execution::MaterialLimits,
}
/// The outer call result distinguishes preparation refusal. This report must
/// still be checked for execution success, including rejection and cleanup.
#[must_use = "check is_success() or into_result(); invocation preparation is not proof acceptance"]
pub struct ProofReport {
    /// Native evidence and proof bytes; raw result storage is removed after
    /// reconstruction. Source results are available only through `outputs`.
    pub native: NativeProofReport,
    pub outputs: Option<NamedValues>,
    pub output_error: Option<String>,
    pub binding_scope: BindingScope,
    invocation: zkc_runtime::vm::ExecutionLedger,
    /// The reconstructed results' live allowance in the invocation root.
    _results: Option<zkc_runtime::vm::LiveReservation>,
}
impl ProofReport {
    /// The invocation root of this call: request decoding and conversion,
    /// setup imports and cache hits, loading, the binding root, proof buffers,
    /// result custody and reconstruction, and result encoding. A child of an
    /// outer invocation uses the outer root; a standalone call's runners keep
    /// their own budgets beside it.
    pub fn invocation_ledger(&self) -> &zkc_runtime::vm::ExecutionLedger {
        &self.invocation
    }
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
        options
            .interface
            .validate()
            .map_err(|e| E::new(P::Admission, e))?;
        let interface = crate::entry::BoundInterface::read_with(&package, options.interface)
            .map_err(|e| E::new(P::Interface, e))?;
        let proof = interface
            .proof()
            .ok_or_else(|| E::new(P::Admission, "entry-job-kind"))?;
        let roles = (proof.prover, proof.verifier);
        let completion = proof.completion;
        let scope = if proof.suite.is_some() {
            BindingScope::Transcript
        } else if proof.format == zkc_format::proof::ProofFormat::Native {
            BindingScope::HeaderOnly
        } else {
            BindingScope::Authored
        };
        if scope != BindingScope::Transcript && options.binding == BindingPolicy::TranscriptRequired
        {
            return Err(E::new(P::Admission, "entry-proof-binding-policy"));
        }
        let ports = if retained_inputs {
            arguments::check_host_ports(&interface, operation)
        } else if let Some(operation) = operation {
            arguments::check_proof_ports(&interface, operation)
        } else {
            arguments::check_ports(&interface)
        };
        ports.map_err(|e| {
            E::boundary_for_role(
                P::Interface,
                e,
                &interface,
                operation.and_then(|op| interface.proof_role(op)),
            )
        })?;
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
        .and_then(|n| {
            options.validate()?;
            n.with_capacity(options.capacity)
        })
        .and_then(|n| {
            n.with_allowances(
                options.capacity,
                options.external_work,
                options.ring_work,
                options.sequence_work,
                zkc_format::proof::MAX_PROOF_BYTES,
            )
        })
        .and_then(|n| n.with_invocation(options.invocation))
        .and_then(|n| n.with_loading_work_limit(options.loading_work))
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
        // Retained imports have their own allowance, independent of the
        // runner's capacity.
        let material = std::sync::Arc::new(std::sync::Mutex::new(
            zkc_cpu::material::VerifierMaterials::new(
                native.capacity().backend().ark_bounds(),
                native.installation().clone(),
                options.material.retained_imports,
            ),
        ));
        Ok(Self {
            material,
            material_limits: options.material,
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
    /// Invalidate the persistent prover imports a named input fed before an
    /// adapter replaces its bytes, including replacements rejected before
    /// document decoding. Each import records the named source of its bytes
    /// and the setup pin it serves, so exactly those pins are cleared; other
    /// slots, verifier imports and already checked calls keep their custody.
    pub fn invalidate_input(&self, name: &str) -> Result<()> {
        self.material
            .lock()
            .map_err(|_| "native-setup-material")?
            .invalidate_source(name);
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
    /// The admitted allowances over the material each call supplies and the
    /// imports retained across calls.
    pub fn material_limits(&self) -> crate::execution::MaterialLimits {
        self.material_limits
    }
    /// The allowances of each call's invocation root.
    pub fn invocation(&self) -> crate::execution::InvocationLimits {
        self.native.invocation()
    }
    /// A new invocation root for one call.
    pub(crate) fn invocation_root(&self) -> zkc_runtime::vm::ExecutionLedger {
        self.native.invocation_root()
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
        let invocation = self.native.invocation_root();
        let mut imports = crate::host::setups::VerifierKeys::new(
            self.native.capacity().backend().ark_bounds(),
            self.installation().clone(),
        )
        .with_material(self.material.clone());
        imports.set_ledger(Some(invocation.clone()));
        self.execute_with(request, proof, attempts, &mut imports, invocation)
    }
    /// Execute one standalone call under its invocation root, which already
    /// holds any charges of the call's preflight.
    pub(crate) fn execute_with(
        &self,
        request: ProofRequest,
        proof: Option<&[u8]>,
        attempts: Option<AttemptOptions>,
        imports: &mut crate::host::setups::VerifierKeys,
        invocation: zkc_runtime::vm::ExecutionLedger,
    ) -> EntryResult<ProofReport> {
        self.observe_setups(&request.setups);
        let producer = proof.is_none();
        let capacity = self.native.capacity();
        let attempts = self.attempt_policy(producer, attempts, capacity)?;
        let inputs = self.inputs(
            request,
            producer,
            capacity,
            self.material_limits,
            &invocation,
        )?;
        let native = self
            .native
            .clone()
            .with_invocation_ledger(invocation.clone());
        Ok(self.report(
            native
                .execute_prepared(
                    &inputs,
                    attempts.as_ref().map_or_else(
                        || crate::proof::Invocation::one_shot(proof),
                        crate::proof::Invocation::Attempts,
                    ),
                    imports,
                )
                .map_err(|e| E::at(P::Preparation, e))?,
            producer,
            invocation,
        ))
    }
    /// Run as a child of an outer invocation. The child takes the same
    /// explicit attempt policy and retained setup material as a standalone
    /// call; the outer ledger charges its work and storage, and `limits`
    /// carries the remaining allowances the parent selected for it.
    pub(crate) fn execute_shared(
        &self,
        request: ProofRequest,
        proof: Option<&[u8]>,
        attempts: Option<AttemptOptions>,
        limits: &crate::run::HostLimits,
        proof_bytes: usize,
        ledger: zkc_runtime::vm::ExecutionLedger,
    ) -> EntryResult<ProofReport> {
        self.observe_setups(&request.setups);
        let producer = proof.is_none();
        if !producer && attempts.is_some() {
            return Err(E::new(P::Request, "entry-attempt-operation"));
        }
        let capacity = limits.capacity;
        let attempts = self.attempt_policy(producer, attempts, capacity)?;
        // Public binding owns one wire copy per verifier-key port. Reserve all
        // copies before argument construction, under the effective child limit.
        let key_bytes = setups::material_bytes(
            &self.interface,
            &request.setups,
            capacity,
            limits.material.setup_bytes,
        )
        .map_err(|e| E::new(P::Request, e))?;
        let _keys_live = crate::host::capacity::RootCharge::BINDING
            .reserve_bytes(Some(&ledger), key_bytes)
            .map_err(|e| E::at(P::Preparation, e))?;
        let inputs = self.inputs(request, producer, capacity, limits.material, &ledger)?;
        let invocation = ledger.clone();
        let native = self
            .native
            .clone()
            .with_allowances(
                capacity,
                limits.external_work,
                limits.ring_work,
                limits.sequence_work,
                proof_bytes,
            )
            .and_then(|n| n.with_loading_work_limit(limits.loading_work))
            .map_err(|e| E::new(P::Preparation, e))?
            .with_shared_ledger(ledger);
        let mut imports = crate::host::setups::VerifierKeys::new(
            capacity.backend().ark_bounds(),
            self.installation().clone(),
        )
        .with_material(self.material.clone());
        Ok(self.report(
            native
                .execute_prepared(
                    &inputs,
                    attempts.as_ref().map_or_else(
                        || crate::proof::Invocation::one_shot(proof),
                        crate::proof::Invocation::Attempts,
                    ),
                    &mut imports,
                )
                .map_err(|e| E::at(P::Preparation, e))?,
            producer,
            invocation,
        ))
    }
    /// Check that this Entry accepts an explicit retry authorization.
    /// Admission of a Host that holds this Entry checks the same rule.
    pub(crate) fn check_attempts(&self, attempts: AttemptOptions) -> EntryResult<()> {
        self.attempt_policy(true, Some(attempts), self.native.capacity())
            .map(drop)
            .map_err(|e| E::new(P::Admission, e.code()))
    }
    /// Validate and load inputs under the same setup, shape and capacity rules
    /// as execution. No randomness, transcript or proof parsing occurs here.
    pub fn check_inputs(
        &self,
        request: ProofRequest,
        operation: ProofOperation,
        attempts: Option<AttemptOptions>,
    ) -> EntryResult<()> {
        // A check is an invocation of its own: one root from conversion
        // through loading.
        let ledger = self.native.invocation_root();
        self.check_inputs_rooted(request, operation, attempts, ledger)
    }
    fn check_inputs_rooted(
        &self,
        request: ProofRequest,
        operation: ProofOperation,
        attempts: Option<AttemptOptions>,
        ledger: zkc_runtime::vm::ExecutionLedger,
    ) -> EntryResult<()> {
        let producer = operation == ProofOperation::Prove;
        if !producer && attempts.is_some() {
            return Err(E::new(P::Request, "entry-attempt-operation"));
        }
        let capacity = self.native.capacity();
        let attempts = self.attempt_policy(producer, attempts, capacity)?;
        let inputs = self.inputs(request, producer, capacity, self.material_limits, &ledger)?;
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
            .clone()
            .with_invocation_ledger(ledger)
            .check_inputs(&inputs, invocation)
            .map_err(|e| E::at(P::Preparation, e))
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
    /// Convert a named request at `Request`, then refuse draw allowances
    /// above the installed maximum at `Preparation`, as every Entry kind does.
    fn inputs(
        &self,
        request: ProofRequest,
        producer: bool,
        capacity: Capacity,
        material: crate::execution::MaterialLimits,
        invocation: &zkc_runtime::vm::ExecutionLedger,
    ) -> EntryResult<ProofInputs> {
        let read = value::request_bytes(
            request
                .public
                .values()
                .chain(request.private.inputs.values()),
        );
        let inputs = self
            .convert(request, producer, capacity, material)
            .map_err(|e| E::at(P::Request, e))?;
        value::charge_conversion(invocation, read, inputs.public.len() + inputs.inputs.len())
            .map_err(|e| E::new(P::Preparation, e))?;
        arguments::check_draw_budgets(
            inputs
                .services
                .iter()
                .copied()
                .chain([inputs.transcript_budget]),
        )?;
        Ok(inputs)
    }
    fn convert(
        &self,
        request: ProofRequest,
        producer: bool,
        capacity: Capacity,
        material: crate::execution::MaterialLimits,
    ) -> Result<ProofInputs> {
        let role = &self.interface.roles()[if producer { self.roles.0 } else { self.roles.1 }];
        let managed = self.native.entry().transcript().is_some();
        let keys = setups::public_keys(
            &self.interface,
            &request.setups,
            capacity,
            material.setup_bytes,
        )?;
        let public = arguments::values(self.interface.public_ports(), request.public, Some(&keys))?;
        let inputs = arguments::proof_inputs(
            &self.interface,
            role,
            &public,
            self.native.public_types(),
            request.private.inputs,
            capacity,
            material.public_bytes,
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
    fn report(
        &self,
        native: NativeProofReport,
        producer: bool,
        invocation: zkc_runtime::vm::ExecutionLedger,
    ) -> ProofReport {
        let mut report = ProofReport {
            native,
            outputs: None,
            output_error: None,
            binding_scope: self.scope,
            invocation,
            _results: None,
        };
        let native_outputs = report.native.outputs.take();
        if report.native.outcome.is_err() || !report.native.cleanup_errors.is_empty() {
            return report;
        }
        if let Some(outputs) = &native_outputs {
            let role = &self.interface.roles()[if producer { self.roles.0 } else { self.roles.1 }];
            let result = (|| -> Result<(NamedValues, zkc_runtime::vm::LiveReservation)> {
                let live = value::charge_reconstruction(
                    &report.invocation,
                    self.interface.output_ports(role).map(|port| &port.schema),
                    outputs.values(),
                )?;
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
                Ok((values, live))
            })();
            match result {
                Ok((values, live)) => {
                    report.outputs = Some(values);
                    report._results = Some(live);
                }
                Err(code) => report.output_error = Some(code),
            }
        }
        report
    }
}

/// One call retains setup imports from output preflight through execution.
/// Candidate proof bytes are supplied only after this preflight succeeds.
/// Its invocation root exists from preflight on, so decoded documents and
/// output-setup imports are charged to the same root as execution.
pub struct ProofCall<'a> {
    host: &'a ProofEntry,
    operation: ProofOperation,
    request: ProofRequest,
    attempts: Option<AttemptOptions>,
    imports: crate::host::setups::VerifierKeys,
    output_setups: zkc_cpu::SetupRegistry,
    encode_results: bool,
    invocation: zkc_runtime::vm::ExecutionLedger,
    /// Live allowance of decoded request documents until conversion.
    documents: Vec<zkc_runtime::vm::LiveReservation>,
}
impl ProofEntry {
    /// Check requested result codecs before input loading or execution.
    pub fn check_result_encoding(&self, operation: ProofOperation) -> Result<()> {
        let proof = self.interface.proof().expect("admitted proof");
        let role = &self.interface.roles()[match operation {
            ProofOperation::Prove => proof.prover,
            ProofOperation::Verify => proof.verifier,
        }];
        for port in self.interface.output_ports(role) {
            value::check_readable_schema(&port.schema)?;
        }
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
        self.preflight_rooted(
            operation,
            request,
            attempts,
            encode_results,
            self.native.invocation_root(),
            Vec::new(),
        )
    }
    /// Preflight under an invocation root that already charged the call's
    /// decoded request documents, whose live allowances `documents` holds.
    pub(super) fn preflight_rooted(
        &self,
        operation: ProofOperation,
        request: ProofRequest,
        attempts: Option<AttemptOptions>,
        encode_results: bool,
        invocation: zkc_runtime::vm::ExecutionLedger,
        documents: Vec<zkc_runtime::vm::LiveReservation>,
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
        // Output-setup imports and their cache hits charge this call's root.
        imports.set_ledger(Some(invocation.clone()));
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
                .map_err(|e| E::at(P::Preparation, e))?
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
            invocation,
            documents,
        })
    }
}
impl ProofCall<'_> {
    /// Validate the assembled inputs without executing or issuing resources.
    /// Check under the call's own root, which holds its decoded documents.
    pub fn check_inputs(self) -> EntryResult<()> {
        self.host
            .check_inputs_rooted(self.request, self.operation, self.attempts, self.invocation)
    }
    pub fn execute(mut self, proof: Option<&[u8]>) -> EntryResult<ProofResult> {
        if (self.operation == ProofOperation::Verify) != proof.is_some() {
            return Err(E::new(P::Request, "entry-proof-operation"));
        }
        let report = self.host.execute_with(
            self.request,
            proof,
            self.attempts,
            &mut self.imports,
            self.invocation,
        )?;
        // Conversion has consumed the decoded documents.
        drop(self.documents);
        Ok(ProofResult {
            installation: self.host.installation().clone(),
            report,
            cpu: self.host.cpu().clone(),
            capacity: self.host.native.capacity(),
            output_setups: self.output_setups,
            encode_results: self.encode_results,
            _imports: self.imports,
        })
    }
}
/// Execution observations survive later result encoding failures. The result
/// keeps the call's invocation root and every reservation in it: imported
/// setups, the proof buffer, the returned values and their reconstruction.
pub struct ProofResult {
    installation: zkc_cpu::CpuInstallation,
    pub report: ProofReport,
    cpu: crate::execution::CpuExecution,
    capacity: Capacity,
    output_setups: zkc_cpu::SetupRegistry,
    encode_results: bool,
    // Keep charged canonical snapshots and imported keys alive with results.
    _imports: crate::host::setups::VerifierKeys,
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
    /// Copy the encoded results for a reader outside the call, as
    /// [`ProofResult::copy_bytes`] does.
    pub fn copy(&self) -> Result<Vec<u8>> {
        self._result.copy_bytes(&self.buffer.bytes)
    }
}
/// A live allowance in a call's invocation root for storage that a reader
/// retains with the result, such as rendered diagnostics. Dropping it releases
/// the live bytes; the fresh charge remains.
#[must_use = "keep the retention while the retained storage exists"]
pub struct ResultRetention {
    _live: Option<zkc_runtime::vm::LiveReservation>,
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
    /// Copy bytes this result retains, such as its proof or an encoding, for a
    /// reader outside the call, such as a browser getter. Every copy is a new
    /// allocation: it is charged to the call's invocation root before copying,
    /// and its live allowance ends when the copy is handed off. Repeated copies
    /// are charged each time; the retained original is never charged again.
    pub fn copy_bytes(&self, bytes: &[u8]) -> Result<Vec<u8>> {
        let _live =
            zkc_runtime::host::wire::reserve_allocation(Some(&self.report.invocation), bytes.len())
                .map_err(|_| "entry-output-limit")?;
        let mut copy = Vec::new();
        copy.try_reserve_exact(bytes.len())
            .map_err(|_| "entry-output-limit")?;
        copy.extend_from_slice(bytes);
        Ok(copy)
    }
    /// Copy the produced proof, as [`Self::copy_bytes`] does. A call without a
    /// produced proof copies nothing.
    pub fn copy_proof(&self) -> Result<Vec<u8>> {
        let proof = self
            .report
            .native
            .outcome
            .as_ref()
            .map_or(&[][..], Vec::as_slice);
        self.copy_bytes(proof)
    }
    /// Charge `bytes` of storage that a reader retains with this result, such
    /// as rendered diagnostics, to the call's invocation root, and hold their
    /// live allowance until the retention is dropped.
    pub fn retain_bytes(&self, bytes: usize) -> Result<ResultRetention> {
        zkc_runtime::host::wire::reserve_allocation(Some(&self.report.invocation), bytes)
            .map(|live| ResultRetention { _live: live })
            .map_err(|_| "entry-output-limit".into())
    }
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
    /// Every encoding is a new buffer charged to the call's invocation root,
    /// which already holds the result's own reservations; repeating it
    /// charges each new buffer and nothing else.
    fn encode_results_buffer(&self) -> Result<Option<super::outputs::EncodedBuffer>> {
        if !self.encode_results {
            return Ok(None);
        }
        let values = self
            .report
            .outputs
            .as_ref()
            .ok_or("entry-proof-incomplete")?;
        let buffer = crate::entry::outputs::proof_outputs_reserved(
            values,
            self.capacity,
            self.output_setups.clone(),
            self.cpu.clone(),
            self.installation.clone(),
            Some(self.report.invocation.clone()),
        )?;
        Ok(Some(buffer))
    }
}

impl ProofOptions {
    pub fn with_external_work(mut self, work: u64) -> Result<Self> {
        if !Allowances::EXTERNAL_WORK.admits(work) {
            return Err("native-proof-external-work-limit".into());
        }
        self.external_work = work;
        Ok(self)
    }
}

#[cfg(test)]
mod publication_tests {
    use super::*;
    use crate::execution::InvocationLimits;
    use sha2::{Digest, Sha256};
    #[test]
    fn encoded_envelopes_hold_result_and_buffer_allowances_until_handoff() {
        let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
        let frame=serde_json::json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": crate::entry::OracleSelection::default()}}).to_string();
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
        let ledger = result.report.invocation_ledger().clone();
        // The call's root already holds the result's own reservations.
        let retained = ledger.snapshot();
        assert!(retained.live_reserved_bytes > 0);
        let first = result.encode_results().unwrap().unwrap();
        let one = ledger.snapshot();
        assert!(one.live_reserved_bytes > retained.live_reserved_bytes);
        let second = result.encode_results().unwrap().unwrap();
        let two = ledger.snapshot();
        assert_eq!(first.as_bytes(), second.as_bytes());
        // A repeated encoding is a second real buffer: it is charged again,
        // and nothing else is replayed.
        assert_eq!(
            two.live_reserved_bytes - one.live_reserved_bytes,
            one.live_reserved_bytes - retained.live_reserved_bytes
        );
        assert_eq!(
            two.total_value_bytes - one.total_value_bytes,
            one.total_value_bytes - retained.total_value_bytes
        );
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
    #[test]
    fn standalone_proofs_charge_conversion_binding_root_and_reconstruction() {
        let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
        let frame=serde_json::json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": crate::entry::OracleSelection::default()}}).to_string();
        let prove = |logical_bytes: u64| {
            let package = Package::capture(
                frame.as_bytes(),
                &Sha256::digest(frame.as_bytes()).into(),
                Package::MAX_BYTES,
            )
            .unwrap();
            ProofEntry::admit(
                package,
                ProofOptions {
                    invocation: InvocationLimits {
                        logical_bytes,
                        ..InvocationLimits::DEFAULT
                    },
                    binding: BindingPolicy::AllowAuthored,
                    ..Default::default()
                },
                Default::default(),
            )
            .unwrap()
            .prove(ProofRequest {
                public: [("公開".into(), true.into())].into(),
                private: RoleInputs {
                    inputs: [("秘密".into(), false.into())].into(),
                    ..Default::default()
                },
                ..Default::default()
            })
        };
        let report = prove(InvocationLimits::DEFAULT.logical_bytes).unwrap();
        assert!(report.is_success());
        let used = report.invocation_ledger().snapshot();
        // Conversion reads both Boolean descriptions; the binding root's
        // canonical encoding and the result reconstruction add to it.
        let read = value::request_bytes([
            &crate::entry::Value::from(true),
            &crate::entry::Value::from(false),
        ]);
        assert!(used.logical_bytes > read as u64, "{used:?}");
        assert!(used.total_value_bytes > 0);
        // Below the conversion's read, the call refuses before native work.
        let refused = prove(read as u64 - 1).err().unwrap();
        assert_eq!(
            (refused.phase, refused.code()),
            (P::Preparation, "entry-request-limit")
        );
        // The conversion fits but the binding root does not.
        let refused = prove(read as u64).err().unwrap();
        assert_eq!(refused.phase, P::Preparation);
        // Everything but reconstruction fits: no partial result.
        let report = prove(used.logical_bytes - 1).unwrap();
        assert_eq!(report.output_error.as_deref(), Some("entry-output-limit"));
        assert!(report.outputs.is_none());
    }
    #[test]
    fn result_encoding_is_refused_over_the_invocation_allowance() {
        let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
        let frame=serde_json::json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": crate::entry::OracleSelection::default()}}).to_string();
        let prove = |capacity: Capacity, invocation: InvocationLimits| {
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
                    invocation,
                    binding: BindingPolicy::AllowAuthored,
                    ..Default::default()
                },
                Default::default(),
            )
            .unwrap()
            .preflight_memory_call(
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
            .unwrap()
        };
        let result = prove(Capacity::default(), InvocationLimits::DEFAULT);
        // The call's root holds its Host-side work: decoding, conversion,
        // loading, the binding root, the proof buffer, result custody and
        // reconstruction. The runner's work stays in its own budget.
        let work = result.report.invocation_ledger().snapshot().logical_bytes;
        assert!(result.report.native.usage.logical_bytes <= work + 511);
        assert!(result.encode_results().unwrap().is_some());
        // The same number as the runner's own logical-work allowance bounds
        // only the runner, which fits it; the root keeps its own allowance.
        let mut capacity = Capacity::default();
        capacity.work.logical_bytes = work + 511;
        let result = prove(capacity, InvocationLimits::DEFAULT);
        assert!(result.report.is_success());
        assert!(result.encode_results().unwrap().is_some());
        // The execution's own work fits the root; the first 512-byte result
        // buffer does not, so encoding refuses without a partial buffer and
        // without replaying any earlier charge.
        let result = prove(
            Capacity::default(),
            InvocationLimits {
                logical_bytes: work + 511,
                ..InvocationLimits::DEFAULT
            },
        );
        assert!(result.report.is_success());
        let before = result.report.invocation_ledger().snapshot();
        assert_eq!(result.encode_results().err().unwrap(), "entry-output-limit");
        assert_eq!(
            result
                .report
                .invocation_ledger()
                .snapshot()
                .live_reserved_bytes,
            before.live_reserved_bytes
        );
    }
    fn entry(invocation: InvocationLimits) -> ProofEntry {
        let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
        let frame=serde_json::json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": crate::entry::OracleSelection::default()}}).to_string();
        let package = Package::capture(
            frame.as_bytes(),
            &Sha256::digest(frame.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap();
        ProofEntry::admit(
            package,
            ProofOptions {
                invocation,
                binding: BindingPolicy::AllowAuthored,
                ..Default::default()
            },
            Default::default(),
        )
        .unwrap()
    }
    fn preflight(host: &ProofEntry, encode: bool) -> EntryResult<ProofCall<'_>> {
        host.preflight_memory_call(
            ProofOperation::Prove,
            Some(r#"{"公開":true}"#.as_bytes()),
            Some(r#"{"秘密":false}"#.as_bytes()),
            &Default::default(),
            Default::default(),
            None,
            encode,
        )
    }
    #[test]
    fn invocation_and_loading_allowances_refuse_above_their_maxima() {
        use crate::host::capacity::Allowances;
        let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
        let frame=serde_json::json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": crate::entry::OracleSelection::default()}}).to_string();
        let admit = |options: ProofOptions| {
            let package = Package::capture(
                frame.as_bytes(),
                &Sha256::digest(frame.as_bytes()).into(),
                Package::MAX_BYTES,
            )
            .unwrap();
            ProofEntry::admit(
                package,
                ProofOptions {
                    binding: BindingPolicy::AllowAuthored,
                    ..options
                },
                Default::default(),
            )
        };
        let admitted = admit(ProofOptions::default()).unwrap();
        assert_eq!(admitted.invocation(), InvocationLimits::DEFAULT);
        for (options, code) in [
            (
                ProofOptions {
                    invocation: InvocationLimits {
                        total_bytes: InvocationLimits::MAXIMUM.total_bytes + 1,
                        ..InvocationLimits::DEFAULT
                    },
                    ..Default::default()
                },
                "native-invocation-limit",
            ),
            (
                ProofOptions {
                    loading_work: Allowances::LOADING_WORK.maximum + 1,
                    ..Default::default()
                },
                "native-proof-loading-work-limit",
            ),
        ] {
            let refused = admit(options).err().unwrap();
            assert_eq!((refused.phase, refused.code()), (P::Admission, code));
        }
        // The deployment's own selections refuse the same way.
        let native = admitted.native.clone();
        assert_eq!(
            native
                .clone()
                .with_invocation(InvocationLimits {
                    live_bytes: InvocationLimits::MAXIMUM.live_bytes + 1,
                    ..InvocationLimits::DEFAULT
                })
                .err()
                .unwrap(),
            "native-invocation-limit"
        );
        assert_eq!(
            native
                .with_loading_work_limit(Allowances::LOADING_WORK.maximum + 1)
                .err()
                .unwrap(),
            "native-proof-loading-work-limit"
        );
    }
    #[test]
    fn decoded_request_documents_charge_the_call_root_at_preflight() {
        let host = entry(InvocationLimits::DEFAULT);
        let call = preflight(&host, false).unwrap();
        // Both decoded documents are fresh allocations of the call's root,
        // live until conversion consumes them.
        let held = call.invocation.snapshot();
        assert!(held.live_reserved_bytes > 0);
        assert_eq!(held.total_value_bytes, held.live_reserved_bytes);
        assert_eq!(held.logical_bytes, held.live_reserved_bytes as u64);
        let root = call.invocation.clone();
        let result = call.execute(None).unwrap();
        assert!(result.report.is_success());
        assert!(root.snapshot().total_value_bytes > held.total_value_bytes);
        // A root that cannot afford the decoded documents refuses at
        // preflight, before any setup import, loading or execution.
        let host = entry(InvocationLimits {
            logical_bytes: held.logical_bytes - 1,
            ..InvocationLimits::DEFAULT
        });
        let refused = preflight(&host, false).err().unwrap();
        assert_eq!(
            (refused.phase, refused.code()),
            (P::Preparation, "entry-request-limit")
        );
    }
    #[test]
    fn reader_copies_are_new_allocations_charged_to_the_call_root() {
        let host = entry(InvocationLimits::DEFAULT);
        let result = std::sync::Arc::new(preflight(&host, true).unwrap().execute(None).unwrap());
        let ledger = result.report.invocation_ledger().clone();
        let owned = result.encode_results_owned().unwrap().unwrap();
        let held = ledger.snapshot();
        // Each copy charges its own bytes; the retained buffer is never
        // charged again, and the copy's live bytes end when it is handed off.
        let first = owned.copy().unwrap();
        assert_eq!(first, owned.as_bytes());
        let one = ledger.snapshot();
        assert_eq!(one.total_value_bytes - held.total_value_bytes, first.len());
        assert_eq!(one.live_reserved_bytes, held.live_reserved_bytes);
        let second = owned.copy().unwrap();
        let two = ledger.snapshot();
        assert_eq!(two.total_value_bytes - one.total_value_bytes, second.len());
        let proof = result.copy_proof().unwrap();
        assert_eq!(&proof, result.report.native.outcome.as_ref().unwrap());
        assert_eq!(
            ledger.snapshot().total_value_bytes - two.total_value_bytes,
            proof.len()
        );
        // Storage a reader keeps with the result, such as rendered
        // diagnostics, holds its live bytes until it is dropped.
        let retained = result.retain_bytes(100).unwrap();
        assert_eq!(
            ledger.snapshot().live_reserved_bytes,
            two.live_reserved_bytes + 100
        );
        drop(retained);
        // A root without room for another copy refuses it.
        let free = InvocationLimits::DEFAULT.live_bytes - ledger.snapshot().live_reserved_bytes;
        let hold = ledger.reserve_live(free - first.len() + 1).unwrap();
        assert_eq!(owned.copy().unwrap_err(), "entry-output-limit");
        drop(hold);
        assert_eq!(owned.copy().unwrap(), first);
        drop((owned, result));
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
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
        host_with(capacity, Default::default())
    }
    fn host_with(capacity: Capacity, material: crate::execution::MaterialLimits) -> ProofEntry {
        let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
        let frame = serde_json::json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": crate::entry::OracleSelection::default()}}).to_string();
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
                material,
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
    fn admitted_material_retention_has_its_own_allowance() {
        use crate::execution::MaterialLimits;
        // The retained-import allowance decides retention. A runner's
        // capacity, however small, does not.
        for (runner, retained_imports, reused) in [
            (0, MaterialLimits::DEFAULT.retained_imports, true),
            (65536, 65536, true),
            (Capacity::default().values.live_bytes, 0, false),
        ] {
            let mut capacity = Capacity::default();
            capacity.values.live_bytes = runner;
            capacity.values.total_bytes = runner;
            let host = host_with(
                capacity,
                MaterialLimits {
                    retained_imports,
                    ..MaterialLimits::DEFAULT
                },
            );
            assert_eq!(host.material_limits().retained_imports, retained_imports);
            let keys = keys(&host);
            let bounds = capacity.backend().ark_bounds();
            let bytes = keys.verifier_key().to_bytes(&bounds).unwrap();
            let pin = keys.verifier_key().metadata().key_id();
            let mut material = host.material.lock().unwrap();
            let first = material.import(&bytes, pin, bounds).unwrap();
            let second = material.import(&bytes, pin, bounds).unwrap();
            assert_eq!(Arc::ptr_eq(&first, &second), reused);
        }
        // An allowance above its maximum refuses at admission, unclamped.
        let (interface, artifact) = crate::entry::interface::tests::unicode::proof_fixture();
        let frame = serde_json::json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": crate::entry::OracleSelection::default()}}).to_string();
        let package = Package::capture(
            frame.as_bytes(),
            &Sha256::digest(frame.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap();
        let refused = ProofEntry::admit(
            package,
            ProofOptions {
                material: MaterialLimits {
                    retained_imports: MaterialLimits::MAXIMUM.retained_imports + 1,
                    ..MaterialLimits::DEFAULT
                },
                binding: BindingPolicy::AllowAuthored,
                ..Default::default()
            },
            Default::default(),
        )
        .err()
        .unwrap();
        assert_eq!(
            (refused.phase, refused.code()),
            (P::Admission, "entry-retained-imports-limit")
        );
    }
    #[test]
    fn persistent_import_reuse_charges_every_call_root_alike() {
        let host = host(Default::default());
        let keys = keys(&host);
        let bounds = host.capacity().backend().ark_bounds();
        let vk = keys.verifier_key().to_bytes(&bounds).unwrap();
        let pin = keys.verifier_key().metadata().key_id();
        let mut charges = Vec::new();
        let mut imported = Vec::new();
        for _ in 0..2 {
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
            let before = call.invocation.snapshot();
            imported.push(call.imports.import(&vk, pin).unwrap());
            let after = call.invocation.snapshot();
            charges.push((
                after.total_value_bytes - before.total_value_bytes,
                after.live_reserved_bytes - before.live_reserved_bytes,
            ));
            // Identical bytes under the same pin share the call's first
            // import and its charge.
            assert!(Arc::ptr_eq(
                &imported[imported.len() - 1],
                &call.imports.import(&vk, pin).unwrap()
            ));
            assert_eq!(call.invocation.snapshot(), after);
            assert!(call.execute(None).unwrap().report.is_success());
        }
        // The second call reused the persistent import without decoding it,
        // yet charged its own root exactly as the first call did.
        assert!(Arc::ptr_eq(&imported[0], &imported[1]));
        assert_eq!(charges[0], charges[1]);
        assert_eq!(charges[0], (16 * vk.len() + 4096, 16 * vk.len() + 4096));
    }
    #[test]
    fn named_input_invalidation_clears_only_its_pin_and_preserves_checked_calls() {
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
            .import_named_prover("key", &pk, fingerprint, keys.verifier_key(), bounds)
            .unwrap();
        // Another slot's import, fed by another named input.
        let other_keys = super::material_tests::keys(&host);
        let other_pk = other_keys.prover_key().to_bytes(&bounds).unwrap();
        let other_fingerprint = other_keys.prover_key().material_fingerprint();
        let kept = host
            .material
            .lock()
            .unwrap()
            .import_named_prover(
                "other key",
                &other_pk,
                other_fingerprint,
                other_keys.verifier_key(),
                bounds,
            )
            .unwrap();
        host.invalidate_input("key").unwrap();
        // The adapter hook precedes even an invalid named binding or malformed
        // public document; the import records the setup pin its source fed.
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
        // Replacing one named input keeps the other slot's import.
        assert!(Arc::ptr_eq(
            &kept,
            &material
                .import_prover(
                    &other_pk,
                    other_fingerprint,
                    other_keys.verifier_key(),
                    bounds
                )
                .unwrap()
        ));
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
