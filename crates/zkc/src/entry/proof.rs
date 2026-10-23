//! Independent named proof calls over the admitted common native deployment.
use super::errors::{EntryError as E, EntryPhase as P, EntryResult};
use super::{
    EntryAssets, Interface, NamedValues, Package, RoleInputs, SetupAuthority, arguments, setups,
    value,
};
use crate::execution::Capacity;
use crate::proof::{AttemptPolicy, NativeDeployment, NativeProofReport, ProofInputs};
use std::collections::BTreeMap;
use zkc_native::NativeBackend;

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
#[derive(Clone, Copy, Debug)]
pub struct ProofOptions {
    pub capacity: Capacity,
    pub external_work: u64,
    pub binding: BindingPolicy,
}
impl Default for ProofOptions {
    fn default() -> Self {
        Self {
            capacity: Capacity::default(),
            external_work: NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
            binding: BindingPolicy::default(),
        }
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
            ),
            Some(op) => NativeDeployment::admit_artifact_operation(
                &package.authenticated_artifact(),
                authority,
                Some(op == ProofOperation::Prove),
                cpu,
            ),
            None => {
                NativeDeployment::admit_artifact(&package.authenticated_artifact(), authority, cpu)
            }
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
        Ok(Self {
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
        let mut imports =
            crate::host::setups::VerifierKeys::new(self.native.capacity().backend().ark_bounds());
        self.execute_with(request, proof, attempts, &mut imports)
    }
    pub(crate) fn execute_with(
        &self,
        request: ProofRequest,
        proof: Option<&[u8]>,
        attempts: Option<AttemptOptions>,
        imports: &mut crate::host::setups::VerifierKeys,
    ) -> EntryResult<ProofReport> {
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

/// One file call retains setup imports from output preflight through execution.
/// Candidate proof bytes are supplied only after this preflight succeeds.
pub struct ProofFileCall<'a> {
    host: &'a ProofEntry,
    operation: ProofOperation,
    request: ProofRequest,
    attempts: Option<AttemptOptions>,
    imports: crate::host::setups::VerifierKeys,
    output_setups: zkc_native::SetupRegistry,
    encode_results: bool,
}
impl ProofEntry {
    /// Check requested file result codecs before input loading or execution.
    pub fn check_result_encoding(&self, operation: ProofOperation) -> Result<()> {
        if self
            .output_types(operation)
            .iter()
            .all(zkc_native::has_native_wire)
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
    pub fn preflight_file_call(
        &self,
        operation: ProofOperation,
        request: ProofRequest,
        attempts: Option<AttemptOptions>,
        encode_results: bool,
    ) -> EntryResult<ProofFileCall<'_>> {
        if operation == ProofOperation::Verify && attempts.is_some() {
            return Err(E::new(P::Request, "entry-attempt-operation"));
        }
        if encode_results {
            self.check_result_encoding(operation)
                .map_err(|e| E::new(P::Request, e))?;
        }
        let capacity = self.native.capacity();
        let mut imports = crate::host::setups::VerifierKeys::new(capacity.backend().ark_bounds());
        let output_setups = if encode_results {
            // Reconstruct logical setup pins from the checked deployment, rather
            // than accepting result-encoding authority from candidate data.
            self.cpu()
                .enter(|| {
                    crate::entry::files::output_setups_with(
                        &request.setups,
                        &self.setup_authority,
                        capacity,
                        &mut imports,
                    )
                })
                .map_err(|e| E::new(P::Preparation, e))?
        } else {
            Default::default()
        };
        Ok(ProofFileCall {
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
impl ProofFileCall<'_> {
    pub fn execute(mut self, proof: Option<&[u8]>) -> EntryResult<ProofFileResult> {
        if (self.operation == ProofOperation::Verify) != proof.is_some() {
            return Err(E::new(P::Request, "entry-proof-operation"));
        }
        let report =
            self.host
                .execute_with(self.request, proof, self.attempts, &mut self.imports)?;
        Ok(ProofFileResult {
            report,
            cpu: self.host.cpu().clone(),
            capacity: self.host.native.capacity(),
            output_setups: self.output_setups,
            encode_results: self.encode_results,
            _imports: self.imports,
        })
    }
}
/// Execution observations survive later result encoding failures.
pub struct ProofFileResult {
    pub report: ProofReport,
    cpu: crate::execution::CpuExecution,
    capacity: Capacity,
    output_setups: zkc_native::SetupRegistry,
    encode_results: bool,
    // Keep charged canonical snapshots and imported keys alive with results.
    _imports: crate::host::setups::VerifierKeys,
}
impl ProofFileResult {
    pub fn encode_results(&self) -> Result<Option<Vec<u8>>> {
        if !self.encode_results {
            return Ok(None);
        }
        crate::entry::files::proof_outputs_with_cpu(
            self.report
                .outputs
                .as_ref()
                .ok_or("entry-proof-incomplete")?,
            self.capacity,
            self.output_setups.clone(),
            self.cpu.clone(),
        )
        .map(Some)
    }
}
impl ProofOptions {
    pub fn with_external_work(mut self, work: u64) -> Result<Self> {
        if work > NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT {
            return Err("native-proof-external-work-limit".into());
        }
        self.external_work = work;
        Ok(self)
    }
}
