//! Application-owned loading and lifecycle for an authenticated native bundle.
use crate::execution::{Capacity, CpuExecution};
use crate::host::{
    admission::{Admission, Input, Operand, ResourceInput, entry_values},
    capacity::Allowances,
    setups::needs_input_setup,
};
use crate::io::bytes::*;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use zkc_cpu::{
    Capability, CpuBackend, Domain, EntryPolicy, PortConstraint, SetupRegistry, Value,
    services::{ServiceReference, ServiceRegistry},
};
use zkc_runtime::host::joint::*;
use zkc_runtime::vm::{EntryRole, Type, Value as RuntimeValue};
mod inputs;
mod report;
use crate::execution::InputValue;
pub use inputs::{RoleInputs, RunInputs, SetupAuthority};
pub use report::{EncodedOutput, HostReport, RoleOutputEncoding};

/// Bundle structure, native value/operation capacity and joint dispatch are separate
/// budgets. The latter counts dispatch occurrences, including repeated loop steps.
/// External, Ring and sequence work are per-role allowances, and `interface`
/// bounds source interface admission; their defaults and maxima are the
/// installed [`Allowances`](crate::host::capacity::Allowances).
#[derive(Clone, Debug)]
pub struct HostLimits {
    pub installation: zkc_cpu::CpuInstallation,
    pub bundle: BundleLimits,
    pub capacity: Capacity,
    pub steps: usize,
    pub message_bytes: usize,
    pub total_wire_bytes: usize,
    /// Joint report storage, including each distinct dynamic path once.
    pub report_bytes: usize,
    pub external_work: u64,
    pub ring_work: u64,
    pub sequence_work: u64,
    pub interface: crate::entry::InterfaceLimits,
}
impl Default for HostLimits {
    fn default() -> Self {
        let run = RunLimits::default();
        Self {
            installation: Default::default(),
            bundle: BundleLimits::default(),
            capacity: Capacity::default(),
            steps: run.steps,
            message_bytes: run.wire_bytes,
            total_wire_bytes: run.total_wire_bytes,
            report_bytes: run.report_bytes,
            external_work: Allowances::EXTERNAL_WORK.default,
            ring_work: Allowances::RING_WORK.default,
            sequence_work: Allowances::SEQUENCE_WORK.default,
            interface: crate::entry::InterfaceLimits::DEFAULT,
        }
    }
}
impl HostLimits {
    /// Select the frozen CPU support view before bundle admission.
    pub fn with_installation(mut self, installation: zkc_cpu::CpuInstallation) -> Self {
        self.installation = installation;
        self
    }

    /// Apply a zkc.bundle-limits/0 document, retaining admission and value capacity.
    pub fn with_work_limits(mut self, bytes: &[u8]) -> Result<Self> {
        let value = parse(bytes, 4096)?;
        let row = array(&value, 5)?;
        if text(&row[0])? != "zkc.bundle-limits/0" {
            return Err("bundle-limits-format".into());
        }
        let size = |v| usize::try_from(natural(v)?).map_err(|_| "bundle-limits".to_owned());
        self.steps = size(&row[1])?;
        self.message_bytes = size(&row[2])?;
        self.total_wire_bytes = size(&row[3])?;
        self.external_work = natural(&row[4])?;
        self.validate()?;
        Ok(self)
    }

    fn execution(&self) -> RunLimits {
        RunLimits {
            steps: self.steps,
            wire_bytes: self.message_bytes,
            total_wire_bytes: self.total_wire_bytes,
            report_bytes: self.report_bytes,
            values: self.capacity.values,
            work: self.capacity.work,
        }
    }
    /// Per-role external primitive work ceiling, independent of instructions.
    pub const MAX_EXTERNAL_WORK_PER_ROLE: u64 = Allowances::EXTERNAL_WORK.maximum;
    /// Validate the requested values without silently changing application policy.
    pub fn validate(&self) -> Result<()> {
        self.capacity.validate()?;
        self.bundle.validate().map_err(|e| e.to_string())?;
        if !Allowances::EXTERNAL_WORK.admits(self.external_work)
            || self.execution().validate().is_err()
        {
            return Err("bundle-limits".into());
        }
        if !Allowances::RING_WORK.admits(self.ring_work) {
            return Err("bundle-ring-work-limit".into());
        }
        if !Allowances::SEQUENCE_WORK.admits(self.sequence_work) {
            return Err("bundle-sequence-work-limit".into());
        }
        self.interface.validate().map_err(|e| e.to_string())
    }
    pub fn record(&self) -> Json {
        json!({"admission":{"bytes":self.bundle.bytes,"candidate_bytes":self.bundle.candidate_bytes,
            "roles":self.bundle.roles,"steps":self.bundle.steps,"depth":self.bundle.depth,
            "nodes":self.bundle.nodes,"string_bytes":self.bundle.string_bytes},
            "capacity":self.capacity.record(),"execution":{"steps":self.steps,
            "message_bytes":self.message_bytes,"total_wire_bytes":self.total_wire_bytes,"report_bytes":self.report_bytes,"external_work_per_role":self.external_work,
            "ring_work_per_role":self.ring_work,"sequence_work_per_role":self.sequence_work},
            "interface":{"work":self.interface.work,"descriptor_bytes":self.interface.descriptor_bytes}})
    }
}
/// Exact byte identity is supplied independently of invocation and bundle data.
/// Native admission proves supplied structure, not source-order correspondence.
#[derive(Clone)]
pub struct RunHost {
    cpu: CpuExecution,
    ring_assets: zkc_cpu::ring::Registry,
    relation_assets: zkc_cpu::relation::Registry,
    shared_ledger: Option<zkc_runtime::vm::ExecutionLedger>,
    retained_inputs: bool,
    bundle: Bundle,
    identity: String,
    limits: HostLimits,
    authority: SetupAuthority,
}
impl RunHost {
    pub fn admit(
        bytes: &[u8],
        expected_sha256: &[u8; 32],
        limits: HostLimits,
        authority: SetupAuthority,
    ) -> Result<Self> {
        Self::admit_with_cpu(
            bytes,
            expected_sha256,
            limits,
            authority,
            CpuExecution::serial().map_err(|e| e.to_string())?,
        )
    }
    /// Admit with one application-owned context shared by all participants.
    pub fn admit_with_cpu(
        bytes: &[u8],
        expected_sha256: &[u8; 32],
        limits: HostLimits,
        authority: SetupAuthority,
        cpu: CpuExecution,
    ) -> Result<Self> {
        let backend = Self::admission_backend(&limits, cpu.clone())?;
        let bundle = Bundle::admit_pinned(
            bytes,
            expected_sha256,
            &backend,
            limits.installation.contracts(),
            limits.bundle,
        )
        .map_err(|e| e.to_string())?;
        Self::from_bundle(bundle, expected_sha256, limits, authority, cpu)
    }
    pub(crate) fn admit_artifact(
        artifact: &crate::entry::AuthenticatedArtifact<'_>,
        limits: HostLimits,
        authority: SetupAuthority,
        cpu: CpuExecution,
    ) -> Result<Self> {
        let backend = Self::admission_backend(&limits, cpu.clone())?;
        let bundle = Bundle::admit(
            artifact.bytes(),
            &backend,
            limits.installation.contracts(),
            limits.bundle,
        )
        .map_err(|e| e.to_string())?;
        Self::from_bundle(bundle, artifact.identity(), limits, authority, cpu)
    }
    fn admission_backend(limits: &HostLimits, cpu: CpuExecution) -> Result<CpuBackend> {
        limits.validate()?;
        CpuBackend::new_with_installation(
            limits.capacity.backend(),
            EntryPolicy::new(
                Domain::new("admission", "admission", "admission", None),
                None,
            ),
            Default::default(),
            cpu,
            limits.installation.clone(),
        )
        .map_err(|e| e.to_string())
    }
    fn from_bundle(
        bundle: Bundle,
        identity: &[u8; 32],
        limits: HostLimits,
        authority: SetupAuthority,
        cpu: CpuExecution,
    ) -> Result<Self> {
        authority.check(&bundle)?;
        Ok(Self {
            cpu,
            ring_assets: Default::default(),
            relation_assets: Default::default(),
            shared_ledger: None,
            retained_inputs: false,
            bundle,
            identity: hex(identity),
            limits,
            authority,
        })
    }
    pub(crate) fn check_session(session: &str) -> Result<()> {
        if inputs::valid_identifier(session) {
            Ok(())
        } else {
            Err("bundle-input-name".into())
        }
    }
    pub fn bundle(&self) -> &Bundle {
        &self.bundle
    }
    pub fn identity(&self) -> &str {
        &self.identity
    }
    pub fn limits(&self) -> HostLimits {
        self.limits.clone()
    }
    /// Share one CPU context across every participant execution backend.
    pub fn with_cpu(mut self, cpu: CpuExecution) -> Self {
        self.cpu = cpu;
        self
    }
    pub fn installation(&self) -> &zkc_cpu::CpuInstallation {
        &self.limits.installation
    }
    pub fn cpu(&self) -> &CpuExecution {
        &self.cpu
    }
    pub(crate) fn with_retained_inputs(mut self) -> Self {
        self.retained_inputs = true;
        self
    }
    pub fn with_ring_assets(mut self, assets: zkc_cpu::ring::Registry) -> Self {
        self.ring_assets = assets;
        self
    }
    pub fn with_relation_assets(mut self, assets: zkc_cpu::relation::Registry) -> Self {
        self.relation_assets = assets;
        self
    }
    /// Select the policy record's per-role Ring work allowance.
    pub fn with_ring_work_limit(mut self, limit: u64) -> Result<Self> {
        if !Allowances::RING_WORK.admits(limit) {
            return Err("bundle-ring-work-limit".into());
        }
        self.limits.ring_work = limit;
        Ok(self)
    }
    /// Attach one outer ledger before constructing any joint runner. It is
    /// also the invocation ledger of every later preparation.
    pub fn with_shared_ledger(mut self, ledger: zkc_runtime::vm::ExecutionLedger) -> Self {
        self.shared_ledger = Some(ledger);
        self
    }
    /// Replace the policy for one child invocation; the installation stays.
    pub(crate) fn with_invocation_limits(mut self, mut limits: HostLimits) -> Self {
        limits.installation = self.limits.installation.clone();
        self.limits = limits;
        self
    }
    /// Positional interface. Candidate SSA and generated service names are not
    /// configuration keys; the authenticated bundle determines each position.
    pub fn layout(&self) -> Json {
        json!(self.bundle.roles().iter().map(|role| json!({"role":role.entry.role,
            "inputs":role.entry.inputs.iter().enumerate().map(|(i,(_,ty))| json!([i,ty.spelling(),inputs::kind(ty, &self.limits.installation)])).collect::<Vec<_>>(),
            "services":role.entry.services.iter().enumerate().map(|(i,p)| json!([i,p.contract.name()])).collect::<Vec<_>>(),
            "outputs":role.entry.outputs.iter().map(|ty|ty.spelling()).collect::<Vec<_>>() })).collect::<Vec<_>>())
    }
    /// Decode all roles and authenticated key files before any execution entropy
    /// is issued. The returned plan is single-use and bound to this host.
    pub fn prepare(&self, bytes: &[u8]) -> Result<PreparedRun<'_>> {
        let request = inputs::decode(self, bytes)?;
        self.prepare_typed(&request)
    }
    /// Prepare already constructed data through the same admission and entry
    /// checks as the byte adapter. No input or service is issued during this call.
    /// The resulting plan owns its loaded values and does not borrow the request.
    /// Native elements must satisfy the upstream cryptographic library invariants;
    /// unchecked scalar constructors are not an alternative to canonical decoding.
    pub fn prepare_typed(&self, request: &RunInputs) -> Result<PreparedRun<'_>> {
        let mut imports = crate::host::setups::VerifierKeys::new(
            self.limits.capacity.backend().ark_bounds(),
            self.installation().clone(),
        );
        self.prepare_with(request, &mut imports)
    }
    pub(crate) fn prepare_with(
        &self,
        request: &RunInputs,
        imports: &mut crate::host::setups::VerifierKeys,
    ) -> Result<PreparedRun<'_>> {
        self.prepare_charged(request, imports, self.invocation_ledger())
    }
    /// Prepare under an invocation ledger that has already charged the
    /// caller's Host-side work for this invocation, such as request conversion.
    pub(crate) fn prepare_charged(
        &self,
        request: &RunInputs,
        imports: &mut crate::host::setups::VerifierKeys,
        invocation: zkc_runtime::vm::ExecutionLedger,
    ) -> Result<PreparedRun<'_>> {
        // Setup imports, including persistent cache hits, charge the root.
        imports.set_ledger(Some(invocation.clone()));
        self.cpu
            .enter(|| inputs::prepare(self, request, imports, invocation))
    }
    /// The invocation accounting root: the outer invocation's ledger when one
    /// is attached, otherwise a new root with the selected capacity. It
    /// charges preparation, loading, setup imports, inspection, transport,
    /// report storage, result reconstruction and encoding. Participant runners
    /// of a standalone run keep their separate per-runner budgets beside it.
    pub(crate) fn invocation_ledger(&self) -> zkc_runtime::vm::ExecutionLedger {
        self.shared_ledger
            .clone()
            .unwrap_or_else(|| self.limits.capacity.invocation_ledger())
    }
}
struct PreparedRole {
    entry: EntryRole,
    backend: CpuBackend,
    values: Vec<Operand>,
    services: Vec<u64>,
}
pub struct PreparedRun<'a> {
    host: &'a RunHost,
    session: String,
    roles: Vec<PreparedRole>,
    loaded: Vec<Value>,
    /// The loaded inputs' live allowance in the invocation root, held while
    /// the Host owns them.
    loading: zkc_runtime::vm::LiveReservation,
    invocation: zkc_runtime::vm::ExecutionLedger,
}
impl PreparedRun<'_> {
    /// Check all prepared ordinary data before issuing any invocation resource.
    /// Every role's inspection and encoding charge the one invocation ledger.
    pub(crate) fn check_common_inputs(
        &self,
        bindings: &zkc_runtime::host::input_binding::InputBindings,
    ) -> Result<()> {
        for role in &self.roles {
            bindings
                .check_role_prepared(
                    &role.entry.role,
                    &role.backend,
                    &entry_values(&role.values, &self.loaded),
                    &self.invocation,
                )
                .map_err(|e| e.to_string())?;
        }
        Ok(())
    }
    /// Produce the canonical common-input context of these prepared inputs,
    /// before any invocation resource is issued. Every role's inspection and
    /// encoding charge the invocation ledger, as checking a context does.
    pub(crate) fn common_input_context(
        &self,
        required: &[zkc_runtime::host::input_binding::InputRequirement],
    ) -> Result<Vec<u8>> {
        let bundle = &self.host.bundle;
        let mut producer = zkc_runtime::host::input_binding::InputBindings::producer(
            bundle.admitted(),
            bundle.entry(),
            required,
        )
        .map_err(|e| e.to_string())?;
        for role in &self.roles {
            producer
                .observe_role(
                    &role.entry.role,
                    &role.backend,
                    &entry_values(&role.values, &self.loaded),
                    &self.invocation,
                )
                .map_err(|e| e.to_string())?;
        }
        producer.encode(&self.invocation).map_err(|e| e.to_string())
    }
    pub(crate) fn host(&self) -> &RunHost {
        self.host
    }
    /// The invocation ledger shared by preparation, execution reports and
    /// result encoding.
    pub fn invocation_ledger(&self) -> &zkc_runtime::vm::ExecutionLedger {
        &self.invocation
    }

    /// Every ordinary exit after issuance retires issued roots and preserves the
    /// primary result. Session freshness remains the application's obligation.
    pub fn execute(self) -> HostReport {
        self.execute_with(|| Ok(()))
    }
    // Injection at the issuance boundary exercises partial custody without
    // installing deterministic entropy or test controls in the public host.
    fn execute_with(self, mut before_issue: impl FnMut() -> Result<()>) -> HostReport {
        let registry = ServiceRegistry::with_installation(
            self.host.limits.capacity.backend(),
            self.host.limits.installation.clone(),
        );
        let mut resources: BTreeMap<String, Vec<(usize, Capability)>> = BTreeMap::new();
        let mut services: BTreeMap<String, Vec<ServiceReference>> = BTreeMap::new();
        let mut inputs = Vec::new();
        let mut failure = None;
        let loaded = self.loaded;
        for mut role in self.roles {
            let name = role.entry.role.clone();
            let caps = resources.entry(name.clone()).or_default();
            let refs = services.entry(name.clone()).or_default();
            let mut values = Vec::new();
            if failure.is_none() {
                let issued = (|| -> Result<()> {
                    let domain = Domain::new(
                        &name,
                        &self.session,
                        self.host.bundle.entry(),
                        Some(&role.entry.instance),
                    );
                    for (position, value) in role.values.into_iter().enumerate() {
                        let value = match value {
                            Operand::Data(index) => loaded[index].clone(),
                            Operand::Resource(ResourceInput {
                                kind,
                                field,
                                budget,
                            }) => {
                                before_issue()?;
                                match kind {
                                    Type::Rng => {
                                        role.backend.issue_rng_for(field, domain.clone(), budget)
                                    }
                                    Type::Nonce => {
                                        role.backend.issue_nonce_for(field, domain.clone(), budget)
                                    }
                                    _ => unreachable!("checked resource kind"),
                                }
                                .map_err(|e| e.to_string())?
                            }
                        };
                        if let Value::Rng(token) | Value::Nonce(token) = &value {
                            caps.push((position, token.clone()));
                        }
                        values.push(value);
                    }
                    let mut ports = BTreeMap::new();
                    for (port, budget) in role.entry.services.iter().zip(role.services) {
                        before_issue()?;
                        let reference = registry
                            .issue_random_for(&name, port.contract, budget)
                            .map_err(|e| e.to_string())?;
                        refs.push(reference.clone());
                        ports.insert(port.name.clone(), reference);
                    }
                    role.backend
                        .install_services(registry.clone(), ports)
                        .map_err(|e| e.to_string())?;
                    Ok(())
                })();
                failure = issued.err();
            }
            inputs.push(RoleInput {
                role: name,
                backend: role.backend,
                values,
            });
        }
        drop(loaded);
        let mut execution_limits = self.host.limits.execution();
        let shared = self.host.shared_ledger.clone();
        let _loading = if shared.is_some() {
            // Runners that share the root reserve their whole live allowance
            // there beside the loaded inputs, so each one's allowance excludes
            // its share of the loading reservation.
            let roles = inputs.len().max(1);
            execution_limits.values.live_bytes = execution_limits
                .values
                .live_bytes
                .saturating_sub(self.loading.bytes().div_ceil(roles));
            Some(self.loading)
        } else {
            // Standalone runners take custody of their inputs under their own
            // budgets; the Host's reservation ends at that boundary.
            drop(self.loading);
            None
        };
        let invocation = self.invocation.clone();
        let mut report = HostReport::new(self.host, &self.session, self.invocation);
        if let Some(error) = failure {
            report.phase = "issuance";
            report.failure = Some(error);
            report.unstarted = inputs.into_iter().map(|i| (i.role, i.backend)).collect();
        } else {
            report.phase = "execution";
            match run_with_ledgers(
                &self.host.bundle,
                &self.session,
                inputs,
                execution_limits,
                &mut NoHooks,
                shared,
                Some(invocation),
            ) {
                Ok(execution) => {
                    if matches!(&execution.outcome, Outcome::DriverFailed(failure) if failure.kind == FailureKind::Setup)
                    {
                        report.phase = "construction";
                    }
                    report.execution = Some(execution);
                }
                Err(error) => {
                    report.phase = "construction";
                    report.failure = Some(error.failure.detail.text);
                    report.unstarted = error
                        .inputs
                        .into_iter()
                        .map(|i| (i.role, i.backend))
                        .collect();
                }
            }
        }
        report.finalize(&registry, &resources, &services);
        report.retain_outputs();
        report
    }
}

#[cfg(test)]
mod tests;
