//! Application-owned loading and lifecycle for an authenticated native bundle.
use super::*;
pub use crate::host::capacity::NativeCapacity;
pub use crate::host::material::ProverMaterial;
use crate::host::{
    admission::{Admission, Input, Operand, ResourceInput, entry_values},
    inputs::*,
    material::MaterialCache,
    setups::needs_input_setup,
};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use zkc_backends::{
    Capability, Domain, EntryPolicy, NativeBackend, PortConstraint, PublicInputs, SetupRegistry,
    Value,
    services::{ServiceReference, ServiceRegistry},
};
use zkc_runtime::interactive::{EntryRole, Type, Value as RuntimeValue};
mod inputs;
mod report;
pub use crate::host::request::InputValue;
pub use inputs::{RoleInputs, RunInputs, SetupAuthority};
pub use report::HostReport;

/// Bundle structure, native value/kernel capacity and joint dispatch are separate
/// budgets. The latter counts dispatch occurrences, including repeated loop steps.
#[derive(Clone, Copy, Debug)]
pub struct HostLimits {
    pub bundle: BundleLimits,
    pub capacity: NativeCapacity,
    pub steps: usize,
    pub message_bytes: usize,
    pub total_wire_bytes: usize,
    pub external_work: u64,
}
impl Default for HostLimits {
    fn default() -> Self {
        let run = RunLimits::default();
        Self {
            bundle: BundleLimits::default(),
            capacity: NativeCapacity::default(),
            steps: run.steps,
            message_bytes: run.wire_bytes,
            total_wire_bytes: run.total_wire_bytes,
            external_work: NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
        }
    }
}
impl HostLimits {
    fn execution(self) -> RunLimits {
        RunLimits {
            steps: self.steps,
            wire_bytes: self.message_bytes,
            total_wire_bytes: self.total_wire_bytes,
            values: self.capacity.values,
            work: self.capacity.work,
        }
        .effective()
    }
    fn effective(mut self) -> Result<Self> {
        self.capacity.check()?;
        self.external_work = self
            .external_work
            .min(NativeBackend::DEFAULT_EXTERNAL_WORK_LIMIT);
        self.bundle = self.bundle.effective();
        let execution = self.execution();
        self.steps = execution.steps;
        self.message_bytes = execution.wire_bytes;
        self.total_wire_bytes = execution.total_wire_bytes;
        Ok(self)
    }
    pub fn record(&self) -> Json {
        json!({"admission":{"bytes":self.bundle.bytes,"candidate_bytes":self.bundle.candidate_bytes,
            "roles":self.bundle.roles,"steps":self.bundle.steps,"depth":self.bundle.depth,
            "nodes":self.bundle.nodes,"string_bytes":self.bundle.string_bytes},
            "capacity":self.capacity.record(),"execution":{"steps":self.steps,
            "message_bytes":self.message_bytes,"total_wire_bytes":self.total_wire_bytes,"external_work_per_role":self.external_work}})
    }
}
/// Exact byte identity is supplied independently of invocation and bundle data.
/// Native admission proves supplied structure, not source-order correspondence.
pub struct RunHost {
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
        let limits = limits.effective()?;
        let backend = NativeBackend::new(
            limits.capacity.backend(),
            EntryPolicy::new(
                Domain::new("admission", "admission", "admission", None),
                None,
                PublicInputs::LocalOnly,
            ),
            None,
        )
        .map_err(|e| e.to_string())?;
        let bundle = Bundle::admit_pinned(bytes, expected_sha256, &backend, limits.bundle)
            .map_err(|e| e.to_string())?;
        authority.check(&bundle)?;
        Ok(Self {
            bundle,
            identity: hex(expected_sha256),
            limits,
            authority,
        })
    }
    pub fn bundle(&self) -> &Bundle {
        &self.bundle
    }
    pub fn identity(&self) -> &str {
        &self.identity
    }
    pub fn limits(&self) -> HostLimits {
        self.limits
    }
    /// Positional interface. Candidate SSA and generated service names are not
    /// configuration keys; the authenticated bundle determines each position.
    pub fn layout(&self) -> Json {
        json!(self.bundle.roles().iter().map(|role| json!({"role":role.entry.role,
            "inputs":role.entry.inputs.iter().enumerate().map(|(i,(_,ty))| json!([i,ty.spelling(),inputs::kind(ty)])).collect::<Vec<_>>(),
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
        inputs::prepare(self, request)
    }
}
struct PreparedRole {
    entry: EntryRole,
    backend: NativeBackend,
    values: Vec<Operand>,
    services: Vec<u64>,
}
pub struct PreparedRun<'a> {
    host: &'a RunHost,
    session: String,
    roles: Vec<PreparedRole>,
    loaded: Vec<Value>,
}
impl PreparedRun<'_> {
    /// Every ordinary exit after issuance retires issued roots and preserves the
    /// primary result. Session freshness remains the application's obligation.
    pub fn execute(self) -> HostReport {
        self.execute_with(|| Ok(()))
    }
    // Injection at the issuance boundary exercises partial custody without
    // installing deterministic entropy or test controls in the public host.
    fn execute_with(self, mut before_issue: impl FnMut() -> Result<()>) -> HostReport {
        let registry = ServiceRegistry::new(self.host.limits.capacity.backend());
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
        let mut report = HostReport::new(self.host, &self.session);
        if let Some(error) = failure {
            report.phase = "issuance";
            report.failure = Some(error);
            report.unstarted = inputs.into_iter().map(|i| (i.role, i.backend)).collect();
        } else {
            report.phase = "execution";
            match run(
                &self.host.bundle,
                &self.session,
                inputs,
                self.host.limits.execution(),
                &mut NoHooks,
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
        report
    }
}

#[cfg(test)]
mod tests;
