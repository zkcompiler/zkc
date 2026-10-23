//! Named source calls adapt to the common native Host. There is no source
//! evaluator here: the bound interface supplies names and product/sum layouts.
use super::errors::{EntryError as E, EntryPhase as P, EntryResult};
use super::{EntryAssets, Interface, Package, SetupAuthority, Value, arguments, setups, value};
use crate::run::{self as native, HostLimits, HostReport, RunHost};
use std::collections::BTreeMap;
use zkc_runtime::host::joint::{Outcome, Report};

type Result<T> = std::result::Result<T, String>;
pub type NamedValues = BTreeMap<String, Value>;
pub type RoleValues = BTreeMap<String, NamedValues>;

#[derive(Debug, Default)]
pub struct RoleInputs {
    pub inputs: NamedValues,
    /// Optional budget overrides for declared services; unknown names refuse.
    pub services: BTreeMap<String, u64>,
}
#[derive(Debug)]
pub struct RunRequest {
    pub session: String,
    pub roles: BTreeMap<String, RoleInputs>,
    pub setups: BTreeMap<String, Vec<u8>>,
}

/// An authenticated package, checked interface, admitted native run artifact
/// and the package's admitted expression assets. The assets are the Host's
/// only evaluator source; no caller-supplied registry can replace them.
pub struct RunEntry {
    package: Package,
    interface: super::BoundInterface,
    assets: EntryAssets,
    native: RunHost,
}
impl RunEntry {
    pub fn with_cpu(mut self, cpu: crate::execution::CpuExecution) -> Self {
        self.native = self.native.with_cpu(cpu);
        self
    }
    pub fn cpu(&self) -> &crate::execution::CpuExecution {
        self.native.cpu()
    }
    pub fn with_ring_work_limit(mut self, limit: u64) -> Result<Self> {
        self.native = self.native.with_ring_work_limit(limit)?;
        Ok(self)
    }
    pub fn admit(
        package: Package,
        limits: HostLimits,
        setups: SetupAuthority,
    ) -> EntryResult<Self> {
        Self::admit_with_cpu(
            package,
            limits,
            setups,
            crate::execution::CpuExecution::serial().map_err(|e| E::new(P::Admission, e))?,
        )
    }
    /// Supply CPU ownership before admitting any native backend.
    pub fn admit_with_cpu(
        package: Package,
        limits: HostLimits,
        setups: SetupAuthority,
        cpu: crate::execution::CpuExecution,
    ) -> EntryResult<Self> {
        Self::admit_inner(package, limits, setups, false, cpu)
    }
    pub(crate) fn admit_host(
        package: Package,
        limits: HostLimits,
        setups: SetupAuthority,
        cpu: crate::execution::CpuExecution,
    ) -> EntryResult<Self> {
        Self::admit_inner(package, limits, setups, true, cpu)
    }
    fn admit_inner(
        package: Package,
        limits: HostLimits,
        setups: SetupAuthority,
        retained_inputs: bool,
        cpu: crate::execution::CpuExecution,
    ) -> EntryResult<Self> {
        let interface =
            crate::entry::BoundInterface::read(&package).map_err(|e| E::new(P::Interface, e))?;
        if interface.is_proof() {
            return Err(E::new(P::Admission, "entry-job-kind"));
        }
        (if retained_inputs {
            arguments::check_host_ports(&interface, None)
        } else {
            arguments::check_ports(&interface)
        })
        .map_err(|e| E::new(P::Interface, e))?;
        let native = RunHost::admit_artifact(
            &package.authenticated_artifact(),
            limits,
            setups::run_authority(&interface, setups).map_err(|e| E::new(P::Authority, e))?,
            cpu,
        )
        .map_err(|e| E::new(P::Admission, e))?;
        interface
            .check_run(&native)
            .map_err(|e| E::new(P::Binding, e))?;
        let assets = EntryAssets::admit(
            &package,
            &interface,
            native.bundle().admitted(),
            native.bundle().entry(),
        )
        .map_err(|e| E::new(P::Assets, e))?;
        let native = if retained_inputs {
            native.with_retained_inputs()
        } else {
            native
        };
        let native = native
            .with_ring_assets(assets.registry().clone())
            .with_relation_assets(assets.relation_registry().clone());
        Ok(Self {
            package,
            interface,
            assets,
            native,
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
    pub fn limits(&self) -> HostLimits {
        self.native.limits()
    }
    pub(crate) fn execute_shared(
        &self,
        request: RunRequest,
        limits: HostLimits,
        ring: u64,
        sequence: u64,
        ledger: zkc_runtime::vm::ExecutionLedger,
    ) -> EntryResult<RunReport> {
        let native = self
            .native
            .clone()
            .with_invocation_limits(limits, ring, sequence)
            .with_shared_ledger(ledger);
        let inputs = self.inputs(request).map_err(|e| E::new(P::Request, e))?;
        let prepared = native
            .prepare_typed(&inputs)
            .map_err(|e| E::new(P::Preparation, e))?;
        Ok(PreparedRun {
            interface: &self.interface,
            native: prepared,
        }
        .execute())
    }

    /// Names cover every role and input exactly. Missing service allowances use
    /// DEFAULT_DRAW_BUDGET; explicit zero is preserved. Empty logical
    /// products are required even though they have no native operand. The plan
    /// owns all prepared input data and may outlive the consumed request.
    pub fn prepare(&self, request: RunRequest) -> EntryResult<PreparedRun<'_>> {
        let mut imports = crate::host::setups::VerifierKeys::new(
            self.native.limits().capacity.backend().ark_bounds(),
        );
        self.prepare_with(request, &mut imports)
    }
    /// Apply execution's input preparation without issuing resources or executing.
    pub fn check_inputs(&self, request: RunRequest) -> EntryResult<()> {
        self.prepare(request).map(drop)
    }
    pub(crate) fn prepare_with(
        &self,
        request: RunRequest,
        imports: &mut crate::host::setups::VerifierKeys,
    ) -> EntryResult<PreparedRun<'_>> {
        let inputs = self.inputs(request).map_err(|e| E::new(P::Request, e))?;
        let native = self
            .native
            .prepare_with(&inputs, imports)
            .map_err(|e| E::new(P::Preparation, e))?;
        Ok(PreparedRun {
            interface: &self.interface,
            native,
        })
    }
    fn inputs(&self, mut request: RunRequest) -> Result<native::RunInputs> {
        if request.roles.len() != self.interface.roles().len() {
            return Err("entry-input-roles".into());
        }
        let material = setups::run_material(
            &self.interface,
            request.setups,
            self.native.limits().capacity,
        )?;
        let mut roles = Vec::new();
        for role in self.interface.roles() {
            let values = request
                .roles
                .remove(&role.name)
                .ok_or("entry-input-roles")?;
            let inputs = arguments::values(self.interface.input_ports(role), values.inputs, None)?;
            let services = arguments::services(self.interface.services(role), values.services)?;
            roles.push(native::RoleInputs {
                role: role.native_name.clone(),
                inputs,
                services,
            });
        }
        Ok(native::RunInputs {
            session: request.session,
            roles,
            setups: material,
        })
    }
}

pub struct PreparedRun<'a> {
    interface: &'a Interface,
    native: native::PreparedRun<'a>,
}
/// Native outcomes and cleanup remain observable even when no complete logical
/// result exists. Outputs are published only on completion with successful cleanup.
#[must_use = "inspect the execution outcome and cleanup report"]
pub struct RunReport {
    pub native: HostReport,
    pub outputs: Option<RoleValues>,
    pub output_error: Option<String>,
}
impl RunReport {
    /// A completed run with successful cleanup and decoded outputs. Protocol
    /// acceptance remains an explicit value, unlike ProofReport::is_success.
    #[must_use]
    pub fn is_success(&self) -> bool {
        self.native.failure.is_none()
            && self.native.cleanup_errors.is_empty()
            && self
                .native
                .execution
                .as_ref()
                .is_some_and(|r| r.outcome == Outcome::Completed)
            && self.output_error.is_none()
            && self.outputs.is_some()
    }
    /// Retain execution and cleanup evidence on either branch.
    pub fn into_result(self) -> std::result::Result<Self, Box<Self>> {
        if self.is_success() {
            Ok(self)
        } else {
            Err(Box::new(self))
        }
    }
}
impl PreparedRun<'_> {
    pub fn execute(self) -> RunReport {
        let native = self.native.execute();
        let mut report = RunReport {
            native,
            outputs: None,
            output_error: None,
        };
        if report.native.failure.is_some() || !report.native.cleanup_errors.is_empty() {
            return report;
        }
        let Some(execution) = &report.native.execution else {
            return report;
        };
        if execution.outcome != Outcome::Completed {
            return report;
        }
        match collect(self.interface, execution) {
            Ok(outputs) => report.outputs = Some(outputs),
            Err(code) => report.output_error = Some(code),
        }
        report
    }
}
fn collect(
    interface: &Interface,
    execution: &Report<zkc_native::NativeBackend>,
) -> Result<RoleValues> {
    let mut outputs = BTreeMap::new();
    for role in interface.roles() {
        let returned = execution
            .roles
            .iter()
            .find(|r| r.role == role.native_name)
            .ok_or("entry-output-role")?;
        let mut leaves = returned.outputs.iter().cloned();
        let mut values = BTreeMap::new();
        for port in interface.output_ports(role) {
            values.insert(
                port.name.clone(),
                value::collect(&port.schema, &mut leaves)?,
            );
        }
        if leaves.next().is_some() {
            return Err("entry-output-shape".into());
        }
        outputs.insert(role.name.clone(), values);
    }
    Ok(outputs)
}
