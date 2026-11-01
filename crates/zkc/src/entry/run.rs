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
    pub fn installation(&self) -> &zkc_cpu::CpuInstallation {
        self.native.installation()
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
        .map_err(|e| E::boundary(P::Interface, e, &interface))?;
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
        interface
            .common_input_requirements(native.bundle())
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
    /// Resolve the authenticated selected original inventory against this Run.
    pub fn common_input_requirements(
        &self,
    ) -> std::result::Result<Vec<super::InputRequirement>, super::InterfaceError> {
        self.interface
            .common_input_requirements(self.native.bundle())
    }
    /// Pin expectations for every supplied joint input. The compiler owns
    /// inventory completeness; the application owns the external pin's trust.
    pub fn bind_common_inputs(
        self,
        bytes: &[u8],
        expected_sha256: &[u8; 32],
    ) -> std::result::Result<InputBoundRunEntry, super::BindingError> {
        let required = self
            .common_input_requirements()
            .map_err(|_| super::BindingError::Requirements)?;
        let bindings = super::InputBindings::admit_pinned(
            self.native.bundle().admitted(),
            self.native.bundle().entry(),
            &required,
            bytes,
            expected_sha256,
        )?;
        Ok(InputBoundRunEntry {
            entry: self,
            bindings,
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
    /// Run as a child of an outer invocation whose ledger charges this run's
    /// preparation, runners and Host-side work. `limits` carries the remaining
    /// allowances the parent selected for this child.
    pub(crate) fn execute_shared(
        &self,
        request: RunRequest,
        limits: HostLimits,
        ledger: zkc_runtime::vm::ExecutionLedger,
    ) -> EntryResult<RunReport> {
        let native = self
            .native
            .clone()
            .with_invocation_limits(limits)
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
            self.native.installation().clone(),
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

/// A named joint Run with immutable source-derived expectations. Preparation
/// checks all supplied roles before issuance or execution; this API does not
/// expose an independent-role transport protocol.
pub struct InputBoundRunEntry {
    entry: RunEntry,
    bindings: super::InputBindings,
}
impl InputBoundRunEntry {
    pub fn package(&self) -> &Package {
        self.entry.package()
    }
    pub fn interface(&self) -> &Interface {
        self.entry.interface()
    }
    pub fn prepare(&self, request: RunRequest) -> EntryResult<PreparedRun<'_>> {
        let prepared = self.entry.prepare(request)?;
        prepared
            .native
            .check_common_inputs(&self.bindings)
            .map_err(|e| E::new(P::Preparation, e))?;
        Ok(prepared)
    }
    pub fn check_inputs(&self, request: RunRequest) -> EntryResult<()> {
        self.prepare(request).map(drop)
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
    /// Execution and cleanup evidence; raw native returns are removed after
    /// reconstruction. Source results are available only through `outputs`.
    pub native: HostReport,
    pub outputs: Option<RoleValues>,
    pub output_error: Option<String>,
    encoding: ResultEncoding,
}
/// The admitted policy that encodes this run's results.
struct ResultEncoding {
    capacity: crate::execution::Capacity,
    cpu: crate::execution::CpuExecution,
    installation: zkc_cpu::CpuInstallation,
}
/// Encoded named results. The buffer keeps its charged live allowance in the
/// run's invocation ledger until it is dropped.
#[must_use = "retain the encoded results through publication or transport copy"]
pub struct EncodedRunResults<'a> {
    buffer: super::outputs::EncodedBuffer,
    _report: &'a RunReport,
}
impl EncodedRunResults<'_> {
    pub fn as_bytes(&self) -> &[u8] {
        &self.buffer.bytes
    }
}
impl AsRef<[u8]> for EncodedRunResults<'_> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}
impl RunReport {
    /// Encode the complete named results as `zkc.entry-outputs/0` under the
    /// invocation ledger that charged this run's Host-side inspection. The
    /// setup registry authenticates result codecs only. Encoding failure
    /// publishes no partial buffer.
    pub fn encode_results(&self, setups: zkc_cpu::SetupRegistry) -> Result<EncodedRunResults<'_>> {
        let values = self
            .outputs
            .as_ref()
            .filter(|_| self.is_success())
            .ok_or("entry-run-incomplete")?;
        let buffer = super::outputs::run_outputs_reserved(
            values,
            self.encoding.capacity,
            setups,
            self.encoding.cpu.clone(),
            self.encoding.installation.clone(),
            Some(self.native.invocation_ledger().clone()),
        )?;
        Ok(EncodedRunResults {
            buffer,
            _report: self,
        })
    }
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
    /// The ledger that charges this invocation's Host-side work.
    pub fn invocation_ledger(&self) -> &zkc_runtime::vm::ExecutionLedger {
        self.native.invocation_ledger()
    }
    pub fn execute(self) -> RunReport {
        let host = self.native.host();
        let encoding = ResultEncoding {
            capacity: host.limits().capacity,
            cpu: host.cpu().clone(),
            installation: host.installation().clone(),
        };
        let native = self.native.execute();
        let mut report = RunReport {
            native,
            outputs: None,
            output_error: None,
            encoding,
        };
        if report.native.failure.is_some() || !report.native.cleanup_errors.is_empty() {
            return public_report(report);
        }
        let Some(execution) = &report.native.execution else {
            return public_report(report);
        };
        if execution.outcome != Outcome::Completed {
            return public_report(report);
        }
        match collect(self.interface, execution) {
            Ok(outputs) => report.outputs = Some(outputs),
            Err(code) => report.output_error = Some(code),
        }
        public_report(report)
    }
}
fn public_report(mut report: RunReport) -> RunReport {
    if let Some(execution) = &mut report.native.execution {
        for role in &mut execution.roles {
            role.outputs.clear();
        }
    }
    report
}

fn collect(interface: &Interface, execution: &Report<zkc_cpu::CpuBackend>) -> Result<RoleValues> {
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

#[cfg(test)]
mod encoding_tests {
    use super::*;
    use serde_json::json;
    use sha2::{Digest, Sha256};

    fn entry(limits: HostLimits) -> RunEntry {
        let boolean: crate::entry::interface::raw::Schema = serde_json::from_value(json!({
            "kind":"boolean","identity":crate::io::bytes::hex(&Sha256::digest(b"bool")),
            "type":"bool","generated":null,"custody":0,"sealed":false,"roles":[],"element":null,
            "constructible":true,"permissions":["Copy","Drop"],"fields":[],"alternatives":[],
            "leaves":["bool"]}))
        .unwrap();
        let (document, artifact) = crate::entry::interface::tests::unicode::run_fixture(
            &boolean.describe(),
            &["P"],
            &["role00000000"],
        );
        let frame = json!({"format":"zkc.entry/0","original":"original",
            "interface":document.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,
                "oracle_realization":crate::entry::OracleSelection::default()}})
        .to_string();
        let package = Package::capture(
            frame.as_bytes(),
            &Sha256::digest(frame.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap();
        RunEntry::admit(package, limits, Default::default()).unwrap()
    }
    fn completed(limits: HostLimits) -> RunReport {
        let report = entry(limits)
            .prepare(RunRequest {
                session: "encoding".into(),
                roles: [(
                    "P".into(),
                    RoleInputs {
                        inputs: [("入力".into(), true.into())].into(),
                        ..Default::default()
                    },
                )]
                .into(),
                setups: Default::default(),
            })
            .unwrap()
            .execute();
        assert!(report.is_success(), "{:?}", report.output_error);
        report
    }

    #[test]
    fn result_encoding_charges_the_run_invocation_ledger() {
        let report = completed(HostLimits::default());
        let ledger = report.native.invocation_ledger().clone();
        let before = ledger.snapshot();
        let encoded = report.encode_results(Default::default()).unwrap();
        let document: serde_json::Value = serde_json::from_slice(encoded.as_bytes()).unwrap();
        assert_eq!(document["format"], "zkc.entry-outputs/0");
        assert_eq!(document["roles"]["P"]["結果"], true);
        let held = ledger.snapshot();
        assert!(held.live_reserved_bytes >= encoded.as_bytes().len());
        assert!(held.total_value_bytes > before.total_value_bytes);
        assert!(held.logical_bytes > before.logical_bytes);
        drop(encoded);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
        assert_eq!(ledger.snapshot().total_value_bytes, held.total_value_bytes);
        // The participant does no logical work, so the run completes under an
        // allowance smaller than the first 512-byte buffer reservation, and
        // encoding refuses without a partial buffer.
        let mut limits = HostLimits::default();
        limits.capacity.work.logical_bytes = 511;
        let report = completed(limits);
        assert_eq!(
            report.encode_results(Default::default()).err().unwrap(),
            "entry-output-limit"
        );
        assert_eq!(
            report
                .native
                .invocation_ledger()
                .snapshot()
                .live_reserved_bytes,
            0
        );
    }
}
