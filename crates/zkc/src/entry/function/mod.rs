//! Authenticated, statically admitted Entry control with native execution owners.
//!
//! Admission binds each numerical or deployment target to its result schema and
//! installed owner. Setup authority and the selected proof operation stay with
//! that deployment; invocation does not reinterpret the serialized carrier.
//! Numerical bodies execute in the existing VM, not in this control evaluator.
mod admission;
mod carrier;
mod data;
mod deployment;
mod execution;
mod schema;

pub use super::interface::raw::{Alternative, Field, Kind as SchemaKind, Permission, Schema};
use super::{EntryError, EntryPhase, NamedValues, Package, SetupAuthority};
use crate::execution::CpuExecution;
use crate::run::HostLimits;
pub use data::TypedValue;
pub use execution::{
    CallReceipt, FunctionFailure, FunctionReport, FunctionUsage, PreparedFunction,
};
pub use schema::{DeploymentInterface, FunctionInterface};
use serde::Deserialize;
use std::collections::BTreeMap;
use zkc_runtime::vm::{LogicalType, Program};

type Result<T> = std::result::Result<T, EntryError>;
fn error(code: &str) -> EntryError {
    EntryError::new(EntryPhase::Admission, code)
}
fn require(ok: bool, code: &str) -> Result<()> {
    if ok { Ok(()) } else { Err(error(code)) }
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub struct FunctionParameter {
    pub name: String,
    pub schema: Schema,
}
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(remote = "Self", deny_unknown_fields)]
pub struct FunctionSignature {
    pub symbol: String,
    pub parameters: Vec<FunctionParameter>,
    pub result: Schema,
}
crate::entry::decode::objects!(FunctionParameter, FunctionSignature);

#[derive(Clone, Debug)]
pub struct FunctionOptions {
    pub limits: HostLimits,
    pub binding: super::BindingPolicy,
    /// Maximum retained child call receipts, including failed calls.
    pub journal_events: usize,
    /// Invocation-wide service allowances, reserved before issuing child roots.
    pub service_draws: u64,
}
impl Default for FunctionOptions {
    fn default() -> Self {
        Self {
            limits: HostLimits::default(),
            binding: super::BindingPolicy::default(),
            journal_events: 256,
            service_draws: 64 * crate::entry::DEFAULT_DRAW_BUDGET,
        }
    }
}
impl FunctionOptions {
    /// Use the same installation for calculations, children and data codecs.
    pub fn with_installation(mut self, installation: zkc_cpu::CpuInstallation) -> Self {
        self.limits = self.limits.with_installation(installation);
        self
    }
}
#[derive(Debug, Default)]
pub struct RunContext {
    /// None draws a fresh OS-random session for each reached call. An explicit
    /// session is reused exactly; its freshness is the application's obligation.
    pub session: Option<String>,
    /// Application-owned setup inputs and service allowances, by source role.
    /// Ordinary data ports are supplied exclusively by the source Inputs record.
    pub roles: BTreeMap<String, super::RoleInputs>,
    pub setups: BTreeMap<String, Vec<u8>>,
}
impl RunContext {
    pub(super) fn session_for_call(&self) -> std::result::Result<String, String> {
        if let Some(session) = &self.session {
            return Ok(session.clone());
        }
        use rand::{TryRng, rngs::SysRng};
        let mut bytes = [0; 16];
        SysRng
            .try_fill_bytes(&mut bytes)
            .map_err(|_| "entry-session-random")?;
        Ok(crate::host::inputs::hex(&bytes))
    }
}
#[derive(Debug, Default)]
pub struct ProofContext {
    pub context: Vec<u8>,
    pub private: super::RoleInputs,
    pub transcript_budget: Option<u64>,
    pub setups: BTreeMap<String, Vec<u8>>,
}
#[derive(Debug)]
pub enum InvocationBinding {
    Run(RunContext),
    Proof(ProofContext),
}
#[derive(Debug, Default)]
pub struct InvocationContext {
    pub deployments: BTreeMap<String, InvocationBinding>,
}
#[derive(Debug, Default)]
pub struct FunctionRequest {
    pub arguments: NamedValues,
    pub context: InvocationContext,
}

struct Calculation {
    function: String,
    results: Vec<Schema>,
    program: Program,
}
struct Deployment {
    result: Schema,
    authority: SetupAuthority,
    kind: DeploymentKind,
}
enum DeploymentKind {
    Run(Box<super::RunEntry>),
    Proof {
        entry: Box<super::ProofEntry>,
        operation: super::ProofOperation,
    },
}
impl Deployment {
    fn operation(&self) -> &str {
        match &self.kind {
            DeploymentKind::Run(_) => "run",
            DeploymentKind::Proof {
                operation: super::ProofOperation::Prove,
                ..
            } => "prove",
            DeploymentKind::Proof {
                operation: super::ProofOperation::Verify,
                ..
            } => "verify",
        }
    }
}
/// Checked execution state owned by the authenticated FunctionEntry.
struct EntryHost {
    cpu: CpuExecution,
    entry: String,
    functions: Vec<carrier::Function>,
    interface: FunctionInterface,
    calculations: BTreeMap<String, Calculation>,
    deployments: BTreeMap<String, Deployment>,
    types: BTreeMap<String, LogicalType>,
    schemas: BTreeMap<String, std::sync::Arc<Schema>>,
    options: FunctionOptions,
    assets: super::EntryAssets,
}
pub struct FunctionEntry {
    package: Package,
    host: EntryHost,
}
impl FunctionEntry {
    /// Share the context with numerical calls and all admitted child deployments.
    pub fn with_cpu(mut self, cpu: CpuExecution) -> Self {
        self.host.deployments = self
            .host
            .deployments
            .into_iter()
            .map(|(id, mut deployment)| {
                deployment.kind = match deployment.kind {
                    DeploymentKind::Run(entry) => {
                        DeploymentKind::Run(Box::new(entry.with_cpu(cpu.clone())))
                    }
                    DeploymentKind::Proof { entry, operation } => DeploymentKind::Proof {
                        entry: Box::new(entry.with_cpu(cpu.clone())),
                        operation,
                    },
                };
                (id, deployment)
            })
            .collect();
        self.host.cpu = cpu;
        self
    }
    pub fn installation(&self) -> &zkc_cpu::CpuInstallation {
        &self.host.options.limits.installation
    }
    pub fn check_result_encoding(&self) -> Result<()> {
        self.host
            .interface
            .check_result_encoding_with_installation(self.installation())
    }
    pub fn cpu(&self) -> &CpuExecution {
        &self.host.cpu
    }
    pub fn admit(
        package: Package,
        options: FunctionOptions,
        authority: BTreeMap<String, SetupAuthority>,
    ) -> Result<Self> {
        Self::admit_with_cpu(
            package,
            options,
            authority,
            CpuExecution::serial().map_err(|e| error(&e.to_string()))?,
        )
    }
    /// Share one context from admission through calculations and child calls.
    pub fn admit_with_cpu(
        package: Package,
        options: FunctionOptions,
        authority: BTreeMap<String, SetupAuthority>,
        cpu: CpuExecution,
    ) -> Result<Self> {
        let host = cpu.enter(|| admission::admit(&package, options, authority, cpu.clone()))?;
        Ok(Self { package, host })
    }
    pub fn deployments(&self) -> impl Iterator<Item = (&str, &str)> {
        self.host
            .deployments
            .iter()
            .map(|(id, deployment)| (id.as_str(), deployment.operation()))
    }
    pub fn package(&self) -> &Package {
        &self.package
    }
    #[cfg(test)]
    fn host(&self) -> &EntryHost {
        &self.host
    }
    pub fn assets(&self) -> &super::EntryAssets {
        &self.host.assets
    }
    pub fn interface(&self) -> &FunctionInterface {
        &self.host.interface
    }
    pub fn signature(&self) -> &FunctionSignature {
        self.host.signature()
    }
    pub fn functions(&self) -> impl Iterator<Item = &FunctionSignature> {
        self.host.functions()
    }
    pub fn describe(&self) -> serde_json::Value {
        self.host.describe()
    }
    pub fn prepare(&self, request: FunctionRequest) -> Result<PreparedFunction<'_>> {
        self.host.cpu.enter(|| self.host.prepare(request))
    }
    pub fn check_inputs(&self, request: FunctionRequest) -> Result<()> {
        self.prepare(request).map(drop)
    }
}
impl EntryHost {
    fn schema(&self, s: &Schema) -> std::sync::Arc<Schema> {
        self.schemas[&s.identity].clone()
    }
    pub fn signature(&self) -> &FunctionSignature {
        &self
            .functions
            .iter()
            .find(|f| f.signature.symbol == self.entry)
            .expect("admitted root")
            .signature
    }
    pub fn functions(&self) -> impl Iterator<Item = &FunctionSignature> {
        self.functions.iter().map(|f| &f.signature)
    }
    pub fn describe(&self) -> serde_json::Value {
        self.interface.describe()
    }
}

#[cfg(test)]
mod tests;
