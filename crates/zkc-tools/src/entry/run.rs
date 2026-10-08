//! Named source calls adapt to the common native Host. There is no source
//! evaluator here: the bound interface supplies names and product/sum layouts.
use super::{Interface, Package, SetupAuthority, Value, arguments, setups, value};
use crate::protocol::run::{self as native, HostLimits, HostReport, Outcome, RunHost};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

type Result<T> = std::result::Result<T, String>;
pub type NamedValues = BTreeMap<String, Value>;
pub type RoleValues = BTreeMap<String, NamedValues>;

#[derive(Debug)]
pub struct RoleInputs {
    pub inputs: NamedValues,
    pub services: BTreeMap<String, u64>,
}
#[derive(Debug)]
pub struct RunRequest {
    pub session: String,
    pub roles: BTreeMap<String, RoleInputs>,
    pub setups: BTreeMap<String, Vec<u8>>,
}

/// An authenticated package, checked interface and admitted native run artifact.
pub struct RunEntry {
    package: Package,
    interface: Interface,
    native: RunHost,
}
impl RunEntry {
    pub fn admit(package: Package, limits: HostLimits, setups: SetupAuthority) -> Result<Self> {
        let interface = Interface::read(&package).map_err(|e| e.to_string())?;
        if interface.is_proof() {
            return Err("entry-job-kind".into());
        }
        for port in &interface.selected_protocol().inputs {
            arguments::check_import(&interface, port)?;
        }
        for port in &interface.selected_protocol().outputs {
            value::check_export(&port.schema)?;
        }
        let native = RunHost::admit(
            package.artifact().as_bytes(),
            &Sha256::digest(package.artifact().as_bytes()).into(),
            limits,
            setups::run_authority(&interface, setups)?,
        )?;
        interface.check_run(&native).map_err(|e| e.to_string())?;
        Ok(Self {
            package,
            interface,
            native,
        })
    }
    pub fn package(&self) -> &Package {
        &self.package
    }
    pub fn interface(&self) -> &Interface {
        &self.interface
    }
    pub fn limits(&self) -> HostLimits {
        self.native.limits()
    }

    /// Names must cover every role, input and service exactly. Empty logical
    /// products are required even though they have no native operand. The plan
    /// owns all prepared input data and may outlive the consumed request.
    pub fn prepare(&self, mut request: RunRequest) -> Result<PreparedRun<'_>> {
        let protocol = self.interface.selected_protocol();
        if request.roles.len() != protocol.roles.len() {
            return Err("entry-input-roles".into());
        }
        setups::check_material(
            &self.interface,
            &request.setups,
            self.native.limits().capacity,
        )?;
        let mut roles = Vec::new();
        for role in &protocol.roles {
            let values = request.roles.remove(role).ok_or("entry-input-roles")?;
            let inputs = arguments::values(
                &self.interface,
                protocol
                    .inputs
                    .iter()
                    .filter(|port| port.roles.contains(role)),
                values.inputs,
                None,
            )?;
            let services = arguments::services(
                protocol.services.iter().filter(|s| &s.owner == role),
                values.services,
            )?;
            roles.push(native::RoleInputs {
                role: role.clone(),
                inputs,
                services,
            });
        }
        let plan = self.native.prepare_typed(&native::RunInputs {
            session: request.session,
            roles,
            setups: request.setups,
        })?;
        Ok(PreparedRun {
            interface: &self.interface,
            native: plan,
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
    execution: &native::Report<zkc_backends::NativeBackend>,
) -> Result<RoleValues> {
    let protocol = interface.selected_protocol();
    let mut outputs = BTreeMap::new();
    for role in &protocol.roles {
        let returned = execution
            .roles
            .iter()
            .find(|r| &r.role == role)
            .ok_or("entry-output-role")?;
        let mut leaves = returned.outputs.iter().cloned();
        let mut values = BTreeMap::new();
        for port in protocol
            .outputs
            .iter()
            .filter(|port| port.roles.contains(role))
        {
            values.insert(
                port.name.clone(),
                value::collect(&port.schema, &mut leaves)?,
            );
        }
        if leaves.next().is_some() {
            return Err("entry-output-shape".into());
        }
        outputs.insert(role.clone(), values);
    }
    Ok(outputs)
}
