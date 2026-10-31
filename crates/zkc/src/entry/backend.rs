//! Source-authenticated application binding for an independently installed backend.
//! Execution uses the Runtime joint Host; this module only binds its source ABI.
use super::{BoundInterface, Interface, Package};
use zkc_runtime::{
    host::{joint, wire::WireBackend},
    vm::Contracts,
};

/// A source package bound to a portable backend's admitted executable.
///
/// Inputs are flat typed backend values in the checked participant ABI order.
/// The backend owns their codecs and capability validation. Native applications
/// normally use [`super::RunEntry`] for named schema-driven inputs and services.
/// This seam deliberately makes no implicit Native installation or setup import.
pub struct BackendRun {
    package: Package,
    interface: BoundInterface,
    bundle: joint::Bundle,
}
impl BackendRun {
    pub fn admit<B: WireBackend>(
        package: Package,
        contracts: &Contracts,
        backend: &B,
        limits: joint::BundleLimits,
    ) -> Result<Self, String> {
        let interface = BoundInterface::read(&package).map_err(|e| e.to_string())?;
        if interface.is_proof() {
            return Err("entry-job-kind".into());
        }
        // Asset evaluation and setup custody require an explicit backend adapter.
        // Refuse absent coverage rather than constructing Native values or roots.
        if !package.assets().is_empty() || !interface.setups.is_empty() {
            return Err("entry-backend-assets".into());
        }
        for role in interface.roles() {
            if interface.services(role).next().is_some() {
                return Err("entry-backend-services".into());
            }
            for port in interface.input_ports(role) {
                crate::entry::interface::schemas::check_import(&port.schema)?;
            }
            for port in interface.output_ports(role) {
                crate::entry::interface::schemas::check_export(&port.schema)?;
            }
        }
        let bundle = joint::Bundle::admit(
            package.authenticated_artifact().bytes(),
            backend,
            contracts,
            limits,
        )
        .map_err(|e| e.to_string())?;
        let identity = crate::io::bytes::hex(package.authenticated_artifact().identity());
        interface
            .check_run_bundle(&bundle, &identity)
            .map_err(|e| e.to_string())?;
        Ok(Self {
            package,
            interface,
            bundle,
        })
    }
    pub fn package(&self) -> &Package {
        &self.package
    }
    pub fn interface(&self) -> &Interface {
        &self.interface
    }
    pub fn bundle(&self) -> &joint::Bundle {
        &self.bundle
    }

    /// Start the common Host with caller-owned backend instances and values.
    /// The common linker independently checks each actual installation again.
    pub fn execute<B: WireBackend, H: joint::Hooks<B>>(
        &self,
        session: &str,
        inputs: Vec<joint::RoleInput<B>>,
        limits: joint::RunLimits,
        hooks: &mut H,
    ) -> Result<joint::Report<B>, joint::StartError<B>> {
        joint::run(&self.bundle, session, inputs, limits, hooks)
    }
}

#[cfg(test)]
mod tests;
