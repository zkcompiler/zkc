//! Source-authenticated application binding for an independently installed backend.
//! Execution uses the Runtime joint Host; this module only binds its source ABI.
use super::{BoundInterface, Interface, Package};
/// Common-context types. The normal Run adapter derives its inventory from the
/// authenticated package. The generic utility retains an explicit application
/// trust seam; neither path derives agreement from public/availability bits.
pub use zkc_runtime::host::input_binding::{
    BindingError, ContextProducer, InputBindings, InputComponent, InputRequirement, Observation,
};
use zkc_runtime::{
    host::{joint, wire::WireBackend},
    interpreter::Runner,
    vm::{
        BackendError, Contracts, ExecutionLedger, Limits, LoadError, RuntimeError, Usage,
        ValueBudget, WorkBudget,
    },
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
        super::arguments::check_boundary(&interface)?;
        for role in interface.roles() {
            if interface.services(role).next().is_some() {
                return Err("entry-backend-services".into());
            }
            for port in interface.input_ports(role) {
                crate::entry::interface::schemas::check_import(&port.schema)?;
            }
            for port in interface.output_ports(role) {
                crate::entry::interface::schemas::check_export(&port.schema)?;
                super::value::check_readable_schema(&port.schema)
                    .map_err(|_| "entry-backend-opaque")?;
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
        interface
            .common_input_requirements(&bundle)
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

    /// The selected original's complete owner-associated inventory, resolved
    /// against the actual admitted Program. This is not a source coverage proof.
    pub fn common_input_requirements(
        &self,
    ) -> Result<Vec<InputRequirement>, super::InterfaceError> {
        self.interface.common_input_requirements(&self.bundle)
    }

    /// Produce the canonical context that these participants' actual inputs
    /// determine. Each role's backend observes its own values; the selected
    /// budgets form the production's ledger, charged for inspection and
    /// encoding as `start_role` charges a check.
    pub fn common_input_context<B: WireBackend>(
        &self,
        inputs: &[joint::RoleInput<B>],
        value_budget: ValueBudget,
        work_budget: WorkBudget,
    ) -> Result<Vec<u8>, BindingError> {
        let required = self
            .common_input_requirements()
            .map_err(|_| BindingError::Requirements)?;
        let ledger = ExecutionLedger::new(value_budget, work_budget);
        let mut producer =
            InputBindings::producer(self.bundle.admitted(), self.bundle.entry(), &required)?;
        for input in inputs {
            producer.observe_role(
                &input.role,
                &input.backend,
                &input.values.iter().map(Some).collect::<Vec<_>>(),
                &ledger,
            )?;
        }
        producer.encode(&ledger)
    }
    /// Bind the package-derived inventory and an externally trusted context pin.
    /// The authenticated compiler owns source/native inventory completeness.
    /// Hashing received context bytes does not establish the pin's authority.
    pub fn bind_common_inputs(
        self,
        bytes: &[u8],
        expected_sha256: &[u8; 32],
    ) -> Result<InputBoundBackendRun, BindingError> {
        let required = self
            .common_input_requirements()
            .map_err(|_| BindingError::Requirements)?;
        let bindings = InputBindings::admit_pinned(
            self.bundle.admitted(),
            self.bundle.entry(),
            &required,
            bytes,
            expected_sha256,
        )?;
        Ok(InputBoundBackendRun {
            run: self,
            bindings,
        })
    }

    /// Start the common Host with caller-owned backend instances and values.
    /// The common linker independently checks each actual installation again.
    ///
    /// The selected `limits` bound the invocation: their live, fresh and
    /// logical byte budgets are the invocation root's allowances. The root
    /// charges wire transport, received payload decoding, report storage and
    /// every runner's bytes as it executes, and the report keeps it
    /// ([`joint::Report::invocation_ledger`]). Each runner keeps its own
    /// instruction and iteration fuel from `limits`.
    pub fn execute<B: WireBackend, H: joint::Hooks<B>>(
        &self,
        session: &str,
        inputs: Vec<joint::RoleInput<B>>,
        limits: joint::RunLimits,
        hooks: &mut H,
    ) -> Result<joint::Report<B>, joint::StartError<B>> {
        let root = ExecutionLedger::bytes_only(limits.values, limits.work.logical_bytes);
        joint::run_with_ledger(&self.bundle, session, inputs, limits, hooks, Some(root))
    }
}

/// A Run with an immutable, externally pinned common-input context. Every
/// participant started through this API checks its actual components before a
/// Runner or backend frame exists. The authenticated compiler owns complete
/// source/native association; the application owns the external pin.
pub struct InputBoundBackendRun {
    run: BackendRun,
    bindings: InputBindings,
}
impl InputBoundBackendRun {
    pub fn package(&self) -> &Package {
        self.run.package()
    }
    pub fn interface(&self) -> &Interface {
        self.run.interface()
    }

    /// Start one participant with the bound Program, entry and context. Refusal
    /// retains backend custody with zero execution usage. Runner admission still
    /// independently checks installations, capabilities, inputs and budgets.
    ///
    /// Each started participant is its own invocation, as in an independent
    /// process, whose only runner shares its root: the selected byte budgets
    /// are that one invocation's allowance, and the selected instructions
    /// and iterations are the Runner's own fuel. Common input inspection and
    /// encoding charge the root before the Runner exists, and the Runner
    /// charges its bytes there after.
    pub fn start_role<B: WireBackend>(
        &self,
        session: &str,
        input: joint::RoleInput<B>,
        value_budget: ValueBudget,
        work_budget: WorkBudget,
    ) -> Result<Runner<B>, LoadError<B>> {
        // The selected logical work is the root's allowance. Above the
        // interpreter's hard ceiling it refuses, as a runner's own would.
        if work_budget.logical_bytes > Limits::LOGICAL_BYTES {
            return Err(LoadError {
                error: RuntimeError::Limit,
                backend: input.backend,
                usage: Usage::default(),
            });
        }
        let ledger = ExecutionLedger::bytes_only(value_budget, work_budget.logical_bytes);
        if let Err(error) =
            self.bindings
                .check_role(&input.role, &input.backend, &input.values, &ledger)
        {
            // Capacity exhaustion keeps its own class; a refused binding keeps
            // its exact code.
            let error = match error {
                BindingError::Limit | BindingError::WorkLimit | BindingError::BytesLimit => {
                    RuntimeError::Limit
                }
                error => RuntimeError::Backend(BackendError::new(error.to_string())),
            };
            return Err(LoadError {
                error,
                backend: input.backend,
                usage: Usage::default(),
            });
        }
        Runner::new_for_role_with_ledger(
            self.run.bundle.admitted(),
            self.run.bundle.entry(),
            &input.role,
            session,
            input.backend,
            input.values,
            ValueBudget::UNBOUNDED,
            WorkBudget::fuel(work_budget.instructions, work_budget.iterations),
            Some(ledger),
        )
    }
}

#[cfg(test)]
mod tests;
