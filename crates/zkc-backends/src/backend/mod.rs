//! Native backend composition and explicit host-issued capabilities.
mod execute;
mod policy;
pub(crate) mod registry;
mod resource_unit;
mod validation;
use crate::setups::Setups;
use crate::{Capability, CapabilityObservation, Domain, Policy, Result, Value};
pub use policy::{EntryPolicy, PortConstraint, PublicInputs};
use std::sync::Arc;
use validation::Core;
use zkc_arkworks::{Metadata, VerifierKey};
use zkc_runtime::interactive::{Backend, Frame, FrameExit, Invocation};

/// Production Arkworks/Dalek field, group, PCS and challenge adapter. Private committed originals are
/// explicit values owned by the caller/runtime, never held in a backend map.
/// Configure a verifier key to decode peer PCS bytes.
pub struct NativeBackend {
    sequence_work: crate::sequence::Budget,
    external_work: crate::external_kernels::Budget,
    public_roles: crate::PublicRolePolicy,
    core: Core,
    services: Option<crate::services::ServiceBindings>,
    implementations: &'static registry::Registry,
}
impl NativeBackend {
    /// Validate data and entry constraints without entering a frame. Pending
    /// RNG/nonce/transcript slots may be None; all ordinary values must exist.
    pub fn check_entry_values(
        &self,
        role: &zkc_runtime::interactive::EntryRole,
        values: &[Option<&Value>],
    ) -> Result<()> {
        use zkc_runtime::interactive::Value as _;
        if role.inputs.len() != values.len() {
            return Err(crate::refused("frame-arguments"));
        }
        for ((_, ty), value) in role.inputs.iter().zip(values) {
            if let Some(value) = value {
                if value.physical_type() != *ty {
                    return Err(crate::refused("input-type"));
                }
                self.core.validate(value)?;
            }
        }
        self.core.check_entry_values(&role.inputs, values)
    }

    /// Bound cumulative expanded-node traversal by sequence kernels. Previously
    /// spent work survives frame cleanup and changes to the limit.
    pub fn with_sequence_work_limit(mut self, limit: u64) -> Self {
        self.sequence_work.limit = limit;
        self
    }
    pub fn sequence_work_spent(&self) -> u64 {
        self.sequence_work.spent
    }
    /// Host bindings are checked against the admitted entry frame before any
    /// lease is acquired. Existing references do not grant wire transfer.
    /// Successful entry bindings last for one run. After extracting a finished
    /// runner's backend with `into_backend`, call this again to rebind its ports.
    pub fn with_services(
        mut self,
        registry: crate::services::ServiceRegistry,
        ports: std::collections::BTreeMap<String, crate::services::ServiceReference>,
    ) -> Result<Self> {
        self.install_services(registry, ports)?;
        Ok(self)
    }

    /// Install service bindings before execution while retaining backend custody
    /// on failure, so hosts can retire any resources they have already issued.
    pub fn install_services(
        &mut self,
        registry: crate::services::ServiceRegistry,
        ports: std::collections::BTreeMap<String, crate::services::ServiceReference>,
    ) -> Result<()> {
        if self.active_frames() != 0 {
            return Err(crate::refused("service-active-backend"));
        }
        self.services = Some(crate::services::ServiceBindings::new(registry, ports)?);
        Ok(())
    }

    /// Independently installed execution owners. A registration does not imply
    /// support for every nominal argument; `Backend::binding_signature` checks it.
    pub fn installed_implementations(&self) -> Vec<(String, &'static str)> {
        self.implementations.implementations()
    }

    /// Default cumulative allowance for external construction primitives.
    pub const DEFAULT_EXTERNAL_WORK_LIMIT: u64 = crate::external_kernels::DEFAULT_WORK_LIMIT;

    /// Set a total primitive-work cap before external construction execution.
    /// Work already consumed is retained; lowering a cap never refunds it.
    pub fn with_external_work_limit(mut self, limit: u64) -> Self {
        self.external_work.limit = limit;
        self
    }
    pub fn external_work_spent(&self) -> u64 {
        self.external_work.spent
    }

    /// Explicit caller-owned publicness assertion. Ordinary constructors grant
    /// nothing. The artifact host derives this from its checked public profile;
    /// arbitrary interactive hosts must justify the assertion themselves.
    pub fn with_public_role_policy(mut self, policy: crate::PublicRolePolicy) -> Self {
        self.public_roles = policy;
        self
    }

    /// Direct native host utility. Key operands come from trusted host inputs;
    /// entry keys must agree, and an optional verifier pins PCS values/decoding.
    /// Use `with_setups` for prior authorization of every independent setup.
    pub fn new(policy: Policy, entry: EntryPolicy, verifier: Option<VerifierKey>) -> Result<Self> {
        let mut backend = Self {
            sequence_work: crate::sequence::Budget::default(),
            external_work: crate::external_kernels::Budget::default(),
            implementations: registry::installed()?,
            public_roles: crate::PublicRolePolicy::default(),
            core: Core::new(policy, entry),
            services: None,
        };
        backend.core.setups = Setups::InputKeys(verifier);
        if let Some(vk) = backend.core.setups.only() {
            backend.validate_value(&Value::VerifierKey(Arc::new(vk.clone())))?;
        }
        Ok(backend)
    }
    /// Install explicit setup authorization for several independent instances.
    /// The entry's optional homogeneous arity still applies when supplied; use
    /// named port constraints for heterogeneous tables, points and PCS values.
    pub fn with_setups(
        policy: Policy,
        entry: EntryPolicy,
        setups: crate::SetupRegistry,
    ) -> Result<Self> {
        setups.validate(&policy)?;
        let mut core = Core::new(policy, entry);
        core.setups = Setups::Registered(setups);
        Ok(Self {
            sequence_work: crate::sequence::Budget::default(),
            external_work: crate::external_kernels::Budget::default(),
            implementations: registry::installed()?,
            public_roles: crate::PublicRolePolicy::default(),
            core,
            services: None,
        })
    }
    /// Bind an explicit private transcript resource to host-authorized canonical
    /// root bytes with Merlin3/Fr64BE identity. Domain is custody-only; its local session is not hashed.
    pub fn issue_transcript(
        &mut self,
        domain: Domain,
        budget: u64,
        root_binding: &[u8],
    ) -> Result<Value> {
        self.core.policy.wire(root_binding.len())?;
        self.core
            .resources
            .issue_transcript(domain, budget, root_binding)
    }
    /// Issue an opaque BLS12-381.Fr nonce for the installed curve contracts.
    pub fn issue_nonce(&mut self, domain: Domain, budget: u64) -> Result<Value> {
        self.core.resources.issue_nonce(domain, budget)
    }
    #[cfg(feature = "test-utils")]
    pub fn issue_test_nonce(
        &mut self,
        domain: Domain,
        budget: u64,
        k: crate::Scalar,
    ) -> Result<Value> {
        self.core.resources.test_nonce(domain, budget, k)
    }
    pub fn issue_rng_for(
        &mut self,
        field: zkc_runtime::interactive::Identity,
        domain: Domain,
        budget: u64,
    ) -> Result<Value> {
        self.core.resources.issue_rng_for(field, domain, budget)
    }
    pub fn issue_nonce_for(
        &mut self,
        field: zkc_runtime::interactive::Identity,
        domain: Domain,
        budget: u64,
    ) -> Result<Value> {
        self.core.resources.issue_nonce_for(field, domain, budget)
    }
    pub fn issue_transcript_for(
        &mut self,
        suite: zkc_runtime::interactive::Identity,
        domain: Domain,
        budget: u64,
        root: &[u8],
    ) -> Result<Value> {
        self.core.policy.wire(root.len())?;
        self.core
            .resources
            .issue_transcript_for(suite, domain, budget, root)
    }
    #[cfg(feature = "test-utils")]
    pub fn issue_test_ristretto_rng(
        &mut self,
        domain: Domain,
        budget: u64,
        seed: [u8; 32],
    ) -> Result<Value> {
        self.core.resources.test_ristretto_rng(domain, budget, seed)
    }
    #[cfg(feature = "test-utils")]
    pub fn issue_test_ristretto_tape(
        &mut self,
        domain: Domain,
        budget: u64,
        tape: Vec<crate::RistrettoScalar>,
    ) -> Result<Value> {
        self.core
            .resources
            .test_ristretto_tape(domain, budget, tape)
    }
    #[cfg(feature = "test-utils")]
    pub fn issue_test_ristretto_nonce(
        &mut self,
        domain: Domain,
        budget: u64,
        k: crate::RistrettoScalar,
    ) -> Result<Value> {
        self.core.resources.test_ristretto_nonce(domain, budget, k)
    }
    pub fn policy(&self) -> &Policy {
        &self.core.policy
    }
    pub(crate) fn setups(&self) -> &Setups {
        &self.core.setups
    }
    pub fn verifier_key(&self) -> Option<&VerifierKey> {
        self.core.setups.only()
    }
    pub(crate) fn has_setup_registry(&self) -> bool {
        self.core.setups.is_registered()
    }
    pub(crate) fn input_setup(&self, port: &str) -> Option<Metadata> {
        self.core.entry.ports.get(port).and_then(|p| p.setup)
    }
    pub fn authorized_verifier_key(&self, identity: Metadata) -> Option<&VerifierKey> {
        self.core.setups.get(identity)
    }
    /// Explicit deterministic BN254 test input, with the same resource custody.
    #[cfg(feature = "test-utils")]
    pub fn issue_test_bn254_tape(
        &mut self,
        domain: Domain,
        budget: u64,
        tape: Vec<crate::Bn254Scalar>,
    ) -> Result<Value> {
        self.core.resources.test_bn254_tape(domain, budget, tape)
    }
    /// Issue a BLS12-381.Fr random source; `_for` selects another installed field.
    pub fn issue_rng(&mut self, domain: Domain, budget: u64) -> Result<Value> {
        self.core.resources.issue_rng(domain, budget)
    }
    #[cfg(feature = "test-utils")]
    pub fn issue_test_rng(&mut self, domain: Domain, budget: u64, seed: [u8; 32]) -> Result<Value> {
        self.core.resources.test_rng(domain, budget, seed)
    }
    #[cfg(feature = "test-utils")]
    pub fn issue_test_tape(
        &mut self,
        domain: Domain,
        budget: u64,
        tape: Vec<crate::Scalar>,
    ) -> Result<Value> {
        self.core.resources.test_tape(domain, budget, tape)
    }
    /// Check authenticated current custody without reconstructing a capability.
    pub fn verify_successor(&self, root: &Capability, successor: &Capability) -> Result<()> {
        self.core.resources.verify_successor(root, successor)
    }
    pub fn observe(&self, token: &Capability) -> Result<CapabilityObservation> {
        self.core.resources.observe(token)
    }
    /// Resource units live after the last frame exit.
    pub fn live_resource_units(&self) -> usize {
        self.core.resources.live_resource_units()
    }
    /// Revoke an attempt-local resource outside all active frames. Returns its
    /// final public counters; persistent RNGs must instead retain their actual
    /// successor handles. Retirement never resets or recreates a resource.
    pub fn retire(&mut self, token: &Capability) -> Result<CapabilityObservation> {
        self.core.resources.retire(token)
    }
    pub fn active_frames(&self) -> usize {
        self.core.resources.frame_count()
    }
}
impl Backend for NativeBackend {
    fn supports_boolean_literals(&self) -> bool {
        true
    }
    type Value = Value;
    fn service_signature(
        &self,
        contract: zkc_runtime::interactive::ServiceContract,
        method: &str,
    ) -> Option<(zkc_runtime::interactive::ServiceSignature, usize)> {
        contract.signature(method).map(|signature| (signature, 512))
    }
    fn query(
        &mut self,
        invocation: &zkc_runtime::interactive::ServiceInvocation<'_>,
        arguments: &[Value],
    ) -> Result<Vec<Value>> {
        use zkc_runtime::interactive::FrameKind;
        self.core.resources.active(invocation.frame)?;
        if !invocation.frame.origin().format.is_program()
            || !matches!(
                invocation.frame.kind(),
                FrameKind::Entry | FrameKind::Loop { .. }
            )
            || !invocation.frame.services().contains(invocation.port)
            || invocation
                .port
                .contract
                .signature(invocation.method)
                .is_none()
            || !arguments.is_empty()
            || invocation.max_output_bytes < 512
        {
            return Err(crate::refused("service-query-context"));
        }
        self.core.policy.output(512, invocation.max_output_bytes)?;
        self.services
            .as_ref()
            .ok_or_else(|| crate::refused("service-bindings"))?
            .draw(&invocation.port.name)
            .map(|value| vec![value])
    }
    fn reject_service_reply(
        &mut self,
        invocation: &zkc_runtime::interactive::ServiceInvocation<'_>,
    ) {
        if let Some(services) = &self.services {
            services.poison(&invocation.port.name);
        }
    }

    fn binding_signature(
        &self,
        binding: &zkc_runtime::interactive::OperationBinding,
    ) -> Option<zkc_runtime::interactive::BoundSignature> {
        self.implementations
            .get(&binding.implementation)?
            .signature(binding)
    }
    fn validate_value(&self, v: &Value) -> Result<()> {
        self.core.validate(v)
    }
    fn enter_frame(&mut self, f: &Frame, args: &[Value]) -> Result<()> {
        let entry = matches!(f.kind(), zkc_runtime::interactive::FrameKind::Entry);
        if entry {
            match &mut self.services {
                Some(services) => services.enter(f)?,
                None if f.services().is_empty() => {}
                None => return Err(crate::refused("service-bindings")),
            }
        }
        if let Err(error) = self.core.enter(f, args) {
            // No data frame exists on failed Core::enter. Release the tentative
            // service lease without cancelling or retiring caller-owned inputs.
            if entry && let Some(services) = &mut self.services {
                services.abort_entry();
            }
            return Err(error);
        }
        Ok(())
    }
    fn leave_frame(&mut self, f: &Frame, exit: FrameExit, outputs: &[Value]) -> Result<()> {
        // Always perform resource cleanup even if a non-resource output is invalid.
        let validation = outputs.iter().try_for_each(|v| self.validate_value(v));
        let cleanup = self.core.resources.leave(f, exit, outputs);
        if self.core.resources.frame_count() == 0
            && let Some(services) = &mut self.services
        {
            services.leave();
        }
        validation.and(cleanup)
    }
    fn apply(&mut self, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
        self.core.resources.active(i.frame)?;
        let implementation = self
            .implementations
            .get(i.binding.implementation())
            .ok_or_else(|| crate::refused("kernel-binding"))?;
        let signature = implementation
            .signature(i.binding.declaration())
            .ok_or_else(|| crate::refused("kernel-binding"))?;
        if crate::sequence::OPERATIONS.contains(&i.binding.declaration().contract.as_str()) {
            self.sequence_work.charge(args)?;
        }
        self.core.invoke(i, args, &signature)?;
        // Every family, including zero-input and early-return kernels, passes
        // the installed security gate before handler execution. Traversal work
        // charged above remains spent if validation or this gate refuses.
        if implementation.public_operands && !self.public_roles.permits(i.frame.role()) {
            return Err(crate::refused("public-operands-required"));
        }
        let outputs = (implementation.handler)(self, i, args)?;
        self.core.outputs(i, outputs)
    }
}

// Constructors propagate installation errors before admitting or executing anything.
// This legacy bool query conservatively requires public operands on installation
// failure; it cannot authorize execution or replace constructor validation.
pub(crate) fn requires_public_operands(identity: &str) -> bool {
    registry::installed().map_or(true, |registry| {
        registry
            .get(identity)
            .is_some_and(|entry| entry.public_operands)
    })
}
