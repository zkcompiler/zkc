//! Native backend composition and explicit host-issued capabilities.
mod execute;
mod policy;
pub(crate) mod registry;
mod resource_unit;
mod validation;
mod work;
use crate::SetupRegistry;
use crate::{Capability, CapabilityObservation, Domain, Policy, Result, Value};
pub use policy::{EntryPolicy, PortConstraint};
use validation::Core;
use zkc_arkworks::{Metadata, VerifierKey};
use zkc_runtime::interactive::{Backend, Frame, FrameExit, Invocation};

/// Production Arkworks/Dalek field, group, PCS and challenge adapter. Private committed originals are
/// explicit values owned by the caller/runtime, never held in a backend map.
/// Configure a verifier key to decode peer PCS bytes.
pub struct NativeBackend {
    ring_assets: crate::ring::Registry,
    relation_assets: crate::relation::Registry,
    ring_work: crate::ring::Budget,
    sequence_work: crate::sequence::Budget,
    external_work: crate::external_kernels::Budget,
    core: Core,
    services: Option<crate::services::ServiceBindings>,
    implementations: &'static registry::Registry,
}
impl NativeBackend {
    pub fn with_relation_assets(mut self, assets: crate::relation::Registry) -> Result<Self> {
        if self.active_frames() != 0 {
            return Err(crate::refused("relation-active-backend"));
        }
        self.relation_assets = assets;
        Ok(self)
    }
    pub fn with_ring_assets(mut self, assets: crate::ring::Registry) -> Result<Self> {
        if self.active_frames() != 0 {
            return Err(crate::refused("ring-active-backend"));
        }
        self.ring_assets = assets;
        Ok(self)
    }
    pub fn with_ring_work_limit(mut self, limit: u64) -> Self {
        self.ring_work.limit = limit;
        self
    }
    pub fn ring_work_spent(&self) -> u64 {
        self.ring_work.spent
    }
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

    /// Bound cumulative sequence work: `3 * (1 + expanded operand nodes)` per
    /// call. Shared subtrees count per occurrence.
    /// Previously spent work survives frame cleanup and changes to the limit.
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
    /// One unit is one hash call, hashed byte, permutation, observe or sample.
    /// Work already consumed is retained; lowering a cap never refunds it.
    pub fn with_external_work_limit(mut self, limit: u64) -> Self {
        self.external_work.limit = limit;
        self
    }
    pub fn external_work_spent(&self) -> u64 {
        self.external_work.spent
    }

    /// Install explicit Host authorization for all PCS setup material.
    /// An empty registry is valid for computations that use no setup.
    pub fn new(policy: Policy, entry: EntryPolicy, setups: crate::SetupRegistry) -> Result<Self> {
        setups.validate(&policy)?;
        Ok(Self {
            ring_assets: crate::ring::Registry::default(),
            relation_assets: crate::relation::Registry::default(),
            ring_work: crate::ring::Budget::default(),
            sequence_work: crate::sequence::Budget::default(),
            external_work: crate::external_kernels::Budget::default(),
            implementations: registry::installed()?,
            core: Core::new(policy, entry, setups),
            services: None,
        })
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
    /// Issue a random source for an explicitly selected installed field.
    pub fn issue_rng_for(
        &mut self,
        field: zkc_runtime::interactive::Identity,
        domain: Domain,
        budget: u64,
    ) -> Result<Value> {
        self.core.resources.issue_rng_for(field, domain, budget)
    }
    /// Issue an opaque nonce for an explicitly selected curve scalar field.
    pub fn issue_nonce_for(
        &mut self,
        field: zkc_runtime::interactive::Identity,
        domain: Domain,
        budget: u64,
    ) -> Result<Value> {
        self.core.resources.issue_nonce_for(field, domain, budget)
    }
    /// Bind a selected transcript suite to Host-authorized canonical root bytes.
    /// Domain controls custody; its local session is not hashed.
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
    pub(crate) fn setups(&self) -> &SetupRegistry {
        &self.core.setups
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
    fn service_support(
        &self,
        contract: zkc_runtime::interactive::ServiceContract,
        method: &str,
    ) -> Option<zkc_runtime::interactive::ServiceSupport> {
        crate::services::support(contract, method)
    }
    fn query(
        &mut self,
        invocation: &zkc_runtime::interactive::ServiceInvocation<'_>,
        arguments: &[Value],
    ) -> Result<Vec<Value>> {
        use zkc_runtime::interactive::FrameKind;
        self.core.resources.active(invocation.frame)?;
        if !matches!(
            invocation.frame.kind(),
            FrameKind::Entry | FrameKind::Loop { .. }
        ) || !invocation.frame.services().contains(invocation.port)
            || crate::services::support(invocation.port.contract, invocation.method).is_none()
            || invocation.max_output_bytes < 512
        {
            return Err(crate::refused("service-query-context"));
        }
        self.core.policy.output(512, invocation.max_output_bytes)?;
        let services = self
            .services
            .as_ref()
            .ok_or_else(|| crate::refused("service-bindings"))?;
        match (invocation.method, arguments) {
            ("draw", []) => services.draw(&invocation.port.name),
            ("index", [Value::Index(bound)]) => services.index(&invocation.port.name, *bound),
            _ => Err(crate::refused("service-query-context")),
        }
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
    fn operand_work(&self, i: &Invocation<'_>, args: &[Value]) -> Option<u64> {
        work::operand_work(&i.binding.declaration().contract, args)
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
        if crate::sequence::IMPLEMENTATIONS
            .iter()
            .any(|(_, contract)| *contract == i.binding.declaration().contract)
        {
            self.sequence_work.charge(args)?;
        }
        self.core.invoke(i, args, &signature)?;
        let outputs = (implementation.handler)(self, i, args)?;
        self.core.outputs(i, args, outputs)
    }
}
