//! Native backend composition and explicit host-issued capabilities.
mod execute;
mod policy;
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
    external_work: crate::external_kernels::Budget,
    public_roles: crate::PublicRolePolicy,
    core: Core,
}
impl NativeBackend {
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
            external_work: crate::external_kernels::Budget::default(),
            public_roles: crate::PublicRolePolicy::default(),
            core: Core::new(policy, entry),
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
            external_work: crate::external_kernels::Budget::default(),
            public_roles: crate::PublicRolePolicy::default(),
            core,
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
    type Value = Value;
    fn binding_signature(
        &self,
        binding: &zkc_runtime::interactive::OperationBinding,
    ) -> Option<zkc_runtime::interactive::BoundSignature> {
        crate::external_kernels::signature(binding).or_else(|| crate::bindings::signature(binding))
    }
    fn validate_value(&self, v: &Value) -> Result<()> {
        self.core.validate(v)
    }
    fn enter_frame(&mut self, f: &Frame, args: &[Value]) -> Result<()> {
        self.core.enter(f, args)
    }
    fn leave_frame(&mut self, f: &Frame, exit: FrameExit, outputs: &[Value]) -> Result<()> {
        // Always perform resource cleanup even if a non-resource output is invalid.
        let validation = outputs.iter().try_for_each(|v| self.validate_value(v));
        let cleanup = self.core.resources.leave(f, exit, outputs);
        validation.and(cleanup)
    }
    fn apply(&mut self, i: &Invocation<'_>, args: &[Value]) -> Result<Vec<Value>> {
        let name = self.core.invoke(i, args)?;
        let outputs = self.execute(&name, i, args)?;
        self.core.outputs(i, outputs)
    }
}
