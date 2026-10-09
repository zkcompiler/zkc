//! Registry-owned native services. References name roots; leases own execution.
#[cfg(feature = "test-utils")]
use crate::Scalar;
use crate::resource::Resources;
use crate::{Capability, CapabilityObservation, Policy, Result, Value, refused};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex, MutexGuard};
use zkc_runtime::interactive::ServiceContract;

/// Native service shapes belong to the executing provider, independently of
/// the runtime contract catalogue. These facts never authorize a root or lease.
pub(crate) fn support(
    contract: ServiceContract,
    method: &str,
) -> Option<zkc_runtime::interactive::ServiceSupport> {
    use zkc_runtime::interactive::{
        Identity, LogicalType, PhysicalType, Representation, ServiceSignature, ServiceSupport, Type,
    };
    if method != "draw" {
        return None;
    }
    let (field, representation) = match contract {
        ServiceContract::RandomBls12381Field => (Identity::Bls12381Fr, Representation::Fr),
        ServiceContract::RandomBn254Field => (Identity::Bn254Fr, Representation::Bn254Fr),
        ServiceContract::RandomRistrettoField => {
            (Identity::Ristretto255Scalar, Representation::DalekScalar)
        }
        ServiceContract::RandomExtensionField => {
            (Identity::KoalaBearExt8, Representation::KoalaBearExt8)
        }
    };
    Some(ServiceSupport {
        signature: ServiceSignature {
            inputs: vec![],
            outputs: vec![
                PhysicalType::new(LogicalType::new(Type::Field, field).ok()?, representation)
                    .ok()?,
            ],
        },
        max_retained_bytes: 512,
    })
}

struct Authority;
struct LeaseIdentity;

/// Authenticated reusable handle. Copying it neither copies nor resets state.
/// There is intentionally no constructor from an integer or an affine token.
/// ```compile_fail
/// use zkc_backends::services::ServiceReference;
/// fn forge(existing: ServiceReference) -> ServiceReference {
///     ServiceReference { id: 0, ..existing }
/// }
/// ```
/// ```compile_fail
/// use zkc_backends::{Capability, services::ServiceReference};
/// fn bind_unmanaged(token: Capability) -> ServiceReference { token }
/// ```
#[derive(Clone)]
pub struct ServiceReference {
    authority: Arc<Authority>,
    id: u64,
    contract: ServiceContract,
}
impl std::fmt::Debug for ServiceReference {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ServiceReference")
            .field("issued_id", &self.id)
            .finish_non_exhaustive()
    }
}
impl ServiceReference {
    /// Registry-local observation, never an authentication credential.
    pub fn issued_id(&self) -> u64 {
        self.id
    }
    pub fn contract(&self) -> &'static str {
        self.contract.name()
    }
    pub fn same_root(&self, other: &Self) -> bool {
        self.id == other.id && Arc::ptr_eq(&self.authority, &other.authority)
    }
}

struct Root {
    owner: String,
    token: Capability,
    lease: Option<Arc<LeaseIdentity>>,
    poisoned: bool,
    completion_known: bool,
}
struct RegistryState {
    resources: Resources,
    roots: BTreeMap<u64, Root>,
}

/// One issuance authority. Clones share the registry, including live leases.
#[derive(Clone)]
pub struct ServiceRegistry {
    authority: Arc<Authority>,
    state: Arc<Mutex<RegistryState>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServiceObservation {
    pub owner: String,
    pub leased: bool,
    pub poisoned: bool,
    /// Absent after an unexpected failure whose exact completion is unknown.
    pub state: Option<CapabilityObservation>,
}

fn identifier(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_.-".contains(&b))
}

impl ServiceRegistry {
    pub fn new(policy: Policy) -> Self {
        Self {
            authority: Arc::new(Authority),
            state: Arc::new(Mutex::new(RegistryState {
                resources: Resources::new(policy),
                roots: BTreeMap::new(),
            })),
        }
    }
    fn lock(&self) -> Result<MutexGuard<'_, RegistryState>> {
        self.state
            .lock()
            .map_err(|_| refused("service-registry-poisoned"))
    }
    fn authenticate(&self, reference: &ServiceReference) -> Result<()> {
        if !Arc::ptr_eq(&self.authority, &reference.authority) {
            return Err(refused("service-authority"));
        }
        Ok(())
    }
    fn issue(
        &self,
        owner: &str,
        create: impl FnOnce(&mut Resources) -> Result<Capability>,
    ) -> Result<ServiceReference> {
        if !identifier(owner) {
            return Err(refused("service-owner"));
        }
        let mut state = self.lock()?;
        let token = create(&mut state.resources)?;
        let id = token.issued_id();
        state.roots.insert(
            id,
            Root {
                owner: owner.into(),
                token,
                lease: None,
                poisoned: false,
                completion_known: true,
            },
        );
        Ok(ServiceReference {
            authority: self.authority.clone(),
            id,
            contract: ServiceContract::for_field(state.roots[&id].token.identity())
                .expect("installed service field"),
        })
    }
    pub fn issue_random_for(
        &self,
        owner: &str,
        contract: ServiceContract,
        budget: u64,
    ) -> Result<ServiceReference> {
        self.issue(owner, |resources| {
            resources.issue_managed_random(owner, contract.field(), budget)
        })
    }
    #[cfg(feature = "test-utils")]
    pub fn issue_test_tape(
        &self,
        owner: &str,
        budget: u64,
        tape: Vec<Scalar>,
    ) -> Result<ServiceReference> {
        self.issue(owner, |resources| {
            resources.issue_managed_tape(owner, budget, tape)
        })
    }
    pub fn observe(&self, reference: &ServiceReference) -> Result<ServiceObservation> {
        self.authenticate(reference)?;
        let state = self.lock()?;
        let root = state
            .roots
            .get(&reference.id)
            .ok_or_else(|| refused("service-unissued"))?;
        Ok(ServiceObservation {
            owner: root.owner.clone(),
            leased: root.lease.is_some(),
            poisoned: root.poisoned,
            state: if root.completion_known {
                Some(state.resources.observe(&root.token)?)
            } else {
                None
            },
        })
    }
    /// Explicit host lifecycle action. Dropping references never retires a root.
    pub fn retire(&self, reference: &ServiceReference) -> Result<ServiceObservation> {
        self.authenticate(reference)?;
        let mut state = self.lock()?;
        let root = state
            .roots
            .get(&reference.id)
            .ok_or_else(|| refused("service-unissued"))?;
        if root.lease.is_some() {
            return Err(refused("service-leased"));
        }
        if !root.completion_known {
            return Err(refused("service-completion-unknown"));
        }
        let token = root.token.clone();
        let observation = state.resources.retire(&token)?;
        let root = state
            .roots
            .remove(&reference.id)
            .expect("authenticated root");
        Ok(ServiceObservation {
            owner: root.owner,
            leased: false,
            poisoned: root.poisoned,
            state: Some(observation),
        })
    }
    pub(crate) fn acquire(
        &self,
        owner: &str,
        references: &[ServiceReference],
    ) -> Result<ServiceLease> {
        if !identifier(owner) {
            return Err(refused("service-owner"));
        }
        if references.len() > 4096 {
            return Err(refused("service-port-limit"));
        }
        let mut ids = BTreeSet::new();
        let mut state = self.lock()?;
        // Validate the complete set before installing any lease.
        for reference in references {
            self.authenticate(reference)?;
            let root = state
                .roots
                .get(&reference.id)
                .ok_or_else(|| refused("service-unissued"))?;
            if root.owner != owner {
                return Err(refused("service-owner"));
            }
            if root.poisoned {
                return Err(refused("service-poisoned"));
            }
            if root.lease.is_some() {
                return Err(refused("service-leased"));
            }
            ids.insert(reference.id);
        }
        let identity = Arc::new(LeaseIdentity);
        for id in &ids {
            state.roots.get_mut(id).expect("checked root").lease = Some(identity.clone());
        }
        Ok(ServiceLease {
            registry: self.clone(),
            identity,
            roots: ids,
            owner: owner.into(),
        })
    }
}

/// One endpoint's authority over all its roots. Not cloneable. Synchronous
/// queries borrow this lease, so dropping it cannot race an in-flight query.
pub(crate) struct ServiceLease {
    registry: ServiceRegistry,
    identity: Arc<LeaseIdentity>,
    roots: BTreeSet<u64>,
    owner: String,
}
impl ServiceLease {
    pub(crate) fn poison(&self, reference: &ServiceReference) {
        if self.registry.authenticate(reference).is_ok()
            && let Ok(mut state) = self.registry.lock()
            && let Some(root) = state.roots.get_mut(&reference.id)
            && root
                .lease
                .as_ref()
                .is_some_and(|lease| Arc::ptr_eq(lease, &self.identity))
        {
            root.poisoned = true;
        }
    }
    pub(crate) fn draw(&self, reference: &ServiceReference) -> Result<Value> {
        self.transition(reference, |resources, token| {
            resources.draw_managed(&self.owner, token)
        })
    }
    fn transition(
        &self,
        reference: &ServiceReference,
        consume: impl FnOnce(&mut Resources, &Capability) -> Result<(Value, Capability)>,
    ) -> Result<Value> {
        self.registry.authenticate(reference)?;
        let mut state = self.registry.lock()?;
        let root = state
            .roots
            .get_mut(&reference.id)
            .ok_or_else(|| refused("service-unissued"))?;
        if !self.roots.contains(&reference.id)
            || !root
                .lease
                .as_ref()
                .is_some_and(|lease| Arc::ptr_eq(lease, &self.identity))
        {
            return Err(refused("service-lease"));
        }
        if root.poisoned {
            return Err(refused("service-poisoned"));
        }
        let token = root.token.clone();
        // Fail closed before entering the backend. Completion and successor
        // installation occur under this same mutex, before cancellation can run.
        root.poisoned = true;
        root.completion_known = false;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            consume(&mut state.resources, &token)
        }));
        let root = state.roots.get_mut(&reference.id).expect("leased root");
        match result {
            Ok(Ok((value, successor))) => {
                root.token = successor;
                root.completion_known = true;
                root.poisoned = false;
                Ok(value)
            }
            Ok(Err(error)) => {
                root.completion_known = true;
                Err(error)
            }
            Err(_) => Err(refused("service-completion-unknown")),
        }
    }
}

pub(crate) struct ServiceBindings {
    pub(crate) registry: ServiceRegistry,
    pub(crate) ports: BTreeMap<String, ServiceReference>,
    lease: Option<ServiceLease>,
}
impl ServiceBindings {
    pub(crate) fn new(
        registry: ServiceRegistry,
        ports: BTreeMap<String, ServiceReference>,
    ) -> Result<Self> {
        if ports.len() > 4096 || ports.keys().any(|port| !identifier(port)) {
            return Err(refused("service-port-interface"));
        }
        for reference in ports.values() {
            registry.authenticate(reference)?;
        }
        Ok(Self {
            registry,
            ports,
            lease: None,
        })
    }
    pub(crate) fn enter(&mut self, frame: &zkc_runtime::interactive::Frame) -> Result<()> {
        if self.lease.is_some()
            || frame.services().len() != self.ports.len()
            || frame.services().iter().any(|port| {
                !self
                    .ports
                    .get(&port.name)
                    .is_some_and(|reference| reference.contract() == port.contract.name())
            })
        {
            return Err(refused("service-port-interface"));
        }
        self.lease = Some(self.registry.acquire(
            frame.role(),
            &self.ports.values().cloned().collect::<Vec<_>>(),
        )?);
        Ok(())
    }
    pub(crate) fn abort_entry(&mut self) {
        self.lease = None;
    }
    pub(crate) fn leave(&mut self) {
        self.lease = None;
        self.ports.clear();
    }
    pub(crate) fn draw(&self, port: &str) -> Result<Value> {
        let reference = self
            .ports
            .get(port)
            .ok_or_else(|| refused("service-port"))?;
        self.lease
            .as_ref()
            .ok_or_else(|| refused("service-lease"))?
            .draw(reference)
    }
    pub(crate) fn poison(&self, port: &str) {
        if let (Some(lease), Some(reference)) = (&self.lease, self.ports.get(port)) {
            lease.poison(reference);
        }
    }
}
impl Drop for ServiceLease {
    fn drop(&mut self) {
        if let Ok(mut state) = self.registry.state.lock() {
            for id in &self.roots {
                if let Some(root) = state.roots.get_mut(id)
                    && root
                        .lease
                        .as_ref()
                        .is_some_and(|lease| Arc::ptr_eq(lease, &self.identity))
                {
                    root.lease = None;
                }
            }
        }
    }
}

#[cfg(all(test, feature = "test-utils"))]
mod tests {
    use super::*;
    fn registry() -> ServiceRegistry {
        ServiceRegistry::new(Policy::default())
    }
    fn tape(registry: &ServiceRegistry, budget: u64, values: &[u64]) -> ServiceReference {
        registry
            .issue_test_tape(
                "Alice",
                budget,
                values.iter().copied().map(Scalar::from).collect(),
            )
            .unwrap()
    }
    fn field(value: Value) -> Scalar {
        let Value::Field(value) = value else {
            panic!("field reply")
        };
        value
    }
    #[test]
    fn typed_services_preserve_field_roots_and_budget_failure() {
        for contract in [
            ServiceContract::RandomBls12381Field,
            ServiceContract::RandomBn254Field,
            ServiceContract::RandomRistrettoField,
            ServiceContract::RandomExtensionField,
        ] {
            let registry = registry();
            let root = registry.issue_random_for("Alice", contract, 1).unwrap();
            assert_eq!(root.contract(), contract.name());
            let alias = root.clone();
            let lease = registry
                .acquire("Alice", std::slice::from_ref(&root))
                .unwrap();
            let value = lease.draw(&alias).unwrap();
            assert_eq!(
                zkc_runtime::interactive::Value::physical_type(&value),
                contract.signature("draw").unwrap().outputs[0]
            );
            assert!(lease.draw(&root).is_err());
            let observed = registry.observe(&root).unwrap();
            assert!(observed.poisoned);
            assert_eq!(observed.state.unwrap().draw_count, 2);
            drop(lease);
            registry.retire(&root).unwrap();
        }
    }
    #[test]
    fn aliases_share_successors_distinct_roots_keep_their_own_tapes() {
        let registry = registry();
        let root = tape(&registry, 3, &[5, 11, 17]);
        let other = tape(&registry, 3, &[5, 11, 17]);
        let alias = root.clone();
        let lease = registry
            .acquire("Alice", &[root.clone(), alias.clone(), other.clone()])
            .unwrap();
        assert_eq!(field(lease.draw(&root).unwrap()), Scalar::from(5u64));
        assert_eq!(field(lease.draw(&alias).unwrap()), Scalar::from(11u64));
        assert_eq!(field(lease.draw(&other).unwrap()), Scalar::from(5u64));
        assert!(root.same_root(&alias));
        assert!(!root.same_root(&other));
        drop(lease);
        let again = registry
            .acquire("Alice", std::slice::from_ref(&root))
            .unwrap();
        assert_eq!(field(again.draw(&root).unwrap()), Scalar::from(17u64));
        assert_eq!(
            registry.observe(&root).unwrap().state.unwrap().generation,
            3
        );
    }
    #[test]
    fn owner_authority_and_live_leases_are_checked_atomically() {
        let registry = registry();
        let root = tape(&registry, 3, &[5]);
        let foreign_registry = ServiceRegistry::new(Policy::default());
        let foreign = tape(&foreign_registry, 3, &[5]);
        assert_eq!(root.issued_id(), foreign.issued_id());
        assert!(!root.same_root(&foreign));
        assert!(registry.acquire("Alice", &[root.clone(), foreign]).is_err());
        assert!(!registry.observe(&root).unwrap().leased);
        assert!(
            registry
                .acquire("Bob", std::slice::from_ref(&root))
                .is_err()
        );
        let lease = registry
            .acquire("Alice", std::slice::from_ref(&root))
            .unwrap();
        assert!(
            registry
                .acquire("Alice", std::slice::from_ref(&root))
                .is_err()
        );
        assert!(registry.retire(&root).is_err());
        drop(lease);
        registry.retire(&root).unwrap();
        assert!(registry.acquire("Alice", &[root]).is_err());
    }
    #[test]
    fn failed_consumption_poisoning_keeps_the_actual_residual_state() {
        for (budget, values, draws, remaining) in [(1, vec![5], 2, 0), (2, vec![], 1, 1)] {
            let registry = registry();
            let root = tape(&registry, budget, &values);
            let lease = registry
                .acquire("Alice", std::slice::from_ref(&root))
                .unwrap();
            if draws == 2 {
                lease.draw(&root).unwrap();
            }
            assert!(lease.draw(&root).is_err());
            assert_eq!(
                lease.draw(&root).unwrap_err().code,
                "refused:service-poisoned"
            );
            let observation = registry.observe(&root).unwrap();
            assert!(observation.poisoned);
            let residual = observation.state.unwrap();
            assert_eq!(
                (residual.generation, residual.draw_count, residual.budget),
                (draws, draws, remaining)
            );
            drop(lease);
            assert!(!registry.observe(&root).unwrap().leased);
            assert!(
                registry
                    .acquire("Alice", std::slice::from_ref(&root))
                    .is_err()
            );
            assert_eq!(registry.retire(&root).unwrap().state.unwrap(), residual);
        }
    }
    #[test]
    fn unexpected_failure_does_not_claim_an_exact_residual_state() {
        let registry = registry();
        let root = tape(&registry, 2, &[5, 11]);
        let lease = registry
            .acquire("Alice", std::slice::from_ref(&root))
            .unwrap();
        assert!(
            lease
                .transition(&root, |resources, token| {
                    resources.draw_managed("Alice", token)?;
                    panic!("uncertain completion")
                })
                .is_err()
        );
        drop(lease);
        let observation = registry.observe(&root).unwrap();
        assert!(observation.poisoned && observation.state.is_none() && !observation.leased);
        assert!(
            registry
                .acquire("Alice", std::slice::from_ref(&root))
                .is_err()
        );
        assert!(registry.retire(&root).is_err());
        let healthy = tape(&registry, 1, &[17]);
        let lease = registry
            .acquire("Alice", std::slice::from_ref(&healthy))
            .unwrap();
        assert!(
            matches!(lease.draw(&healthy).unwrap(), Value::Field(value) if value == Scalar::from(17u64))
        );
    }
    #[test]
    fn concurrent_entries_grant_exactly_one_lease() {
        let registry = registry();
        let root = tape(&registry, 2, &[5, 11]);
        let barrier = Arc::new(std::sync::Barrier::new(2));
        let mut threads = vec![];
        for _ in 0..2 {
            let registry = registry.clone();
            let root = root.clone();
            let barrier = barrier.clone();
            threads.push(std::thread::spawn(move || {
                barrier.wait();
                let lease = registry.acquire("Alice", std::slice::from_ref(&root));
                barrier.wait(); // Keep a successful lease live through both attempts.
                let acquired = lease.is_ok();
                drop(lease);
                acquired
            }));
        }
        let successes = threads
            .into_iter()
            .filter_map(|thread| thread.join().unwrap().then_some(()))
            .count();
        assert_eq!(successes, 1);
        assert!(!registry.observe(&root).unwrap().leased);
        assert!(registry.acquire("Alice", &[root]).is_ok());
    }
}
