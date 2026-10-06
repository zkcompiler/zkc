//! Invocation entropy issuance. Deterministic tapes exist only in test builds.
use super::io::Result;
use zkc_backends::{
    Domain, NativeBackend, Value,
    services::{ServiceReference, ServiceRegistry},
};
use zkc_runtime::interactive::{Identity, Type};

#[derive(Default)]
pub(super) enum Entropy {
    #[default]
    System,
    #[cfg(feature = "test-utils")]
    Tapes(std::collections::BTreeMap<usize, Vec<zkc_backends::Scalar>>),
}
impl Entropy {
    pub(super) fn capability(
        &self,
        backend: &mut NativeBackend,
        kind: Type,
        field: Identity,
        port: usize,
        domain: Domain,
        budget: u64,
    ) -> Result<Value> {
        #[cfg(feature = "test-utils")]
        if let Self::Tapes(tapes) = self {
            if field != Identity::Bls12381Fr {
                return Err("native-proof-test-entropy-field".into());
            }
            let tape = tapes.get(&port).ok_or("native-proof-test-entropy-port")?;
            return match kind {
                Type::Nonce if tape.len() == 1 => backend.issue_test_nonce(domain, budget, tape[0]),
                Type::Rng => backend.issue_test_tape(domain, budget, tape.clone()),
                _ => return Err("native-proof-test-entropy-kind".into()),
            }
            .map_err(|e| e.to_string());
        }
        let _ = port;
        match kind {
            Type::Nonce => backend.issue_nonce_for(field, domain, budget),
            Type::Rng => backend.issue_rng_for(field, domain, budget),
            _ => return Err("native-proof-role-input-kind".into()),
        }
        .map_err(|e| e.to_string())
    }
    pub(super) fn service(
        &self,
        registry: &ServiceRegistry,
        owner: &str,
        contract: zkc_runtime::interactive::ServiceContract,
        port: usize,
        budget: u64,
    ) -> Result<ServiceReference> {
        #[cfg(feature = "test-utils")]
        if let Self::Tapes(tapes) = self {
            if contract.field() != Identity::Bls12381Fr {
                return Err("native-proof-test-entropy-field".into());
            }
            return registry
                .issue_test_tape(
                    owner,
                    budget,
                    tapes
                        .get(&port)
                        .ok_or("native-proof-test-entropy-port")?
                        .clone(),
                )
                .map_err(|e| e.to_string());
        }
        let _ = port;
        registry
            .issue_random_for(owner, contract, budget)
            .map_err(|e| e.to_string())
    }
}
