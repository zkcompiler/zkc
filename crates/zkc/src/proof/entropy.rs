//! Invocation entropy issuance. Deterministic tapes exist only in test builds.
use crate::host::inputs::Result;
use zkc_cpu::{
    CpuBackend, Domain, Value,
    services::{ServiceReference, ServiceRegistry},
};
use zkc_runtime::vm::{Identity, Type};

#[derive(Default)]
pub(super) enum Entropy {
    #[default]
    System,
    #[cfg(feature = "test-utils")]
    Tapes(std::collections::BTreeMap<usize, zkc_cpu::TestTape>),
}
impl Entropy {
    pub(super) fn capability(
        &self,
        backend: &mut CpuBackend,
        kind: Type,
        field: Identity,
        port: usize,
        domain: Domain,
        budget: u64,
    ) -> Result<Value> {
        #[cfg(feature = "test-utils")]
        if let Self::Tapes(tapes) = self {
            use zkc_cpu::TestTape;
            let tape = tapes.get(&port).ok_or("native-proof-test-entropy-port")?;
            if tape.identity() != field {
                return Err("native-proof-test-entropy-field".into());
            }
            return match (kind, tape) {
                (Type::Nonce, TestTape::Bls12381(t)) if t.len() == 1 => {
                    backend.issue_test_nonce(domain, budget, t[0])
                }
                (Type::Nonce, TestTape::Ristretto(t)) if t.len() == 1 => {
                    backend.issue_test_ristretto_nonce(domain, budget, t[0])
                }
                (Type::Rng, TestTape::Bls12381(t)) => {
                    backend.issue_test_tape(domain, budget, t.clone())
                }
                (Type::Rng, TestTape::Bn254(t)) => {
                    backend.issue_test_bn254_tape(domain, budget, t.clone())
                }
                (Type::Rng, TestTape::Ristretto(t)) => {
                    backend.issue_test_ristretto_tape(domain, budget, t.clone())
                }
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
        contract: zkc_runtime::vm::ServiceContract,
        port: usize,
        budget: u64,
    ) -> Result<ServiceReference> {
        #[cfg(feature = "test-utils")]
        if let Self::Tapes(tapes) = self {
            let tape = tapes.get(&port).ok_or("native-proof-test-entropy-port")?;
            if tape.identity() != contract.field() {
                return Err("native-proof-test-entropy-field".into());
            }
            return registry
                .issue_test_tape(owner, budget, tape.clone())
                .map_err(|e| e.to_string());
        }
        let _ = port;
        registry
            .issue_random_for(owner, contract, budget)
            .map_err(|e| e.to_string())
    }
}
