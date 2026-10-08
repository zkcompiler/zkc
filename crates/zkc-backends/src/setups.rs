use crate::{Policy, Result, Value, exhausted, refused};
use zkc_arkworks::{Metadata, VerifierKey};
use zkc_runtime::interactive::Value as RuntimeValue;

/// Host-authorized public verifier material. Registering keys is an explicit
/// trust decision; identifiers in peer messages never extend this registry.
#[derive(Clone, Debug, Default)]
pub struct SetupRegistry {
    keys: Vec<VerifierKey>,
}
impl SetupRegistry {
    /// Keep a bounded immutable set. Repeated metadata is rejected, rather than
    /// silently choosing one of two supplied materials with the same identity.
    pub fn new(keys: Vec<VerifierKey>, policy: &Policy) -> Result<Self> {
        if keys.len() > 64 {
            return Err(exhausted("setup-count"));
        }
        let mut bytes = 0usize;
        for (index, key) in keys.iter().enumerate() {
            if keys[..index].iter().any(|k| k.metadata() == key.metadata()) {
                return Err(refused("duplicate-setup"));
            }
            policy.table_len(key.metadata().arity())?;
            bytes = bytes
                .checked_add(Value::VerifierKey(std::sync::Arc::new(key.clone())).retained_bytes())
                .ok_or_else(|| exhausted("setup-bytes"))?;
            policy.output(bytes, usize::MAX)?;
        }
        Ok(Self { keys })
    }
    pub fn get(&self, identity: Metadata) -> Option<&VerifierKey> {
        self.keys.iter().find(|key| key.metadata() == identity)
    }
    pub(crate) fn validate(&self, policy: &Policy) -> Result<()> {
        // Registry construction is bounded, but a backend may select a tighter policy.
        Self::new(self.keys.clone(), policy).map(|_| ())
    }
}

impl SetupRegistry {
    pub(crate) fn check(&self, identity: Metadata) -> Result<()> {
        self.get(identity)
            .map(|_| ())
            .ok_or_else(|| refused("unauthorized-setup"))
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }
    pub(crate) fn by_key_id(&self, id: &[u8]) -> Option<&VerifierKey> {
        self.keys.iter().find(|key| key.metadata().key_id() == id)
    }
}
