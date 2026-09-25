use crate::{Policy, Result, Value, exhausted, refused};
use zkc_arkworks::{Metadata, VerifierKey};
use zkc_runtime::interactive::Value as RuntimeValue;

/// Host-authorized public verifier material. Registering keys is an explicit
/// trust decision; identifiers in peer messages never extend this registry.
#[derive(Clone, Debug)]
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
    pub(crate) fn only(&self) -> Option<&VerifierKey> {
        match self.keys.as_slice() {
            [key] => Some(key),
            _ => None,
        }
    }
    pub(crate) fn validate(&self, policy: &Policy) -> Result<()> {
        // Registry construction is bounded, but a backend may select a tighter policy.
        Self::new(self.keys.clone(), policy).map(|_| ())
    }
}

/// Direct native callers supply trusted key operands; a registry additionally
/// authorizes every setup before use. Neither policy selects source semantics.
pub(crate) enum Setups {
    InputKeys(Option<VerifierKey>),
    Registered(SetupRegistry),
}
impl Setups {
    pub(crate) fn only(&self) -> Option<&VerifierKey> {
        match self {
            Self::InputKeys(key) => key.as_ref(),
            Self::Registered(keys) => keys.only(),
        }
    }
    pub(crate) fn get(&self, identity: Metadata) -> Option<&VerifierKey> {
        match self {
            Self::InputKeys(key) => key.as_ref().filter(|key| key.metadata() == identity),
            Self::Registered(keys) => keys.get(identity),
        }
    }
    pub(crate) fn check(&self, identity: Metadata) -> Result<()> {
        match self {
            Self::InputKeys(Some(key)) if key.metadata() != identity => {
                Err(refused("key-mismatch"))
            }
            Self::Registered(keys) if keys.get(identity).is_none() => {
                Err(refused("unauthorized-setup"))
            }
            _ => Ok(()),
        }
    }
    pub(crate) fn is_registered(&self) -> bool {
        matches!(self, Self::Registered(_))
    }
}
