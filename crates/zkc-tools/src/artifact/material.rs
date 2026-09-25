//! Only validated immutable key material crosses invocation boundaries.
use super::io::Result;
use std::{collections::BTreeMap, sync::Arc};
use zkc_arkworks::{ProverKey, VerifierKey};
use zkc_backends::{Policy, Value};
use zkc_runtime::interactive::Value as RuntimeValue;

/// Bounds for retained key material and identities, separate from per-call
/// input/runtime budgets. Zero disables retention. Oversized/full caches simply
/// skip insertion; validation still runs. No eviction or negative caching.
#[derive(Clone, Copy, Debug)]
pub struct CacheLimits {
    pub entries: usize,
    pub bytes: usize,
}
impl Default for CacheLimits {
    fn default() -> Self {
        Self {
            entries: 64,
            bytes: 64 << 20,
        }
    }
}

/// `bytes` is the conservative retained-value/identity charge, not process RSS.
/// Map/allocator overhead is additionally bounded by `entries` (at most 64).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CacheUsage {
    pub entries: usize,
    pub bytes: usize,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum KeyIdentity {
    Verifier(Vec<u8>),
    Prover {
        wire_sha256: [u8; 32],
        fingerprint: [u8; 32],
        verifier: Vec<u8>,
    },
}
impl KeyIdentity {
    fn bytes(&self) -> usize {
        std::mem::size_of::<Self>()
            + match self {
                Self::Verifier(bytes) => bytes.len(),
                Self::Prover { verifier, .. } => verifier.len(),
            }
    }
}

enum Material {
    Verifier(Arc<VerifierKey>),
    Prover(Arc<ProverKey>),
}
impl Material {
    fn retained_bytes(&self) -> usize {
        match self {
            Self::Verifier(k) => Value::VerifierKey(k.clone()).retained_bytes(),
            Self::Prover(k) => Value::ProverKey(k.clone()).retained_bytes(),
        }
    }
}

pub(super) struct MaterialCache {
    limits: CacheLimits,
    usage: CacheUsage,
    // Insertion is private: resource/witness Values cannot enter this store.
    values: BTreeMap<KeyIdentity, Material>,
}
impl MaterialCache {
    pub fn new(limits: CacheLimits) -> Self {
        let hard = CacheLimits::default();
        Self {
            limits: CacheLimits {
                entries: limits.entries.min(hard.entries),
                bytes: limits.bytes.min(hard.bytes),
            },
            usage: CacheUsage::default(),
            values: BTreeMap::new(),
        }
    }
    pub fn disabled() -> Self {
        Self::new(CacheLimits {
            entries: 0,
            bytes: 0,
        })
    }
    pub fn usage(&self) -> CacheUsage {
        self.usage
    }
    pub fn clear(&mut self) {
        self.values.clear();
        self.usage = CacheUsage::default();
    }
    fn insert(&mut self, identity: KeyIdentity, value: Material) {
        let Some(bytes) = identity
            .bytes()
            .checked_add(value.retained_bytes())
            .and_then(|n| n.checked_add(std::mem::size_of::<Material>()))
            .and_then(|n| n.checked_add(self.usage.bytes))
        else {
            return;
        };
        if self.usage.entries >= self.limits.entries || bytes > self.limits.bytes {
            return;
        }
        self.values.insert(identity, value);
        self.usage.entries += 1;
        self.usage.bytes = bytes;
    }
    pub fn verifier(&mut self, bytes: &[u8], policy: &Policy) -> Result<Arc<VerifierKey>> {
        let identity = KeyIdentity::Verifier(bytes.to_vec());
        if let Some(Material::Verifier(key)) = self.values.get(&identity) {
            return Ok(key.clone());
        }
        let id = bytes
            .get(49..81)
            .ok_or("artifact-verifier-key")?
            .try_into()
            .map_err(|_| "artifact-verifier-key")?;
        #[cfg(test)]
        VERIFIER_IMPORTS.set(VERIFIER_IMPORTS.get() + 1);
        let key = Arc::new(
            VerifierKey::from_bytes(bytes, id, &policy.ark_bounds()).map_err(|e| e.to_string())?,
        );
        if key
            .to_bytes(&policy.ark_bounds())
            .map_err(|e| e.to_string())?
            != bytes
        {
            return Err("artifact-verifier-key".into());
        }
        self.insert(identity, Material::Verifier(key.clone()));
        Ok(key)
    }
    pub fn prover(&self, identity: &KeyIdentity) -> Option<Arc<ProverKey>> {
        match self.values.get(identity) {
            Some(Material::Prover(key)) => Some(key.clone()),
            _ => None,
        }
    }
    pub fn retain_prover(&mut self, identity: KeyIdentity, key: Arc<ProverKey>) {
        self.insert(identity, Material::Prover(key));
    }
}

#[cfg(test)]
thread_local! {
    pub(super) static VERIFIER_IMPORTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
