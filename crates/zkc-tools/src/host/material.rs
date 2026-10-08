//! Only validated immutable key material crosses invocation boundaries.
use super::inputs::Result;
use std::{collections::BTreeMap, sync::Arc};
use zkc_arkworks::{ProverKey, VerifierKey};
use zkc_backends::{Policy, Value};
use zkc_runtime::interactive::Value as RuntimeValue;

/// Validated immutable prover material, reusable across independent invocations.
/// This authenticates material identity, not the honesty of a trusted setup.
#[derive(Clone)]
pub struct ProverMaterial {
    key: Arc<ProverKey>,
}
impl std::fmt::Debug for ProverMaterial {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ProverMaterial")
            .field("metadata", &self.key.metadata())
            .field("fingerprint", &self.fingerprint())
            .finish_non_exhaustive()
    }
}
impl ProverMaterial {
    /// Bind imported bytes to an independently expected material fingerprint and
    /// the supplied verifier key. Each invocation separately checks this identity
    /// against its own authority-selected setup; import grants no such authority.
    pub fn from_bytes(
        bytes: &[u8],
        fingerprint: [u8; 32],
        verifier: &VerifierKey,
        capacity: super::capacity::NativeCapacity,
    ) -> Result<Self> {
        capacity.check()?;
        capacity.check_wire(bytes.len())?;
        let estimate =
            Value::key_retained_bytes(zkc_runtime::interactive::Type::ProverKey, verifier)
                .map_err(|e| e.to_string())?;
        if estimate > capacity.value_bytes {
            return Err("native-material-value-limit".into());
        }
        let key = ProverKey::from_bytes(
            bytes,
            fingerprint,
            verifier,
            &capacity.backend().ark_bounds(),
        )
        .map_err(|e| e.to_string())?;
        Ok(Self { key: Arc::new(key) })
    }
    /// Freeze one bounded regular file, then use the same authenticated import.
    /// Later requests retain the key independently of this file or its path.
    pub fn from_file(
        path: impl AsRef<std::path::Path>,
        fingerprint: [u8; 32],
        verifier: &VerifierKey,
        capacity: super::capacity::NativeCapacity,
    ) -> Result<Self> {
        capacity.check()?;
        let bytes = super::inputs::read_regular(path, capacity.wire_bytes).map_err(|e| {
            if e == "artifact-byte-limit" {
                "native-capacity-wire".into()
            } else {
                e
            }
        })?;
        Self::from_bytes(&bytes, fingerprint, verifier, capacity)
    }
    pub fn fingerprint(&self) -> [u8; 32] {
        self.key.material_fingerprint()
    }
    pub(crate) fn value(&self) -> Value {
        Value::ProverKey(self.key.clone())
    }
    /// Key checks use fixed metadata and the current installed policy. Perform
    /// them while planning; Ready then reserves the ordinary per-call charges.
    pub(crate) fn operand(
        &self,
        ty: &zkc_runtime::interactive::PhysicalType,
        selected: &VerifierKey,
        backend: &zkc_backends::NativeBackend,
    ) -> Result<Value> {
        let value = self.value();
        if value.physical_type() != *ty {
            return Err("native-input-type".into());
        }
        super::setups::check_input(&value, selected)?;
        zkc_runtime::interactive::Backend::validate_value(backend, &value)
            .map_err(|e| e.to_string())?;
        Ok(value)
    }
}

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
pub(crate) enum KeyIdentity {
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

pub(crate) struct MaterialCache {
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
    pub(crate) static VERIFIER_IMPORTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::host::capacity::NativeCapacity;
    #[test]
    fn reusable_material_import_authenticates_and_bounds_before_retention() {
        fn send_sync<T: Send + Sync>() {}
        send_sync::<ProverMaterial>();
        let capacity = NativeCapacity::default();
        let bounds = capacity.backend().ark_bounds();
        let keys = zkc_arkworks::Keys::setup_for_development(1, &bounds).unwrap();
        let other = zkc_arkworks::Keys::setup_for_development(1, &bounds).unwrap();
        let bytes = keys.prover_key().to_bytes(&bounds).unwrap();
        let pin = keys.prover_key().material_fingerprint();
        let vk = keys.verifier_key();
        let material = ProverMaterial::from_bytes(&bytes, pin, vk, capacity).unwrap();
        assert_eq!(material.fingerprint(), pin);
        assert!(Arc::ptr_eq(&material.key, &material.clone().key));
        let mut wrong = pin;
        wrong[0] ^= 1;
        let mismatch = zkc_arkworks::Error::KeyMismatch.to_string();
        assert_eq!(
            ProverMaterial::from_bytes(&bytes, wrong, vk, capacity).unwrap_err(),
            mismatch
        );
        assert_eq!(
            ProverMaterial::from_bytes(&bytes, pin, other.verifier_key(), capacity).unwrap_err(),
            mismatch
        );
        let mut small = capacity;
        small.wire_bytes = bytes.len() - 1;
        assert_eq!(
            ProverMaterial::from_bytes(&bytes, pin, vk, small).unwrap_err(),
            "native-capacity-wire"
        );
        small = capacity;
        small.value_bytes = material.value().retained_bytes() - 1;
        assert_eq!(
            ProverMaterial::from_bytes(&bytes, pin, vk, small).unwrap_err(),
            "native-material-value-limit"
        );
        small = capacity;
        small.elements = usize::MAX;
        assert_eq!(
            ProverMaterial::from_bytes(&[], pin, vk, small).unwrap_err(),
            "native-capacity-limit"
        );
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(ProverMaterial::from_bytes(&trailing, pin, vk, capacity).is_err());
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("material.pk");
        std::fs::write(&path, &bytes).unwrap();
        let from_file = ProverMaterial::from_file(&path, pin, vk, capacity).unwrap();
        small = capacity;
        small.wire_bytes = bytes.len() - 1;
        assert_eq!(
            ProverMaterial::from_file(&path, pin, vk, small).unwrap_err(),
            "native-capacity-wire"
        );
        assert_eq!(from_file.fingerprint(), pin);
        std::fs::remove_file(&path).unwrap();
        assert_eq!(
            from_file.value().retained_bytes(),
            material.value().retained_bytes()
        );
        assert_eq!(
            ProverMaterial::from_file(&path, pin, vk, capacity).unwrap_err(),
            "artifact-io"
        );
    }
}
