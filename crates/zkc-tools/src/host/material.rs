//! Only validated immutable key material crosses invocation boundaries.
use super::inputs::Result;
use std::sync::Arc;
use zkc_arkworks::{ProverKey, VerifierKey};
use zkc_backends::Value;
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
        capacity: super::capacity::Capacity,
    ) -> Result<Self> {
        capacity.validate()?;
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
        capacity: super::capacity::Capacity,
    ) -> Result<Self> {
        capacity.validate()?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::host::capacity::Capacity;
    #[test]
    fn reusable_material_import_authenticates_and_bounds_before_retention() {
        fn send_sync<T: Send + Sync>() {}
        send_sync::<ProverMaterial>();
        let capacity = Capacity::default();
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
