//! Immutable numerical setup imports. This module grants no invocation authority
//! and retains no resource reservations; SDK Hosts own both policies.
use crate::{CpuInstallation, Value};
use std::{collections::BTreeMap, sync::Arc};
use zkc_kernels::arkworks::bls12_381::{Bounds, ProverKey, VerifierKey};
type Result<T> = std::result::Result<T, String>;

/// Apply an independently selected setup recursively to all numerical leaves.
pub fn check_input(value: &Value, key: &VerifierKey) -> Result<()> {
    let metadata = match value {
        Value::Commitment(v) => Some(v.metadata()),
        Value::Proof(v) => Some(v.metadata()),
        Value::ProverKey(v) => Some(v.metadata()),
        Value::VerifierKey(v) => Some(v.metadata()),
        Value::Sequence(v) => {
            for child in v.iter() {
                check_input(child, key)?;
            }
            None
        }
        Value::Variant(v) => {
            for child in v.payload() {
                check_input(child, key)?;
            }
            None
        }
        _ => None,
    };
    if metadata.is_some_and(|actual| actual != key.metadata()) {
        return Err("native-proof-input-setup".into());
    }
    Ok(())
}

pub fn import_prover(
    bytes: &[u8],
    fingerprint: [u8; 32],
    verifier: &VerifierKey,
    bounds: Bounds,
) -> Result<Arc<ProverKey>> {
    ProverKey::from_bytes(bytes, fingerprint, verifier, &bounds)
        .map(Arc::new)
        .map_err(|e| e.to_string())
}

/// Immutable imports tied to one frozen installation and numerical capacity.
/// A pin has one current byte snapshot; replacement evicts before validation,
/// so malformed material cannot recover the previous cached import.
/// The aggregate budget covers canonical snapshots and conservative decoded
/// backing/collection overhead. It does not reserve invocation resources.
pub struct VerifierMaterials {
    bounds: Bounds,
    installation: CpuInstallation,
    retained_budget: usize,
    retained_bytes: usize,
    keys: BTreeMap<[u8; 32], ImportedVerifier>,
    provers: BTreeMap<[u8; 32], ImportedProver>,
}
struct ImportedProver {
    retained_bytes: usize,
    bytes: Vec<u8>,
    verifier: Vec<u8>,
    fingerprint: [u8; 32],
    key: Arc<ProverKey>,
}
struct ImportedVerifier {
    retained_bytes: usize,
    bytes: Vec<u8>,
    key: Arc<VerifierKey>,
}
impl VerifierMaterials {
    /// Zero disables retention; valid imports still authenticate and succeed.
    pub fn new(bounds: Bounds, installation: CpuInstallation, retained_budget: usize) -> Self {
        Self {
            bounds,
            installation,
            retained_budget,
            retained_bytes: 0,
            keys: BTreeMap::new(),
            provers: BTreeMap::new(),
        }
    }
    pub fn import(
        &mut self,
        bytes: &[u8],
        pin: [u8; 32],
        bounds: Bounds,
    ) -> Result<Arc<VerifierKey>> {
        if self.bounds != bounds {
            return Err("native-setup-capacity".into());
        }
        if !self.installation.supports_setup() {
            return Err("cpu-installation-setup".into());
        }
        if let Some(previous) = self
            .keys
            .get(&pin)
            .filter(|previous| previous.bytes == bytes)
        {
            return Ok(previous.key.clone());
        }
        self.invalidate(&pin);
        let key =
            Arc::new(VerifierKey::from_bytes(bytes, pin, &self.bounds).map_err(|e| e.to_string())?);
        let Some(retained_bytes) = snapshot_bound(bytes.len()).filter(|n| self.make_room(*n))
        else {
            return Ok(key);
        };
        self.keys.insert(
            pin,
            ImportedVerifier {
                retained_bytes,
                bytes: bytes.to_vec(),
                key: key.clone(),
            },
        );
        self.retained_bytes += retained_bytes;
        Ok(key)
    }
    pub fn import_prover(
        &mut self,
        bytes: &[u8],
        fingerprint: [u8; 32],
        verifier: &VerifierKey,
        bounds: Bounds,
    ) -> Result<Arc<ProverKey>> {
        if bounds != self.bounds {
            return Err("native-setup-capacity".into());
        }
        if !self.installation.supports_setup() {
            return Err("cpu-installation-setup".into());
        }
        let pin = verifier.metadata().key_id();
        let verifier_bytes = verifier.to_bytes(&self.bounds).map_err(|e| e.to_string())?;
        if let Some(previous) = self.provers.get(&pin).filter(|previous| {
            previous.bytes == bytes
                && previous.fingerprint == fingerprint
                && previous.verifier == verifier_bytes
        }) {
            return Ok(previous.key.clone());
        }
        self.remove_prover(&pin);
        let key = import_prover(bytes, fingerprint, verifier, self.bounds)?;
        let retained_bytes = snapshot_bound(bytes.len())
            .and_then(|n| n.checked_add(snapshot_bound(verifier_bytes.len())?));
        let Some(retained_bytes) = retained_bytes.filter(|n| self.make_room(*n)) else {
            return Ok(key);
        };
        self.provers.insert(
            pin,
            ImportedProver {
                retained_bytes,
                bytes: bytes.to_vec(),
                verifier: verifier_bytes,
                fingerprint,
                key: key.clone(),
            },
        );
        self.retained_bytes += retained_bytes;
        Ok(key)
    }
    pub fn observe_replacement(&mut self, pin: &[u8; 32], bytes: Option<&[u8]>) {
        if self
            .keys
            .get(pin)
            .is_some_and(|previous| Some(previous.bytes.as_slice()) != bytes)
            || self
                .provers
                .get(pin)
                .is_some_and(|previous| Some(previous.verifier.as_slice()) != bytes)
        {
            self.invalidate(pin);
        }
    }
    /// Explicitly invalidate independently of whether replacement bytes validate.
    pub fn invalidate(&mut self, pin: &[u8; 32]) {
        if let Some(previous) = self.keys.remove(pin) {
            self.retained_bytes -= previous.retained_bytes;
        }
        self.remove_prover(pin);
    }
    /// Named sources do not yet identify a setup pin. Preserve verifier imports
    /// while forgetting all prover imports before a replacement can fail.
    pub fn invalidate_provers(&mut self) {
        while let Some(pin) = self.provers.keys().next().copied() {
            self.remove_prover(&pin);
        }
    }
    fn remove_prover(&mut self, pin: &[u8; 32]) {
        if let Some(previous) = self.provers.remove(pin) {
            self.retained_bytes -= previous.retained_bytes;
        }
    }
    fn make_room(&mut self, bytes: usize) -> bool {
        if bytes > self.retained_budget {
            return false;
        }
        // Evict whole setup pins in byte order, independent of hit timing. Calls
        // holding an imported Arc keep their checked material after eviction.
        while self.retained_bytes > self.retained_budget - bytes {
            let pin = self
                .keys
                .keys()
                .next()
                .into_iter()
                .chain(self.provers.keys().next())
                .min()
                .copied();
            let Some(pin) = pin else { return false };
            self.invalidate(&pin);
        }
        true
    }
}

// Match the Host's conservative VK snapshot/import convention. The multiplier
// also covers decoded affine points and both PK basis families in the pinned
// codec; the fixed allowance covers Arc wrappers, metadata and map nodes. Charge
// the PK and its separate canonical VK snapshot independently, without sharing
// discounts. Overflow disables retention rather than refusing a valid import.
fn snapshot_bound(bytes: usize) -> Option<usize> {
    bytes.checked_mul(16)?.checked_add(4096)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (Bounds, zkc_kernels::arkworks::bls12_381::Keys) {
        let bounds = crate::Policy::default().ark_bounds();
        let keys = zkc_kernels::arkworks::bls12_381::Keys::setup_with_rng(
            1,
            &mut ark_std::rand::thread_rng(),
            &bounds,
        )
        .unwrap();
        (bounds, keys)
    }
    fn assert_bounded(material: &VerifierMaterials) {
        let actual = material
            .keys
            .values()
            .map(|v| v.retained_bytes)
            .sum::<usize>()
            + material
                .provers
                .values()
                .map(|v| v.retained_bytes)
                .sum::<usize>();
        assert_eq!(actual, material.retained_bytes);
        assert!(actual <= material.retained_budget);
    }
    #[test]
    fn mixed_imports_count_both_prover_and_verifier_snapshots() {
        let (bounds, keys) = fixture();
        let verifier = keys.verifier_key();
        let vk = verifier.to_bytes(&bounds).unwrap();
        let pk = keys.prover_key().to_bytes(&bounds).unwrap();
        let pin = verifier.metadata().key_id();
        let fingerprint = keys.prover_key().material_fingerprint();
        let total = snapshot_bound(vk.len()).unwrap() * 2 + snapshot_bound(pk.len()).unwrap();
        let mut material = VerifierMaterials::new(bounds, Default::default(), total);
        let v = material.import(&vk, pin, bounds).unwrap();
        let p = material
            .import_prover(&pk, fingerprint, verifier, bounds)
            .unwrap();
        assert_eq!(material.retained_bytes, total);
        assert_bounded(&material);
        assert!(Arc::ptr_eq(&v, &material.import(&vk, pin, bounds).unwrap()));
        assert!(Arc::ptr_eq(
            &p,
            &material
                .import_prover(&pk, fingerprint, verifier, bounds)
                .unwrap()
        ));
        material.invalidate_provers();
        assert_eq!(material.retained_bytes, snapshot_bound(vk.len()).unwrap());
        assert!(Arc::ptr_eq(&v, &material.import(&vk, pin, bounds).unwrap()));
        assert!(!Arc::ptr_eq(
            &p,
            &material
                .import_prover(&pk, fingerprint, verifier, bounds)
                .unwrap()
        ));
        assert_bounded(&material);
    }
    #[test]
    fn individually_admissible_mixed_pair_evicts_and_reimports_under_tiny_total() {
        let (bounds, keys) = fixture();
        let verifier = keys.verifier_key();
        let vk = verifier.to_bytes(&bounds).unwrap();
        let pk = keys.prover_key().to_bytes(&bounds).unwrap();
        let pin = verifier.metadata().key_id();
        let fingerprint = keys.prover_key().material_fingerprint();
        let budget = snapshot_bound(pk.len()).unwrap() + snapshot_bound(vk.len()).unwrap();
        let mut material = VerifierMaterials::new(bounds, Default::default(), budget);
        let old = material.import(&vk, pin, bounds).unwrap();
        let prover = material
            .import_prover(&pk, fingerprint, verifier, bounds)
            .unwrap();
        assert_eq!(material.retained_bytes, budget);
        assert!(material.keys.is_empty());
        assert_bounded(&material);
        let fresh = material.import(&vk, pin, bounds).unwrap();
        assert!(!Arc::ptr_eq(&old, &fresh));
        assert!(material.provers.is_empty());
        assert_bounded(&material);
        // Eviction never changes already checked immutable keys.
        assert_eq!(old.metadata(), fresh.metadata());
        assert_eq!(prover.material_fingerprint(), fingerprint);
    }
    #[test]
    fn zero_and_single_oversized_imports_bypass_without_refusing_valid_material() {
        let (bounds, keys) = fixture();
        let verifier = keys.verifier_key();
        let vk = verifier.to_bytes(&bounds).unwrap();
        let pk = keys.prover_key().to_bytes(&bounds).unwrap();
        let pin = verifier.metadata().key_id();
        let fingerprint = keys.prover_key().material_fingerprint();
        for budget in [0, snapshot_bound(vk.len()).unwrap() - 1] {
            let mut material = VerifierMaterials::new(bounds, Default::default(), budget);
            let first = material.import(&vk, pin, bounds).unwrap();
            assert!(!Arc::ptr_eq(
                &first,
                &material.import(&vk, pin, bounds).unwrap()
            ));
            let first = material
                .import_prover(&pk, fingerprint, verifier, bounds)
                .unwrap();
            assert!(!Arc::ptr_eq(
                &first,
                &material
                    .import_prover(&pk, fingerprint, verifier, bounds)
                    .unwrap()
            ));
            assert_eq!(material.retained_bytes, 0);
            assert_bounded(&material);
            let mut wrong_pin = pin;
            wrong_pin[0] ^= 1;
            assert!(material.import(&vk, wrong_pin, bounds).is_err());
            let mut wrong_fingerprint = fingerprint;
            wrong_fingerprint[0] ^= 1;
            assert!(
                material
                    .import_prover(&pk, wrong_fingerprint, verifier, bounds)
                    .is_err()
            );
            assert_eq!(material.retained_bytes, 0);
        }
        let mut material = VerifierMaterials::new(
            bounds,
            Default::default(),
            snapshot_bound(vk.len()).unwrap(),
        );
        let held = material.import(&vk, pin, bounds).unwrap();
        material
            .import_prover(&pk, fingerprint, verifier, bounds)
            .unwrap();
        assert!(Arc::ptr_eq(
            &held,
            &material.import(&vk, pin, bounds).unwrap()
        ));
        assert!(material.provers.is_empty());
        assert_bounded(&material);
        assert_eq!(snapshot_bound(usize::MAX), None);
    }
    #[test]
    fn pressure_evicts_smallest_pin_deterministically_across_hits() {
        let (bounds, first) = fixture();
        let (_, second) = fixture();
        let (_, third) = fixture();
        let mut fixtures = [&first, &second, &third];
        fixtures.sort_by_key(|k| k.verifier_key().metadata().key_id());
        let vk = |k: &zkc_kernels::arkworks::bls12_381::Keys| {
            k.verifier_key().to_bytes(&bounds).unwrap()
        };
        let pin = |k: &zkc_kernels::arkworks::bls12_381::Keys| k.verifier_key().metadata().key_id();
        let mut material = VerifierMaterials::new(
            bounds,
            Default::default(),
            snapshot_bound(vk(fixtures[0]).len()).unwrap() * 2,
        );
        let small = material
            .import(&vk(fixtures[0]), pin(fixtures[0]), bounds)
            .unwrap();
        let middle = material
            .import(&vk(fixtures[1]), pin(fixtures[1]), bounds)
            .unwrap();
        assert!(Arc::ptr_eq(
            &small,
            &material
                .import(&vk(fixtures[0]), pin(fixtures[0]), bounds)
                .unwrap()
        ));
        material
            .import(&vk(fixtures[2]), pin(fixtures[2]), bounds)
            .unwrap();
        assert!(!material.keys.contains_key(&pin(fixtures[0])));
        assert!(Arc::ptr_eq(
            &middle,
            &material
                .import(&vk(fixtures[1]), pin(fixtures[1]), bounds)
                .unwrap()
        ));
        assert!(!Arc::ptr_eq(
            &small,
            &material
                .import(&vk(fixtures[0]), pin(fixtures[0]), bounds)
                .unwrap()
        ));
        assert_bounded(&material);
    }
    #[test]
    fn malformed_replacements_release_charges_and_never_revive_prior_imports() {
        let (bounds, keys) = fixture();
        let verifier = keys.verifier_key();
        let vk = verifier.to_bytes(&bounds).unwrap();
        let pk = keys.prover_key().to_bytes(&bounds).unwrap();
        let pin = verifier.metadata().key_id();
        let fingerprint = keys.prover_key().material_fingerprint();
        let budget = snapshot_bound(vk.len()).unwrap() * 2 + snapshot_bound(pk.len()).unwrap();
        let mut material = VerifierMaterials::new(bounds, Default::default(), budget);
        let v = material.import(&vk, pin, bounds).unwrap();
        let p = material
            .import_prover(&pk, fingerprint, verifier, bounds)
            .unwrap();
        let mut malformed = pk.clone();
        malformed.push(0);
        assert!(
            material
                .import_prover(&malformed, fingerprint, verifier, bounds)
                .is_err()
        );
        assert_eq!(material.retained_bytes, snapshot_bound(vk.len()).unwrap());
        assert!(Arc::ptr_eq(&v, &material.import(&vk, pin, bounds).unwrap()));
        assert!(!Arc::ptr_eq(
            &p,
            &material
                .import_prover(&pk, fingerprint, verifier, bounds)
                .unwrap()
        ));
        malformed = vk.clone();
        malformed.push(0);
        assert!(material.import(&malformed, pin, bounds).is_err());
        assert_eq!(material.retained_bytes, 0);
        assert!(!Arc::ptr_eq(
            &v,
            &material.import(&vk, pin, bounds).unwrap()
        ));
        assert_bounded(&material);
    }
    #[test]
    fn setup_replacement_invalidates_a_prover_without_a_retained_standalone_vk() {
        let (bounds, keys) = fixture();
        let verifier = keys.verifier_key();
        let pk = keys.prover_key().to_bytes(&bounds).unwrap();
        let vk = verifier.to_bytes(&bounds).unwrap();
        let pin = verifier.metadata().key_id();
        let fingerprint = keys.prover_key().material_fingerprint();
        let mut material = VerifierMaterials::new(
            bounds,
            Default::default(),
            snapshot_bound(pk.len()).unwrap() + snapshot_bound(vk.len()).unwrap(),
        );
        for replacement in [Some(&vk[..]), Some(&b"malformed"[..]), None] {
            let p = material
                .import_prover(&pk, fingerprint, verifier, bounds)
                .unwrap();
            material.observe_replacement(&pin, replacement);
            let fresh = material
                .import_prover(&pk, fingerprint, verifier, bounds)
                .unwrap();
            assert_eq!(Arc::ptr_eq(&p, &fresh), replacement == Some(&vk[..]));
            assert_bounded(&material);
        }
    }
}
