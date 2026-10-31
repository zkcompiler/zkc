//! Setup checks shared by native invocation hosts. Authority maps stay with each host.
use crate::io::bytes::Result;
use std::{collections::BTreeMap, sync::Arc};
use zkc_kernels::arkworks::bls12_381::{Bounds, VerifierKey};
use zkc_runtime::vm::{ExecutionLedger, LiveReservation, LogicalType, Type};
pub(crate) fn needs_input_setup(ty: &LogicalType) -> bool {
    ty.kind() == Type::ProverKey || zkc_cpu::requires_setup(ty.clone())
}
pub(crate) use zkc_cpu::material::check_input;

/// Authenticated imports within one invocation. Pins, full canonical bytes and
/// fixed bounds participate in reuse; per-operand accounting stays with Admission.
/// Canonical byte snapshots are owned: moving or mutating a source request cannot
/// change an authenticated cache entry. This context ends with one invocation.
pub(crate) struct VerifierKeys {
    bounds: Bounds,
    ledger: Option<ExecutionLedger>,
    retained: Vec<LiveReservation>,
    keys: BTreeMap<[u8; 32], Vec<ImportedVerifierKey>>,
    material: Arc<std::sync::Mutex<zkc_cpu::material::VerifierMaterials>>,
}
struct ImportedVerifierKey {
    bytes: Vec<u8>,
    key: Arc<VerifierKey>,
    charged: bool,
}
impl VerifierKeys {
    pub fn new(bounds: Bounds, installation: zkc_cpu::CpuInstallation) -> Self {
        Self {
            bounds,
            ledger: None,
            retained: Vec::new(),
            keys: Default::default(),
            material: Arc::new(std::sync::Mutex::new(
                // This cache lives for one call. Invocation imports below own
                // their snapshots already; avoid a duplicate retention layer.
                zkc_cpu::material::VerifierMaterials::new(bounds, installation, 0),
            )),
        }
    }
    pub(crate) fn set_ledger(&mut self, ledger: Option<ExecutionLedger>) {
        self.ledger = ledger;
    }
    pub(crate) fn check_bounds(&self, bounds: Bounds) -> Result<()> {
        if self.bounds != bounds {
            return Err("native-setup-capacity".into());
        }
        Ok(())
    }
    pub(crate) fn retained_bytes(&self) -> usize {
        self.keys.values().flatten().fold(0usize, |total, key| {
            total.saturating_add(key.bytes.len().saturating_mul(16).saturating_add(4096))
        })
    }
    pub(crate) fn material(&self) -> Arc<std::sync::Mutex<zkc_cpu::material::VerifierMaterials>> {
        self.material.clone()
    }
    pub(crate) fn with_material(
        mut self,
        material: Arc<std::sync::Mutex<zkc_cpu::material::VerifierMaterials>>,
    ) -> Self {
        self.material = material;
        self
    }
    pub fn import(&mut self, bytes: &[u8], pin: [u8; 32]) -> Result<Arc<VerifierKey>> {
        let bound = bytes
            .len()
            .checked_mul(16)
            .and_then(|n| n.checked_add(4096))
            .ok_or("native-setup-capacity")?;
        if let Some(imported) = self
            .keys
            .get_mut(&pin)
            .and_then(|keys| keys.iter_mut().find(|imported| imported.bytes == bytes))
        {
            // Output preflight may have imported before the invocation ledger was
            // installed. Charge its retained snapshot on the first ledger use.
            if !imported.charged && self.ledger.is_some() {
                self.retained
                    .extend(zkc_runtime::host::wire::reserve_allocation(
                        self.ledger.as_ref(),
                        bound,
                    )?);
                imported.charged = true;
            }
            return Ok(imported.key.clone());
        }
        let guard = zkc_runtime::host::wire::reserve_allocation(self.ledger.as_ref(), bound)?;
        self.retained.extend(guard);
        let key = self
            .material
            .lock()
            .map_err(|_| "native-setup-material")?
            .import(bytes, pin, self.bounds)?;
        self.keys.entry(pin).or_default().push(ImportedVerifierKey {
            bytes: bytes.to_vec(),
            key: key.clone(),
            charged: self.ledger.is_some(),
        });
        Ok(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zkc_kernels::arkworks::bls12_381::Keys;
    #[test]
    fn verifier_reuse_requires_identical_bytes_and_authority() {
        let bounds = zkc_cpu::Policy::default().ark_bounds();
        let keys = Keys::setup_with_rng(1, &mut ark_std::rand::thread_rng(), &bounds).unwrap();
        let key = keys.verifier_key();
        let bytes = key.to_bytes(&bounds).unwrap();
        let same_bytes = bytes.clone();
        let mut changed = bytes.clone();
        changed.push(0);
        let pin = key.metadata().key_id();
        let mut imports = VerifierKeys::new(bounds, Default::default());
        let first = imports.import(&bytes, pin).unwrap();
        let again = imports.import(&same_bytes, pin).unwrap();
        assert!(Arc::ptr_eq(&first, &again));
        let mut wrong_pin = pin;
        wrong_pin[0] ^= 1;
        assert!(imports.import(&bytes, wrong_pin).is_err());
        assert!(imports.import(&changed, pin).is_err());
        let mut source = same_bytes.clone();
        let owned = imports.import(&source, pin).unwrap();
        source.fill(0);
        assert!(imports.import(&source, pin).is_err());
        assert!(Arc::ptr_eq(
            &owned,
            &imports.import(&same_bytes, pin).unwrap()
        ));
        assert!(imports.check_bounds(Bounds::new(0, 0, 0, 0)).is_err());
    }
}

#[cfg(test)]
mod reusable_tests {
    use super::*;
    use zkc_kernels::arkworks::bls12_381::Keys;
    #[test]
    fn immutable_vk_and_pk_reuse_invalidates_replacements_and_rechecks_support() {
        let bounds = zkc_cpu::Policy::default().ark_bounds();
        let keys = Keys::setup_with_rng(1, &mut ark_std::rand::thread_rng(), &bounds).unwrap();
        let verifier = keys.verifier_key();
        let bytes = verifier.to_bytes(&bounds).unwrap();
        let pk = keys.prover_key().to_bytes(&bounds).unwrap();
        let pin = verifier.metadata().key_id();
        let fingerprint = keys.prover_key().material_fingerprint();
        let mut material = zkc_cpu::material::VerifierMaterials::new(
            bounds,
            Default::default(),
            crate::execution::Capacity::default().values.live_bytes,
        );
        let first = material.import(&bytes, pin, bounds).unwrap();
        assert!(Arc::ptr_eq(
            &first,
            &material.import(&bytes.clone(), pin, bounds).unwrap()
        ));
        let prover = material
            .import_prover(&pk, fingerprint, verifier, bounds)
            .unwrap();
        assert!(Arc::ptr_eq(
            &prover,
            &material
                .import_prover(&pk.clone(), fingerprint, verifier, bounds)
                .unwrap()
        ));
        let mut malformed = pk.clone();
        malformed.push(0);
        assert!(
            material
                .import_prover(&malformed, fingerprint, verifier, bounds)
                .is_err()
        );
        assert!(!Arc::ptr_eq(
            &prover,
            &material
                .import_prover(&pk, fingerprint, verifier, bounds)
                .unwrap()
        ));
        let mut malformed = bytes.clone();
        malformed.push(0);
        assert!(material.import(&malformed, pin, bounds).is_err());
        assert!(!Arc::ptr_eq(
            &first,
            &material.import(&bytes, pin, bounds).unwrap()
        ));
        let fresh = material.import(&bytes, pin, bounds).unwrap();
        material.observe_replacement(&pin, Some(&malformed));
        assert!(!Arc::ptr_eq(
            &fresh,
            &material.import(&bytes, pin, bounds).unwrap()
        ));
        let mut wrong = pin;
        wrong[0] ^= 1;
        assert!(material.import(&bytes, wrong, bounds).is_err());
        assert!(
            material
                .import(&bytes, pin, Bounds::new(0, 0, 0, 0))
                .is_err()
        );
        let installation = zkc_cpu::CpuInstallation::builder()
            .include(zkc_cpu::providers::Plonky3)
            .finish()
            .unwrap();
        let mut restricted = zkc_cpu::material::VerifierMaterials::new(bounds, installation, 0);
        assert_eq!(
            restricted.import(&bytes, pin, bounds).unwrap_err(),
            "cpu-installation-setup"
        );
        assert_eq!(
            restricted
                .import_prover(&pk, fingerprint, verifier, bounds)
                .unwrap_err(),
            "cpu-installation-setup"
        );
    }
    #[test]
    fn cache_hits_and_preflight_imports_keep_per_invocation_reservation_custody() {
        let bounds = zkc_cpu::Policy::default().ark_bounds();
        let keys = Keys::setup_with_rng(1, &mut ark_std::rand::thread_rng(), &bounds).unwrap();
        let bytes = keys.verifier_key().to_bytes(&bounds).unwrap();
        let pin = keys.verifier_key().metadata().key_id();
        let material = Arc::new(std::sync::Mutex::new(
            zkc_cpu::material::VerifierMaterials::new(
                bounds,
                Default::default(),
                crate::execution::Capacity::default().values.live_bytes,
            ),
        ));
        let mut previous = None;
        let mut previous_charge = None;
        for _ in 0..2 {
            let ledger = ExecutionLedger::new(Default::default(), Default::default());
            let mut imports =
                VerifierKeys::new(bounds, Default::default()).with_material(material.clone());
            // Output preflight has no ledger yet; Host preflight installs it.
            let key = imports.import(&bytes, pin).unwrap();
            imports.set_ledger(Some(ledger.clone()));
            let same = imports.import(&bytes, pin).unwrap();
            assert!(Arc::ptr_eq(&key, &same));
            let usage = ledger.snapshot();
            assert!(usage.live_reserved_bytes > 0);
            if let Some(previous) = previous.as_ref() {
                assert!(Arc::ptr_eq(previous, &key));
            }
            if let Some(charge) = previous_charge {
                assert_eq!(charge, usage.total_value_bytes);
            }
            previous = Some(key);
            previous_charge = Some(usage.total_value_bytes);
            drop(imports);
            assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
            assert_eq!(ledger.snapshot().total_value_bytes, usage.total_value_bytes);
        }
    }

    #[test]
    fn persistent_prover_hits_bypass_and_invalidation_keep_current_call_charges() {
        use crate::host::admission::{Admission, Input, KeySource};
        use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Value};
        let policy = Policy::default();
        let bounds = policy.ark_bounds();
        let keys = Keys::setup_with_rng(1, &mut ark_std::rand::thread_rng(), &bounds).unwrap();
        let fingerprint = keys.prover_key().material_fingerprint();
        let verifier = Arc::new(keys.verifier_key().clone());
        let source = crate::execution::InputSource::from_bytes(Arc::new(
            keys.prover_key().to_bytes(&bounds).unwrap(),
        ));
        let backend = CpuBackend::new(
            policy,
            EntryPolicy::new(Domain::new("P", "session", "main", None), None),
            Default::default(),
        )
        .unwrap();
        let mut charges = Vec::new();
        for budget in [0, crate::execution::Capacity::default().values.live_bytes] {
            let material = Arc::new(std::sync::Mutex::new(
                zkc_cpu::material::VerifierMaterials::new(bounds, Default::default(), budget),
            ));
            let mut previous = None;
            for _ in 0..2 {
                let ledger = ExecutionLedger::new(Default::default(), Default::default());
                let mut admission = Admission::new(Default::default())
                    .unwrap()
                    .with_shared_ledger(Some(ledger.clone()))
                    .with_material(material.clone());
                admission
                    .add(Input::Key {
                        source: KeySource::File(&source),
                        fingerprint,
                        verifier: verifier.clone(),
                    })
                    .unwrap();
                let (values, held) = admission
                    .load_shared(&backend, &policy, &ledger, 0)
                    .unwrap();
                let Value::ProverKey(key) = &values[0] else {
                    panic!("prover key")
                };
                let usage = ledger.snapshot();
                assert!(usage.live_reserved_bytes > 0);
                charges.push(usage.total_value_bytes);
                if let Some(previous) = previous.as_ref() {
                    assert_eq!(Arc::ptr_eq(previous, key), budget != 0);
                }
                // Adapter replacement cannot release the current invocation's
                // resources or mutate its already checked immutable key.
                material.lock().unwrap().invalidate_provers();
                assert_eq!(key.material_fingerprint(), fingerprint);
                assert_eq!(
                    ledger.snapshot().live_reserved_bytes,
                    usage.live_reserved_bytes
                );
                // Refill to exercise a persistent hit in the next invocation.
                let replacement = material
                    .lock()
                    .unwrap()
                    .import_prover(
                        &keys.prover_key().to_bytes(&bounds).unwrap(),
                        fingerprint,
                        &verifier,
                        bounds,
                    )
                    .unwrap();
                assert!(!Arc::ptr_eq(key, &replacement));
                previous = Some(replacement);
                drop(values);
                drop(held);
                assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
                assert_eq!(ledger.snapshot().total_value_bytes, usage.total_value_bytes);
            }
        }
        assert!(charges.iter().all(|charge| *charge == charges[0]));
    }

    #[test]
    fn byte_source_prover_limits_normalize_with_and_without_shared_ledger() {
        use crate::host::admission::{Admission, Input, KeySource, LoadLimits};
        use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, Value};
        use zkc_runtime::vm::Value as _;
        let policy = Policy::default();
        let bounds = policy.ark_bounds();
        let keys = Keys::setup_with_rng(1, &mut ark_std::rand::thread_rng(), &bounds).unwrap();
        let bytes = keys.prover_key().to_bytes(&bounds).unwrap();
        let decoded = Value::ProverKey(Arc::new(keys.prover_key().clone())).retained_bytes();
        let source = crate::execution::InputSource::from_bytes(Arc::new(bytes.clone()));
        let verifier = Arc::new(keys.verifier_key().clone());
        for shared in [false, true] {
            for work_limited in [false, true] {
                let mut policy = policy;
                let mut limits = LoadLimits::default();
                let expected = if work_limited {
                    limits.work = decoded + bytes.len() - 1;
                    "artifact-input-work-limit"
                } else {
                    policy.max_wire_bytes = bytes.len() - 1;
                    "artifact-byte-limit"
                };
                let ledger =
                    shared.then(|| ExecutionLedger::new(Default::default(), Default::default()));
                let mut admission = Admission::new(limits).unwrap().with_shared_ledger(ledger);
                admission
                    .add(Input::Key {
                        source: KeySource::File(&source),
                        fingerprint: keys.prover_key().material_fingerprint(),
                        verifier: verifier.clone(),
                    })
                    .unwrap();
                let backend = CpuBackend::new(
                    policy,
                    EntryPolicy::new(Domain::new("P", "session", "main", None), None),
                    Default::default(),
                )
                .unwrap();
                assert_eq!(admission.load(&backend, &policy).unwrap_err(), expected);
            }
        }
    }
}
