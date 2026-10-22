//! Setup checks shared by native invocation hosts. Authority maps stay with each host.
use super::inputs::Result;
use zkc_native::Value;
use zkc_runtime::vm::{LogicalType, Type};
pub(crate) fn needs_input_setup(ty: &LogicalType) -> bool {
    ty.kind() == Type::ProverKey || zkc_native::requires_setup(ty.clone())
}
// Apply a port's configured setup recursively. Copyable aggregates may contain
// PCS leaves; neither aggregate construction nor unused entry data bypasses it.
pub(crate) fn check_input(
    value: &Value,
    key: &zkc_kernels::arkworks::bls12_381::VerifierKey,
) -> Result<()> {
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

/// Authenticated imports within one invocation. Pins, full canonical bytes and
/// fixed bounds participate in reuse; per-operand accounting stays with Admission.
/// Canonical byte snapshots are owned: moving or mutating a source request cannot
/// change an authenticated cache entry. This context ends with one invocation.
pub(crate) struct VerifierKeys {
    bounds: zkc_kernels::arkworks::bls12_381::Bounds,
    ledger: Option<zkc_runtime::vm::ExecutionLedger>,
    retained: Vec<zkc_runtime::vm::LiveReservation>,
    keys: std::collections::BTreeMap<[u8; 32], Vec<ImportedVerifierKey>>,
}
struct ImportedVerifierKey {
    bytes: Vec<u8>,
    key: std::sync::Arc<zkc_kernels::arkworks::bls12_381::VerifierKey>,
}
impl VerifierKeys {
    pub fn new(bounds: zkc_kernels::arkworks::bls12_381::Bounds) -> Self {
        Self {
            bounds,
            ledger: None,
            retained: Vec::new(),
            keys: Default::default(),
        }
    }
    pub(crate) fn set_ledger(&mut self, ledger: Option<zkc_runtime::vm::ExecutionLedger>) {
        self.ledger = ledger;
    }
    pub(crate) fn check_bounds(
        &self,
        bounds: zkc_kernels::arkworks::bls12_381::Bounds,
    ) -> Result<()> {
        if self.bounds != bounds {
            return Err("native-setup-capacity".into());
        }
        Ok(())
    }
    pub fn import(
        &mut self,
        bytes: &[u8],
        pin: [u8; 32],
        canonical_error: &str,
    ) -> Result<std::sync::Arc<zkc_kernels::arkworks::bls12_381::VerifierKey>> {
        if let Some(imported) = self
            .keys
            .get(&pin)
            .and_then(|keys| keys.iter().find(|imported| imported.bytes == bytes))
        {
            return Ok(imported.key.clone());
        }
        // Fixed compressed points expand by less than this factor, including
        // both decoded key material and the retained canonical snapshot.
        let bound = bytes
            .len()
            .checked_mul(16)
            .and_then(|n| n.checked_add(4096))
            .ok_or("native-setup-capacity")?;
        let guard = zkc_runtime::host::wire::reserve_allocation(self.ledger.as_ref(), bound)?;
        self.retained.extend(guard);
        let key =
            zkc_kernels::arkworks::bls12_381::VerifierKey::from_bytes(bytes, pin, &self.bounds)
                .map_err(|e| e.to_string())?;
        if key.to_bytes(&self.bounds).map_err(|e| e.to_string())? != bytes {
            return Err(canonical_error.into());
        }
        let key = std::sync::Arc::new(key);
        self.keys.entry(pin).or_default().push(ImportedVerifierKey {
            bytes: bytes.to_vec(),
            key: key.clone(),
        });
        Ok(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn verifier_reuse_requires_identical_bytes_and_authority() {
        let bounds = zkc_native::Policy::default().ark_bounds();
        let keys =
            zkc_kernels::arkworks::bls12_381::Keys::setup_for_development(1, &bounds).unwrap();
        let key = keys.verifier_key();
        let bytes = key.to_bytes(&bounds).unwrap();
        let same_bytes = bytes.clone();
        let mut changed = bytes.clone();
        changed.push(0);
        let pin = key.metadata().key_id();
        let mut imports = VerifierKeys::new(bounds);
        let first = imports.import(&bytes, pin, "canonical").unwrap();
        let again = imports.import(&same_bytes, pin, "canonical").unwrap();
        assert!(std::sync::Arc::ptr_eq(&first, &again));
        let mut wrong_pin = pin;
        wrong_pin[0] ^= 1;
        assert!(imports.import(&bytes, wrong_pin, "canonical").is_err());
        assert!(imports.import(&changed, pin, "canonical").is_err());
        let mut source = same_bytes.clone();
        let owned = imports.import(&source, pin, "canonical").unwrap();
        source.fill(0);
        assert!(imports.import(&source, pin, "canonical").is_err());
        assert!(std::sync::Arc::ptr_eq(
            &owned,
            &imports.import(&same_bytes, pin, "canonical").unwrap()
        ));
        assert!(
            imports
                .check_bounds(zkc_kernels::arkworks::bls12_381::Bounds::new(0, 0, 0, 0))
                .is_err()
        );
    }
}
