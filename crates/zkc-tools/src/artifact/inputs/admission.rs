//! Per-bind admission and authenticated immutable import reuse. No global cache.
use super::super::{
    io::{Result, read, text, unhex},
    material::{KeyIdentity, MaterialCache},
};
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, sync::Arc};
use zkc_arkworks::{Metadata, ProverKey, VerifierKey};
use zkc_backends::{NativeBackend, Policy, Value};
use zkc_runtime::interactive::{Limits, LogicalType, PhysicalType, Type, Value as RuntimeValue};

/// Per-bind ceilings for retained input bytes, value/operand count and
/// cumulative loading work. Each is clamped to the existing runtime hard limit.
/// Work charges wire bytes and retained estimates, including cache hits.
#[derive(Clone, Copy, Debug)]
pub struct LoadLimits {
    pub bytes: usize,
    pub values: usize,
    pub work: usize,
}
impl Default for LoadLimits {
    fn default() -> Self {
        Self {
            bytes: Limits::VALUE_BYTES.min(Limits::TOTAL_VALUE_BYTES),
            values: Limits::LIVE_VALUES,
            work: Limits::TOTAL_VALUE_BYTES,
        }
    }
}

pub(super) enum Input<'a> {
    Wire {
        ty: LogicalType,
        setup: Option<Metadata>,
        hex: &'a Json,
    },
    Key {
        path: &'a str,
        fingerprint: [u8; 32],
        verifier: Arc<VerifierKey>,
    },
    Ready(Value),
}
impl<'a> Input<'a> {
    pub fn wire(ty: LogicalType, setup: Option<Metadata>, hex: &'a Json) -> Result<Self> {
        // Scan without allocating the binary payload; canonical hex is required.
        let s = text(hex)?;
        if !s.len().is_multiple_of(2)
            || !s
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err("artifact-hex".into());
        }
        Ok(Self::Wire { ty, setup, hex })
    }
    fn ty(&self) -> Type {
        match self {
            Self::Wire { ty, .. } => ty.kind(),
            Self::Key { .. } => Type::ProverKey,
            Self::Ready(value) => value.ty(),
        }
    }
    fn estimate(&self, policy: &Policy) -> Result<usize> {
        match self {
            Self::Wire { ty, hex, .. } => Value::typed_wire_retained_bytes_bound(
                PhysicalType::default_for(ty.clone()),
                text(hex)?.len() / 2,
                policy,
            )
            .map_err(|e| e.to_string()),
            Self::Key { verifier, .. } => {
                Value::key_retained_bytes(Type::ProverKey, verifier).map_err(|e| e.to_string())
            }
            Self::Ready(value) => Ok(value.retained_bytes()),
        }
    }
}

fn add(total: &mut usize, amount: usize, limit: usize, error: &str) -> Result<()> {
    *total = total
        .checked_add(amount)
        .filter(|n| *n <= limit)
        .ok_or(error)?;
    Ok(())
}

pub(super) struct Admission<'a> {
    limits: LoadLimits,
    inputs: Vec<(Input<'a>, usize)>,
    pool_bytes: usize,
    entry_bytes: usize,
    operands: usize,
    work: usize,
}
impl<'a> Admission<'a> {
    pub fn new(limits: LoadLimits) -> Self {
        let hard = LoadLimits::default();
        let limits = LoadLimits {
            bytes: limits.bytes.min(hard.bytes),
            values: limits.values.min(hard.values),
            work: limits.work.min(hard.work),
        };
        Self {
            limits,
            inputs: Vec::new(),
            pool_bytes: 0,
            entry_bytes: 0,
            operands: 0,
            work: 0,
        }
    }
    pub fn work(&mut self, amount: usize) -> Result<()> {
        add(
            &mut self.work,
            amount,
            self.limits.work,
            "artifact-input-work-limit",
        )
    }
    pub fn add(&mut self, input: Input<'a>, policy: &Policy) -> Result<usize> {
        let estimate = input.estimate(policy)?;
        if self.inputs.len() >= self.limits.values {
            return Err("artifact-input-count-limit".into());
        }
        add(
            &mut self.pool_bytes,
            estimate,
            self.limits.bytes,
            "artifact-input-bytes-limit",
        )?;
        self.inputs.push((input, estimate));
        Ok(self.inputs.len() - 1)
    }
    pub fn same_wire(&self, index: usize, input: &Input<'_>) -> bool {
        matches!((&self.inputs[index].0, input),
            (Input::Wire { ty: a, setup: s, hex: x }, Input::Wire { ty: b, setup: t, hex: y }) if a == b && s == t && x == y)
    }
    pub fn operand(&mut self, index: usize, ty: Type) -> Result<()> {
        let (input, estimate) = &self.inputs[index];
        if input.ty() != ty {
            return Err("artifact-input-type".into());
        }
        add(
            &mut self.operands,
            1,
            self.limits.values,
            "artifact-input-count-limit",
        )?;
        // Every occurrence counts, even when it reuses an immutable backing.
        add(
            &mut self.entry_bytes,
            *estimate,
            self.limits.bytes,
            "artifact-input-bytes-limit",
        )
    }
    #[cfg(test)]
    pub fn load(self, backend: &NativeBackend, policy: &Policy) -> Result<Vec<Value>> {
        self.load_cached(backend, policy, &mut MaterialCache::disabled())
    }
    pub fn load_cached(
        mut self,
        backend: &NativeBackend,
        policy: &Policy,
        cache: &mut MaterialCache,
    ) -> Result<Vec<Value>> {
        // Work is a cumulative conservative proxy: bytes read/scanned plus
        // retained charges for every value, including cache hits. Reserve all
        // charges before material reads; charge actual file lengths as read.
        self.work(self.pool_bytes)?;
        let wire_bytes = self.inputs.iter().try_fold(0usize, |sum, (input, _)| {
            let len = match input {
                Input::Wire { hex, .. } => text(hex)?.len() / 2,
                _ => 0,
            };
            sum.checked_add(len)
                .ok_or_else(|| "artifact-input-work-limit".to_string())
        })?;
        self.work(wire_bytes)?;
        let mut values = Vec::new();
        let mut actual_bytes = 0;
        let mut wire_cache = BTreeMap::new();
        let mut key_cache = BTreeMap::new();
        for (input, estimate) in std::mem::take(&mut self.inputs) {
            let value = match input {
                Input::Ready(value) => value,
                Input::Wire { ty, setup, hex } => {
                    let encoded = text(hex)?;
                    let identity = (
                        ty.clone(),
                        setup.map(|s| (s.arity(), s.setup_id(), s.key_id())),
                        encoded,
                    );
                    if let Some(value) = wire_cache.get(&identity) {
                        Value::clone(value)
                    } else {
                        let bytes = unhex(hex)?;
                        let physical = PhysicalType::default_for(ty);
                        let value = match setup {
                            Some(setup) => backend.decode_for_setup(physical, setup, &bytes),
                            None => backend.decode_typed_value(physical, &bytes),
                        }
                        .map_err(|e| e.to_string())?;
                        if backend.encode_value(&value).map_err(|e| e.to_string())? != bytes {
                            return Err("artifact-canonical-value".into());
                        }
                        wire_cache.insert(identity, value.clone());
                        #[cfg(test)]
                        DECODE_COUNT.with(|n| n.set(n.get() + 1));
                        value
                    }
                }
                Input::Key {
                    path,
                    fingerprint,
                    verifier,
                } => {
                    let remaining = self.limits.work - self.work;
                    let limit = policy.max_wire_bytes.min(remaining);
                    // Freeze precisely this named file into bounded owned bytes.
                    // Never reopen between SHA and import. Even a cache hit must
                    // satisfy this path's current captured bytes and declared pin.
                    let bytes = read(path, limit).map_err(|e| {
                        if e == "artifact-byte-limit" && remaining < policy.max_wire_bytes {
                            "artifact-input-work-limit".into()
                        } else {
                            e
                        }
                    })?;
                    self.work(bytes.len())?;
                    let digest: [u8; 32] = Sha256::digest(&bytes).into();
                    // The material pin is NOT the wire SHA. Include both, and
                    // full VK bytes, so only a previously authenticated import
                    // can hit. A different file with a claimed pin must import.
                    let identity = KeyIdentity::Prover {
                        wire_sha256: digest,
                        fingerprint,
                        verifier: verifier
                            .to_bytes(&policy.ark_bounds())
                            .map_err(|e| e.to_string())?,
                    };
                    if let Some(key) = key_cache.get(&identity) {
                        Value::ProverKey(Arc::clone(key))
                    } else if let Some(key) = cache.prover(&identity) {
                        key_cache.insert(identity, key.clone());
                        Value::ProverKey(key)
                    } else {
                        #[cfg(test)]
                        IMPORT_COUNT.with(|n| n.set(n.get() + 1));
                        let key = Arc::new(
                            ProverKey::from_bytes(
                                &bytes,
                                fingerprint,
                                &verifier,
                                &policy.ark_bounds(),
                            )
                            .map_err(|e| e.to_string())?,
                        );
                        cache.retain_prover(identity.clone(), key.clone());
                        key_cache.insert(identity, key.clone());
                        Value::ProverKey(key)
                    }
                }
            };
            let actual = value.retained_bytes();
            if actual > estimate {
                return Err("artifact-input-size-estimate".into());
            }
            add(
                &mut actual_bytes,
                actual,
                self.limits.bytes,
                "artifact-input-bytes-limit",
            )?;
            values.push(value);
        }
        Ok(values)
    }
}

#[cfg(test)]
thread_local! {
    pub(in crate::artifact) static IMPORT_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    pub(in crate::artifact) static DECODE_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use zkc_arkworks::Keys;
    use zkc_backends::{Domain, EntryPolicy, PublicInputs};

    #[test]
    fn cache_requires_full_vk_identity_and_checked_sums_never_wrap() {
        let policy = Policy::default();
        let first = Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
        let other = Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("key.pk");
        std::fs::write(
            &path,
            first.prover_key().to_bytes(&policy.ark_bounds()).unwrap(),
        )
        .unwrap();
        let mut plan = Admission::new(LoadLimits::default());
        for verifier in [first.verifier_key(), other.verifier_key()] {
            plan.add(
                Input::Key {
                    path: path.to_str().unwrap(),
                    fingerprint: first.prover_key().material_fingerprint(),
                    verifier: Arc::new(verifier.clone()),
                },
                &policy,
            )
            .unwrap();
        }
        let backend = NativeBackend::new(
            policy,
            EntryPolicy::new(
                Domain::new("P", "s", "main", None),
                Some(1),
                PublicInputs::LocalOnly,
            ),
            Some(first.verifier_key().clone()),
        )
        .unwrap();
        IMPORT_COUNT.set(0);
        assert_eq!(plan.load(&backend, &policy).unwrap_err(), "key-mismatch");
        assert_eq!(IMPORT_COUNT.get(), 2);
        let mut total = usize::MAX;
        assert_eq!(
            add(&mut total, 1, usize::MAX, "overflow").unwrap_err(),
            "overflow"
        );
        let mut plan = Admission::new(LoadLimits {
            bytes: usize::MAX,
            values: usize::MAX,
            work: usize::MAX,
        });
        assert_eq!(
            plan.work(usize::MAX).unwrap_err(),
            "artifact-input-work-limit"
        );
    }
}
