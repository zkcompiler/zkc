//! Per-bind admission and authenticated immutable import reuse. No global cache.
mod native;
use super::inputs::{Result, read_regular};
pub(crate) use native::{check_native_data, check_retained_data};
use sha2::{Digest, Sha256};
use std::{borrow::Cow, collections::BTreeMap, sync::Arc};
use zkc_kernels::arkworks::bls12_381::ProverKey;
use zkc_kernels::arkworks::bls12_381::VerifierKey;
use zkc_native::{NativeBackend, Policy, Value};
use zkc_runtime::vm::{Limits, PhysicalType, Type, Value as RuntimeValue};

/// Per-bind ceilings for retained input bytes, value/operand count and
/// cumulative loading work. Requests above the Host's installed loading ceilings refuse.
/// Work charges each input node, wire scan or native measurement, and retained
/// estimates, including cache hits.
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

/// A capability declaration; issuance policy and domain remain with the host.
#[derive(Clone, Copy)]
pub(crate) struct ResourceInput {
    pub kind: Type,
    pub field: zkc_runtime::vm::Identity,
    pub budget: u64,
}
/// A planned entry operand. Hosts obtain these from Admission before loading.
pub(crate) enum Operand {
    Data(usize),
    Resource(ResourceInput),
}
/// Pure entry constraints see decoded data and holes for unissued capabilities.
pub(crate) fn entry_values<'a>(
    operands: &[Operand],
    loaded: &'a [Value],
) -> Vec<Option<&'a Value>> {
    operands
        .iter()
        .map(|operand| match operand {
            Operand::Data(index) => Some(&loaded[*index]),
            Operand::Resource(_) => None,
        })
        .collect()
}

pub(crate) enum KeySource<'a> {
    Path(&'a str),
    File(&'a super::input_file::InputFile),
}
pub(crate) enum Input<'a> {
    Native {
        ty: PhysicalType,
        value: &'a Value,
        estimate: usize,
        selected: Option<Arc<VerifierKey>>,
    },
    NativeWire {
        ty: PhysicalType,
        bytes: Cow<'a, [u8]>,
        estimate: usize,
        selected: Option<Arc<VerifierKey>>,
    },
    Variant {
        ty: PhysicalType,
        alternative: usize,
        payload: Vec<Input<'a>>,
        estimate: usize,
    },
    Key {
        source: KeySource<'a>,
        fingerprint: [u8; 32],
        verifier: Arc<VerifierKey>,
    },
    Ready(Value),
    Retained {
        ty: PhysicalType,
        value: &'a Value,
        selected: Option<Arc<VerifierKey>>,
    },
}
impl<'a> Input<'a> {
    /// Borrow immutable application data until loading has reserved its full
    /// charge. Foreign capabilities and setup keys require separate host paths.
    pub fn native_value(
        ty: PhysicalType,
        value: &'a Value,
        selected: Option<Arc<VerifierKey>>,
        estimate: Option<usize>,
    ) -> Result<Self> {
        if value.physical_type() != ty {
            return Err("native-input-type".into());
        }
        if matches!(ty.kind(), Type::ProverKey | Type::VerifierKey)
            || !ty.is_duplicable()
            || !zkc_native::has_native_wire(&ty)
        {
            return Err("native-input-private".into());
        }
        Ok(Self::Native {
            ty,
            value,
            estimate: estimate.unwrap_or_else(|| value.retained_bytes()),
            selected,
        })
    }
    fn ty(&self) -> Type {
        match self {
            Self::NativeWire { ty, .. } | Self::Native { ty, .. } | Self::Variant { ty, .. } => {
                ty.kind()
            }
            Self::Key { .. } => Type::ProverKey,
            Self::Ready(value) => value.ty(),
            Self::Retained { ty, .. } => ty.kind(),
        }
    }
    fn estimate(&self) -> Result<usize> {
        match self {
            Self::Key { verifier, .. } => {
                Value::key_retained_bytes(Type::ProverKey, verifier).map_err(|e| e.to_string())
            }
            Self::Ready(value) => Ok(value.retained_bytes()),
            Self::Retained { value, .. } => Ok(value.retained_bytes()),
            Self::Native { estimate, .. }
            | Self::NativeWire { estimate, .. }
            | Self::Variant { estimate, .. } => Ok(*estimate),
        }
    }
}

fn check_native(
    backend: &NativeBackend,
    value: &Value,
    selected: Option<&VerifierKey>,
) -> Result<()> {
    backend
        .validate_native_input(value)
        .map_err(|e| e.to_string())?;
    if let Some(key) = selected {
        super::setups::check_input(value, key)?;
    }
    Ok(())
}

fn add(total: &mut usize, amount: usize, limit: usize, error: &str) -> Result<()> {
    *total = total
        .checked_add(amount)
        .filter(|n| *n <= limit)
        .ok_or(error)?;
    Ok(())
}

pub(crate) struct Admission<'a> {
    limits: LoadLimits,
    inputs: Vec<(Input<'a>, usize)>,
    pool_bytes: usize,
    private_values: usize,
    entry_bytes: usize,
    operands: usize,
    work: usize,
    ledger: Option<zkc_runtime::vm::ExecutionLedger>,
    wire_retained: Vec<zkc_runtime::vm::LiveReservation>,
    retained_inputs: bool,
}
impl<'a> Admission<'a> {
    pub fn new(limits: LoadLimits) -> Result<Self> {
        let hard = LoadLimits::default();
        if limits.bytes > hard.bytes || limits.values > hard.values || limits.work > hard.work {
            return Err("artifact-input-limits".into());
        }
        Ok(Self {
            limits,
            inputs: Vec::new(),
            pool_bytes: 0,
            private_values: 0,
            entry_bytes: 0,
            operands: 0,
            work: 0,
            ledger: None,
            wire_retained: Vec::new(),
            retained_inputs: false,
        })
    }
    pub fn with_retained_inputs(mut self, enabled: bool) -> Self {
        self.retained_inputs = enabled;
        self
    }
    pub fn with_shared_ledger(mut self, ledger: Option<zkc_runtime::vm::ExecutionLedger>) -> Self {
        self.ledger = ledger;
        self
    }
    pub fn work(&mut self, amount: usize) -> Result<()> {
        let mut work = self.work;
        add(
            &mut work,
            amount,
            self.limits.work,
            "artifact-input-work-limit",
        )?;
        if let Some(ledger) = &self.ledger {
            ledger
                .charge(
                    zkc_runtime::vm::WorkBudget {
                        instructions: 0,
                        iterations: 0,
                        logical_bytes: amount as u64,
                    },
                    0,
                )
                .map_err(|e| e.to_string())?;
        }
        self.work = work;
        Ok(())
    }
    /// Charge the scan before traversing framing, then reserve its retention.
    pub fn native_wire(
        &mut self,
        backend: &NativeBackend,
        ty: PhysicalType,
        bytes: impl Into<Cow<'a, [u8]>>,
        selected: Option<Arc<VerifierKey>>,
    ) -> Result<usize> {
        self.work(1)?;
        let (input, _) = self.plan_wire(backend, ty, bytes.into(), None, selected)?;
        self.add(input)
    }
    pub(super) fn file_wire(
        &mut self,
        file: &super::input_file::InputFile,
        sha256: &[u8; 32],
        limit: usize,
    ) -> Result<Vec<u8>> {
        let remaining = self.limits.work - self.work;
        let bytes = if let Some(ledger) = &self.ledger {
            let buffer = file
                .read_shared(limit.min(remaining), ledger)
                .map_err(|e| {
                    if e == "entry-input-reference-byte-limit" && remaining < limit {
                        "artifact-input-work-limit".into()
                    } else {
                        e
                    }
                })?;
            self.wire_retained.extend(buffer.retained);
            buffer.bytes
        } else {
            file.read(limit.min(remaining)).map_err(|e| match e {
                super::io::ReadError::Limit if remaining < limit => "artifact-input-work-limit",
                super::io::ReadError::Limit => "entry-input-reference-byte-limit",
                _ => "entry-input-reference",
            })?
        };
        if <[u8; 32]>::from(Sha256::digest(&bytes)) != *sha256 {
            return Err("entry-input-reference-digest".into());
        }
        Ok(bytes)
    }
    pub fn add(&mut self, input: Input<'a>) -> Result<usize> {
        let estimate = input.estimate()?;
        if self.inputs.len() + self.private_values >= self.limits.values {
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
    /// Reserve a not-yet-issued private operand under the same cumulative
    /// loading and entry budgets as decoded data.
    fn private_operand(&mut self, bytes: usize) -> Result<()> {
        if self.inputs.len() + self.private_values >= self.limits.values {
            return Err("artifact-input-count-limit".into());
        }
        add(
            &mut self.pool_bytes,
            bytes,
            self.limits.bytes,
            "artifact-input-bytes-limit",
        )?;
        add(
            &mut self.entry_bytes,
            bytes,
            self.limits.bytes,
            "artifact-input-bytes-limit",
        )?;
        add(
            &mut self.operands,
            1,
            self.limits.values,
            "artifact-input-count-limit",
        )?;
        self.private_values += 1;
        Ok(())
    }
    fn operand(&mut self, index: usize, ty: Type) -> Result<()> {
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
    /// Every entry occurrence is charged, including repeated immutable data.
    pub fn data(&mut self, index: usize, ty: Type) -> Result<Operand> {
        self.operand(index, ty)?;
        Ok(Operand::Data(index))
    }
    pub fn resource(&mut self, input: ResourceInput) -> Result<Operand> {
        self.private_operand(Value::capability_retained_bytes())?;
        Ok(Operand::Resource(input))
    }
    /// Reserve the decoded pool before any decoder allocates. Loading also
    /// charges conservative byte work separately from numerical execution.
    pub fn load_shared(
        self,
        backend: &NativeBackend,
        policy: &Policy,
        ledger: &zkc_runtime::vm::ExecutionLedger,
        metadata: usize,
    ) -> Result<(Vec<Value>, zkc_runtime::vm::LiveReservation)> {
        let bytes = self
            .pool_bytes
            .checked_add(metadata)
            .ok_or("entry-host-loading-limit")?;
        let work = if self.ledger.is_some() {
            metadata
        } else {
            self.work
                .checked_add(bytes)
                .ok_or("entry-host-loading-limit")?
        };
        ledger
            .charge(
                zkc_runtime::vm::WorkBudget {
                    instructions: 0,
                    iterations: 0,
                    logical_bytes: work as u64,
                },
                bytes,
            )
            .map_err(|e| e.to_string())?;
        let live = ledger.reserve_live(bytes).map_err(|e| e.to_string())?;
        let values = self.load(backend, policy)?;
        Ok((values, live))
    }
    pub fn load(mut self, backend: &NativeBackend, policy: &Policy) -> Result<Vec<Value>> {
        // Work is a cumulative conservative proxy: bytes read/scanned plus
        // retained charges for every value, including cache hits. Reserve all
        // charges before material reads; charge actual file lengths as read.
        self.work(self.pool_bytes)?;
        // Refuse already constructed data before decoding earlier wires or
        // opening key files. The complete invocation charge is reserved first.
        for (input, _) in &self.inputs {
            native::check(backend, input)?;
        }
        let mut values = Vec::new();
        let mut actual_bytes = 0;
        let mut key_cache = BTreeMap::new();
        for (input, estimate) in std::mem::take(&mut self.inputs) {
            let value = match input {
                Input::Ready(value) => value,
                Input::Retained { value, .. } => value.clone(),
                input @ (Input::Native { .. }
                | Input::NativeWire { .. }
                | Input::Variant { .. }) => native::load(backend, input)?,
                Input::Key {
                    source,
                    fingerprint,
                    verifier,
                } => {
                    let remaining = self.limits.work - self.work;
                    let limit = policy.max_wire_bytes.min(remaining);
                    // Freeze precisely this named file into bounded owned bytes.
                    // Never reopen between SHA and import. Even a cache hit must
                    // satisfy this path's current captured bytes and declared pin.
                    let buffer = if let Some(ledger) = &self.ledger {
                        Some(
                            (match &source {
                                KeySource::Path(path) => {
                                    let mut file =
                                        super::io::open_regular(path).map_err(|_| "artifact-io")?;
                                    super::io::read_shared(&mut file, limit, Some(ledger))
                                }
                                KeySource::File(file) => file.read_shared(limit, ledger),
                            })
                            .map_err(|e| {
                                if e == "entry-input-reference-byte-limit" {
                                    if remaining < policy.max_wire_bytes {
                                        "artifact-input-work-limit".into()
                                    } else {
                                        "artifact-byte-limit".into()
                                    }
                                } else {
                                    e
                                }
                            })?,
                        )
                    } else {
                        None
                    };
                    let unshared;
                    let bytes = if let Some(buffer) = &buffer {
                        &buffer.bytes
                    } else {
                        unshared = match source {
                            KeySource::Path(path) => read_regular(path, limit),
                            KeySource::File(file) => file.read(limit).map_err(|e| match e {
                                super::io::ReadError::Limit => "artifact-byte-limit".into(),
                                _ => "entry-input-reference".into(),
                            }),
                        }
                        .map_err(|e| {
                            if e == "artifact-byte-limit" && remaining < policy.max_wire_bytes {
                                "artifact-input-work-limit".into()
                            } else {
                                e
                            }
                        })?;
                        &unshared
                    };
                    self.work(bytes.len())?;
                    let digest: [u8; 32] = Sha256::digest(bytes).into();
                    // The material pin is NOT the wire SHA. Include both, and
                    // full VK bytes, so only a previously authenticated import
                    // can hit. A different file with a claimed pin must import.
                    let identity = (
                        digest,
                        fingerprint,
                        verifier
                            .to_bytes(&policy.ark_bounds())
                            .map_err(|e| e.to_string())?,
                    );
                    if let Some(key) = key_cache.get(&identity) {
                        Value::ProverKey(Arc::clone(key))
                    } else {
                        #[cfg(test)]
                        IMPORT_COUNT.with(|n| n.set(n.get() + 1));
                        let key = Arc::new(
                            ProverKey::from_bytes(
                                bytes,
                                fingerprint,
                                &verifier,
                                &policy.ark_bounds(),
                            )
                            .map_err(|e| e.to_string())?,
                        );
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
    pub(crate) static DECODE_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    pub(crate) static IMPORT_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use zkc_kernels::arkworks::bls12_381::Keys;
    use zkc_native::{Domain, EntryPolicy};

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
        let mut plan = Admission::new(LoadLimits::default()).unwrap();
        for verifier in [first.verifier_key(), other.verifier_key()] {
            plan.add(Input::Key {
                source: KeySource::Path(path.to_str().unwrap()),
                fingerprint: first.prover_key().material_fingerprint(),
                verifier: Arc::new(verifier.clone()),
            })
            .unwrap();
        }
        let backend = NativeBackend::new(
            policy,
            EntryPolicy::new(Domain::new("P", "s", "main", None), Some(1)),
            zkc_native::SetupRegistry::new(
                vec![first.verifier_key().clone()],
                &zkc_native::Policy::default(),
            )
            .unwrap(),
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
        assert!(matches!(Admission::new(LoadLimits {
            bytes: usize::MAX,
            values: usize::MAX,
            work: usize::MAX,
        }), Err(code) if code == "artifact-input-limits"));
    }
}
