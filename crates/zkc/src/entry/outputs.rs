//! Stream logical results into one bounded buffer before atomic publication.
use super::inputs::MAX_REQUEST_BYTES;
use super::{NamedValues, SetupAuthority, Value};
type Result<T> = std::result::Result<T, String>;
use crate::{
    entry::RoleValues,
    host::{capacity::Capacity, request::InputValue},
};
use serde::{
    Serialize, Serializer,
    ser::{Error, SerializeMap, SerializeSeq},
};
use std::io::Write;
use zkc_cpu::CpuBackend;
use zkc_runtime::vm::Value as _;

pub(crate) struct EncodedBuffer {
    pub bytes: Vec<u8>,
    pub _retained: Vec<zkc_runtime::vm::LiveReservation>,
}
struct Buffer {
    bytes: Vec<u8>,
    exhausted: bool,
    ledger: Option<zkc_runtime::vm::ExecutionLedger>,
    retained: Vec<zkc_runtime::vm::LiveReservation>,
}
impl Write for Buffer {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        let wanted = self.bytes.len().checked_add(bytes.len());
        let Some(wanted) = wanted.filter(|n| *n <= MAX_REQUEST_BYTES) else {
            self.exhausted = true;
            return Err(std::io::Error::other("entry output limit"));
        };
        if wanted > self.bytes.capacity() {
            let next = wanted
                .max(self.bytes.capacity().saturating_mul(2))
                .clamp(512, MAX_REQUEST_BYTES);
            let guard = zkc_runtime::host::wire::reserve_allocation(
                self.ledger.as_ref(),
                next - self.bytes.capacity(),
            );
            let Ok(guard) = guard else {
                self.exhausted = true;
                return Err(std::io::Error::other("entry output limit"));
            };
            self.retained.extend(guard);
            if self
                .bytes
                .try_reserve_exact(next - self.bytes.len())
                .is_err()
            {
                self.exhausted = true;
                return Err(std::io::Error::other("entry output limit"));
            }
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
fn encode(value: impl Serialize) -> Result<Vec<u8>> {
    encode_reserved(value, None).map(|encoded| encoded.bytes)
}
fn encode_reserved(
    value: impl Serialize,
    ledger: Option<zkc_runtime::vm::ExecutionLedger>,
) -> Result<EncodedBuffer> {
    let mut out = Buffer {
        bytes: Vec::new(),
        exhausted: false,
        ledger,
        retained: Vec::new(),
    };
    serde_json::to_writer(&mut out, &value).map_err(|_| {
        if out.exhausted {
            "entry-output-limit"
        } else {
            "entry-output-encoding"
        }
    })?;
    Ok(EncodedBuffer {
        bytes: out.bytes,
        _retained: out.retained,
    })
}
// Native wire frames depend on value shape and capacity, not the session domain.
// Outputs have already been admitted under their role's setup policy; encoding
// here adds no setup authorization and issues no resources.
fn backend(
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
    cpu: crate::execution::CpuExecution,
    installation: zkc_cpu::CpuInstallation,
) -> Result<CpuBackend> {
    capacity.validate()?;
    CpuBackend::new_with_installation(
        capacity.backend(),
        zkc_cpu::EntryPolicy::new(
            zkc_cpu::Domain::new("host", "entry_results", "results", None),
            None,
        ),
        setups,
        cpu,
        installation,
    )
    .map_err(|e| e.to_string())
}
/// Authenticate the same invocation setup material for result serialization.
/// This registry grants no authority to execute or accept a proof.
pub fn output_setups(
    material: &std::collections::BTreeMap<String, Vec<u8>>,
    authority: &SetupAuthority,
    capacity: Capacity,
) -> Result<zkc_cpu::SetupRegistry> {
    output_setups_with_installation(material, authority, capacity, &Default::default())
}
/// Import output setup material under explicit CPU support.
pub fn output_setups_with_installation(
    material: &std::collections::BTreeMap<String, Vec<u8>>,
    authority: &SetupAuthority,
    capacity: Capacity,
    installation: &zkc_cpu::CpuInstallation,
) -> Result<zkc_cpu::SetupRegistry> {
    let mut imports = crate::host::setups::VerifierKeys::new(
        capacity.backend().ark_bounds(),
        installation.clone(),
    );
    output_setups_with(material, authority, capacity, &mut imports, installation)
}
pub(crate) fn output_setups_with(
    material: &std::collections::BTreeMap<String, Vec<u8>>,
    authority: &SetupAuthority,
    capacity: Capacity,
    imports: &mut crate::host::setups::VerifierKeys,
    installation: &zkc_cpu::CpuInstallation,
) -> Result<zkc_cpu::SetupRegistry> {
    capacity.validate()?;
    imports.check_bounds(capacity.backend().ark_bounds())?;
    if material.len() != authority.keys.len() {
        return Err("entry-setup-material".into());
    }
    let policy = capacity.backend();
    let mut keys = Vec::new();
    for (name, bytes) in material {
        capacity.check_wire(bytes.len())?;
        let pin = *authority.keys.get(name).ok_or("entry-setup-authority")?;
        if !installation.supports_setup() {
            return Err("cpu-installation-setup".into());
        }
        let key = imports.import(bytes, pin)?;
        if !keys
            .iter()
            .any(|old: &zkc_kernels::arkworks::bls12_381::VerifierKey| {
                old.metadata() == key.metadata()
            })
        {
            keys.push((*key).clone());
        }
    }
    zkc_cpu::SetupRegistry::new(keys, &policy).map_err(|e| e.to_string())
}
/// Encode explicitly requested role results under the admitted capacity and a
/// 16 MiB whole-file limit. Private capabilities retain their codec refusal.
pub fn run_outputs(
    values: &RoleValues,
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
) -> Result<Vec<u8>> {
    run_outputs_with_cpu(
        values,
        capacity,
        setups,
        crate::execution::CpuExecution::serial().map_err(|e| e.to_string())?,
    )
}
/// Encode role results using the caller's existing CPU context.
pub fn run_outputs_with_cpu(
    values: &RoleValues,
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
    cpu: crate::execution::CpuExecution,
) -> Result<Vec<u8>> {
    run_outputs_with_installation(values, capacity, setups, cpu, Default::default())
}
/// Encode using the selected installation for every nested value.
pub fn run_outputs_with_installation(
    values: &RoleValues,
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
    cpu: crate::execution::CpuExecution,
    installation: zkc_cpu::CpuInstallation,
) -> Result<Vec<u8>> {
    #[derive(Serialize)]
    struct Document<T> {
        format: &'static str,
        roles: T,
    }
    let backend = backend(capacity, setups, cpu.clone(), installation)?;
    struct Roles<'a> {
        values: &'a RoleValues,
        backend: &'a CpuBackend,
    }
    impl Serialize for Roles<'_> {
        fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
            let mut map = serializer.serialize_map(Some(self.values.len()))?;
            for (name, values) in self.values {
                map.serialize_entry(
                    name,
                    &Named {
                        values,
                        backend: self.backend,
                        depth: 2,
                    },
                )?;
            }
            map.end()
        }
    }
    cpu.enter(|| {
        encode(Document {
            format: "zkc.entry-outputs/0",
            roles: Roles {
                values,
                backend: &backend,
            },
        })
    })
}
/// Encode one proof participant's named results without changing runtime state.
pub fn proof_outputs(
    values: &NamedValues,
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
) -> Result<Vec<u8>> {
    proof_outputs_with_cpu(
        values,
        capacity,
        setups,
        crate::execution::CpuExecution::serial().map_err(|e| e.to_string())?,
    )
}
/// Encode proof results using the caller's existing CPU context.
pub fn proof_outputs_with_cpu(
    values: &NamedValues,
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
    cpu: crate::execution::CpuExecution,
) -> Result<Vec<u8>> {
    proof_outputs_with_installation(values, capacity, setups, cpu, Default::default())
}
/// Encode using the selected installation for every nested value.
pub fn proof_outputs_with_installation(
    values: &NamedValues,
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
    cpu: crate::execution::CpuExecution,
    installation: zkc_cpu::CpuInstallation,
) -> Result<Vec<u8>> {
    proof_outputs_reserved(values, capacity, setups, cpu, installation, None)
        .map(|encoded| encoded.bytes)
}
pub(crate) fn proof_outputs_reserved(
    values: &NamedValues,
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
    cpu: crate::execution::CpuExecution,
    installation: zkc_cpu::CpuInstallation,
    ledger: Option<zkc_runtime::vm::ExecutionLedger>,
) -> Result<EncodedBuffer> {
    #[derive(Serialize)]
    struct Document<T> {
        format: &'static str,
        values: T,
    }
    let backend = backend(capacity, setups, cpu.clone(), installation)?;
    cpu.enter(|| {
        encode_reserved(
            Document {
                format: "zkc.entry-outputs/0",
                values: Named {
                    values,
                    backend: &backend,
                    depth: 1,
                },
            },
            ledger,
        )
    })
}
/// Encode only the explicit successful source return, using native wire codecs.
pub fn function_output(
    value: &Value,
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
) -> Result<Vec<u8>> {
    function_output_with_cpu(
        value,
        capacity,
        setups,
        crate::execution::CpuExecution::serial().map_err(|e| e.to_string())?,
    )
}
/// Encode a function result using the caller's existing CPU context.
pub fn function_output_with_cpu(
    value: &Value,
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
    cpu: crate::execution::CpuExecution,
) -> Result<Vec<u8>> {
    function_output_with_installation(value, capacity, setups, cpu, Default::default())
}
/// Encode using the selected installation for every nested value.
pub fn function_output_with_installation(
    value: &Value,
    capacity: Capacity,
    setups: zkc_cpu::SetupRegistry,
    cpu: crate::execution::CpuExecution,
    installation: zkc_cpu::CpuInstallation,
) -> Result<Vec<u8>> {
    #[derive(Serialize)]
    struct Document<T> {
        format: &'static str,
        value: T,
    }
    let backend = backend(capacity, setups, cpu.clone(), installation)?;
    cpu.enter(|| {
        encode(Document {
            format: "zkc.entry-outputs/0",
            value: Item {
                value,
                backend: &backend,
                depth: 1,
            },
        })
    })
}
struct Named<'a> {
    values: &'a NamedValues,
    backend: &'a CpuBackend,
    depth: usize,
}
impl Serialize for Named<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        if self.depth > crate::host::document::MAX_DEPTH {
            return Err(S::Error::custom("entry output depth"));
        }
        let mut map = serializer.serialize_map(Some(self.values.len()))?;
        for (name, value) in self.values {
            map.serialize_entry(
                name,
                &Item {
                    value,
                    backend: self.backend,
                    depth: self.depth + 1,
                },
            )?;
        }
        map.end()
    }
}
struct Item<'a> {
    value: &'a Value,
    backend: &'a CpuBackend,
    depth: usize,
}
impl Serialize for Item<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        if self.depth > crate::host::document::MAX_DEPTH {
            return Err(S::Error::custom("entry output depth"));
        }
        match self.value {
            Value::Unit => serializer.serialize_unit(),
            Value::Tuple(values) | Value::Array(values) => {
                let mut seq = serializer.serialize_seq(Some(values.len()))?;
                for value in values {
                    seq.serialize_element(&Item {
                        value,
                        backend: self.backend,
                        depth: self.depth + 1,
                    })?;
                }
                seq.end()
            }
            Value::Record(values) => Named {
                values,
                backend: self.backend,
                depth: self.depth,
            }
            .serialize(serializer),
            Value::Variant {
                alternative,
                fields,
            } => {
                let mut map = serializer.serialize_map(Some(2))?;
                map.serialize_entry("case", alternative)?;
                map.serialize_entry(
                    "fields",
                    &Named {
                        values: fields,
                        backend: self.backend,
                        depth: self.depth + 1,
                    },
                )?;
                map.end()
            }
            Value::Associated(value) => Item {
                value,
                backend: self.backend,
                depth: self.depth + 1,
            }
            .serialize(serializer),
            Value::Leaf(InputValue::Native(v)) => {
                if !self
                    .backend
                    .installation()
                    .supports_wire(&v.physical_type())
                {
                    return Err(S::Error::custom("entry output is not serializable"));
                }
                self.backend
                    .encode_readable_value(v)
                    .map_err(S::Error::custom)?
                    .serialize(serializer)
            }
            _ => Err(S::Error::custom("entry output value")),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::host::inputs::hex;
    use zkc_cpu::Value as Native;
    use zkc_runtime::vm::Identity;
    #[test]
    fn function_returns_use_one_value_envelope_and_existing_codecs() {
        let value = Value::Record(
            [
                ("ok".into(), false.into()),
                ("count".into(), u64::MAX.into()),
                ("unit".into(), Value::Unit),
            ]
            .into(),
        );
        let encoded = function_output(&value, Capacity::default(), Default::default()).unwrap();
        let document: serde_json::Value = serde_json::from_slice(&encoded).unwrap();
        assert_eq!(
            document,
            serde_json::json!({"format":"zkc.entry-outputs/0",
            "value":{"ok":false,"count":u64::MAX.to_string(),"unit":null}})
        );
        let small = Capacity {
            wire_bytes: 0,
            ..Default::default()
        };
        assert_eq!(
            function_output(&value, small, Default::default()).unwrap_err(),
            "entry-output-encoding"
        );
    }
    #[test]
    fn pcs_outputs_require_explicit_authenticated_setup_material() {
        let capacity = Capacity::default();
        let policy = capacity.backend();
        let keys = zkc_kernels::arkworks::bls12_381::Keys::setup_with_rng(
            1,
            &mut ark_std::rand::thread_rng(),
            &policy.ark_bounds(),
        )
        .unwrap();
        let table = zkc_kernels::arkworks::bls12_381::Table::from_logical_vec(
            vec![zkc_cpu::Scalar::from(1); 2],
            &policy.ark_bounds(),
        )
        .unwrap();
        let commitment = keys.prover_key().commit(&table).unwrap();
        let value = Native::Commitment(std::sync::Arc::new(commitment.commitment().clone()));
        let values = [("commitment".into(), value.clone().into())].into();
        assert_eq!(
            proof_outputs(&values, capacity, Default::default()).unwrap_err(),
            "entry-output-encoding"
        );
        let material = [(
            "setup".into(),
            keys.verifier_key().to_bytes(&policy.ark_bounds()).unwrap(),
        )]
        .into();
        let authority = super::SetupAuthority {
            keys: [("setup".into(), keys.verifier_key().metadata().key_id())].into(),
        };
        let registry = output_setups(&material, &authority, capacity).unwrap();
        let expected = backend(
            capacity,
            registry.clone(),
            crate::execution::CpuExecution::serial().unwrap(),
            Default::default(),
        )
        .unwrap()
        .encode_native_value(&value)
        .unwrap();
        let document: serde_json::Value =
            serde_json::from_slice(&proof_outputs(&values, capacity, registry).unwrap()).unwrap();
        assert_eq!(document["values"]["commitment"]["wire"], hex(&expected));
        let mut wrong = authority.clone();
        wrong.keys.get_mut("setup").unwrap()[0] ^= 1;
        assert!(output_setups(&material, &wrong, capacity).is_err());
        assert!(output_setups(&material, &Default::default(), capacity).is_err());
    }
    #[test]
    fn exact_file_limit_and_no_partial_result() {
        let exact = "a".repeat(MAX_REQUEST_BYTES - 2);
        assert_eq!(encode(&exact).unwrap().len(), MAX_REQUEST_BYTES);
        assert_eq!(encode(exact + "a").unwrap_err(), "entry-output-limit");
    }
    #[test]
    fn private_capabilities_refuse_without_consuming_them() {
        let capacity = Capacity::default();
        let mut native = backend(
            capacity,
            Default::default(),
            crate::execution::CpuExecution::serial().unwrap(),
            Default::default(),
        )
        .unwrap();
        let value = native
            .issue_rng_for(
                Identity::Bls12381Fr,
                zkc_cpu::Domain::new("host", "entry_results", "results", None),
                1,
            )
            .unwrap();
        let Native::Rng(token) = &value else { panic!() };
        let token = token.clone();
        assert_eq!(
            proof_outputs(
                &[("private".into(), value.into())].into(),
                capacity,
                Default::default()
            )
            .unwrap_err(),
            "entry-output-encoding"
        );
        assert_eq!(native.retire(&token).unwrap().draw_count, 0);
        let values = [(
            "scalar".into(),
            Native::Field(zkc_cpu::Scalar::from(7u64)).into(),
        )]
        .into();
        let small = Capacity {
            wire_bytes: 1,
            ..capacity
        };
        assert_eq!(
            proof_outputs(&values, small, Default::default()).unwrap_err(),
            "entry-output-encoding"
        );
    }
    #[test]
    fn maximum_source_variant_depth_fits_an_input_document() {
        let mut value = Value::from(true);
        for _ in 0..32 {
            value = Value::Variant {
                alternative: "More".into(),
                fields: [("0".into(), value)].into(),
            };
        }
        let outputs = proof_outputs(
            &[("nested".into(), value)].into(),
            Capacity::default(),
            Default::default(),
        )
        .unwrap();
        let values: serde_json::Value = serde_json::from_slice(&outputs).unwrap();
        let request = values["values"].to_string();
        assert!(crate::host::document::read(request.as_bytes(), MAX_REQUEST_BYTES).is_ok());
    }
    #[test]
    fn structured_values_roundtrip_and_depth_is_bounded() {
        let values: NamedValues = [(
            "record".into(),
            Value::Record(
                [
                    ("bool".into(), true.into()),
                    ("index".into(), u64::MAX.into()),
                    ("empty".into(), ().into()),
                ]
                .into(),
            ),
        )]
        .into();
        let bytes = proof_outputs(&values, Capacity::default(), Default::default()).unwrap();
        let document: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(document["values"]["record"]["index"], u64::MAX.to_string());
        let mut nested = Value::Unit;
        for _ in 0..crate::host::document::MAX_DEPTH {
            nested = Value::Associated(Box::new(nested));
        }
        assert_eq!(
            proof_outputs(
                &[("deep".into(), nested)].into(),
                Capacity::default(),
                Default::default()
            )
            .unwrap_err(),
            "entry-output-encoding"
        );
    }
}

/// Result encoding retains the imported setup material and its original limits.
/// It grants no execution authority.
pub struct FunctionResultEncoder {
    pub(crate) installation: zkc_cpu::CpuInstallation,
    pub(crate) setups: zkc_cpu::SetupRegistry,
    pub(crate) capacity: crate::execution::Capacity,
}
impl FunctionResultEncoder {
    pub fn encode(&self, value: &crate::entry::Value) -> Result<Vec<u8>> {
        self.encode_with_cpu(
            value,
            crate::execution::CpuExecution::serial().map_err(|e| e.to_string())?,
        )
    }
    /// Share the execution owner's context through result serialization.
    pub fn encode_with_cpu(
        &self,
        value: &crate::entry::Value,
        cpu: crate::execution::CpuExecution,
    ) -> Result<Vec<u8>> {
        crate::entry::outputs::function_output_with_installation(
            value,
            self.capacity,
            self.setups.clone(),
            cpu,
            self.installation.clone(),
        )
    }
}

#[cfg(test)]
mod allocation_tests {
    use super::*;
    use zkc_runtime::vm::{ExecutionLedger, ValueBudget};
    #[test]
    fn encoding_reserves_before_growth_and_withholds_partial_buffers() {
        let ledger = ExecutionLedger::new(
            ValueBudget {
                live_bytes: 4096,
                total_bytes: 4096,
            },
            Default::default(),
        );
        let encoded = encode_reserved("x".repeat(700), Some(ledger.clone())).unwrap();
        let usage = ledger.snapshot();
        assert!(usage.live_reserved_bytes >= encoded.bytes.len());
        drop(encoded);
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
        assert_eq!(ledger.snapshot().total_value_bytes, usage.total_value_bytes);
        let ledger = ExecutionLedger::new(
            ValueBudget {
                live_bytes: 512,
                total_bytes: 512,
            },
            Default::default(),
        );
        assert_eq!(
            encode_reserved("x".repeat(700), Some(ledger.clone()))
                .err()
                .unwrap(),
            "entry-output-limit"
        );
        assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
    }
}
