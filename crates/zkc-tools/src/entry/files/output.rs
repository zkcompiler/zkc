//! Stream logical results into one bounded buffer before atomic publication.
use super::{MAX_REQUEST_BYTES, NamedValues, Result, Value};
use crate::{
    entry::RoleValues,
    host::{capacity::NativeCapacity, inputs::hex, request::InputValue},
};
use serde::{
    Serialize, Serializer,
    ser::{Error, SerializeMap, SerializeSeq},
};
use std::io::Write;
use zkc_backends::{NativeBackend, Value as Native};
use zkc_runtime::interactive::Value as _;

struct Buffer {
    bytes: Vec<u8>,
    exhausted: bool,
}
impl Write for Buffer {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        if bytes.len() > MAX_REQUEST_BYTES.saturating_sub(self.bytes.len())
            || self.bytes.try_reserve(bytes.len()).is_err()
        {
            self.exhausted = true;
            return Err(std::io::Error::other("entry output limit"));
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
fn encode(value: impl Serialize) -> Result<Vec<u8>> {
    let mut out = Buffer {
        bytes: Vec::new(),
        exhausted: false,
    };
    serde_json::to_writer(&mut out, &value).map_err(|_| {
        if out.exhausted {
            "entry-output-limit"
        } else {
            "entry-output-encoding"
        }
    })?;
    Ok(out.bytes)
}
// Native wire frames depend on value shape and capacity, not the session domain.
// Outputs have already been admitted under their role's setup policy; encoding
// here adds no setup authorization and issues no resources.
fn backend(capacity: NativeCapacity, setups: zkc_backends::SetupRegistry) -> Result<NativeBackend> {
    capacity.check()?;
    NativeBackend::new(
        capacity.backend(),
        zkc_backends::EntryPolicy::new(
            zkc_backends::Domain::new("host", "entry_results", "results", None),
            None,
        ),
        setups,
    )
    .map_err(|e| e.to_string())
}
/// Authenticate the same invocation setup material for result serialization.
/// This registry grants no authority to execute or accept a proof.
pub fn output_setups(
    material: &std::collections::BTreeMap<String, Vec<u8>>,
    authority: &super::SetupAuthority,
    capacity: NativeCapacity,
) -> Result<zkc_backends::SetupRegistry> {
    capacity.check()?;
    if material.len() != authority.keys.len() {
        return Err("entry-setup-material".into());
    }
    let policy = capacity.backend();
    let mut imports = crate::host::setups::VerifierKeys::new(policy.ark_bounds());
    let mut keys = Vec::new();
    for (name, bytes) in material {
        capacity.check_wire(bytes.len())?;
        let pin = *authority.keys.get(name).ok_or("entry-setup-authority")?;
        let key = imports.import(bytes, pin, "entry-output-setup")?;
        if !keys
            .iter()
            .any(|old: &zkc_arkworks::VerifierKey| old.metadata() == key.metadata())
        {
            keys.push((*key).clone());
        }
    }
    zkc_backends::SetupRegistry::new(keys, &policy).map_err(|e| e.to_string())
}
/// Encode explicitly requested role results under the admitted capacity and a
/// 16 MiB whole-file limit. Private capabilities retain their codec refusal.
pub fn run_outputs(
    values: &RoleValues,
    capacity: NativeCapacity,
    setups: zkc_backends::SetupRegistry,
) -> Result<Vec<u8>> {
    #[derive(Serialize)]
    struct Document<T> {
        format: &'static str,
        roles: T,
    }
    let backend = backend(capacity, setups)?;
    struct Roles<'a> {
        values: &'a RoleValues,
        backend: &'a NativeBackend,
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
    encode(Document {
        format: "zkc.entry-outputs/1",
        roles: Roles {
            values,
            backend: &backend,
        },
    })
}
/// Encode one proof participant's named results without changing runtime state.
pub fn proof_outputs(
    values: &NamedValues,
    capacity: NativeCapacity,
    setups: zkc_backends::SetupRegistry,
) -> Result<Vec<u8>> {
    #[derive(Serialize)]
    struct Document<T> {
        format: &'static str,
        values: T,
    }
    let backend = backend(capacity, setups)?;
    encode(Document {
        format: "zkc.entry-outputs/1",
        values: Named {
            values,
            backend: &backend,
            depth: 1,
        },
    })
}
struct Named<'a> {
    values: &'a NamedValues,
    backend: &'a NativeBackend,
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
    backend: &'a NativeBackend,
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
                if !zkc_backends::has_native_wire(&v.physical_type()) {
                    return Err(S::Error::custom("entry output is not serializable"));
                }
                match &**v {
                    Native::Bool(v) => serializer.serialize_bool(*v),
                    Native::Index(v) => serializer.serialize_u64(*v),
                    _ => serializer.serialize_str(&hex(&self
                        .backend
                        .encode_native_value(v)
                        .map_err(S::Error::custom)?)),
                }
            }
            _ => Err(S::Error::custom("entry output value")),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use zkc_runtime::interactive::Identity;
    #[test]
    fn pcs_outputs_require_explicit_authenticated_setup_material() {
        let capacity = NativeCapacity::default();
        let policy = capacity.backend();
        let keys = zkc_arkworks::Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
        let table = zkc_arkworks::Table::from_logical_vec(
            vec![zkc_backends::Scalar::from(1); 2],
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
        let authority = super::super::SetupAuthority {
            keys: [("setup".into(), keys.verifier_key().metadata().key_id())].into(),
        };
        let registry = output_setups(&material, &authority, capacity).unwrap();
        let expected = backend(capacity, registry.clone())
            .unwrap()
            .encode_native_value(&value)
            .unwrap();
        let document: serde_json::Value =
            serde_json::from_slice(&proof_outputs(&values, capacity, registry).unwrap()).unwrap();
        assert_eq!(document["values"]["commitment"], hex(&expected));
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
        let capacity = NativeCapacity::default();
        let mut native = backend(capacity, Default::default()).unwrap();
        let value = native
            .issue_rng_for(
                Identity::Bls12381Fr,
                zkc_backends::Domain::new("host", "entry_results", "results", None),
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
            Native::Field(zkc_backends::Scalar::from(7u64)).into(),
        )]
        .into();
        let small = NativeCapacity {
            wire_bytes: 1,
            ..capacity
        };
        assert_eq!(
            proof_outputs(&values, small, Default::default()).unwrap_err(),
            "entry-output-encoding"
        );
    }
    #[test]
    fn maximum_source_variant_depth_fits_the_request_envelope() {
        let mut value = Value::from(true);
        for _ in 0..32 {
            value = Value::Variant {
                alternative: "More".into(),
                fields: [("0".into(), value)].into(),
            };
        }
        let outputs = proof_outputs(
            &[("nested".into(), value)].into(),
            NativeCapacity::default(),
            Default::default(),
        )
        .unwrap();
        let values: serde_json::Value = serde_json::from_slice(&outputs).unwrap();
        let request = serde_json::json!({"format":"zkc.entry-run/1", "session":"nested", "roles":{"P":{"inputs":values["values"]}}}).to_string();
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
        let bytes = proof_outputs(&values, NativeCapacity::default(), Default::default()).unwrap();
        let document: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(document["values"]["record"]["index"], u64::MAX);
        let mut nested = Value::Unit;
        for _ in 0..crate::host::document::MAX_DEPTH {
            nested = Value::Associated(Box::new(nested));
        }
        assert_eq!(
            proof_outputs(
                &[("deep".into(), nested)].into(),
                NativeCapacity::default(),
                Default::default()
            )
            .unwrap_err(),
            "entry-output-encoding"
        );
    }
}
