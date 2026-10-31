//! Application-owned immutable inputs. Invocation authority stays in Entry/Host.
use crate::Result;
use serde::{Deserialize, Serialize};
use serde_json::Value as Json;
use zkc::{
    entry::{NamedValues, Value, inputs::InputGroup},
    execution::{Capacity, CpuExecution, InputValue, PreparedData},
};
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, SetupRegistry};
use zkc_runtime::vm::{LogicalType, PhysicalType, Value as RuntimeValue};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Ingress {
    Json,
    Wire,
    Native,
    Prepared,
}

pub struct Owner {
    values: NamedValues,
    pub retained_payload_bytes: usize,
}
impl Owner {
    pub fn new(
        values: NamedValues,
        group: &InputGroup<'_>,
        ingress: Ingress,
        capacity: Capacity,
        cpu: &CpuExecution,
    ) -> Result<Self> {
        if ingress == Ingress::Json {
            return Err("benchmark-ingress: JSON has no preowned inputs".into());
        }
        let description = group.describe();
        let ports = array(&description, "ports")?;
        let mut conversion = Conversion {
            ingress,
            capacity,
            cpu,
            retained_payload_bytes: 0,
        };
        let values = values
            .into_iter()
            .map(|(name, value)| {
                let port = ports
                    .iter()
                    .find(|p| p["name"] == name)
                    .ok_or("benchmark-ingress: missing admitted port")?;
                // Key initializers remain constructor descriptions, never data.
                let value = if !port["initializer"].is_null() {
                    value
                } else {
                    conversion.convert(value, &port["schema"])?
                };
                Ok((name, value))
            })
            .collect::<Result<_>>()?;
        Ok(Self {
            values,
            retained_payload_bytes: conversion.retained_payload_bytes,
        })
    }

    pub fn share(&self) -> Result<NamedValues> {
        share_fields(&self.values)
    }
}

fn array<'a>(schema: &'a Json, name: &str) -> Result<&'a [Json]> {
    schema
        .get(name)
        .and_then(Json::as_array)
        .map(Vec::as_slice)
        .ok_or_else(|| format!("benchmark-ingress: unsupported {name} schema").into())
}
fn field<'a>(fields: &'a [Json], name: &str) -> Result<&'a Json> {
    fields
        .iter()
        .find(|f| f["name"] == name)
        .map(|f| &f["schema"])
        .ok_or_else(|| format!("benchmark-ingress: missing admitted field {name}").into())
}
struct Conversion<'a> {
    ingress: Ingress,
    capacity: Capacity,
    cpu: &'a CpuExecution,
    retained_payload_bytes: usize,
}
impl Conversion<'_> {
    fn convert(&mut self, value: Value, schema: &Json) -> Result<Value> {
        let value = match value {
            Value::Leaf(InputValue::WireSource { file, sha256 }) => Value::Leaf(InputValue::Wire(
                file.read_verified(&sha256, self.capacity.wire_bytes)?
                    .into(),
            )),
            other => other,
        };
        let converted = match value {
            Value::Leaf(InputValue::Wire(bytes)) => {
                let types = array(schema, "native_types")?;
                if types.len() != 1 {
                    return Err(
                        "benchmark-ingress: leaf requires one admitted physical type".into(),
                    );
                }
                let spelling = types[0]
                    .as_str()
                    .ok_or("benchmark-ingress: unknown admitted leaf type")?;
                // Metadata supplies syntax; numerical input conversion independently
                // forms its native type before the selected codec admits the value.
                let logical = LogicalType::parse(spelling).map_err(|e| e.to_string())?;
                // Identical to the public named Decoder's physical codec selection.
                let ty = PhysicalType::default_for(logical).map_err(|e| e.to_string())?;
                let (value, bytes_retained) =
                    convert_wire(bytes, ty, self.ingress, self.capacity, self.cpu)?;
                self.retained_payload_bytes = self
                    .retained_payload_bytes
                    .checked_add(bytes_retained)
                    .ok_or("benchmark-ingress: retained payload overflow")?;
                Value::Leaf(value)
            }
            Value::Unit => Value::Unit,
            Value::Tuple(values) | Value::Array(values) => {
                let fields = array(schema, "fields")?;
                if fields.len() != values.len() {
                    return Err("benchmark-ingress: product shape mismatch".into());
                }
                let values = values
                    .into_iter()
                    .zip(fields)
                    .map(|(v, f)| self.convert(v, &f["schema"]))
                    .collect::<Result<_>>()?;
                match schema["kind"].as_str() {
                    Some("tuple") => Value::Tuple(values),
                    Some("array") => Value::Array(values),
                    _ => return Err("benchmark-ingress: unsupported product schema".into()),
                }
            }
            Value::Record(values) => {
                Value::Record(self.convert_fields(values, array(schema, "fields")?)?)
            }
            Value::Variant {
                alternative,
                fields,
            } => {
                let arm = array(schema, "cases")?
                    .iter()
                    .find(|a| a["name"] == alternative)
                    .ok_or("benchmark-ingress: unsupported variant alternative")?;
                Value::Variant {
                    alternative,
                    fields: self.convert_fields(fields, array(arm, "fields")?)?,
                }
            }
            Value::Associated(value) => {
                let fields = array(schema, "fields")?;
                if fields.len() != 1 {
                    return Err("benchmark-ingress: unsupported associated schema".into());
                }
                Value::Associated(Box::new(self.convert(*value, &fields[0]["schema"])?))
            }
            Value::Leaf(
                value @ (InputValue::Resource { .. }
                | InputValue::VerifierKey
                | InputValue::ProverKey(_)
                | InputValue::ProverKeyFile { .. }
                | InputValue::ProverKeyInput { .. }),
            ) => Value::Leaf(value),
            Value::Leaf(_) => {
                return Err("benchmark-ingress: unsupported non-Wire data leaf".into());
            }
        };
        Ok(converted)
    }
    fn convert_fields(&mut self, values: NamedValues, fields: &[Json]) -> Result<NamedValues> {
        if values.len() != fields.len() {
            return Err("benchmark-ingress: record shape mismatch".into());
        }
        values
            .into_iter()
            .map(|(name, value)| {
                let value = self.convert(value, field(fields, &name)?)?;
                Ok((name, value))
            })
            .collect()
    }
}
fn codec(capacity: Capacity, cpu: &CpuExecution) -> Result<CpuBackend> {
    capacity.validate()?;
    let policy = Policy {
        max_table_elements: capacity.elements,
        max_groups: capacity.groups,
        max_wire_bytes: capacity.wire_bytes,
        max_value_bytes: capacity.value_bytes,
        ..Policy::default()
    };
    CpuBackend::new_with_cpu(
        policy,
        EntryPolicy::new(Domain::new("benchmark", "ingress", "data", None), None),
        SetupRegistry::new(Vec::new(), &policy).map_err(|e| e.to_string())?,
        cpu.clone(),
    )
    .map_err(|e| e.to_string().into())
}
fn convert_wire(
    bytes: std::sync::Arc<Vec<u8>>,
    ty: PhysicalType,
    ingress: Ingress,
    capacity: Capacity,
    cpu: &CpuExecution,
) -> Result<(InputValue, usize)> {
    if ingress == Ingress::Wire {
        let retained = bytes.len();
        return Ok((InputValue::Wire(bytes), retained));
    }
    if !ty.is_duplicable()
        || !zkc_cpu::has_native_wire(&ty)
        || zkc_cpu::requires_setup(ty.logical().clone())
    {
        return Err(
            "benchmark-ingress: unsupported data conversion (private or setup-dependent type)"
                .into(),
        );
    }
    // Enter on the caller: codec validation may install parallel numerical
    // leaves, while conversion, retention and accounting keep caller custody.
    cpu.enter(|| match ingress {
        Ingress::Native => {
            let backend = codec(capacity, cpu)?;
            let value = backend
                .decode_native_value(&ty, bytes.as_slice())
                .map_err(|e| format!("benchmark-ingress: native decode: {e}"))?;
            backend
                .validate_native_input(&value)
                .map_err(|e| format!("benchmark-ingress: native validation: {e}"))?;
            if value.physical_type() != ty {
                return Err("benchmark-ingress: physical type mismatch".into());
            }
            let retained = value.retained_bytes();
            Ok((value.into(), retained))
        }
        Ingress::Prepared => {
            // Move the Decoder allocation when unique; no retained Wire duplicate.
            let data = PreparedData::from_wire_with_cpu(
                ty,
                std::sync::Arc::unwrap_or_clone(bytes),
                capacity,
                cpu.clone(),
            )
            .map_err(|e| format!("benchmark-ingress: prepared decode: {e}"))?;
            let retained = data.retained_bytes();
            Ok((data.into(), retained))
        }
        _ => Err("benchmark-ingress: unsupported conversion policy".into()),
    })
}
fn share_fields(values: &NamedValues) -> Result<NamedValues> {
    values
        .iter()
        .map(|(name, value)| Ok((name.clone(), share_value(value)?)))
        .collect()
}
fn share_value(value: &Value) -> Result<Value> {
    Ok(match value {
        Value::Leaf(value) => Value::Leaf(share_leaf(value)?),
        Value::Unit => Value::Unit,
        Value::Tuple(values) => {
            Value::Tuple(values.iter().map(share_value).collect::<Result<_>>()?)
        }
        Value::Array(values) => {
            Value::Array(values.iter().map(share_value).collect::<Result<_>>()?)
        }
        Value::Record(values) => Value::Record(share_fields(values)?),
        Value::Variant {
            alternative,
            fields,
        } => Value::Variant {
            alternative: alternative.clone(),
            fields: share_fields(fields)?,
        },
        Value::Associated(value) => Value::Associated(Box::new(share_value(value)?)),
    })
}
fn share_leaf(value: &InputValue) -> Result<InputValue> {
    Ok(match value {
        InputValue::Wire(bytes) => InputValue::Wire(bytes.clone()),
        // Value::clone shares immutable collection backing; inline values copy.
        InputValue::Native(value) => InputValue::Native(value.clone()),
        InputValue::Prepared(data) => InputValue::Prepared(data.clone()),
        InputValue::Resource { budget } => InputValue::Resource { budget: *budget },
        InputValue::VerifierKey => InputValue::VerifierKey,
        InputValue::ProverKey(material) => InputValue::ProverKey(material.clone()),
        InputValue::ProverKeyFile { path, fingerprint } => InputValue::ProverKeyFile {
            path: path.clone(),
            fingerprint: *fingerprint,
        },
        InputValue::ProverKeyInput { file, fingerprint } => InputValue::ProverKeyInput {
            file: file.clone(),
            fingerprint: *fingerprint,
        },
        // Ordinary files were materialized before ownership. Physical variants
        // are represented by their admitted source Value shape.
        _ => return Err("benchmark-ingress: unsupported input constructor".into()),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use sha2::{Digest, Sha256};
    use std::sync::Arc;
    use zkc::entry::{BoundInterface, Interface, Package, inputs::Decoder};

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn schema(kind: &str, name: &str, leaves: Json) -> Json {
        // Same checked metadata shape as zkc' interface fixtures.
        json!({"kind":kind,"identity":hex(&Sha256::digest(name.as_bytes())),"type":name,
            "custody":false,"constructible":true,"permissions":["Copy","Drop"],
            "fields":[],"alternatives":[],"leaves":leaves})
    }

    fn product(kind: &str, name: &str, fields: Vec<(&str, Json)>) -> Json {
        let mut leaves = Vec::new();
        let fields: Vec<_> = fields
            .into_iter()
            .map(|(name, child)| {
                let offset = leaves.len();
                leaves.extend(child["leaves"].as_array().unwrap().iter().cloned());
                json!({"name":name,"offset":offset,"schema":child})
            })
            .collect();
        let mut value = schema(kind, name, json!(leaves));
        value["fields"] = json!(fields);
        value
    }

    fn document(statement: Json) -> Json {
        let count = statement["leaves"].as_array().unwrap().len();
        json!({"format":"zkc.language-interface/0","setups":[],
            "capture":hex(&Sha256::digest(b"capture")),"original":hex(&Sha256::digest(b"original")),
            "toolchain":"test-toolchain","entry":"sample::Ingress","protocol":"Ingress",
            "protocols":[{"symbol":"Ingress","roles":["P"],
                "inputs":[{"name":"statement","index":0,"native":(0..count).collect::<Vec<_>>(),
                    "roles":["P"],"type":statement["type"],"schema":statement}],
                "outputs":[],"services":[],"clauses":[]}],"relations":[],"job":{"kind":"run"}})
    }

    fn proof_document(statement: Json) -> Json {
        let count = statement["leaves"].as_array().unwrap().len();
        let mut doc = document(statement.clone());
        let protocol = &mut doc["protocols"][0];
        protocol["roles"] = json!(["P", "V"]);
        protocol["inputs"][0]["roles"] = json!(["P", "V"]);
        protocol["inputs"].as_array_mut().unwrap().push(json!({
            "name":"witness","index":1,"native":(count..2*count).collect::<Vec<_>>(),
            "roles":["P"],"type":statement["type"],"schema":statement
        }));
        protocol["outputs"] = json!([{"name":"accepted","index":0,"native":[0],
            "roles":["V"],"type":"bool","schema":schema("boolean", "bool", json!(["bool"]))}]);
        doc["job"] = json!({"kind":"proof","prover":"P","verifier":"V","public":[0],
            "acceptance":{"direction":"output","port":0,"role":"V","path":[]},
            "completion":null,"target":null,
            "construction":{"kind":"authored","format":"zkc.framed/0"}});
        doc
    }

    fn package(document: &Json, artifact: &str) -> Package {
        // Authenticate the hand-built fixture, as in zkc' asset tests.
        let frame = json!({"format":"zkc.entry/0","original":"original",
            "interface":document.to_string(),"artifact":artifact,"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": zkc::entry::OracleSelection::default()}}).to_string();
        Package::capture(
            frame.as_bytes(),
            &Sha256::digest(frame.as_bytes()).into(),
            Package::MAX_BYTES,
        )
        .unwrap()
    }

    fn read_interface(document: &Json) -> Interface {
        BoundInterface::read(&package(document, "metadata only"))
            .unwrap()
            .into_view()
    }

    fn decode(group: &InputGroup<'_>, input: &Json) -> NamedValues {
        Decoder::new(Capacity::default())
            .unwrap()
            .decode(group, &serde_json::to_vec(input).unwrap(), None)
            .unwrap()
    }

    fn choice_schema() -> Json {
        // The explicit canonical graph encodes Choice = Empty | Flag(bool).
        // Reuse the public metadata fixture's nominal encoding without a new codec.
        let graph = json!([
            "zkc.variant/0",
            [
                "zkc.language",
                zkc::source_names::encode_nominal_identity("sample::Choice"),
                ["0", "1"],
                "case00000000",
                [],
                ["3", "4"],
                "case00000001",
                "bool",
                ["7"],
                ["6", "8"],
                ["5", "9"],
                ["2", "10"]
            ]
        ]);
        let spelling = format!("variant:{}", hex(&serde_json::to_vec(&graph).unwrap()));
        let mut choice = schema("variant", "sample::Choice", json!([spelling]));
        choice["alternatives"] = json!([{"name":"Empty","fields":[]},
            {"name":"Flag","fields":[{"name":"0","offset":0,
                "schema":schema("boolean", "bool", json!(["bool"]))}]}]);
        choice
    }

    fn assert_boolean(value: &Value, expected: bool, ingress: Ingress, cpu: &CpuExecution) {
        let expected = wire(&zkc_cpu::Value::Bool(expected), cpu);
        match (ingress, value) {
            (Ingress::Wire, Value::Leaf(InputValue::Wire(bytes))) => {
                assert_eq!(bytes.as_slice(), expected.as_slice())
            }
            (Ingress::Native, Value::Leaf(InputValue::Native(value))) => {
                assert_eq!(wire(value, cpu).as_slice(), expected.as_slice())
            }
            (Ingress::Prepared, Value::Leaf(InputValue::Prepared(data))) => {
                assert_eq!(data.canonical_bytes(), expected.as_slice())
            }
            _ => panic!("wrong ingress representation"),
        }
    }

    fn wire(value: &zkc_cpu::Value, cpu: &CpuExecution) -> Arc<Vec<u8>> {
        cpu.enter(|| {
            codec(Capacity::default(), cpu)
                .unwrap()
                .encode_native_value(value)
                .unwrap()
        })
        .into()
    }

    #[test]
    fn repeated_codecs_execute_on_the_supplied_worker() {
        let cpu = CpuExecution::new(1).unwrap();
        let caller = std::thread::current().id();
        let worker = cpu.execute(|| std::thread::current().id());
        assert_ne!(worker, caller);
        for _ in 0..4 {
            let backend = codec(Capacity::default(), &cpu).unwrap();
            assert_eq!(
                backend.cpu().execute(|| std::thread::current().id()),
                worker
            );
            assert_eq!(std::thread::current().id(), caller);
        }
    }

    #[test]
    fn native_and_prepared_use_the_same_canonical_statement() {
        let cpu = CpuExecution::new(2).unwrap();
        let value = zkc_cpu::Value::Vector(vec![zkc_cpu::Scalar::from(7); 17].into());
        let bytes = wire(&value, &cpu);
        let backend = codec(Capacity::default(), &cpu).unwrap();
        for ingress in [Ingress::Wire, Ingress::Native, Ingress::Prepared] {
            for _ in 0..3 {
                let (input, retained) = convert_wire(
                    bytes.clone(),
                    value.physical_type(),
                    ingress,
                    Capacity::default(),
                    &cpu,
                )
                .unwrap();
                let shared = share_leaf(&input).unwrap();
                match (&input, shared) {
                    (InputValue::Wire(a), InputValue::Wire(b)) => {
                        assert!(Arc::ptr_eq(a, &b));
                        assert_eq!(retained, bytes.len());
                    }
                    (InputValue::Native(a), InputValue::Native(b)) => {
                        assert_eq!(backend.encode_native_value(&b).unwrap(), *bytes);
                        let (zkc_cpu::Value::Vector(a), zkc_cpu::Value::Vector(b)) =
                            (a.as_ref(), b.as_ref())
                        else {
                            panic!("vector owners")
                        };
                        assert_eq!(a.as_ptr(), b.as_ptr());
                        assert_eq!(retained, value.retained_bytes());
                    }
                    (InputValue::Prepared(a), InputValue::Prepared(b)) => {
                        assert_eq!(a.canonical_bytes(), bytes.as_slice());
                        assert_eq!(a.canonical_bytes().as_ptr(), b.canonical_bytes().as_ptr());
                        assert_eq!(retained, a.retained_bytes());
                    }
                    _ => panic!("ingress changed the representation"),
                }
            }
        }
    }

    #[test]
    fn changing_run_and_proof_inputs_keep_distinct_nested_owners() {
        let cpu = CpuExecution::new(2).unwrap();
        let boolean = schema("boolean", "bool", json!(["bool"]));
        let pair = product(
            "tuple",
            "(bool,[bool;2])",
            vec![
                ("0", boolean.clone()),
                (
                    "1",
                    product(
                        "array",
                        "[bool;2]",
                        vec![("0", boolean.clone()), ("1", boolean)],
                    ),
                ),
            ],
        );
        let nested = product(
            "record",
            "sample::Statement",
            vec![
                ("empty", schema("unit", "()", json!([]))),
                ("pair", pair),
                ("choice", choice_schema()),
            ],
        );
        for doc in [document(nested.clone()), proof_document(nested)] {
            let interface = read_interface(&doc);
            let groups = interface.input_groups();
            if doc["job"]["kind"] == "proof" {
                assert_eq!(
                    groups.iter().map(|g| g.name()).collect::<Vec<_>>(),
                    ["public", "witness"]
                );
            }
            for ingress in [Ingress::Wire, Ingress::Native, Ingress::Prepared] {
                // Keep public and witness owners alive together, as the proof worker does.
                let owners: Vec<Vec<_>> = groups
                    .iter()
                    .map(|group| {
                        let name = if group.name() == "witness" {
                            "witness"
                        } else {
                            "statement"
                        };
                        [false, true]
                            .into_iter()
                            .map(|flag| {
                                // Public and witness data differ, so an owner mixup is visible.
                                let flag = flag ^ (group.name() == "witness");
                                let input = json!({name:{"empty":null,"pair":[flag,[!flag,flag]],
                        "choice":{"case":if flag {"Flag"} else {"Empty"},
                            "fields":if flag {json!({"0":flag})} else {json!({})}}}});
                                Owner::new(
                                    decode(group, &input),
                                    group,
                                    ingress,
                                    Capacity::default(),
                                    &cpu,
                                )
                                .unwrap()
                            })
                            .collect()
                    })
                    .collect();
                for (group, owners) in groups.iter().zip(&owners) {
                    let name = if group.name() == "witness" {
                        "witness"
                    } else {
                        "statement"
                    };
                    assert!(owners[0].retained_payload_bytes > 0);
                    let empty_index = usize::from(group.name() == "witness");
                    assert!(
                        owners[1 - empty_index].retained_payload_bytes
                            > owners[empty_index].retained_payload_bytes
                    );
                    for index in [0, 1, 0, 1] {
                        let request = owners[index].share().unwrap();
                        let flag = (index == 1) ^ (group.name() == "witness");
                        let Value::Record(record) = &request[name] else {
                            panic!("record")
                        };
                        assert!(matches!(record["empty"], Value::Unit));
                        let Value::Tuple(pair) = &record["pair"] else {
                            panic!("tuple")
                        };
                        assert_boolean(&pair[0], flag, ingress, &cpu);
                        let Value::Array(array) = &pair[1] else {
                            panic!("array")
                        };
                        assert_boolean(&array[0], !flag, ingress, &cpu);
                        assert_boolean(&array[1], flag, ingress, &cpu);
                        let Value::Variant {
                            alternative,
                            fields,
                        } = &record["choice"]
                        else {
                            panic!("variant")
                        };
                        if flag {
                            assert_eq!(alternative, "Flag");
                            assert_boolean(&fields["0"], true, ingress, &cpu);
                        } else {
                            assert_eq!(alternative, "Empty");
                            assert!(fields.is_empty());
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn associated_ownership_does_not_grant_decoder_constructor_permission() {
        let cpu = CpuExecution::new(2).unwrap();
        let boolean = schema("boolean", "bool", json!(["bool"]));
        let plain = read_interface(&document(boolean.clone()));
        let mut associated = product(
            "associated",
            "sample::Domain::Value",
            vec![("value", boolean)],
        );
        associated["constructible"] = json!(false);
        let associated = read_interface(&document(associated));
        let groups = associated.input_groups();
        let group = &groups[0];
        let error = Decoder::new(Capacity::default())
            .unwrap()
            .decode(group, br#"{"statement":true}"#, None)
            .unwrap_err();
        assert_eq!(error.code, "entry-input-constructor");
        for ingress in [Ingress::Wire, Ingress::Native, Ingress::Prepared] {
            // Associated values can be shared by the helper but are output-only
            // at Entry. Decode the underlying data through a constructible group.
            let mut values = decode(&plain.input_groups()[0], &json!({"statement":true}));
            let value = values.remove("statement").unwrap();
            values.insert("statement".into(), Value::Associated(Box::new(value)));
            let owner = Owner::new(values, group, ingress, Capacity::default(), &cpu).unwrap();
            let request = owner.share().unwrap();
            let Value::Associated(value) = &request["statement"] else {
                panic!("associated")
            };
            assert_boolean(value, true, ingress, &cpu);
        }
    }

    #[test]
    fn decoder_key_initializers_remain_descriptors_without_data_conversion() {
        let cpu = CpuExecution::new(2).unwrap();
        use zkc::{entry::inputs::Resolver, execution::InputSource};
        struct KeyFile;
        impl Resolver for KeyFile {
            fn resolve(&mut self, relative: &str) -> std::result::Result<InputSource, String> {
                assert_eq!(relative, "key");
                InputSource::new(
                    std::fs::File::open(concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml"))
                        .unwrap(),
                )
            }
        }
        let leaf = "prover_key:multilinear.kzg.bls12-381/0";
        let mut key = schema("builtin", leaf, json!([leaf]));
        key["constructible"] = json!(false);
        let mut doc = document(key);
        doc["setups"] = json!([{"name":"pcs","inputs":[{"port":0,"path":[]}]}]);
        let interface = read_interface(&doc);
        let groups = interface.input_groups();
        let group = &groups[0];
        assert_eq!(group.describe()["ports"][0]["initializer"], "prover_key");
        let input =
            serde_json::to_vec(&json!({"statement":{"file":"key","fingerprint":hex(&[7;32])}}))
                .unwrap();
        for ingress in [Ingress::Wire, Ingress::Native, Ingress::Prepared] {
            // The file is only a descriptor fixture: no key is imported here.
            let values = Decoder::new(Capacity::default())
                .unwrap()
                .decode(group, &input, Some(&mut KeyFile))
                .unwrap();
            let owner = Owner::new(values, group, ingress, Capacity::default(), &cpu).unwrap();
            assert_eq!(owner.retained_payload_bytes, 0);
            for _ in 0..2 {
                let request = owner.share().unwrap();
                assert!(
                    matches!(&request["statement"], Value::Leaf(InputValue::ProverKeyInput {
                    fingerprint, .. }) if fingerprint == &[7;32])
                );
            }
        }
    }

    #[test]
    fn schema_directed_owners_refuse_unsupported_types_and_leaf_capacity() {
        let cpu = CpuExecution::new(2).unwrap();
        let interface = read_interface(&document(schema("boolean", "bool", json!(["bool"]))));
        let groups = interface.input_groups();
        let group = &groups[0];
        let input = json!({"statement":true});
        assert!(
            Owner::new(
                decode(group, &input),
                group,
                Ingress::Json,
                Capacity::default(),
                &cpu,
            )
            .is_err()
        );
        for ingress in [Ingress::Native, Ingress::Prepared] {
            let capacity = Capacity {
                wire_bytes: wire(&zkc_cpu::Value::Bool(true), &cpu).len() - 1,
                ..Capacity::default()
            };
            assert!(Owner::new(decode(group, &input), group, ingress, capacity, &cpu).is_err());
            let capacity = Capacity {
                value_bytes: 0,
                ..Capacity::default()
            };
            assert!(Owner::new(decode(group, &input), group, ingress, capacity, &cpu).is_err());
        }
        for leaf in [
            "point:bls12-381.fr",
            "commitment:multilinear.kzg.bls12-381/0",
        ] {
            let mut doc = document(schema("builtin", leaf, json!([leaf])));
            if leaf.starts_with("commitment:") {
                doc["setups"] = json!([{"name":"pcs","inputs":[{"port":0,"path":[]}]}]);
            }
            let interface = read_interface(&doc);
            let groups = interface.input_groups();
            let group = &groups[0];
            // These logical types have no readable Entry input codec. Supplying
            // Wire directly must still refuse Native/Prepared before decoding.
            assert!(
                Decoder::new(Capacity::default())
                    .unwrap()
                    .decode(group, br#"{"statement":[]}"#, None)
                    .is_err()
            );
            for ingress in [Ingress::Native, Ingress::Prepared] {
                let values = [(
                    "statement".into(),
                    Value::Leaf(InputValue::Wire(Vec::new().into())),
                )]
                .into();
                let error = Owner::new(values, group, ingress, Capacity::default(), &cpu)
                    .err()
                    .unwrap();
                assert!(
                    matches!(error, crate::Failure::Failed(message) if message ==
                    "benchmark-ingress: unsupported data conversion (private or setup-dependent type)")
                );
            }
        }
    }

    fn run_artifact(document: &Json) -> String {
        let leaves = document["protocols"][0]["inputs"][0]["schema"]["leaves"]
            .as_array()
            .unwrap();
        let inputs: Vec<_> = leaves
            .iter()
            .enumerate()
            .map(|(index, leaf)| {
                let logical = zkc_runtime::vm::LogicalType::parse(leaf.as_str().unwrap()).unwrap();
                json!([
                    format!("input{index}"),
                    PhysicalType::default_for(logical).unwrap().spelling()
                ])
            })
            .collect();
        let program = json!([
            "zkc.program/0",
            [],
            [],
            [[
                "participant",
                "p",
                "root",
                "role00000000",
                inputs,
                [],
                [["return", []]],
                []
            ]],
            [["entry", "Ingress", [["role00000000", "p"]]]]
        ]);
        json!({"format":"zkc.run/0","candidate":program.to_string(),"entry":"Ingress",
            "roles":["role00000000"],"steps":[{"role":0,"instruction":0,"anchor":null}]})
        .to_string()
    }

    #[test]
    fn entry_preflight_checks_aggregate_loading_for_every_representation() {
        use zkc::entry::{EntryPhase, RoleInputs, RunEntry, RunRequest, SetupAuthority};
        use zkc::run::HostLimits;
        let cpu = CpuExecution::new(2).unwrap();
        let boolean = schema("boolean", "bool", json!(["bool"]));
        for pair in [false, true] {
            let statement = if pair {
                product(
                    "tuple",
                    "(bool,bool)",
                    vec![("0", boolean.clone()), ("1", boolean.clone())],
                )
            } else {
                boolean.clone()
            };
            let doc = document(statement);
            let input = json!({"statement":if pair {json!([true,false])} else {json!(true)}});
            for limited in [false, true] {
                let mut limits = HostLimits::default();
                if limited {
                    let value = zkc_cpu::Value::Bool(true);
                    // One Prepared owner retains both native and wire data;
                    // that fits while two independently loaded values do not.
                    limits.capacity.values.live_bytes =
                        value.retained_bytes() + wire(&value, &cpu).len();
                }
                let entry = RunEntry::admit_with_cpu(
                    package(&doc, &run_artifact(&doc)),
                    limits.clone(),
                    SetupAuthority::default(),
                    cpu.clone(),
                )
                .unwrap();
                let groups = entry.interface().input_groups();
                let group = &groups[0];
                for ingress in [Ingress::Wire, Ingress::Native, Ingress::Prepared] {
                    let owner = Owner::new(
                        decode(group, &input),
                        group,
                        ingress,
                        limits.capacity,
                        entry.cpu(),
                    )
                    .unwrap();
                    // Each leaf was admitted for ownership; Entry must still
                    // charge the whole invocation on every shared request.
                    for _ in 0..2 {
                        let result = entry.check_inputs(RunRequest {
                            session: "ingress".into(),
                            setups: Default::default(),
                            roles: [(
                                "P".into(),
                                RoleInputs {
                                    inputs: owner.share().unwrap(),
                                    services: Default::default(),
                                },
                            )]
                            .into(),
                        });
                        if limited && pair {
                            let error = result.unwrap_err();
                            assert_eq!(error.phase, EntryPhase::Preparation);
                            assert_eq!(error.code(), "artifact-input-bytes-limit");
                        } else {
                            result.unwrap();
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn conversion_refuses_invalid_wire_and_current_capacity() {
        let cpu = CpuExecution::new(2).unwrap();
        let value = zkc_cpu::Value::Bool(true);
        let ty = value.physical_type();
        let bytes = wire(&value, &cpu);
        for ingress in [Ingress::Native, Ingress::Prepared] {
            assert!(
                convert_wire(
                    vec![0].into(),
                    ty.clone(),
                    ingress,
                    Capacity::default(),
                    &cpu
                )
                .is_err()
            );
            let capacity = Capacity {
                wire_bytes: bytes.len() - 1,
                ..Capacity::default()
            };
            assert!(convert_wire(bytes.clone(), ty.clone(), ingress, capacity, &cpu).is_err());
        }
        assert!(convert_wire(bytes, ty, Ingress::Json, Capacity::default(), &cpu).is_err());
        let private =
            zkc_cpu::Value::point(vec![zkc_cpu::Scalar::from(7); 4], &Policy::default()).unwrap();
        for ingress in [Ingress::Native, Ingress::Prepared] {
            let error = convert_wire(
                Vec::new().into(),
                private.physical_type(),
                ingress,
                Capacity::default(),
                &cpu,
            )
            .unwrap_err();
            assert!(
                matches!(error, crate::Failure::Failed(message) if message ==
                "benchmark-ingress: unsupported data conversion (private or setup-dependent type)")
            );
        }
        // Resource constructor descriptions stay descriptions.
        assert!(matches!(
            share_leaf(&InputValue::Resource { budget: 3 }).unwrap(),
            InputValue::Resource { budget: 3 }
        ));
    }
}
