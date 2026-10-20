//! Exact named argument admission shared by run and independent proof jobs.
use super::{
    Interface, NamedValues, Value,
    interface::{
        InputPort, RolePorts,
        raw::{Schema, Service},
    },
    value,
};
use crate::host::request::InputValue;
use std::collections::BTreeMap;

pub(super) fn check_ports(interface: &Interface) -> Result<(), String> {
    for i in 0..interface.selected_protocol().inputs.len() {
        let port = interface.input(i);
        if port.key.is_none() {
            check_input(interface, &port.schema)?;
        }
    }
    for port in &interface.selected_protocol().outputs {
        value::check_export(&port.schema)?;
    }
    Ok(())
}
pub(super) fn check_input(interface: &Interface, schema: &Schema) -> Result<(), String> {
    value::check_import(schema)?;
    if !schema.leaves.iter().all(|leaf| {
        interface
            .logical_type(leaf)
            .is_some_and(|ty| ty.is_native_message_data())
    }) {
        return Err("entry-input-codec".into());
    }
    Ok(())
}
pub(super) fn values<'a>(
    ports: impl Iterator<Item = InputPort<'a>>,
    mut values: NamedValues,
    public_keys: Option<&BTreeMap<u32, &[u8]>>,
) -> Result<Vec<InputValue>, String> {
    let mut inputs = Vec::new();
    for port in ports {
        match port.key {
            Some(zkc_runtime::vm::Type::VerifierKey) => {
                inputs.push(if let Some(keys) = public_keys {
                    InputValue::Wire(
                        keys.get(&port.native[0])
                            .ok_or("entry-setup-material")?
                            .to_vec()
                            .into(),
                    )
                } else {
                    InputValue::VerifierKey
                });
            }
            Some(zkc_runtime::vm::Type::ProverKey) => {
                let value = values.remove(&port.name).ok_or("entry-input-names")?;
                let Value::Leaf(
                    value @ (InputValue::ProverKey(_)
                    | InputValue::ProverKeyFile { .. }
                    | InputValue::ProverKeyInput { .. }),
                ) = value
                else {
                    return Err("entry-input-key".into());
                };
                inputs.push(value);
            }
            _ => {
                let value = values.remove(&port.name).ok_or("entry-input-names")?;
                value::flatten(&port.schema, value, &mut inputs)?;
            }
        }
    }
    if !values.is_empty() {
        return Err("entry-input-names".into());
    }
    Ok(inputs)
}
pub(super) fn services<'a>(
    ports: impl Iterator<Item = &'a Service>,
    mut values: BTreeMap<String, u64>,
) -> Result<Vec<u64>, String> {
    let mut budgets = Vec::new();
    for port in ports {
        budgets.push(
            values
                .remove(&port.name)
                .unwrap_or(super::DEFAULT_DRAW_BUDGET),
        );
    }
    if !values.is_empty() {
        return Err("entry-service-names".into());
    }
    Ok(budgets)
}

/// Supply public statement data once at the source boundary. Only immutable data
/// is duplicated, after native constructor/shape checks and before native byte
/// admission independently checks the complete invocation.
pub(super) fn proof_inputs(
    interface: &Interface,
    role: &RolePorts,
    public: &[InputValue],
    private: NamedValues,
    capacity: crate::host::capacity::Capacity,
) -> Result<Vec<InputValue>, String> {
    use zkc_runtime::vm::PhysicalType;
    let private = values(interface.named_inputs(role), private, None)?;
    let mut private = private.into_iter();
    let mut inputs = Vec::new();
    let mut public_wire_bytes = 0usize;
    for port in interface.input_ports(role) {
        if port.key == Some(zkc_runtime::vm::Type::VerifierKey) {
            inputs.push(InputValue::VerifierKey);
        } else if let Some((start, len)) = port.public {
            for (input, spelling) in public[start..start + len].iter().zip(&port.schema.leaves) {
                let logical = interface
                    .logical_type(spelling)
                    .expect("checked input type");
                let physical =
                    PhysicalType::default_for(logical.clone()).map_err(|e| e.to_string())?;
                crate::host::admission::check_native_data(&physical, input, capacity)?;
                inputs.push(duplicate(input, capacity, &mut public_wire_bytes)?);
            }
        } else {
            inputs.extend(private.by_ref().take(port.native.len()));
        }
    }
    Ok(inputs)
}
fn duplicate(
    input: &InputValue,
    capacity: crate::host::capacity::Capacity,
    public_wire_bytes: &mut usize,
) -> Result<InputValue, String> {
    Ok(match input {
        InputValue::Wire(bytes) => {
            // Public statement quotas count every occurrence, including shared owners.
            *public_wire_bytes = public_wire_bytes
                .checked_add(bytes.len())
                .ok_or("entry-input-limit")?;
            if *public_wire_bytes > capacity.values.live_bytes.min(capacity.values.total_bytes) {
                return Err("entry-input-limit".into());
            }
            InputValue::Wire(bytes.clone())
        }
        InputValue::Native(value) => InputValue::Native(value.clone()),
        InputValue::Prepared(data) => InputValue::Prepared(data.clone()),
        InputValue::WireFile { file, sha256 } => InputValue::WireFile {
            file: file.clone(),
            sha256: *sha256,
        },
        InputValue::Variant {
            alternative,
            payload,
        } => InputValue::Variant {
            alternative: *alternative,
            payload: payload
                .iter()
                .map(|p| duplicate(p, capacity, public_wire_bytes))
                .collect::<Result<_, _>>()?,
        },
        _ => return Err("entry-input-public".into()),
    })
}
