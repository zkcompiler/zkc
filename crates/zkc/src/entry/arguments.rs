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

pub(super) fn check_boundary(interface: &Interface) -> Result<(), String> {
    check_role_boundary(interface, None)
}
fn check_role_boundary(interface: &Interface, role: Option<&str>) -> Result<(), String> {
    if let Some(r) = interface
        .outstanding_requirements()
        .iter()
        .find(|r| role.is_none_or(|role| r.role == role))
    {
        return Err(if matches!(
            r.reason,
            "constructor" | "element-constructor" | "hidden" | "sealed"
        ) {
            "entry-input-constructor"
        } else {
            "entry-interface-native-binding"
        }
        .into());
    }
    Ok(())
}
pub(super) fn check_ports(interface: &Interface) -> Result<(), String> {
    check_boundary(interface)?;
    for role in interface.roles() {
        for port in interface.input_ports(role) {
            if port.key.is_none() {
                check_input(&port.schema)?;
            }
        }
        for port in interface.output_ports(role) {
            crate::entry::interface::schemas::check_export(&port.schema)?;
        }
    }
    Ok(())
}
pub(super) fn check_host_ports(
    interface: &Interface,
    operation: Option<super::ProofOperation>,
) -> Result<(), String> {
    let roles = interface.roles().iter().filter(|role| {
        operation.is_none_or(|operation| {
            let proof = interface.proof().expect("proof operation");
            role.native_name
                == interface.roles()[if operation == super::ProofOperation::Prove {
                    proof.prover
                } else {
                    proof.verifier
                }]
                .native_name
        })
    });
    for role in roles {
        check_role_boundary(interface, Some(&role.name))?;
        for port in interface.input_ports(role) {
            check_host_input(interface, port)?;
        }
        for port in interface.output_ports(role) {
            crate::entry::interface::schemas::check_export(&port.schema)?;
        }
    }
    // Public binding must still have the native owner's canonical codec.
    if operation.is_some() {
        for port in interface.public_ports() {
            check_host_input(interface, port)?;
            if port.key.is_none() {
                check_codec(&port.schema)?;
            }
        }
    }
    Ok(())
}
fn check_host_input(interface: &Interface, port: InputPort<'_>) -> Result<(), String> {
    if port.key.is_none() {
        crate::entry::interface::schemas::check_export(&port.schema)?;
        // Setup-bearing context values arrive through the external context map,
        // while source data comes from retained typed operands.
        if !interface.is_source_data(port) {
            check_input(&port.schema)?;
        }
    }
    Ok(())
}
pub(super) fn check_proof_ports(
    interface: &Interface,
    operation: super::ProofOperation,
) -> Result<(), String> {
    let proof = interface.proof().ok_or("entry-job-kind")?;
    let role = &interface.roles()[if operation == super::ProofOperation::Prove {
        proof.prover
    } else {
        proof.verifier
    }];
    check_role_boundary(interface, Some(&role.name))?;
    for port in interface.public_ports().chain(interface.input_ports(role)) {
        if port.key.is_none() {
            check_input(&port.schema)?;
        }
    }
    for port in interface.output_ports(role) {
        crate::entry::interface::schemas::check_export(&port.schema)?;
    }
    Ok(())
}
pub(super) fn check_input(schema: &Schema) -> Result<(), String> {
    super::interface::schemas::check_import(schema)?;
    check_codec(schema)
}
fn check_codec(schema: &Schema) -> Result<(), String> {
    if !schema.leaves.iter().all(|leaf| {
        zkc_runtime::vm::LogicalType::parse(leaf).is_ok_and(|ty| ty.is_native_message_data())
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
    let mut assigned = BTreeMap::new();
    for port in ports {
        let mut inputs = Vec::new();
        match port.key {
            Some("verifier_key") => {
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
            Some("prover_key") => {
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
        if inputs.len() != port.native.len() {
            return Err("entry-input-shape".into());
        }
        for (&coordinate, value) in port.native.iter().zip(inputs) {
            if assigned.insert(coordinate, value).is_some() {
                return Err("entry-input-overlap".into());
            }
        }
    }
    if !values.is_empty() {
        return Err("entry-input-names".into());
    }
    Ok(assigned.into_values().collect())
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
    public_types: &[zkc_runtime::vm::PhysicalType],
    private: NamedValues,
    capacity: crate::host::capacity::Capacity,
    installation: &zkc_cpu::CpuInstallation,
) -> Result<Vec<InputValue>, String> {
    let private = values(interface.named_inputs(role), private, None)?;
    let private_coordinates: Vec<_> = interface
        .named_inputs(role)
        .flat_map(|p| p.definition.native.iter().copied())
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    let mut assigned: BTreeMap<_, _> = private_coordinates.into_iter().zip(private).collect();
    let public_coordinates = interface.public_native();
    if public.len() != public_coordinates.len() || public_types.len() != public.len() {
        return Err("entry-input-public".into());
    }
    let mut public_wire_bytes = 0usize;
    for port in interface.input_ports(role) {
        if port.key == Some("verifier_key") {
            if assigned
                .insert(port.native[0], InputValue::VerifierKey)
                .is_some()
            {
                return Err("entry-input-overlap".into());
            }
        } else if port.public {
            for original in &port.native {
                let index = public_coordinates
                    .binary_search(original)
                    .map_err(|_| "entry-input-public")?;
                let input = &public[index];
                crate::host::admission::check_native_data(
                    &public_types[index],
                    input,
                    capacity,
                    installation,
                )?;
                if assigned
                    .insert(
                        *original,
                        duplicate(input, capacity, &mut public_wire_bytes)?,
                    )
                    .is_some()
                {
                    return Err("entry-input-overlap".into());
                }
            }
        }
    }
    if !assigned
        .keys()
        .copied()
        .eq(interface.role_native_inputs(role))
    {
        return Err("entry-input-coverage".into());
    }
    Ok(assigned.into_values().collect())
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
        InputValue::WireSource { file, sha256 } => InputValue::WireSource {
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
