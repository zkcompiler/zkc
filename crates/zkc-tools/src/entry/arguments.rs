//! Exact named argument admission shared by run and independent proof jobs.
use super::{
    Interface, NamedValues, Value,
    interface::raw::{Port, Service},
    setups, value,
};
use crate::host::request::InputValue;
use std::collections::BTreeMap;

pub(super) fn check_ports(interface: &Interface) -> Result<(), String> {
    for port in &interface.selected_protocol().inputs {
        check_import(interface, port)?;
    }
    for port in &interface.selected_protocol().outputs {
        value::check_export(&port.schema)?;
    }
    Ok(())
}
fn check_import(interface: &Interface, port: &Port) -> Result<(), String> {
    if setups::key_kind(interface, port).is_some() {
        Ok(())
    } else {
        value::check_import(&port.schema)
    }
}
pub(super) fn values<'a>(
    interface: &Interface,
    ports: impl Iterator<Item = &'a Port>,
    mut values: NamedValues,
    public_keys: Option<&BTreeMap<u32, &[u8]>>,
) -> Result<Vec<InputValue>, String> {
    let mut inputs = Vec::new();
    for port in ports {
        match setups::key_kind(interface, port) {
            Some(zkc_runtime::interactive::Type::VerifierKey) => {
                inputs.push(if let Some(keys) = public_keys {
                    InputValue::Wire(
                        keys.get(&port.native[0])
                            .ok_or("entry-setup-material")?
                            .to_vec(),
                    )
                } else {
                    InputValue::VerifierKey
                });
            }
            Some(zkc_runtime::interactive::Type::ProverKey) => {
                let value = values.remove(&port.name).ok_or("entry-input-names")?;
                let Value::Leaf(
                    value @ (InputValue::ProverKey(_) | InputValue::ProverKeyFile { .. }),
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
