//! Exact named argument admission shared by run and independent proof jobs.
use super::{
    NamedValues,
    interface::raw::{Port, Service},
    value,
};
use crate::host::request::InputValue;
use std::collections::BTreeMap;

pub(super) fn values<'a>(
    ports: impl Iterator<Item = &'a Port>,
    mut values: NamedValues,
) -> Result<Vec<InputValue>, String> {
    let mut inputs = Vec::new();
    for port in ports {
        let value = values.remove(&port.name).ok_or("entry-input-names")?;
        value::flatten(&port.schema, value, &mut inputs)?;
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
        budgets.push(values.remove(&port.name).ok_or("entry-service-names")?);
    }
    if !values.is_empty() {
        return Err("entry-service-names".into());
    }
    Ok(budgets)
}
