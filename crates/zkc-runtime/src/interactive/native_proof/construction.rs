//! The executable construction plan owns state shape and handler selection.
//! It records ordinary functions; it does not authenticate their source or
//! assert a sampling distribution for arbitrary Local code.
use super::{Result, refuse};
use crate::interactive::{LogicalType, PhysicalType, Type};
use serde_json::Value;
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
pub struct ConstructionPlan {
    pub(super) symbol: String,
    pub(super) host: bool,
    pub(super) state: Vec<PhysicalType>,
    pub(super) initializer: String,
    pub(super) start: String,
    pub(super) inputs: Vec<usize>,
    pub(super) adapters: Vec<Adapter>,
}
#[derive(Clone, Debug)]
pub(super) struct Adapter {
    pub symbol: String,
    pub native: bool,
    pub origins: Vec<String>,
}
fn list(value: &Value, limit: usize) -> Result<&[Value]> {
    value
        .as_array()
        .filter(|v| v.len() <= limit)
        .map(Vec::as_slice)
        .ok_or_else(|| refuse("native-proof-construction-plan"))
}
fn record(value: &Value, size: usize) -> Result<&[Value]> {
    let values = list(value, size)?;
    if values.len() != size {
        return Err(refuse("native-proof-construction-plan"));
    }
    Ok(values)
}
fn text(value: &Value) -> Result<&str> {
    value
        .as_str()
        .filter(|v| v.len() <= 1024 * 1024)
        .ok_or_else(|| refuse("native-proof-construction-plan"))
}
fn name(value: &Value, empty: bool) -> Result<String> {
    let value = text(value)?;
    if !(empty && value.is_empty()) && !super::super::decode::valid_name(value) {
        return Err(refuse("native-proof-construction-plan"));
    }
    Ok(value.into())
}
impl ConstructionPlan {
    /// Read the single current schema. An empty array selects the installed
    /// native or authored path; unknown fields and partial plans refuse.
    pub fn read(value: &Value) -> Result<Option<Self>> {
        if list(value, 7)?.is_empty() {
            return Ok(None);
        }
        let row = record(value, 7)?;
        if text(&row[0])? != "zkc.construction-plan/0" {
            return Err(refuse("native-proof-construction-plan"));
        }
        let symbol = name(&row[1], false)?;
        let host = match text(&row[2])? {
            "host" => true,
            "local" => false,
            _ => return Err(refuse("native-proof-construction-root")),
        };
        let state = list(&row[3], 1024)?
            .iter()
            .map(|v| {
                let logical = LogicalType::parse(text(v)?)
                    .map_err(|_| refuse("native-proof-construction-state"))?;
                PhysicalType::default_for(logical)
                    .map_err(|_| refuse("native-proof-construction-state"))
            })
            .collect::<Result<Vec<_>>>()?;
        if host {
            if state.len() != 1 || state[0].kind() != Type::Transcript {
                return Err(refuse("native-proof-construction-state"));
            }
        } else if state
            .iter()
            .any(|t| !t.is_duplicable() || !t.is_discardable())
        {
            return Err(refuse("native-proof-construction-state"));
        }
        let initializer = name(&row[4], host)?;
        if host && !initializer.is_empty() {
            return Err(refuse("native-proof-construction-root"));
        }
        let start = record(&row[5], 2)?;
        let start_name = name(&start[0], host)?;
        let mut inputs = Vec::new();
        for input in list(&start[1], 1024)? {
            let encoded = text(input)?;
            let index = encoded
                .parse::<usize>()
                .ok()
                .filter(|i| *i < 1024 && i.to_string() == encoded)
                .ok_or_else(|| refuse("native-proof-construction-start"))?;
            if inputs.contains(&index) {
                return Err(refuse("native-proof-construction-start"));
            }
            inputs.push(index);
        }
        if start_name.is_empty() && !inputs.is_empty() {
            return Err(refuse("native-proof-construction-start"));
        }
        let mut adapters = Vec::new();
        let mut names = BTreeSet::new();
        let mut origins = BTreeSet::new();
        let mut origin_bytes = 0usize;
        for adapter in list(&row[6], 2048)? {
            let adapter = record(adapter, 3)?;
            let symbol = name(&adapter[0], false)?;
            let native = match text(&adapter[1])? {
                "native" => true,
                "local" => false,
                _ => return Err(refuse("native-proof-construction-helper")),
            };
            if !names.insert(symbol.clone())
                || symbol == initializer
                || symbol == start_name
                || native && !host
            {
                return Err(refuse("native-proof-construction-helper"));
            }
            let mut selected = Vec::new();
            for origin in list(&adapter[2], 2048)? {
                let origin = text(origin)?;
                origin_bytes += origin.len();
                if origin_bytes > 16 * 1024 * 1024
                    || origins.len() == 2048
                    || !origins.insert(origin.to_owned())
                {
                    return Err(refuse("native-proof-construction-coverage"));
                }
                selected.push(origin.to_owned());
            }
            if selected.is_empty() || native && selected.len() != 1 {
                return Err(refuse("native-proof-construction-coverage"));
            }
            adapters.push(Adapter {
                symbol,
                native,
                origins: selected,
            });
        }
        Ok(Some(Self {
            symbol,
            host,
            state,
            initializer,
            start: start_name,
            inputs,
            adapters,
        }))
    }
    pub fn symbol(&self) -> &str {
        &self.symbol
    }
    pub fn input_slots(&self) -> usize {
        if self.host { self.state.len() } else { 0 }
    }
    pub fn output_slots(&self) -> usize {
        self.state.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn plan() -> Value {
        json!([
            "zkc.construction-plan/0",
            "selected",
            "local",
            ["index"],
            "initialize",
            ["start", ["0"]],
            [["observe", "local", ["message"]]]
        ])
    }

    #[test]
    fn current_shape_and_empty_state_are_explicit() {
        assert!(ConstructionPlan::read(&json!([])).unwrap().is_none());
        let mut value = plan();
        let parsed = ConstructionPlan::read(&value).unwrap().unwrap();
        assert_eq!(parsed.symbol(), "selected");
        assert_eq!(parsed.input_slots(), 0);
        assert_eq!(parsed.output_slots(), 1);
        value[3] = json!([]);
        assert_eq!(
            ConstructionPlan::read(&value)
                .unwrap()
                .unwrap()
                .output_slots(),
            0
        );
        value.as_array_mut().unwrap().push(json!([]));
        assert!(ConstructionPlan::read(&value).is_err());
    }

    #[test]
    fn invalid_roots_states_and_selectors_refuse() {
        for (field, replacement) in [
            (0, json!("other")),
            (1, json!("")),
            (2, json!("unknown")),
            (3, json!(["not-a-type"])),
            (4, json!("")),
            (5, json!(["start", ["00"]])),
            (5, json!(["start", ["0", "0"]])),
            (5, json!(["start", ["1024"]])),
            (5, json!(["", ["0"]])),
            (6, json!([["initialize", "local", ["message"]]])),
            (6, json!([["observe", "local", []]])),
            (6, json!([["observe", "local", ["message", "message"]]])),
            (6, json!([["observe", "native", ["message"]]])),
        ] {
            let mut value = plan();
            value[field] = replacement;
            assert!(ConstructionPlan::read(&value).is_err(), "{value}");
        }
    }
}
