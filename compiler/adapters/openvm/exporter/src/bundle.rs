//! Relation-bundle carriers of the export, the data they carry, and the
//! adapter's own reading of the bundle semantics.
//!
//! The carriers follow `docs/spec/domains/relation-bundles.md`. Every bus is
//! one `field-balance` channel: OpenVM's balance condition is that the sum of
//! field-valued multiplicities of every distinct message on a bus is zero,
//! which is the bundle's field-weighted balance with no natural
//! interpretation of a count. Every record declares no count bound (`null`):
//! upstream `count_weight` is the coefficient of an interaction in the
//! trace-height inequality `sum(weight * height) < p`, not a bound on any
//! row's count, so it stays in the provenance report with the height
//! constraints it belongs to.

use crate::arena::hex_sha256;
use crate::field::{F, FIELD_IDENTITY, decimal};
use crate::model::{AirExport, Export, Height, Input, Scope};
use crate::refusal::{Result, ensure, refuse};
use crate::slice::{Execution, Trace};
use p3_field::PrimeCharacteristicRing;
use serde_json::{Value, json};
use std::collections::BTreeMap;

pub const BUNDLE_FORMAT: &str = "zkc.relation-bundle/0";
pub const CONFIGURATION_FORMAT: &str = "zkc.relation-configuration/0";
pub const INSTANCE_FORMAT: &str = "zkc.relation-instance/0";
pub const WITNESS_FORMAT: &str = "zkc.relation-witness/0";
pub const HEIGHT_LIMIT: usize = 1 << 20;
pub const HEIGHT_MINIMUM: usize = 2;

/// Data of one present table: configuration groups (cached mains), witness
/// group (common main) and the height.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableData {
    pub height: usize,
    pub cached: Vec<Vec<F>>,
    pub main: Vec<F>,
}

/// Carrier data: per table `None` when absent, plus the public values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Data {
    pub tables: Vec<Option<TableData>>,
    pub publics: Vec<F>,
}

impl Data {
    pub fn from_execution(export: &Export, execution: &Execution) -> Self {
        let tables = execution
            .traces
            .iter()
            .map(|t| {
                t.as_ref().map(|t: &Trace| TableData {
                    height: t.height(),
                    cached: t.cached_mains.iter().map(|m| m.values.clone()).collect(),
                    main: t.common_main.values.clone(),
                })
            })
            .collect();
        let mut publics = vec![];
        for (_, air, index) in &export.publics {
            let trace = execution.traces[*air]
                .as_ref()
                .expect("an AIR with public values is present");
            publics.push(trace.public_values[*index]);
        }
        Self { tables, publics }
    }

    /// Per-AIR traces for the upstream evaluators, when every group width
    /// divides the data and heights are consistent.
    pub fn traces(&self, export: &Export) -> Result<Vec<Option<Trace>>> {
        check_shape(export, self)?;
        let mut out = vec![];
        for (i, table) in self.tables.iter().enumerate() {
            let air = &export.airs[i];
            let Some(table) = table else {
                out.push(None);
                continue;
            };
            let mut cached_mains = vec![];
            let mut groups = air.groups.iter();
            for values in &table.cached {
                let g = groups.next().ok_or_else(|| crate::refusal::Refusal {
                    id: "openvm-data-shape",
                    detail: format!("{}: too many cached parts", air.name),
                })?;
                ensure(
                    g.authority == "config" && values.len() == table.height * g.width,
                    "openvm-data-shape",
                    || format!("{}: cached part length", air.name),
                )?;
                cached_mains.push(openvm_stark_backend::p3_matrix::dense::RowMajorMatrix::new(
                    values.clone(),
                    g.width,
                ));
            }
            let main = groups.next().ok_or_else(|| crate::refusal::Refusal {
                id: "openvm-data-shape",
                detail: format!("{}: no main group", air.name),
            })?;
            ensure(
                main.authority == "witness" && table.main.len() == table.height * main.width,
                "openvm-data-shape",
                || format!("{}: main length", air.name),
            )?;
            let public_values = export
                .publics
                .iter()
                .enumerate()
                .filter(|(_, (_, a, _))| *a == i)
                .map(|(slot, _)| self.publics[slot])
                .collect();
            out.push(Some(Trace {
                cached_mains,
                common_main: openvm_stark_backend::p3_matrix::dense::RowMajorMatrix::new(
                    table.main.clone(),
                    main.width,
                ),
                public_values,
            }));
        }
        Ok(out)
    }
}

fn scope_value(scope: Scope) -> Value {
    match scope {
        Scope::All => json!(["all"]),
        Scope::First => json!(["first"]),
        Scope::Last => json!(["last"]),
        Scope::Transition => json!(["interior", 0, 1]),
        Scope::Interior => json!(["interior", 1, 1]),
        Scope::Tail => json!(["interior", 1, 0]),
    }
}

fn scalars(values: &[F]) -> Value {
    Value::Array(values.iter().map(|v| Value::String(decimal(*v))).collect())
}

/// The `zkc.relation-bundle/0` array.
pub fn bundle(export: &Export) -> Result<Value> {
    let publics: Vec<Value> = export
        .publics
        .iter()
        .map(|(name, _, _)| json!([name, FIELD_IDENTITY]))
        .collect();
    let channels: Vec<Value> = export
        .buses
        .iter()
        .map(|b| {
            json!([
                b.name,
                "field-balance",
                vec![FIELD_IDENTITY; b.arity],
                FIELD_IDENTITY
            ])
        })
        .collect();
    let mut tables = vec![];
    for air in &export.airs {
        let height = match air.height {
            Height::Fixed(h) => json!(["fixed", h]),
            Height::Config => json!(["config", HEIGHT_MINIMUM, HEIGHT_LIMIT, true]),
            Height::Instance => json!(["instance", HEIGHT_MINIMUM, HEIGHT_LIMIT, true]),
        };
        let groups: Vec<Value> = air
            .groups
            .iter()
            .map(|g| json!([g.name, g.authority, FIELD_IDENTITY, g.width]))
            .collect();
        let arena: Value =
            serde_json::from_str(&air.arena.canonical()).expect("canonical arena is JSON");
        let inputs: Vec<Value> = air
            .inputs
            .iter()
            .map(|input| match *input {
                Input::Read {
                    group,
                    offset,
                    column,
                } => json!(["read", group, offset.to_string(), column]),
                Input::Public(slot) => json!(["public", slot]),
            })
            .collect();
        let assertions: Vec<Value> = air
            .assertions
            .iter()
            .map(|a| json!([a.output, scope_value(a.scope)]))
            .collect();
        let interactions: Vec<Value> = air
            .interactions
            .iter()
            .map(|x| {
                json!([
                    "field-balance",
                    x.bus,
                    ["global"],
                    ["all"],
                    x.message,
                    x.count,
                    Value::Null
                ])
            })
            .collect();
        tables.push(json!([
            air.name,
            if air.required { "required" } else { "optional" },
            height,
            "cyclic",
            groups,
            arena,
            inputs,
            assertions,
            interactions
        ]));
    }
    ensure(tables.len() <= 256, "openvm-bundle-limit", || {
        "table count".into()
    })?;
    Ok(json!([BUNDLE_FORMAT, publics, channels, tables]))
}

/// Canonical compact text and its identity.
pub fn identity(value: &Value) -> (String, String) {
    let text = value.to_string();
    let digest = hex_sha256(text.as_bytes());
    (text, digest)
}

fn check_shape(export: &Export, data: &Data) -> Result<()> {
    ensure(
        data.tables.len() == export.airs.len(),
        "openvm-data-shape",
        || "table count".into(),
    )?;
    ensure(
        data.publics.len() == export.publics.len(),
        "openvm-data-shape",
        || "public count".into(),
    )?;
    for (i, table) in data.tables.iter().enumerate() {
        let air = &export.airs[i];
        if let Some(t) = table {
            let admitted_height = (HEIGHT_MINIMUM..=HEIGHT_LIMIT).contains(&t.height)
                && t.height.is_power_of_two()
                && match air.height {
                    Height::Fixed(h) => t.height == h,
                    _ => true,
                };
            ensure(admitted_height, "openvm-data-shape", || {
                format!("{}: height", air.name)
            })?;
            ensure(
                t.cached.len() + 1 == air.groups.len(),
                "openvm-data-shape",
                || format!("{}: group count", air.name),
            )?;
            for (g, values) in air
                .groups
                .iter()
                .zip(t.cached.iter().chain(std::iter::once(&t.main)))
            {
                ensure(
                    t.height.checked_mul(g.width) == Some(values.len()),
                    "openvm-data-shape",
                    || format!("{}: matrix size", air.name),
                )?;
            }
        } else {
            ensure(!air.required, "openvm-data-shape", || {
                format!("{}: required table is absent", air.name)
            })?;
        }
    }
    Ok(())
}

/// Verifier configuration: the cached program code, with its height.
pub fn configuration(export: &Export, bundle_identity: &str, data: &Data) -> Result<Value> {
    check_shape(export, data)?;
    let mut tables = vec![];
    for (i, air) in export.airs.iter().enumerate() {
        let config_groups = air
            .groups
            .iter()
            .filter(|g| g.authority == "config")
            .count();
        let (height, groups) = match (&data.tables[i], air.height) {
            (Some(t), Height::Config) => (
                json!(t.height),
                t.cached.iter().map(|v| scalars(v)).collect::<Vec<_>>(),
            ),
            (None, Height::Config) => {
                return refuse(
                    "openvm-data-shape",
                    format!("{}: configured table is absent", air.name),
                );
            }
            _ => (Value::Null, vec![]),
        };
        ensure(groups.len() == config_groups, "openvm-data-shape", || {
            format!("{}: configuration groups", air.name)
        })?;
        tables.push(json!([height, groups]));
    }
    Ok(json!([CONFIGURATION_FORMAT, bundle_identity, tables]))
}

/// Verifier instance: public values, presence and instance heights.
pub fn instance(export: &Export, bundle_identity: &str, data: &Data) -> Result<Value> {
    check_shape(export, data)?;
    let mut tables = vec![];
    for (i, air) in export.airs.iter().enumerate() {
        tables.push(match (&data.tables[i], air.height) {
            (None, _) => json!(["absent"]),
            (Some(t), Height::Instance) => json!(["present", t.height, []]),
            (Some(_), _) => json!(["present", Value::Null, []]),
        });
    }
    Ok(json!([
        INSTANCE_FORMAT,
        bundle_identity,
        scalars(&data.publics),
        tables
    ]))
}

/// Prover witness: the common main of every present table.
pub fn witness(export: &Export, bundle_identity: &str, data: &Data) -> Result<Value> {
    check_shape(export, data)?;
    let tables: Vec<Value> = data
        .tables
        .iter()
        .map(|t| match t {
            None => Value::Null,
            Some(t) => json!([scalars(&t.main)]),
        })
        .collect();
    Ok(json!([WITNESS_FORMAT, bundle_identity, tables]))
}

/// The four carriers as one conformance-transport line.
pub fn carriers(export: &Export, data: &Data) -> Result<[Value; 4]> {
    let b = bundle(export)?;
    let (_, id) = identity(&b);
    Ok([
        b,
        configuration(export, &id, data)?,
        instance(export, &id, data)?,
        witness(export, &id, data)?,
    ])
}

/// Nonzero residuals `(table, assertion, row, value)` and unbalanced keys
/// `(channel, tuple, sum)` under the bundle semantics, read by the adapter's
/// own arena interpreter: scoped assertions, cyclic reads, field-weighted
/// balance of every present table.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Outcome {
    pub residuals: Vec<(usize, usize, usize, F)>,
    pub unbalanced: Vec<(usize, Vec<F>, F)>,
}

impl Outcome {
    pub fn satisfied(&self) -> bool {
        self.residuals.is_empty() && self.unbalanced.is_empty()
    }
}

/// Arena outputs of one table row with cyclic reads. The table's matrices
/// must have the export's group widths; its height is not checked against
/// the table's height policy.
pub fn row_outputs(air: &AirExport, table: &TableData, publics: &[F], row: usize) -> Vec<F> {
    air.arena.evaluate(|slot| match air.inputs[slot] {
        Input::Read {
            group,
            offset,
            column,
        } => {
            let values = if group + 1 == air.groups.len() {
                &table.main
            } else {
                &table.cached[group]
            };
            values[((row + offset) % table.height) * air.groups[group].width + column]
        }
        Input::Public(slot) => publics[slot],
    })
}

pub fn evaluate(export: &Export, data: &Data) -> Result<Outcome> {
    check_shape(export, data)?;
    let mut residuals = vec![];
    let mut sums: BTreeMap<(usize, Vec<u32>), (Vec<F>, F)> = BTreeMap::new();
    for (t, table) in data.tables.iter().enumerate() {
        let Some(table) = table else { continue };
        let air = &export.airs[t];
        let height = table.height;
        ensure(height >= 1, "openvm-data-shape", || {
            format!("{}: empty table", air.name)
        })?;
        for row in 0..height {
            let outputs = row_outputs(air, table, &data.publics, row);
            for (a, assertion) in air.assertions.iter().enumerate() {
                if assertion.scope.contains(row, height) {
                    let v = outputs[assertion.output];
                    if v != F::ZERO {
                        residuals.push((t, a, row, v));
                    }
                }
            }
            for x in &air.interactions {
                let tuple: Vec<F> = x.message.iter().map(|p| outputs[*p]).collect();
                let count = outputs[x.count];
                let key = (x.bus, tuple.iter().map(|v| v.as_canonical_u32()).collect());
                let entry = sums.entry(key).or_insert((tuple, F::ZERO));
                entry.1 += count;
            }
        }
    }
    let unbalanced = sums
        .into_iter()
        .filter(|(_, (_, sum))| *sum != F::ZERO)
        .map(|((channel, _), (tuple, sum))| (channel, tuple, sum))
        .collect();
    Ok(Outcome {
        residuals,
        unbalanced,
    })
}

use p3_field::PrimeField32;
