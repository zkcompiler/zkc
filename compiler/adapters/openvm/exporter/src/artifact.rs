//! Readable provenance and lowering report for a pinned upstream capture.
//!
//! This module only emits reports. The imported contract is the ordinary
//! relation-bundle carrier, independently admitted by the native compiler and
//! runtime; this report is evidence about its origin, not an input authority.
use crate::arena::{Arena, hex_sha256};
use crate::bundle::{bundle, identity};
use crate::model::{DagNode, Export, Height, Input, RowClass, VariableKind};
use crate::refusal::Result;
use serde_json::{Value, json};
pub const EXPORT_FORMAT: &str = "zkc.openvm-relation-export/0";
pub const EXPORTER: &str = concat!("zkc-openvm-relation ", env!("CARGO_PKG_VERSION"));

pub const OPENVM_REPOSITORY: &str = "https://github.com/openvm-org/openvm";
pub const OPENVM_COMMIT: &str = "f08bf2836409f3c0a5f6b6cfe73eb177a8a3e8c8";
pub const STARK_BACKEND_REPOSITORY: &str = "https://github.com/openvm-org/stark-backend";
/// Tag `v2.0.1`, the commit the adapter's lockfile records for `branch = "main"`.
pub const STARK_BACKEND_COMMIT: &str = "362c7ad8c6b042b320471a137e3eadec7ec69a44";
/// The commit OpenVM's own lockfile selects; its tree is identical to the tag.
pub const STARK_BACKEND_LOCKED_BY_OPENVM: &str = "d667af5929d0ea9e5194adf639d6bddeb8c10f9a";
pub const UPSTREAM_LICENSE: &str = "MIT OR Apache-2.0";
pub const PLONKY3_VERSION: &str = "0.4.3";

/// One sorted top-level field per line, each value in compact JSON.
pub fn canonical(value: &Value) -> String {
    let Value::Object(map) = value else {
        return format!("{value}\n");
    };
    let fields: Vec<String> = map
        .iter()
        .map(|(key, value)| format!("  {}: {value}", Value::String(key.clone())))
        .collect();
    format!("{{\n{}\n}}\n", fields.join(",\n"))
}

fn kind_value(kind: VariableKind) -> Value {
    json!(kind.name())
}

fn dag_node_value(node: &DagNode) -> Value {
    match node {
        DagNode::Variable {
            kind,
            part,
            offset,
            index,
        } => json!(["variable", kind_value(*kind), part, offset, index]),
        DagNode::IsFirstRow => json!(["is_first_row"]),
        DagNode::IsLastRow => json!(["is_last_row"]),
        DagNode::IsTransition => json!(["is_transition"]),
        DagNode::Constant(c) => json!(["constant", c.to_string()]),
        DagNode::Add(l, r, d) => json!(["add", l, r, d]),
        DagNode::Sub(l, r, d) => json!(["sub", l, r, d]),
        DagNode::Neg(x, d) => json!(["neg", x, d]),
        DagNode::Mul(l, r, d) => json!(["mul", l, r, d]),
    }
}

fn height_value(h: Height) -> Value {
    match h {
        Height::Fixed(n) => json!(["fixed", n]),
        Height::Config => json!(["config"]),
        Height::Instance => json!(["instance"]),
    }
}

fn arena_value(arena: &Arena) -> Value {
    serde_json::from_str(&arena.canonical()).expect("canonical arena is JSON")
}

impl Export {
    /// The export as a JSON object with the derived bundle identity.
    pub fn to_value(&self) -> Result<Value> {
        let (_, bundle_sha256) = identity(&bundle(self)?);
        let airs: Vec<Value> = self
            .airs
            .iter()
            .map(|air| {
                json!({
                    "name": air.name,
                    "upstream_type": air.upstream_type,
                    "required": air.required,
                    "groups": air.groups.iter().map(|g| json!([g.name, g.authority, g.width])).collect::<Vec<_>>(),
                    "num_public_values": air.num_public_values,
                    "column_names": air.column_names,
                    "need_rot": air.need_rot,
                    "max_constraint_degree": air.max_constraint_degree,
                    "unused_variables": air.unused_variables.iter().map(|(k, p, o, i)| json!([kind_value(*k), p, o, i])).collect::<Vec<_>>(),
                    "dag": {
                        "nodes": air.dag.nodes.iter().map(dag_node_value).collect::<Vec<_>>(),
                        "constraint_idx": air.dag.constraint_idx,
                        "interactions": air.dag.interactions.iter().map(|x| json!([x.bus, x.message, x.count, x.count_weight])).collect::<Vec<_>>(),
                    },
                    "recorder_constraints": air.recorder_constraints,
                    "recorder_degrees": air.recorder_degrees,
                    "inputs": air.inputs.iter().map(|i| match *i {
                        Input::Read { group, offset, column } => json!(["read", group, offset, column]),
                        Input::Public(slot) => json!(["public", slot]),
                    }).collect::<Vec<_>>(),
                    "arena": arena_value(&air.arena),
                    "arena_sha256": air.arena.sha256(),
                    "assertions": air.assertions.iter().map(|a| json!([a.constraint, a.scope.name(), a.output, a.degree])).collect::<Vec<_>>(),
                    "vacuous": air.vacuous.iter().map(|(c, class)| json!([c, match class { RowClass::First => "first", RowClass::Interior => "interior", RowClass::Last => "last" }])).collect::<Vec<_>>(),
                    "interactions": air.interactions.iter().map(|x| json!([x.bus, x.message, x.count, x.count_weight, x.degree])).collect::<Vec<_>>(),
                    "height": height_value(air.height),
                })
            })
            .collect();
        Ok(json!({
            "format": EXPORT_FORMAT,
            "exporter": EXPORTER,
            "field": crate::field::FIELD_IDENTITY,
            "upstream": {
                "openvm": {"repository": OPENVM_REPOSITORY, "commit": OPENVM_COMMIT, "license": UPSTREAM_LICENSE},
                "stark_backend": {"repository": STARK_BACKEND_REPOSITORY, "commit": STARK_BACKEND_COMMIT, "tag": "v2.0.1", "openvm_locked_commit": STARK_BACKEND_LOCKED_BY_OPENVM, "license": UPSTREAM_LICENSE},
                "plonky3": PLONKY3_VERSION,
            },
            "parameters": {
                "timestamp_max_bits": self.parameters.timestamp_max_bits,
                "range_max_bits": self.parameters.range_max_bits,
                "pc_base": self.parameters.pc_base,
                "step_limit": self.parameters.step_limit,
            },
            "system": {
                "l_skip": self.l_skip,
                "max_constraint_degree": self.max_constraint_degree,
                "max_interaction_count": self.max_interaction_count,
                "log_max_message_length": self.log_max_message_length,
            },
            "selector_law": "row-indicator; heights at least two",
            "read_model": "cyclic",
            "buses": self.buses.iter().map(|b| json!({"name": b.name, "index": b.index, "arity": b.arity})).collect::<Vec<_>>(),
            "publics": self.publics.iter().map(|(n, a, i)| json!([n, a, i])).collect::<Vec<_>>(),
            "airs": airs,
            "trace_height_constraints": self.trace_height_constraints.iter().map(|c| json!([c.coefficients, c.threshold])).collect::<Vec<_>>(),
            "vk_pre_hash": self.vk_pre_hash,
            "bundle_sha256": bundle_sha256,
        }))
    }

    pub fn canonical_text(&self) -> Result<String> {
        Ok(canonical(&self.to_value()?))
    }

    pub fn sha256(&self) -> Result<String> {
        Ok(hex_sha256(self.canonical_text()?.as_bytes()))
    }
}
