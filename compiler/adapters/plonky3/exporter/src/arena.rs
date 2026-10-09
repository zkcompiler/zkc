//! The KoalaBear fragment of the shared `zkc.ring/0` arena: encoding, formation,
//! identity, weighted degree and a generic reference interpreter.
//!
//! Formation follows `docs/spec/domains/ring-expressions.md`. The adapter only
//! emits KoalaBear inputs and constants and never needs an embedding, so this
//! decoder refuses every other field identity and the `embed` row.

use crate::field::{F, FIELD_IDENTITY, MODULUS};
use crate::refusal::{Result, ensure, refuse};
use p3_field::PrimeCharacteristicRing;
use serde_json::Value;
use sha2::{Digest, Sha256};

pub const FORMAT: &str = "zkc.ring/0";
pub const NODE_LIMIT: usize = 65_536;
pub const OUTPUT_LIMIT: usize = 4_096;
pub const DEPTH_LIMIT: u32 = 1_024;
pub const DEGREE_LIMIT: u64 = 1_048_576;
pub const BYTE_LIMIT: usize = 8 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Node {
    /// Canonical representative strictly below the modulus.
    Constant(u32),
    Input(usize),
    Add(usize, usize),
    Mul(usize, usize),
    Neg(usize),
}

impl Node {
    pub fn children(&self) -> impl Iterator<Item = usize> {
        let (a, b) = match *self {
            Node::Constant(_) | Node::Input(_) => (None, None),
            Node::Add(a, b) | Node::Mul(a, b) => (Some(a), Some(b)),
            Node::Neg(a) => (Some(a), None),
        };
        a.into_iter().chain(b)
    }
}

/// A formed arena: every input has the KoalaBear sort.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arena {
    inputs: usize,
    nodes: Vec<Node>,
    outputs: Vec<usize>,
}

impl Arena {
    /// Check formation exactly as the shared contract states it.
    pub fn new(inputs: usize, nodes: Vec<Node>, outputs: Vec<usize>) -> Result<Self> {
        ensure(
            inputs <= NODE_LIMIT && nodes.len() <= NODE_LIMIT && outputs.len() <= OUTPUT_LIMIT,
            "plonky3-arena-limit",
            || {
                format!(
                    "{inputs} inputs, {} nodes, {} outputs",
                    nodes.len(),
                    outputs.len()
                )
            },
        )?;
        let mut depth: Vec<u32> = Vec::with_capacity(nodes.len());
        for (i, node) in nodes.iter().enumerate() {
            let mut d = 1;
            match *node {
                Node::Constant(c) => {
                    ensure(c < MODULUS, "plonky3-arena-literal", || format!("node {i}"))?
                }
                Node::Input(slot) => {
                    ensure(slot < inputs, "plonky3-arena-input", || format!("node {i}"))?
                }
                _ => {
                    for child in node.children() {
                        ensure(child < i, "plonky3-arena-edge", || {
                            format!("node {i} refers to {child}")
                        })?;
                        d = d.max(depth[child] + 1);
                    }
                }
            }
            ensure(d <= DEPTH_LIMIT, "plonky3-arena-limit", || {
                format!("node {i} has depth {d}")
            })?;
            depth.push(d);
        }
        for (position, output) in outputs.iter().enumerate() {
            ensure(*output < nodes.len(), "plonky3-arena-output", || {
                format!("output {position}")
            })?;
        }
        let arena = Self {
            inputs,
            nodes,
            outputs,
        };
        let live = arena.live(&(0..arena.outputs.len()).collect::<Vec<_>>());
        if let Some(dead) = live.iter().position(|l| !l) {
            return refuse(
                "plonky3-arena-unreachable",
                format!("node {dead} is not reachable from an output"),
            );
        }
        let formation = arena.degrees(&vec![1; inputs])?;
        ensure(
            formation.iter().all(|d| *d <= DEGREE_LIMIT),
            "plonky3-arena-limit",
            || "formation degree".into(),
        )?;
        ensure(
            arena.canonical().len() <= BYTE_LIMIT,
            "plonky3-arena-limit",
            || "canonical encoding size".into(),
        )?;
        Ok(arena)
    }

    pub fn inputs(&self) -> usize {
        self.inputs
    }
    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }
    pub fn outputs(&self) -> &[usize] {
        &self.outputs
    }

    /// Byte-exact canonical text: compact JSON arrays, as the native decoder re-encodes.
    pub fn canonical(&self) -> String {
        let mut text = String::with_capacity(32 + 24 * self.nodes.len());
        text.push_str("[\"zkc.ring/0\",[");
        for i in 0..self.inputs {
            if i > 0 {
                text.push(',');
            }
            text.push('"');
            text.push_str(FIELD_IDENTITY);
            text.push('"');
        }
        text.push_str("],[");
        for (i, node) in self.nodes.iter().enumerate() {
            if i > 0 {
                text.push(',');
            }
            let row = match *node {
                Node::Constant(c) => format!("[\"constant\",\"{FIELD_IDENTITY}\",\"{c}\"]"),
                Node::Input(s) => format!("[\"input\",{s}]"),
                Node::Add(a, b) => format!("[\"add\",{a},{b}]"),
                Node::Mul(a, b) => format!("[\"mul\",{a},{b}]"),
                Node::Neg(a) => format!("[\"neg\",{a}]"),
            };
            text.push_str(&row);
        }
        text.push_str("],[");
        for (i, output) in self.outputs.iter().enumerate() {
            if i > 0 {
                text.push(',');
            }
            text.push_str(&output.to_string());
        }
        text.push_str("]]");
        text
    }

    /// Structural identity: SHA-256 of the canonical encoding, lowercase hex.
    pub fn sha256(&self) -> String {
        hex_sha256(self.canonical().as_bytes())
    }

    /// Decode a parsed `zkc.ring/0` value with exact row arities.
    pub fn decode(value: &Value) -> Result<Self> {
        let schema = |what: &str| refuse::<Self>("plonky3-arena-schema", what.to_string());
        let Some([format, inputs, nodes, outputs]) = value.as_array().map(Vec::as_slice) else {
            return schema("arena row");
        };
        if format.as_str() != Some(FORMAT) {
            return schema("format");
        }
        let (Some(inputs), Some(nodes), Some(outputs)) =
            (inputs.as_array(), nodes.as_array(), outputs.as_array())
        else {
            return schema("arena sections");
        };
        ensure(
            inputs.len() <= NODE_LIMIT
                && nodes.len() <= NODE_LIMIT
                && outputs.len() <= OUTPUT_LIMIT,
            "plonky3-arena-limit",
            || "arena section length".into(),
        )?;
        for input in inputs {
            ensure(
                input.as_str() == Some(FIELD_IDENTITY),
                "plonky3-arena-field",
                || format!("input sort {input} is not {FIELD_IDENTITY}"),
            )?;
        }
        let index = |v: &Value| {
            v.as_u64()
                .filter(|x| *x <= u32::MAX as u64)
                .map(|x| x as usize)
                .ok_or_else(|| crate::refusal::Refusal {
                    id: "plonky3-arena-schema",
                    detail: format!("index {v}"),
                })
        };
        let mut decoded = Vec::with_capacity(nodes.len());
        for node in nodes {
            let Some(row) = node.as_array() else {
                return schema("node row");
            };
            let tag = row.first().and_then(Value::as_str);
            decoded.push(match (tag, &row[..]) {
                (Some("constant"), [_, field, literal]) => {
                    ensure(
                        field.as_str() == Some(FIELD_IDENTITY),
                        "plonky3-arena-field",
                        || format!("constant sort {field}"),
                    )?;
                    let literal = literal.as_str().ok_or_else(|| crate::refusal::Refusal {
                        id: "plonky3-arena-schema",
                        detail: "constant literal".into(),
                    })?;
                    let value = crate::field::parse_decimal(literal).map_err(|e| {
                        crate::refusal::Refusal {
                            id: "plonky3-arena-literal",
                            detail: e.detail,
                        }
                    })?;
                    Node::Constant(p3_field::PrimeField32::as_canonical_u32(&value))
                }
                (Some("input"), [_, slot]) => Node::Input(index(slot)?),
                (Some("add"), [_, a, b]) => Node::Add(index(a)?, index(b)?),
                (Some("mul"), [_, a, b]) => Node::Mul(index(a)?, index(b)?),
                (Some("neg"), [_, a]) => Node::Neg(index(a)?),
                (Some("embed"), _) => {
                    return refuse(
                        "plonky3-arena-field",
                        "embedding is outside the KoalaBear fragment",
                    );
                }
                _ => return schema("node row"),
            });
        }
        let outputs = outputs.iter().map(index).collect::<Result<Vec<_>>>()?;
        Self::new(inputs.len(), decoded, outputs)
    }

    /// Weighted degree of every node; weights are per input slot.
    pub fn degrees(&self, weights: &[u64]) -> Result<Vec<u64>> {
        ensure(weights.len() == self.inputs, "plonky3-arena-input", || {
            "weight count".into()
        })?;
        let mut degree: Vec<u64> = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            degree.push(match *node {
                Node::Constant(_) => 0,
                Node::Input(s) => weights[s],
                Node::Add(a, b) => degree[a].max(degree[b]),
                Node::Mul(a, b) => {
                    degree[a]
                        .checked_add(degree[b])
                        .ok_or_else(|| crate::refusal::Refusal {
                            id: "plonky3-arena-limit",
                            detail: "degree overflow".into(),
                        })?
                }
                Node::Neg(a) => degree[a],
            });
        }
        Ok(degree)
    }

    /// Nodes needed by the selected output positions.
    pub fn live(&self, positions: &[usize]) -> Vec<bool> {
        let mut live = vec![false; self.nodes.len()];
        for p in positions {
            live[self.outputs[*p]] = true;
        }
        for i in (0..self.nodes.len()).rev() {
            if live[i] {
                for child in self.nodes[i].children() {
                    live[child] = true;
                }
            }
        }
        live
    }

    /// Reference substitution into any commutative ring with a KoalaBear map.
    /// It is a third, independent reading of the arena used by the adapter's
    /// own checks; it is not the native provider.
    pub fn evaluate<R: PrimeCharacteristicRing + From<F>>(
        &self,
        input: impl Fn(usize) -> R,
    ) -> Vec<R> {
        let mut values: Vec<R> = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let value = match *node {
                Node::Constant(c) => R::from(F::from_u32(c)),
                Node::Input(s) => input(s),
                Node::Add(a, b) => values[a].clone() + values[b].clone(),
                Node::Mul(a, b) => values[a].clone() * values[b].clone(),
                Node::Neg(a) => -values[a].clone(),
            };
            values.push(value);
        }
        self.outputs.iter().map(|o| values[*o].clone()).collect()
    }
}

pub fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_round_trip_and_formation_refusals() {
        let arena = Arena::new(
            2,
            vec![
                Node::Input(0),
                Node::Constant(2_130_706_432),
                Node::Mul(0, 1),
                Node::Input(1),
                Node::Neg(3),
                Node::Add(2, 4),
            ],
            vec![5, 2, 5],
        )
        .unwrap();
        let text = arena.canonical();
        assert_eq!(
            text,
            r#"["zkc.ring/0",["koala-bear","koala-bear"],[["input",0],["constant","koala-bear","2130706432"],["mul",0,1],["input",1],["neg",3],["add",2,4]],[5,2,5]]"#
        );
        let value: Value = serde_json::from_str(&text).unwrap();
        assert_eq!(Arena::decode(&value).unwrap(), arena);
        assert_eq!(
            Arena::new(0, vec![], vec![]).unwrap().canonical(),
            r#"["zkc.ring/0",[],[],[]]"#
        );
        let cases = [
            (
                Arena::new(1, vec![Node::Input(0), Node::Input(0)], vec![1]),
                "plonky3-arena-unreachable",
            ),
            (
                Arena::new(1, vec![Node::Add(0, 0)], vec![0]),
                "plonky3-arena-edge",
            ),
            (
                Arena::new(1, vec![Node::Input(1)], vec![0]),
                "plonky3-arena-input",
            ),
            (
                Arena::new(0, vec![Node::Constant(MODULUS)], vec![0]),
                "plonky3-arena-literal",
            ),
            (
                Arena::new(0, vec![Node::Constant(1)], vec![1]),
                "plonky3-arena-output",
            ),
        ];
        for (result, id) in cases {
            assert_eq!(result.unwrap_err().id, id);
        }
        for text in [
            r#"["zkc.ring/0",["koala-bear.ext8-binomial3"],[["input",0]],[0]]"#,
            r#"["zkc.ring/0",[],[["constant","koala-bear","07"]],[0]]"#,
            r#"["zkc.ring/0",["koala-bear"],[["input",0],["embed","koala-bear.ext8-binomial3",0]],[1]]"#,
            r#"["zkc.ring/0",["koala-bear"],[["input",0,1]],[0]]"#,
            r#"["zkc.ring/1",[],[],[]]"#,
        ] {
            assert!(
                Arena::decode(&serde_json::from_str(text).unwrap()).is_err(),
                "{text}"
            );
        }
    }

    #[test]
    fn depth_limit_is_checked_before_emission() {
        let mut nodes = vec![Node::Input(0)];
        for i in 0..DEPTH_LIMIT as usize {
            nodes.push(Node::Neg(i));
        }
        let last = nodes.len() - 1;
        assert_eq!(
            Arena::new(1, nodes, vec![last]).unwrap_err().id,
            "plonky3-arena-limit"
        );
    }
}
