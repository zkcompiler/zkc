//! The KoalaBear fragment of the shared `zkc.ring/0` arena: a hash-consing
//! builder with the algebraic simplifications of the upstream verifying-key
//! DAG builder, canonical encoding, identity and a reference interpreter.
//!
//! Formation follows `docs/spec/domains/ring-expressions.md`. The adapter
//! emits KoalaBear inputs and constants only and never needs an embedding.
//! The simplifications are the ones `SymbolicDagBuilder::add_expr` in the
//! pinned `air_builders/symbolic/dag.rs` applies: constant folding, `x + 0`,
//! `x - 0`, `x * 1`, `x * 0` and `-c`. The ring has no subtraction, so
//! `x - y` is `add(x, neg(y))`. Encoding and bounds follow the pattern of
//! `compiler/adapters/plonky3/exporter/src/arena.rs`.

use crate::field::{F, FIELD_IDENTITY, MODULUS};
use crate::refusal::{Result, ensure, refuse};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use sha2::{Digest, Sha256};
use std::collections::HashMap;

pub const FORMAT: &str = "zkc.ring/0";
pub const NODE_LIMIT: usize = 65_536;
pub const OUTPUT_LIMIT: usize = 4_096;
pub const DEPTH_LIMIT: u32 = 1_024;
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

/// Hash-consing builder over a growing node list. Node indices it returns
/// are stable until `finish` renumbers the reachable nodes.
#[derive(Clone, Debug, Default)]
pub struct Builder {
    nodes: Vec<Node>,
    index: HashMap<Node, usize>,
}

impl Builder {
    pub fn new() -> Self {
        Self::default()
    }

    fn intern(&mut self, node: Node) -> usize {
        if let Some(&i) = self.index.get(&node) {
            return i;
        }
        let i = self.nodes.len();
        self.nodes.push(node);
        self.index.insert(node, i);
        i
    }

    pub fn constant(&mut self, c: F) -> usize {
        self.intern(Node::Constant(c.as_canonical_u32()))
    }

    pub fn input(&mut self, slot: usize) -> usize {
        self.intern(Node::Input(slot))
    }

    pub fn as_constant(&self, i: usize) -> Option<F> {
        match self.nodes[i] {
            Node::Constant(c) => Some(F::from_u32(c)),
            _ => None,
        }
    }

    pub fn add(&mut self, a: usize, b: usize) -> usize {
        match (self.as_constant(a), self.as_constant(b)) {
            (Some(x), Some(y)) => self.constant(x + y),
            (Some(x), _) if x == F::ZERO => b,
            (_, Some(y)) if y == F::ZERO => a,
            _ => self.intern(Node::Add(a, b)),
        }
    }

    pub fn mul(&mut self, a: usize, b: usize) -> usize {
        match (self.as_constant(a), self.as_constant(b)) {
            (Some(x), Some(y)) => self.constant(x * y),
            (Some(x), _) if x == F::ZERO => a,
            (_, Some(y)) if y == F::ZERO => b,
            (Some(x), _) if x == F::ONE => b,
            (_, Some(y)) if y == F::ONE => a,
            _ => self.intern(Node::Mul(a, b)),
        }
    }

    pub fn neg(&mut self, a: usize) -> usize {
        match self.as_constant(a) {
            Some(x) => self.constant(-x),
            None => self.intern(Node::Neg(a)),
        }
    }

    pub fn sub(&mut self, a: usize, b: usize) -> usize {
        match (self.as_constant(a), self.as_constant(b)) {
            (Some(x), Some(y)) => self.constant(x - y),
            (_, Some(y)) if y == F::ZERO => a,
            _ => {
                let n = self.neg(b);
                self.add(a, n)
            }
        }
    }

    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }

    /// Keep the nodes the selected outputs reach, renumbered in order, and
    /// form the arena. Returns the arena and the map from builder indices to
    /// arena indices for the retained nodes.
    pub fn finish(&self, inputs: usize, outputs: &[usize]) -> Result<(Arena, Vec<Option<usize>>)> {
        let mut live = vec![false; self.nodes.len()];
        for &o in outputs {
            ensure(o < self.nodes.len(), "openvm-arena-output", || {
                format!("output {o}")
            })?;
            live[o] = true;
        }
        for i in (0..self.nodes.len()).rev() {
            if live[i] {
                for child in self.nodes[i].children() {
                    live[child] = true;
                }
            }
        }
        let mut map = vec![None; self.nodes.len()];
        let mut nodes = Vec::new();
        for (i, node) in self.nodes.iter().enumerate() {
            if !live[i] {
                continue;
            }
            let renumbered = match *node {
                Node::Add(a, b) => Node::Add(map[a].unwrap(), map[b].unwrap()),
                Node::Mul(a, b) => Node::Mul(map[a].unwrap(), map[b].unwrap()),
                Node::Neg(a) => Node::Neg(map[a].unwrap()),
                other => other,
            };
            map[i] = Some(nodes.len());
            nodes.push(renumbered);
        }
        let outputs = outputs.iter().map(|o| map[*o].unwrap()).collect();
        Ok((Arena::new(inputs, nodes, outputs)?, map))
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
    /// Check formation as the shared contract states it.
    pub fn new(inputs: usize, nodes: Vec<Node>, outputs: Vec<usize>) -> Result<Self> {
        ensure(
            inputs <= NODE_LIMIT && nodes.len() <= NODE_LIMIT && outputs.len() <= OUTPUT_LIMIT,
            "openvm-arena-limit",
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
                    ensure(c < MODULUS, "openvm-arena-literal", || format!("node {i}"))?
                }
                Node::Input(slot) => {
                    ensure(slot < inputs, "openvm-arena-input", || format!("node {i}"))?
                }
                _ => {
                    for child in node.children() {
                        ensure(child < i, "openvm-arena-edge", || {
                            format!("node {i} refers to {child}")
                        })?;
                        d = d.max(depth[child] + 1);
                    }
                }
            }
            ensure(d <= DEPTH_LIMIT, "openvm-arena-limit", || {
                format!("node {i} has depth {d}")
            })?;
            depth.push(d);
        }
        for (position, output) in outputs.iter().enumerate() {
            ensure(*output < nodes.len(), "openvm-arena-output", || {
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
                "openvm-arena-unreachable",
                format!("node {dead} is not reachable from an output"),
            );
        }
        ensure(
            arena.canonical().len() <= BYTE_LIMIT,
            "openvm-arena-limit",
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

    /// Weighted degree of every node; weights are per input slot.
    pub fn degrees(&self, weights: &[u64]) -> Result<Vec<u64>> {
        ensure(weights.len() == self.inputs, "openvm-arena-input", || {
            "weight count".into()
        })?;
        let mut degree: Vec<u64> = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            degree.push(match *node {
                Node::Constant(_) => 0,
                Node::Input(s) => weights[s],
                Node::Add(a, b) => degree[a].max(degree[b]),
                Node::Mul(a, b) => degree[a].saturating_add(degree[b]),
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

    /// Input slots each output position reads.
    pub fn reads(&self, position: usize) -> Vec<usize> {
        let live = self.live(&[position]);
        let mut slots: Vec<usize> = self
            .nodes
            .iter()
            .zip(&live)
            .filter_map(|(node, l)| match (node, l) {
                (Node::Input(s), true) => Some(*s),
                _ => None,
            })
            .collect();
        slots.sort_unstable();
        slots.dedup();
        slots
    }

    /// Reference substitution over KoalaBear: the adapter's own reading of the
    /// arena, independent of the native providers and of upstream.
    pub fn evaluate(&self, input: impl Fn(usize) -> F) -> Vec<F> {
        let mut values: Vec<F> = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let value = match *node {
                Node::Constant(c) => F::from_u32(c),
                Node::Input(s) => input(s),
                Node::Add(a, b) => values[a] + values[b],
                Node::Mul(a, b) => values[a] * values[b],
                Node::Neg(a) => -values[a],
            };
            values.push(value);
        }
        self.outputs.iter().map(|o| values[*o]).collect()
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
    fn builder_folds_like_the_upstream_dag_builder_and_forms_a_canonical_arena() {
        let mut b = Builder::new();
        let x = b.input(0);
        let zero = b.constant(F::ZERO);
        let one = b.constant(F::ONE);
        assert_eq!(b.add(x, zero), x);
        assert_eq!(b.add(zero, x), x);
        assert_eq!(b.mul(x, one), x);
        assert_eq!(b.mul(one, x), x);
        assert_eq!(b.mul(x, zero), zero);
        assert_eq!(b.mul(zero, x), zero);
        assert_eq!(b.sub(x, zero), x);
        let two = b.constant(F::TWO);
        let three = b.add(one, two);
        let negative_one = b.neg(one);
        assert_eq!(b.as_constant(three), Some(F::from_u32(3)));
        assert_eq!(b.as_constant(negative_one), Some(F::NEG_ONE));
        let y = b.input(1);
        let s = b.sub(x, y);
        let s_again = b.sub(x, y);
        assert_eq!(s, s_again, "hash-consing shares structurally equal nodes");
        let (arena, map) = b.finish(2, &[s, x]).unwrap();
        assert_eq!(map[s], Some(arena.outputs()[0]));
        assert_eq!(
            arena.canonical(),
            r#"["zkc.ring/0",["koala-bear","koala-bear"],[["input",0],["input",1],["neg",1],["add",0,2]],[3,0]]"#
        );
        let values = arena.evaluate(|slot| F::from_u32([5, 7][slot]));
        assert_eq!(
            values,
            vec![F::from_u32(5) - F::from_u32(7), F::from_u32(5)]
        );
        assert_eq!(arena.degrees(&[1, 1]).unwrap(), vec![1, 1, 1, 1]);
        assert_eq!(arena.reads(0), vec![0, 1]);
        assert_eq!(arena.reads(1), vec![0]);
    }

    #[test]
    fn formation_refusals() {
        let cases = [
            (
                Arena::new(1, vec![Node::Input(0), Node::Input(0)], vec![1]),
                "openvm-arena-unreachable",
            ),
            (
                Arena::new(1, vec![Node::Add(0, 0)], vec![0]),
                "openvm-arena-edge",
            ),
            (
                Arena::new(1, vec![Node::Input(1)], vec![0]),
                "openvm-arena-input",
            ),
            (
                Arena::new(0, vec![Node::Constant(MODULUS)], vec![0]),
                "openvm-arena-literal",
            ),
            (
                Arena::new(0, vec![Node::Constant(1)], vec![1]),
                "openvm-arena-output",
            ),
        ];
        for (result, id) in cases {
            assert_eq!(result.unwrap_err().id, id);
        }
    }
}
