//! Independent admission of the shared, typed ring-expression contract.
//! This module provides no field arithmetic or claim about a consuming protocol.
use crate::interactive::Identity;
use serde_json::{Value, json};

pub const BYTE_LIMIT: usize = 8 * 1024 * 1024;
pub const NODE_LIMIT: usize = 65_536;
pub const OUTPUT_LIMIT: usize = 4_096;
pub const DEGREE_LIMIT: u32 = 1_048_576;
pub const DEPTH_LIMIT: u32 = 1_024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Error(pub &'static str);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Constant(Identity, String),
    Input(usize),
    Add(usize, usize),
    Mul(usize, usize),
    Neg(usize),
    Embed(Identity, usize),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fact {
    pub field: Identity,
    pub degree: u32,
    pub depth: u32,
}
#[derive(Clone, Debug)]
pub struct Expression {
    inputs: Vec<Identity>,
    nodes: Vec<Node>,
    outputs: Vec<usize>,
    facts: Vec<Fact>,
}
fn field(value: &Value) -> Result<Identity> {
    let field = Identity::parse(value.as_str().ok_or(Error("ring-schema"))?)
        .map_err(|_| Error("ring-field"))?;
    modulus(field).ok_or(Error("ring-field"))?;
    Ok(field)
}
fn modulus(field: Identity) -> Option<&'static str> {
    match field {
        Identity::KoalaBear | Identity::KoalaBearExt8 => Some("2130706433"),
        Identity::Bls12381Fr => {
            Some("52435875175126190479447740508185965837690552500527637822603658699938581184513")
        }
        Identity::Bn254Fr => {
            Some("21888242871839275222246405745257275088548364400416034343698204186575808495617")
        }
        Identity::Ristretto255Scalar => {
            Some("7237005577332262213973186563042994240857116359379907606001950938285454250989")
        }
        _ => None,
    }
}
fn literal(field: Identity, value: &str) -> bool {
    let Some(modulus) = modulus(field) else {
        return false;
    };
    !value.is_empty()
        && value.bytes().all(|b| b.is_ascii_digit())
        && (value.len() == 1 || !value.starts_with('0'))
        && (value.len() < modulus.len() || (value.len() == modulus.len() && value < modulus))
}
fn index(value: &Value) -> Result<usize> {
    value
        .as_u64()
        .filter(|x| *x <= u32::MAX as u64)
        .map(|x| x as usize)
        .ok_or(Error("ring-schema"))
}
fn array(value: &Value) -> Result<&[Value]> {
    value
        .as_array()
        .map(Vec::as_slice)
        .ok_or(Error("ring-schema"))
}

/// Bound bytes and nesting before serde allocation. Only arrays, strings and
/// canonical natural number tokens occur in this schema; objects never occur.
pub fn parse_json(text: &str) -> Result<Value> {
    if text.len() > BYTE_LIMIT {
        return Err(Error("ring-limit"));
    }
    let bytes = text.as_bytes();
    let (mut i, mut depth) = (0, 0usize);
    while i < bytes.len() {
        match bytes[i] {
            b'[' => {
                depth += 1;
                if depth > 16 {
                    return Err(Error("ring-limit"));
                }
                i += 1;
            }
            b']' => {
                depth = depth.checked_sub(1).ok_or(Error("ring-schema"))?;
                i += 1;
            }
            b'"' => {
                i += 1;
                loop {
                    let b = *bytes.get(i).ok_or(Error("ring-schema"))?;
                    i += 1;
                    if b == b'"' {
                        break;
                    }
                    if b == b'\\' {
                        i = i.checked_add(1).ok_or(Error("ring-limit"))?;
                    }
                }
            }
            b'0'..=b'9' => {
                let start = i;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
                if (i - start > 1 && bytes[start] == b'0') || i - start > 10 {
                    return Err(Error("ring-schema"));
                }
            }
            b',' | b' ' | b'\r' | b'\n' | b'\t' => i += 1,
            _ => return Err(Error("ring-schema")),
        }
    }
    if depth != 0 {
        return Err(Error("ring-schema"));
    }
    serde_json::from_str(text).map_err(|_| Error("ring-schema"))
}

impl Expression {
    pub fn parse(text: &str) -> Result<Self> {
        Self::decode(&parse_json(text)?)
    }
    pub fn decode(value: &Value) -> Result<Self> {
        let row = array(value)?;
        if row.len() != 4 || row[0].as_str() != Some("zkc.ring/0") {
            return Err(Error("ring-schema"));
        }
        let (inputs, nodes, outputs) = (array(&row[1])?, array(&row[2])?, array(&row[3])?);
        if inputs.len() > NODE_LIMIT || nodes.len() > NODE_LIMIT || outputs.len() > OUTPUT_LIMIT {
            return Err(Error("ring-limit"));
        }
        let inputs = inputs.iter().map(field).collect::<Result<Vec<_>>>()?;
        let mut decoded = Vec::with_capacity(nodes.len());
        for node in nodes {
            let n = array(node)?;
            let node = match n {
                [tag, f, c] if tag.as_str() == Some("constant") => {
                    Node::Constant(field(f)?, c.as_str().ok_or(Error("ring-schema"))?.into())
                }
                [tag, i] if tag.as_str() == Some("input") => Node::Input(index(i)?),
                [tag, a, b] if tag.as_str() == Some("add") => Node::Add(index(a)?, index(b)?),
                [tag, a, b] if tag.as_str() == Some("mul") => Node::Mul(index(a)?, index(b)?),
                [tag, a] if tag.as_str() == Some("neg") => Node::Neg(index(a)?),
                [tag, f, a] if tag.as_str() == Some("embed") => Node::Embed(field(f)?, index(a)?),
                _ => return Err(Error("ring-schema")),
            };
            decoded.push(node);
        }
        Self::new(
            inputs,
            decoded,
            outputs.iter().map(index).collect::<Result<_>>()?,
        )
    }
    pub fn new(inputs: Vec<Identity>, nodes: Vec<Node>, outputs: Vec<usize>) -> Result<Self> {
        if inputs.len() > NODE_LIMIT || nodes.len() > NODE_LIMIT || outputs.len() > OUTPUT_LIMIT {
            return Err(Error("ring-limit"));
        }
        if inputs.iter().any(|f| modulus(*f).is_none()) {
            return Err(Error("ring-field"));
        }
        let mut facts: Vec<Fact> = Vec::with_capacity(nodes.len());
        for node in &nodes {
            let get = |i: usize| facts.get(i).copied().ok_or(Error("ring-edge"));
            let fact = match node {
                Node::Constant(f, n) => {
                    if modulus(*f).is_none() {
                        return Err(Error("ring-field"));
                    }
                    if !literal(*f, n) {
                        return Err(Error("ring-literal"));
                    }
                    Fact {
                        field: *f,
                        degree: 0,
                        depth: 1,
                    }
                }
                Node::Input(i) => Fact {
                    field: *inputs.get(*i).ok_or(Error("ring-input"))?,
                    degree: 1,
                    depth: 1,
                },
                Node::Add(a, b) | Node::Mul(a, b) => {
                    let (a, b) = (get(*a)?, get(*b)?);
                    if a.field != b.field {
                        return Err(Error("ring-field-mismatch"));
                    }
                    Fact {
                        field: a.field,
                        degree: if matches!(node, Node::Mul(..)) {
                            a.degree.checked_add(b.degree).ok_or(Error("ring-degree"))?
                        } else {
                            a.degree.max(b.degree)
                        },
                        depth: a.depth.max(b.depth) + 1,
                    }
                }
                Node::Neg(a) => {
                    let mut f = get(*a)?;
                    f.depth += 1;
                    f
                }
                Node::Embed(target, a) => {
                    let mut f = get(*a)?;
                    if *target != Identity::KoalaBearExt8 || f.field != Identity::KoalaBear {
                        return Err(Error("ring-embedding"));
                    }
                    f.field = *target;
                    f.depth += 1;
                    f
                }
            };
            if fact.degree > DEGREE_LIMIT {
                return Err(Error("ring-degree"));
            }
            if fact.depth > DEPTH_LIMIT {
                return Err(Error("ring-depth"));
            }
            facts.push(fact);
        }
        let expression = Self {
            inputs,
            nodes,
            outputs,
            facts,
        };
        let positions: Vec<_> = (0..expression.outputs.len()).collect();
        if expression
            .dependencies(&positions)?
            .iter()
            .any(|live| !live)
        {
            return Err(Error("ring-unreachable-node"));
        }
        if expression.canonical().len() > BYTE_LIMIT {
            return Err(Error("ring-limit"));
        }
        Ok(expression)
    }
    pub fn inputs(&self) -> &[Identity] {
        &self.inputs
    }
    pub fn nodes(&self) -> &[Node] {
        &self.nodes
    }
    pub fn outputs(&self) -> &[usize] {
        &self.outputs
    }
    pub fn facts(&self) -> &[Fact] {
        &self.facts
    }
    pub fn encode(&self) -> Value {
        let nodes: Vec<_> = self
            .nodes
            .iter()
            .map(|n| match n {
                Node::Constant(f, n) => json!(["constant", f.name(), n]),
                Node::Input(i) => json!(["input", i]),
                Node::Add(a, b) => json!(["add", a, b]),
                Node::Mul(a, b) => json!(["mul", a, b]),
                Node::Neg(a) => json!(["neg", a]),
                Node::Embed(f, a) => json!(["embed", f.name(), a]),
            })
            .collect();
        json!([
            "zkc.ring/0",
            self.inputs.iter().map(|f| f.name()).collect::<Vec<_>>(),
            nodes,
            self.outputs
        ])
    }
    pub fn canonical(&self) -> String {
        self.encode().to_string()
    }
    pub fn degrees(&self, weights: &[u32]) -> Result<Vec<u32>> {
        if weights.len() != self.inputs.len() {
            return Err(Error("ring-input"));
        }
        if weights.iter().any(|w| *w > DEGREE_LIMIT) {
            return Err(Error("ring-degree"));
        }
        let mut degree: Vec<u32> = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let d = match *node {
                Node::Constant(..) => 0,
                Node::Input(i) => weights[i],
                Node::Add(a, b) => degree[a].max(degree[b]),
                Node::Mul(a, b) => degree[a]
                    .checked_add(degree[b])
                    .ok_or(Error("ring-degree"))?,
                Node::Neg(a) | Node::Embed(_, a) => degree[a],
            };
            if d > DEGREE_LIMIT {
                return Err(Error("ring-degree"));
            }
            degree.push(d);
        }
        Ok(degree)
    }
    fn dependencies(&self, positions: &[usize]) -> Result<Vec<bool>> {
        let mut live = vec![false; self.nodes.len()];
        for p in positions {
            let i = *self.outputs.get(*p).ok_or(Error("ring-output"))?;
            *live.get_mut(i).ok_or(Error("ring-output"))? = true;
        }
        for i in (0..live.len()).rev() {
            if !live[i] {
                continue;
            }
            match self.nodes[i] {
                Node::Add(a, b) | Node::Mul(a, b) => {
                    live[a] = true;
                    live[b] = true;
                }
                Node::Neg(a) | Node::Embed(_, a) => live[a] = true,
                _ => (),
            }
        }
        Ok(live)
    }
    pub fn used_inputs(&self, positions: &[usize]) -> Result<Vec<usize>> {
        let live = self.dependencies(positions)?;
        let mut used = vec![false; self.inputs.len()];
        for (i, n) in self.nodes.iter().enumerate() {
            if live[i]
                && let Node::Input(j) = n
            {
                used[*j] = true;
            }
        }
        Ok(used
            .iter()
            .enumerate()
            .filter_map(|(i, b)| b.then_some(i))
            .collect())
    }
    /// Prepare a compact schedule once. Runtime work then scales with selected
    /// nodes rather than scanning every unselected branch on every trace row.
    pub fn select(&self, positions: &[usize]) -> Result<Self> {
        let live = self.dependencies(positions)?;
        let mut remap = vec![0; self.nodes.len()];
        let mut nodes = Vec::new();
        for (i, n) in self.nodes.iter().enumerate() {
            if !live[i] {
                continue;
            }
            remap[i] = nodes.len();
            nodes.push(match n {
                Node::Constant(..) | Node::Input(_) => n.clone(),
                Node::Add(a, b) => Node::Add(remap[*a], remap[*b]),
                Node::Mul(a, b) => Node::Mul(remap[*a], remap[*b]),
                Node::Neg(a) => Node::Neg(remap[*a]),
                Node::Embed(f, a) => Node::Embed(*f, remap[*a]),
            });
        }
        Self::new(
            self.inputs.clone(),
            nodes,
            positions.iter().map(|p| remap[self.outputs[*p]]).collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn independent_schema_and_weighted_analysis() {
        let text = r#"["zkc.ring/0",["koala-bear","koala-bear.ext8-binomial3"],[["input",0],["embed","koala-bear.ext8-binomial3",0],["input",1],["mul",1,2]],[3,2]]"#;
        let e = Expression::parse(text).unwrap();
        assert_eq!(e.canonical(), text);
        assert_eq!(e.degrees(&[0, 7]).unwrap(), [0, 0, 7, 7]);
        assert_eq!(e.used_inputs(&[1]).unwrap(), [1]);
        assert_eq!(e.select(&[1]).unwrap().nodes(), [Node::Input(1)]);
        assert_eq!(e.degrees(&[DEGREE_LIMIT, 1]), Err(Error("ring-degree")));
        for invalid in [
            text.replace("[3,2]", "[4,2]"),
            text.replace("[3,2]", "[3.0,2]"),
            text.replace("[3,2]", "[03,2]"),
            text.replace("\"mul\",1,2", "\"mul\",0,2"),
            text.replace("\"input\",0", "\"input\",2"),
            text.replace("[3,2]", "[2]"),
            text.replace("\"mul\",1,2", "\"mul\",1,3"),
        ] {
            assert!(Expression::parse(&invalid).is_err(), "{invalid}");
        }
        assert!(Expression::parse(r#"["zkc.ring/0",[],[],[]]"#).is_ok());
        assert!(
            Expression::parse(r#"["zkc.ring/0",[],[["constant","koala-bear","2130706433"]],[0]]"#)
                .is_err()
        );
    }
}
