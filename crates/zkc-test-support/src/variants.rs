//! Test fixture encoding, independent of every production reader.
use serde_json::{Value, json};
use std::collections::BTreeMap;

pub fn tree(spelling: &str) -> Value {
    let bytes = crate::unhex(&spelling[8..]);
    let raw: Value = serde_json::from_slice(&bytes).unwrap();
    let mut nodes: Vec<Value> = Vec::new();
    for node in raw[1].as_array().unwrap() {
        nodes.push(match node {
            Value::String(_) => node.clone(),
            Value::Array(refs) => Value::Array(
                refs.iter()
                    .map(|r| nodes[r.as_str().unwrap().parse::<usize>().unwrap()].clone())
                    .collect(),
            ),
            _ => panic!("fixture graph node"),
        });
    }
    nodes.pop().unwrap()
}

pub fn encode_tree(tree: Value) -> String {
    fn intern(tree: Value, nodes: &mut Vec<Value>, ids: &mut BTreeMap<String, usize>) -> usize {
        let node = match tree {
            Value::Array(a) => Value::Array(
                a.into_iter()
                    .map(|v| Value::String(intern(v, nodes, ids).to_string()))
                    .collect(),
            ),
            _ => tree,
        };
        let key = node.to_string();
        if let Some(id) = ids.get(&key) {
            return *id;
        }
        let id = nodes.len();
        nodes.push(node);
        ids.insert(key, id);
        id
    }
    let mut nodes = Vec::new();
    intern(tree, &mut nodes, &mut BTreeMap::new());
    let bytes = serde_json::to_vec(&json!(["zkc.variant/1", nodes])).unwrap();
    format!(
        "variant:{}",
        bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()
    )
}

pub fn logical(nominal: &str, mut arms: Value) -> String {
    for arm in arms.as_array_mut().unwrap() {
        for payload in arm[1].as_array_mut().unwrap() {
            if let Some(s) = payload
                .as_str()
                .filter(|s| s.starts_with("variant:") && !s.contains('@'))
            {
                *payload = tree(s);
            }
        }
    }
    encode_tree(json!([nominal, arms]))
}
