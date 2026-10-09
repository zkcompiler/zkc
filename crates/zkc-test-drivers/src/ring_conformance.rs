//! Test transport for the independent Rust arena reader.
use serde_json::json;
use sha2::{Digest, Sha256};
use std::io::{self, BufRead};
use zkc_runtime::ring::Expression;

fn main() {
    for line in io::stdin().lock().lines() {
        let line = line.expect("test input");
        let report = match Expression::parse(&line) {
            Ok(expression) => json!({
                "accepted":true,
                "arena":expression.encode(),
                "identity":format!("{:x}",Sha256::digest(expression.canonical().as_bytes())),
                "facts":expression.facts().iter().map(|f|
                    json!([f.field.name(),f.degree,f.depth])).collect::<Vec<_>>()
            }),
            Err(_) => json!({"accepted":false}),
        };
        println!("{report}");
    }
}
