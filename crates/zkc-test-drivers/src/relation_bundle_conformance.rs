//! Bounded test transport for independent bundle admission and native field arithmetic.
use p3_field::{BasedVectorSpace, PrimeField32};
use serde_json::{Value, json};
use std::io::{self, Read};
use zkc_backends::{KoalaBear, KoalaBearExt8, plonky3};
use zkc_runtime::interactive::Identity;
use zkc_runtime::relation::{self, Algebra, Bundle, ChannelKind, Error};

type Result<T> = std::result::Result<T, Error>;
struct Native;
impl Algebra for Native {
    type Value = KoalaBearExt8;
    fn value(&self, field: Identity, coordinates: &[String]) -> Result<Self::Value> {
        let width = match field {
            Identity::KoalaBear => 1,
            Identity::KoalaBearExt8 => 8,
            _ => return Err(Error("test-field")),
        };
        if coordinates.len() != width {
            return Err(Error("test-coordinate"));
        }
        let mut values = [KoalaBear::new(0); 8];
        for (out, text) in values.iter_mut().zip(coordinates) {
            *out = plonky3::parse_decimal(text).map_err(|_| Error("test-coordinate"))?;
        }
        Ok(KoalaBearExt8::from(values))
    }
    fn constant(&self, field: Identity, text: &str) -> Result<Self::Value> {
        if !matches!(field, Identity::KoalaBear | Identity::KoalaBearExt8) {
            return Err(Error("test-field"));
        }
        Ok(plonky3::parse_decimal(text)
            .map_err(|_| Error("test-coordinate"))?
            .into())
    }
    fn add(&self, _: Identity, a: &Self::Value, b: &Self::Value) -> Self::Value {
        *a + *b
    }
    fn mul(&self, _: Identity, a: &Self::Value, b: &Self::Value) -> Self::Value {
        *a * *b
    }
    fn neg(&self, _: Identity, a: &Self::Value) -> Self::Value {
        -*a
    }
    fn embed(&self, from: Identity, to: Identity, a: &Self::Value) -> Result<Self::Value> {
        if from != Identity::KoalaBear || to != Identity::KoalaBearExt8 {
            return Err(Error("test-embedding"));
        }
        Ok(*a)
    }
    fn coordinates(&self, field: Identity, value: &Self::Value) -> Vec<String> {
        let values: &[KoalaBear] = value.as_basis_coefficients_slice();
        values[..if field == Identity::KoalaBear { 1 } else { 8 }]
            .iter()
            .map(|v| v.as_canonical_u32().to_string())
            .collect()
    }
}
fn scalar(values: &[String]) -> Value {
    if values.len() == 1 {
        json!(values[0])
    } else {
        json!(values)
    }
}
fn evaluate(text: &str) -> Result<Value> {
    let input = relation::parse_json(text, 1024 * 1024, "bundle-data-schema", "bundle-data-limit")?;
    let rows = input
        .as_array()
        .filter(|a| a.len() == 4)
        .ok_or(Error("test-schema"))?;
    let bundle = Bundle::decode(&rows[0])?;
    let config = bundle.decode_configuration(&rows[1])?;
    let instance = bundle.decode_instance(&rows[2])?;
    let witness = bundle.decode_witness(&rows[3])?;
    let result = bundle.evaluate(&config, &instance, &witness, &Native)?;
    let residuals: Vec<_> = result
        .residuals
        .iter()
        .map(|r| json!([r.table, r.assertion, r.row, scalar(&r.value)]))
        .collect();
    let balances: Vec<_> = result
        .balances
        .iter()
        .map(|b| {
            let tuple: Vec<_> = b.tuple.iter().map(|v| scalar(v)).collect();
            match b.kind {
                ChannelKind::FieldBalance => json!([
                    "field-balance",
                    b.channel,
                    b.local,
                    tuple,
                    scalar(&b.sum),
                    b.balanced
                ]),
                ChannelKind::Multiset => json!([
                    "multiset", b.channel, b.local, tuple, b.push, b.pull, b.balanced
                ]),
            }
        })
        .collect();
    Ok(
        json!({"accepted":true, "identity":bundle.identity(), "bundle":bundle.encode(),
        "result":{"satisfied":result.satisfied, "work":result.work, "residuals":residuals,
            "balances":balances, "range_failures":result.range_failures}}),
    )
}
fn main() {
    let mut line = Vec::new();
    for byte in io::stdin().lock().bytes() {
        let byte = byte.expect("test input");
        if byte != b'\n' {
            assert!(line.len() < 1024 * 1024, "test transport limit");
            line.push(byte);
            continue;
        }
        let result = std::str::from_utf8(&line)
            .map_err(|_| Error("bundle-data-schema"))
            .and_then(evaluate);
        let report = result.unwrap_or_else(|e| json!({"accepted":false, "error":e.0}));
        println!("{report}");
        line.clear();
    }
    assert!(line.is_empty(), "incomplete test input");
}
