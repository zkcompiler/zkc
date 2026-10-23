//! Bounded test transport for independent bundle and staged-program admission
//! and evaluation with native field arithmetic.
use p3_field::PrimeField64;
use serde_json::{Value, json};
use std::io::{self, Read};
use zkc_kernels::plonky3::residue::{self, Residue};
use zkc_native::{
    BabyBear, BabyBearExt4, Goldilocks, GoldilocksExt2, KoalaBear, KoalaBearExt4, KoalaBearExt8,
};
use zkc_runtime::relation::{self, Algebra, Bundle, ChannelKind, Error, Staged};
use zkc_runtime::vm::Identity;

type Result<T> = std::result::Result<T, Error>;
struct Native;

fn native_value<E: Residue>(coordinates: &[String]) -> Result<E> {
    if coordinates.len() != E::DIMENSION {
        return Err(Error("test-coordinate"));
    }
    let values = coordinates
        .iter()
        .map(|text| residue::parse_base::<E::Base>(text).map_err(|_| Error("test-coordinate")))
        .collect::<Result<Vec<_>>>()?;
    Ok(E::from_basis_coefficients_fn(|i| values[i]))
}

fn native_coordinates<E: Residue>(value: &E) -> Vec<String> {
    value
        .as_basis_coefficients_slice()
        .iter()
        .map(|v| v.as_canonical_u64().to_string())
        .collect()
}

// Keep each nominal field in its own native carrier: the two KoalaBear
// extensions have different quotient polynomials and cannot share arithmetic.
macro_rules! native_algebra {
    ($($field:ident),+ $(,)?) => {
        #[derive(Clone)]
        enum NativeValue {
            $($field($field),)+
        }

        impl Algebra for Native {
            type Value = NativeValue;

            fn value(&self, field: Identity, coordinates: &[String]) -> Result<Self::Value> {
                match field {
                    $(Identity::$field => native_value(coordinates).map(NativeValue::$field),)+
                    _ => Err(Error("test-field")),
                }
            }

            fn constant(&self, field: Identity, text: &str) -> Result<Self::Value> {
                match field {
                    $(Identity::$field => residue::parse_decimal(text)
                        .map(NativeValue::$field)
                        .map_err(|_| Error("test-coordinate")),)+
                    _ => Err(Error("test-field")),
                }
            }

            fn add(&self, field: Identity, a: &Self::Value, b: &Self::Value) -> Self::Value {
                match (field, a, b) {
                    $((Identity::$field, NativeValue::$field(a), NativeValue::$field(b)) =>
                        NativeValue::$field(*a + *b),)+
                    _ => unreachable!("admitted field operands"),
                }
            }

            fn mul(&self, field: Identity, a: &Self::Value, b: &Self::Value) -> Self::Value {
                match (field, a, b) {
                    $((Identity::$field, NativeValue::$field(a), NativeValue::$field(b)) =>
                        NativeValue::$field(*a * *b),)+
                    _ => unreachable!("admitted field operands"),
                }
            }

            fn neg(&self, field: Identity, a: &Self::Value) -> Self::Value {
                match (field, a) {
                    $((Identity::$field, NativeValue::$field(a)) => NativeValue::$field(-*a),)+
                    _ => unreachable!("admitted field operand"),
                }
            }

            fn embed(&self, from: Identity, to: Identity, a: &Self::Value) -> Result<Self::Value> {
                match (from, to, a) {
                    (Identity::KoalaBear, Identity::KoalaBearExt4, NativeValue::KoalaBear(a)) =>
                        Ok(NativeValue::KoalaBearExt4((*a).into())),
                    (Identity::KoalaBear, Identity::KoalaBearExt8, NativeValue::KoalaBear(a)) =>
                        Ok(NativeValue::KoalaBearExt8((*a).into())),
                    (Identity::BabyBear, Identity::BabyBearExt4, NativeValue::BabyBear(a)) =>
                        Ok(NativeValue::BabyBearExt4((*a).into())),
                    (Identity::Goldilocks, Identity::GoldilocksExt2, NativeValue::Goldilocks(a)) =>
                        Ok(NativeValue::GoldilocksExt2((*a).into())),
                    _ => Err(Error("test-embedding")),
                }
            }

            fn coordinates(&self, field: Identity, value: &Self::Value) -> Vec<String> {
                match (field, value) {
                    $((Identity::$field, NativeValue::$field(value)) => native_coordinates(value),)+
                    _ => unreachable!("admitted field value"),
                }
            }
        }
    };
}
native_algebra!(
    KoalaBear,
    KoalaBearExt4,
    KoalaBearExt8,
    BabyBear,
    BabyBearExt4,
    Goldilocks,
    GoldilocksExt2,
);
fn scalar(values: &[String]) -> Value {
    if values.len() == 1 {
        json!(values[0])
    } else {
        json!(values)
    }
}
/// `[bundle, configuration, instance, witness]` reports the bundle relation;
/// `[..., staged, assignment]` also reports the separate staged predicate
/// over the same base data.
fn evaluate(text: &str) -> Result<Value> {
    let input = relation::parse_json(text, 1024 * 1024, "bundle-data-schema", "bundle-data-limit")?;
    let rows = input
        .as_array()
        .filter(|a| a.len() == 4 || a.len() == 6)
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
    let mut report = json!({"accepted":true, "identity":bundle.identity(), "bundle":bundle.encode(),
        "result":{"satisfied":result.satisfied, "work":result.work, "residuals":residuals,
            "balances":balances, "range_failures":result.range_failures}});
    if rows.len() == 6 {
        let staged = Staged::decode(&bundle, &rows[4])?;
        let assignment = staged.decode_assignment(&rows[5])?;
        let result =
            staged.evaluate(&bundle, &config, &instance, &witness, &assignment, &Native)?;
        let residuals: Vec<_> = result
            .residuals
            .iter()
            .map(|r| json!([r.phase, r.table, r.assertion, r.row, scalar(&r.value)]))
            .collect();
        let global: Vec<_> = result.global.iter().map(|v| scalar(v)).collect();
        report["staged_identity"] = json!(staged.identity());
        report["staged"] = staged.encode();
        report["assignment"] = staged.encode_assignment(&assignment);
        report["staged_result"] = json!({"satisfied":result.satisfied, "work":result.work,
            "residuals":residuals, "global":global});
    }
    Ok(report)
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
