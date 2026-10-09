#![allow(dead_code)]

use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use serde_json::Value;
use zkc_plonky3_air::arena::Arena;
use zkc_plonky3_air::artifact::{canonical, values_sha256};
use zkc_plonky3_air::field::{Ext8, F, ext_from_coordinates, parse_decimal};
use zkc_plonky3_air::{ClosedView, Export, Instance};

/// Points with every extension coordinate nonzero.
pub fn points() -> Vec<Ext8> {
    vec![
        ext_from_coordinates([1, 2, 3, 4, 5, 6, 7, 8]),
        ext_from_coordinates([2_130_706_432, 99, 1 << 30, 17, 5, 1_000_003, 2, 41]),
    ]
}

/// The trace with one cell increased by one.
pub fn perturb(trace: &RowMajorMatrix<F>, row: usize, column: usize) -> RowMajorMatrix<F> {
    let mut values = trace.values.clone();
    values[row * trace.width() + column] += F::ONE;
    RowMajorMatrix::new(values, trace.width())
}

/// Perturbations of the first, a middle and the last row in every column.
pub fn perturbations(trace: &RowMajorMatrix<F>) -> Vec<(String, RowMajorMatrix<F>)> {
    let height = trace.height();
    let mut rows = vec![0, height / 2, height - 1];
    rows.dedup();
    let mut cases = vec![];
    for row in rows {
        for column in 0..trace.width() {
            cases.push((
                format!("row {row} column {column}"),
                perturb(trace, row, column),
            ));
        }
    }
    cases
}

pub fn instance(export: &Export, height: usize, public_values: &[F]) -> Instance {
    Instance {
        export_sha256: export.sha256(),
        height,
        public_values: public_values.to_vec(),
    }
}

pub fn bind<'a>(export: &'a Export, height: usize, public_values: &[F]) -> ClosedView<'a> {
    ClosedView::bind(export, &instance(export, height, public_values)).unwrap()
}

/// Horner evaluation of ascending base-field coefficients at an extension point.
pub fn horner(coefficients: &[F], point: Ext8) -> Ext8 {
    coefficients
        .iter()
        .rev()
        .fold(Ext8::ZERO, |acc, c| acc * point + *c)
}

pub fn export_value(export: &Export) -> Value {
    serde_json::from_str(&export.to_text()).unwrap()
}

/// Re-encode a mutated export with digests made consistent again, as a
/// careless or malicious exporter would.
pub fn redigest(mut value: Value) -> String {
    let arena = Arena::decode(&value["arena"]).unwrap();
    value["arena_sha256"] = Value::String(arena.sha256());
    if let Some(p) = value["layout"]["preprocessed"].as_object_mut() {
        let values: Vec<F> = p["values"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| parse_decimal(v.as_str().unwrap()).unwrap())
            .collect();
        p.insert(
            "values_sha256".into(),
            Value::String(values_sha256(&values)),
        );
    }
    canonical(&value)
}

/// Index of the arena node reading `slot`.
pub fn input_node(export: &Export, slot: zkc_plonky3_air::Slot) -> usize {
    let slot = export.slots.iter().position(|s| *s == slot).unwrap();
    export
        .arena
        .nodes()
        .iter()
        .position(|n| *n == zkc_plonky3_air::arena::Node::Input(slot))
        .unwrap()
}
