//! Rust ring-provider side of the Clean export comparison. Test transport:
//! `clean_air_conformance CONTROL NATIVE_REPORT`, where the report comes from
//! the C++ `zkc-clean_air_conformance-test` tool for the same control.
//!
//! Every relation arena and every per-constraint `AIR::expressionView` arena is
//! admitted by the independent Rust reader and evaluated by the KoalaBear/Ext8
//! `ring::rows` provider, scalar and packed, whose arithmetic schedule the ring
//! kernels share. Results must equal the control's residuals: Clean's for the
//! export and the zkc AIR model's for mutants.
use p3_field::PrimeField32;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::io::Read;
use zkc_backends::{
    KoalaBear as F, KoalaBearExt8 as E, Policy, parse_koala_bear_decimal,
    plonky3::{MODULUS_DECIMAL, PACKING_WIDTH},
    ring::{self, Budget, Carrier},
};
use zkc_runtime::{interactive::Identity, ring::Expression};

// The report is linear in the control; both are bounded before parsing.
const CONTROL_LIMIT: u64 = 1 << 20;
const REPORT_LIMIT: u64 = 4 << 20;

type Refusal = String;

fn read(path: &str, limit: u64) -> Result<String, Refusal> {
    let mut text = String::new();
    std::fs::File::open(path)
        .and_then(|file| file.take(limit + 1).read_to_string(&mut text))
        .map_err(|_| "clean-read".to_string())?;
    if text.len() as u64 > limit {
        return Err("clean-limit".into());
    }
    Ok(text)
}

fn digest(text: &str) -> String {
    format!("{:x}", Sha256::digest(text.as_bytes()))
}

fn field<'a>(value: &'a Value, key: &str, code: &str) -> Result<&'a Value, Refusal> {
    value.get(key).ok_or_else(|| code.to_string())
}

fn array<'a>(value: &'a Value, key: &str, code: &str) -> Result<&'a Vec<Value>, Refusal> {
    field(value, key, code)?
        .as_array()
        .ok_or_else(|| code.to_string())
}

fn text<'a>(value: &'a Value, key: &str, code: &str) -> Result<&'a str, Refusal> {
    field(value, key, code)?
        .as_str()
        .ok_or_else(|| code.to_string())
}

fn strings(values: &[Value], code: &str) -> Result<Vec<String>, Refusal> {
    values
        .iter()
        .map(|v| {
            v.as_str()
                .map(str::to_string)
                .ok_or_else(|| code.to_string())
        })
        .collect()
}

/// Admit an arena exactly as emitted; its identity is the emitted bytes' digest.
fn admit(arena: &Value) -> Result<(Expression, String, String), Refusal> {
    let bytes = serde_json::to_string(arena).map_err(|_| "clean-control-shape")?;
    let expression = Expression::parse(&bytes).map_err(|e| e.0.to_string())?;
    let identity = digest(&expression.canonical());
    Ok((expression, identity, digest(&bytes)))
}

/// Row-major results of one arena over row-major inputs. Packed KoalaBear and
/// scalar/packed Ext8 runs over the embedded inputs must reproduce the scalar
/// KoalaBear results; a mismatch is reported and the scalar values returned.
fn evaluate(
    expression: &Expression,
    input: &[F],
    rows: usize,
    disagreements: &mut Vec<Value>,
    context: &Value,
) -> Result<Vec<F>, Refusal> {
    fn run<S: Carrier>(
        e: &Expression,
        input: &[S],
        rows: usize,
        packed: bool,
    ) -> Result<Vec<S>, Refusal> {
        ring::rows(
            e,
            S::IDENTITY,
            input,
            rows,
            packed,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX,
        )
        .map_err(|e| format!("clean-provider:{}", e.code))
    }
    let scalar = run(expression, input, rows, false)?;
    if run(expression, input, rows, true)? != scalar {
        disagreements.push(
            json!({"code": "clean-provider-mode", "mode": "koala-bear-packed", "at": context}),
        );
    }
    let extension: Vec<E> = input.iter().map(|v| E::from(*v)).collect();
    for (mode, packed) in [("ext8-scalar", false), ("ext8-packed", true)] {
        let values = run(expression, &extension, rows, packed)?;
        if values.len() != scalar.len()
            || values.iter().zip(&scalar).any(|(e, f)| *e != E::from(*f))
        {
            disagreements.push(json!({"code": "clean-provider-mode", "mode": mode, "at": context}));
        }
    }
    Ok(scalar)
}

fn decimal(value: F) -> String {
    value.as_canonical_u32().to_string()
}

struct Component<'a> {
    name: &'a str,
    width: usize,
    cells: Vec<Vec<F>>,
}

fn check(control_text: &str, report_text: &str) -> Result<Value, Refusal> {
    let control: Value = serde_json::from_str(control_text).map_err(|_| "clean-control-shape")?;
    let report: Value = serde_json::from_str(report_text).map_err(|_| "clean-report-shape")?;
    if text(&control, "format", "clean-control-shape")? != "zkc.clean-air-control/0" {
        return Err("clean-control-shape".into());
    }
    // This provider supports exactly the KoalaBear residue presentation.
    let presentation = field(&control, "presentation", "clean-control-shape")?;
    if text(presentation, "field", "clean-control-shape")? != Identity::KoalaBear.name()
        || text(presentation, "modulus", "clean-control-shape")? != MODULUS_DECIMAL
    {
        return Err("clean-presentation".into());
    }
    // The report must describe this exact control.
    if text(&report, "control_sha256", "clean-report-shape")? != digest(control_text)
        || text(&report, "format", "clean-report-shape")? != "zkc.clean-air-native/0"
    {
        return Err("clean-report-binding".into());
    }
    let controls = array(&control, "components", "clean-control-shape")?;
    let natives = array(&report, "components", "clean-report-shape")?;
    if controls.len() != natives.len() {
        return Err("clean-report-binding".into());
    }
    let mut disagreements = Vec::new();
    let mut results = Vec::new();
    for (control, native) in controls.iter().zip(natives) {
        let rows = array(control, "rows", "clean-control-shape")?;
        let mut component = Component {
            name: text(control, "name", "clean-control-shape")?,
            width: 0,
            cells: Vec::new(),
        };
        if text(native, "name", "clean-report-shape")? != component.name {
            return Err("clean-report-binding".into());
        }
        for row in rows {
            let cells = array(row, "cells", "clean-control-shape")?;
            component.cells.push(
                strings(cells, "clean-control-shape")?
                    .iter()
                    .map(|c| {
                        parse_koala_bear_decimal(c).map_err(|_| "clean-control-shape".to_string())
                    })
                    .collect::<Result<_, _>>()?,
            );
        }
        component.width = component.cells.first().map_or(0, Vec::len);
        if component
            .cells
            .iter()
            .any(|row| row.len() != component.width)
        {
            return Err("clean-control-shape".into());
        }
        let subjects = array(control, "subjects", "clean-control-shape")?;
        let native_subjects = array(native, "subjects", "clean-report-shape")?;
        if subjects.len() != native_subjects.len() {
            return Err("clean-report-binding".into());
        }
        let mut subject_results = Vec::new();
        for (subject, native) in subjects.iter().zip(native_subjects) {
            subject_results.push(check_subject(
                &component,
                subject,
                native,
                &mut disagreements,
            )?);
        }
        results.push(json!({"name": component.name, "subjects": subject_results}));
    }
    Ok(json!({
        "format": "zkc.clean-air-ring/0",
        "status": if disagreements.is_empty() { "pass" } else { "disagree" },
        "packing_width": PACKING_WIDTH,
        "components": results,
        "disagreements": disagreements,
    }))
}

fn check_subject(
    component: &Component,
    subject: &Value,
    native: &Value,
    disagreements: &mut Vec<Value>,
) -> Result<Value, Refusal> {
    let name = text(subject, "name", "clean-control-shape")?;
    if text(native, "name", "clean-report-shape")? != name {
        return Err("clean-report-binding".into());
    }
    let height = component.cells.len();
    let expected: Vec<Vec<String>> = array(subject, "rows", "clean-control-shape")?
        .iter()
        .map(|row| {
            strings(
                array(row, "residuals", "clean-control-shape")?,
                "clean-control-shape",
            )
        })
        .collect::<Result<_, _>>()?;
    let native_residuals: Vec<Vec<String>> = array(native, "residuals", "clean-report-shape")?
        .iter()
        .map(|row| {
            strings(
                row.as_array().ok_or("clean-report-shape")?,
                "clean-report-shape",
            )
        })
        .collect::<Result<_, _>>()?;
    let constraints = expected.first().map_or(0, Vec::len);
    if expected.len() != height
        || native_residuals.len() != height
        || expected.iter().any(|row| row.len() != constraints)
    {
        return Err("clean-control-shape".into());
    }
    let at = |source: &str, row: usize, constraint: usize| {
        json!({"component": component.name, "subject": name, "source": source,
               "row": row, "constraint": constraint})
    };
    // The emitted relation arena: input i is column i of the row.
    let (arena, identity, emitted) = admit(field(subject, "arena", "clean-control-shape")?)?;
    if identity != emitted || identity != text(native, "arena_identity", "clean-report-shape")? {
        disagreements
            .push(json!({"code": "clean-arena-identity", "at": at("relation-arena", 0, 0)}));
    }
    if arena.inputs().len() != component.width
        || arena.outputs().len() != constraints
        || arena.inputs().iter().any(|i| *i != Identity::KoalaBear)
    {
        return Err("clean-arena-shape".into());
    }
    let input: Vec<F> = component.cells.concat();
    let context = at("relation-arena", 0, 0);
    let values = evaluate(&arena, &input, height, disagreements, &context)?;
    for (row, claimed) in expected.iter().enumerate() {
        for (c, claimed) in claimed.iter().enumerate() {
            if decimal(values[row * constraints + c]) != *claimed {
                disagreements
                    .push(json!({"code": "clean-residual", "at": at("relation-arena", row, c)}));
            }
        }
    }
    for (row, (claimed, native)) in expected.iter().zip(&native_residuals).enumerate() {
        if claimed != native {
            disagreements.push(json!({"code": "clean-native-residual", "at": at("air", row, 0)}));
        }
    }

    // The C++ AIR::expressionView arenas, one per constraint, with read maps.
    let views = array(native, "views", "clean-report-shape")?;
    if views.len() != constraints {
        return Err("clean-report-shape".into());
    }
    for (c, view) in views.iter().enumerate() {
        let (expression, view_identity, emitted) =
            admit(field(view, "arena", "clean-report-shape")?)?;
        if view_identity != emitted
            || view_identity != text(view, "identity", "clean-report-shape")?
        {
            disagreements.push(json!({"code": "clean-view-identity", "at": at("view", 0, c)}));
        }
        let columns: Vec<usize> = array(view, "reads", "clean-report-shape")?
            .iter()
            .map(|read| match read.as_array().map(Vec::as_slice) {
                Some([offset, column]) if offset.as_u64() == Some(0) => column
                    .as_u64()
                    .and_then(|c| usize::try_from(c).ok())
                    .filter(|c| *c < component.width)
                    .ok_or_else(|| "clean-binding".to_string()),
                _ => Err("clean-binding".to_string()),
            })
            .collect::<Result<_, _>>()?;
        if columns.len() != expression.inputs().len() || expression.outputs().len() != 1 {
            return Err("clean-binding".into());
        }
        let input: Vec<F> = component
            .cells
            .iter()
            .flat_map(|row| columns.iter().map(|column| row[*column]))
            .collect();
        let view_values = evaluate(
            &expression,
            &input,
            height,
            disagreements,
            &at("view", 0, c),
        )?;
        for (row, claimed) in expected.iter().enumerate() {
            if decimal(view_values[row]) != claimed[c] {
                disagreements.push(json!({"code": "clean-residual", "at": at("view", row, c)}));
            }
        }
    }
    Ok(json!({
        "name": name,
        "arena_identity": identity,
        "residuals": (0..height)
            .map(|row| (0..constraints).map(|c| decimal(values[row * constraints + c])).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        "views": views.len(),
    }))
}

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    let [_, control, report] = arguments.as_slice() else {
        eprintln!("usage: clean_air_conformance CONTROL NATIVE_REPORT");
        std::process::exit(2);
    };
    let result = read(control, CONTROL_LIMIT)
        .and_then(|control| Ok((control, read(report, REPORT_LIMIT)?)))
        .and_then(|(control, report)| check(&control, &report));
    match result {
        Ok(report) => {
            println!("{report}");
            std::process::exit(if report["status"] == "pass" { 0 } else { 1 });
        }
        Err(code) => {
            println!("{}", json!({"status": "refused", "code": code}));
            std::process::exit(1);
        }
    }
}
