//! Canonical JSON artifacts. Each has one exact schema: unknown or missing
//! fields refuse, and accepted text must equal its canonical re-encoding, so a
//! SHA-256 of the bytes is a well-defined identity.
//!
//! - `zkc.plonky3-air-export/0` is the candidate relation view captured from
//!   one AIR. It is not authority until a verifier configuration selects it.
//! - `zkc.plonky3-air-instance/0` is the verifier's statement: the selected
//!   export identity, trace height and public values.
//! - `zkc.plonky3-air-witness/0` is the prover's main trace.

use crate::arena::{Arena, hex_sha256};
use crate::field::{F, decimal, parse_decimal};
use crate::model::{
    Assertion, Export, Layout, Origin, PROBED_ABSENT, Preprocessed, SelectorKind, Slot,
};
use crate::refusal::{Refusal, Result, ensure, refuse};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use serde_json::{Map, Value, json};

pub const EXPORT_FORMAT: &str = "zkc.plonky3-air-export/0";
pub const INSTANCE_FORMAT: &str = "zkc.plonky3-air-instance/0";
pub const WITNESS_FORMAT: &str = "zkc.plonky3-air-witness/0";
pub const EXPORT_BYTE_LIMIT: usize = 64 << 20;
pub const INSTANCE_BYTE_LIMIT: usize = 1 << 20;
pub const WITNESS_BYTE_LIMIT: usize = 256 << 20;
pub const WITNESS_CELL_LIMIT: usize = 1 << 22;

/// Upstream source of the capture. 0.5.1 is the crates.io release of this commit.
pub const UPSTREAM_COMMIT: &str = "45e0ffe4d294816755522dd2cf7c38d6bcd701ce";
pub const UPSTREAM_CRATES: [(&str, &str); 4] = [
    ("p3-air", "0.5.1"),
    ("p3-field", "0.5.1"),
    ("p3-koala-bear", "0.5.1"),
    ("p3-matrix", "0.5.1"),
];
pub const EXPORTER: &str = concat!("zkc-plonky3-air ", env!("CARGO_PKG_VERSION"));
pub const READ_MODEL: &str = "cyclic";
pub const SELECTOR_SEMANTICS: &str = "guard-only";

fn schema<T>(what: impl Into<String>) -> Result<T> {
    refuse("plonky3-artifact-schema", what)
}

fn parse_text(text: &str, limit: usize) -> Result<Value> {
    ensure(text.len() <= limit, "plonky3-artifact-limit", || {
        format!("{} bytes exceed {limit}", text.len())
    })?;
    serde_json::from_str(text).map_err(|e| Refusal {
        id: "plonky3-artifact-schema",
        detail: e.to_string(),
    })
}

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

fn require_canonical(text: &str, value: &Value) -> Result<()> {
    ensure(
        text == canonical(value),
        "plonky3-artifact-noncanonical",
        || "text differs from its canonical encoding".into(),
    )
}

fn object<'a>(value: &'a Value, keys: &[&str], what: &str) -> Result<&'a Map<String, Value>> {
    let Some(map) = value.as_object() else {
        return schema(format!("{what} is not an object"));
    };
    let mut actual: Vec<&str> = map.keys().map(String::as_str).collect();
    actual.sort_unstable();
    let mut expected = keys.to_vec();
    expected.sort_unstable();
    ensure(actual == expected, "plonky3-artifact-schema", || {
        format!("{what} fields {actual:?}, expected {expected:?}")
    })?;
    Ok(map)
}

fn natural(value: &Value, limit: usize, what: &str) -> Result<usize> {
    match value.as_u64() {
        Some(n) if n <= limit as u64 => Ok(n as usize),
        _ => schema(format!("{what} is not a natural number up to {limit}")),
    }
}

fn string<'a>(value: &'a Value, what: &str) -> Result<&'a str> {
    value
        .as_str()
        .map_or_else(|| schema(format!("{what} is not a string")), Ok)
}

fn array<'a>(value: &'a Value, what: &str) -> Result<&'a [Value]> {
    value.as_array().map_or_else(
        || schema(format!("{what} is not an array")),
        |a| Ok(a.as_slice()),
    )
}

fn exact(value: &Value, expected: &str, what: &str) -> Result<()> {
    ensure(
        value.as_str() == Some(expected),
        "plonky3-artifact-schema",
        || format!("{what} must be {expected:?}"),
    )
}

fn scalars(values: &[F]) -> Value {
    Value::Array(values.iter().map(|v| Value::String(decimal(*v))).collect())
}

fn parse_scalars(value: &Value, what: &str) -> Result<Vec<F>> {
    array(value, what)?
        .iter()
        .map(|v| parse_decimal(string(v, what)?))
        .collect()
}

/// SHA-256 of the compact canonical decimal array of row-major values.
pub fn values_sha256(values: &[F]) -> String {
    hex_sha256(scalars(values).to_string().as_bytes())
}

fn slot_value(slot: &Slot) -> Value {
    match *slot {
        Slot::Main { offset, column } => json!(["main", column, offset]),
        Slot::Preprocessed { offset, column } => json!(["preprocessed", column, offset]),
        Slot::Public(i) => json!(["public", i]),
        Slot::Selector(kind) => json!(["selector", kind.name()]),
    }
}

fn parse_slot(value: &Value) -> Result<Slot> {
    let row = array(value, "slot")?;
    let index = |v: &Value| natural(v, usize::MAX >> 1, "slot index");
    match (row.first().and_then(Value::as_str), row) {
        (Some("main"), [_, column, offset]) => Ok(Slot::Main {
            column: index(column)?,
            offset: index(offset)?,
        }),
        (Some("preprocessed"), [_, column, offset]) => Ok(Slot::Preprocessed {
            column: index(column)?,
            offset: index(offset)?,
        }),
        (Some("public"), [_, i]) => Ok(Slot::Public(index(i)?)),
        (Some("selector"), [_, kind]) => SelectorKind::parse(string(kind, "selector")?)
            .map_or_else(
                || schema(format!("selector {kind}")),
                |k| Ok(Slot::Selector(k)),
            ),
        _ => schema(format!("slot {value}")),
    }
}

fn names(values: &[&str]) -> Value {
    Value::Array(
        values
            .iter()
            .map(|s| Value::String(s.to_string()))
            .collect(),
    )
}

impl Export {
    pub fn to_value(&self) -> Value {
        let preprocessed = self.layout.preprocessed.as_ref().map_or(Value::Null, |p| {
            json!({
                "height": p.height,
                "next_row_columns": p.next_row_columns,
                "values": scalars(&p.values),
                "values_sha256": values_sha256(&p.values),
                "width": p.width,
            })
        });
        let arena: Value =
            serde_json::from_str(&self.arena.canonical()).expect("canonical arena is JSON");
        json!({
            "air": self.air,
            "arena": arena,
            "arena_sha256": self.arena.sha256(),
            "assertions": self.assertions.iter().map(|a| json!({
                "constraint": a.constraint,
                "degree_multiple": a.degree_multiple,
                "selectors": a.selectors.iter().map(|s| s.name()).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "exporter": EXPORTER,
            "features": self.features,
            "format": EXPORT_FORMAT,
            "layout": {
                "main": {"next_row_columns": self.layout.main_next_row_columns, "width": self.layout.main_width},
                "preprocessed": preprocessed,
                "public_values": self.layout.public_values,
            },
            "node_origins": self.origins.iter().map(|o| o.name()).collect::<Vec<_>>(),
            "probed_absent": names(&PROBED_ABSENT),
            "read_model": READ_MODEL,
            "selector_semantics": SELECTOR_SEMANTICS,
            "slots": self.slots.iter().map(slot_value).collect::<Vec<_>>(),
            "upstream": {
                "commit": UPSTREAM_COMMIT,
                "crates": UPSTREAM_CRATES.iter().map(|(n, v)| (n.to_string(), json!(v))).collect::<Map<_, _>>(),
            },
        })
    }

    /// Canonical artifact text.
    pub fn to_text(&self) -> String {
        canonical(&self.to_value())
    }

    /// Identity of the candidate export: SHA-256 of its canonical text.
    pub fn sha256(&self) -> String {
        hex_sha256(self.to_text().as_bytes())
    }

    /// Exact arena text for the native ring-asset registry.
    pub fn arena_text(&self) -> String {
        self.arena.canonical()
    }

    /// Import: decode, then recheck every derived fact from the content.
    pub fn parse(text: &str) -> Result<Self> {
        let value = parse_text(text, EXPORT_BYTE_LIMIT)?;
        let root = object(
            &value,
            &[
                "air",
                "arena",
                "arena_sha256",
                "assertions",
                "exporter",
                "features",
                "format",
                "layout",
                "node_origins",
                "probed_absent",
                "read_model",
                "selector_semantics",
                "slots",
                "upstream",
            ],
            "export",
        )?;
        exact(&root["format"], EXPORT_FORMAT, "format")?;
        exact(&root["exporter"], EXPORTER, "exporter")?;
        exact(&root["read_model"], READ_MODEL, "read_model")?;
        exact(
            &root["selector_semantics"],
            SELECTOR_SEMANTICS,
            "selector_semantics",
        )?;
        ensure(
            root["probed_absent"] == names(&PROBED_ABSENT),
            "plonky3-artifact-schema",
            || "probed_absent".into(),
        )?;
        let upstream = object(&root["upstream"], &["commit", "crates"], "upstream")?;
        exact(&upstream["commit"], UPSTREAM_COMMIT, "upstream commit")?;
        let crates = object(
            &upstream["crates"],
            &UPSTREAM_CRATES.map(|(n, _)| n),
            "upstream crates",
        )?;
        for (name, version) in UPSTREAM_CRATES {
            exact(&crates[name], version, name)?;
        }

        let arena = Arena::decode(&root["arena"])?;
        ensure(
            root["arena_sha256"].as_str() == Some(arena.sha256().as_str()),
            "plonky3-arena-identity",
            || "arena_sha256 differs from the arena's canonical encoding".into(),
        )?;

        let layout_value = object(
            &root["layout"],
            &["main", "preprocessed", "public_values"],
            "layout",
        )?;
        let main = object(
            &layout_value["main"],
            &["next_row_columns", "width"],
            "layout.main",
        )?;
        let columns = |v: &Value, what: &str| -> Result<Vec<usize>> {
            array(v, what)?
                .iter()
                .map(|c| natural(c, crate::model::MAX_WIDTH, what))
                .collect()
        };
        let preprocessed = match &layout_value["preprocessed"] {
            Value::Null => None,
            value => {
                let p = object(
                    value,
                    &[
                        "height",
                        "next_row_columns",
                        "values",
                        "values_sha256",
                        "width",
                    ],
                    "preprocessed",
                )?;
                let values = parse_scalars(&p["values"], "preprocessed values")?;
                ensure(
                    p["values_sha256"].as_str() == Some(values_sha256(&values).as_str()),
                    "plonky3-preprocessed-identity",
                    || "values_sha256 differs from the preprocessed values".into(),
                )?;
                Some(Preprocessed {
                    width: natural(&p["width"], crate::model::MAX_WIDTH, "preprocessed width")?,
                    height: natural(
                        &p["height"],
                        1 << crate::field::MAX_LOG_HEIGHT,
                        "preprocessed height",
                    )?,
                    next_row_columns: columns(
                        &p["next_row_columns"],
                        "preprocessed next_row_columns",
                    )?,
                    values,
                })
            }
        };
        let layout = Layout {
            main_width: natural(&main["width"], crate::model::MAX_WIDTH, "main width")?,
            main_next_row_columns: columns(&main["next_row_columns"], "main next_row_columns")?,
            preprocessed,
            public_values: natural(
                &layout_value["public_values"],
                crate::model::MAX_PUBLIC_VALUES,
                "public_values",
            )?,
        };
        let slots = array(&root["slots"], "slots")?
            .iter()
            .map(parse_slot)
            .collect::<Result<Vec<_>>>()?;
        let origins = array(&root["node_origins"], "node_origins")?
            .iter()
            .map(|o| {
                let name = string(o, "origin")?;
                Origin::parse(name).map_or_else(|| schema(format!("origin {name}")), Ok)
            })
            .collect::<Result<Vec<_>>>()?;
        let assertions = array(&root["assertions"], "assertions")?
            .iter()
            .map(|a| {
                let a = object(
                    a,
                    &["constraint", "degree_multiple", "selectors"],
                    "assertion",
                )?;
                Ok(Assertion {
                    constraint: natural(
                        &a["constraint"],
                        crate::arena::OUTPUT_LIMIT,
                        "constraint",
                    )?,
                    degree_multiple: natural(
                        &a["degree_multiple"],
                        crate::arena::DEGREE_LIMIT as usize,
                        "degree_multiple",
                    )? as u64,
                    selectors: array(&a["selectors"], "selectors")?
                        .iter()
                        .map(|s| {
                            let name = string(s, "selector")?;
                            SelectorKind::parse(name)
                                .map_or_else(|| schema(format!("selector {name}")), Ok)
                        })
                        .collect::<Result<Vec<_>>>()?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let features = array(&root["features"], "features")?
            .iter()
            .map(|f| string(f, "feature").map(String::from))
            .collect::<Result<Vec<_>>>()?;
        let export = Export {
            air: string(&root["air"], "air")?.to_string(),
            layout,
            arena,
            slots,
            origins,
            assertions,
            features,
        };
        export.validate()?;
        require_canonical(text, &export.to_value())?;
        Ok(export)
    }
}

/// The verifier's statement for one selected export.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instance {
    pub export_sha256: String,
    pub height: usize,
    pub public_values: Vec<F>,
}

impl Instance {
    pub fn to_text(&self) -> String {
        canonical(&json!({
            "export_sha256": self.export_sha256,
            "format": INSTANCE_FORMAT,
            "height": self.height,
            "public_values": scalars(&self.public_values),
        }))
    }

    pub fn parse(text: &str) -> Result<Self> {
        let value = parse_text(text, INSTANCE_BYTE_LIMIT)?;
        let root = object(
            &value,
            &["export_sha256", "format", "height", "public_values"],
            "instance",
        )?;
        exact(&root["format"], INSTANCE_FORMAT, "format")?;
        let digest = string(&root["export_sha256"], "export_sha256")?;
        ensure(
            digest.len() == 64
                && digest
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
            "plonky3-artifact-schema",
            || "export_sha256 is not 64 lowercase hexadecimal digits".into(),
        )?;
        let instance = Self {
            export_sha256: digest.to_string(),
            height: natural(&root["height"], usize::MAX >> 1, "height")?,
            public_values: parse_scalars(&root["public_values"], "public_values")?,
        };
        require_canonical(text, &value)?;
        Ok(instance)
    }
}

/// The prover's main trace, row-major.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Witness {
    pub trace: RowMajorMatrix<F>,
}

impl Witness {
    pub fn to_text(&self) -> String {
        let rows: Vec<Value> = (0..self.trace.height())
            .map(|r| {
                scalars(&self.trace.values[r * self.trace.width()..(r + 1) * self.trace.width()])
            })
            .collect();
        canonical(&json!({
            "format": WITNESS_FORMAT,
            "height": self.trace.height(),
            "trace": rows,
            "width": self.trace.width(),
        }))
    }

    pub fn parse(text: &str) -> Result<Self> {
        let value = parse_text(text, WITNESS_BYTE_LIMIT)?;
        let root = object(&value, &["format", "height", "trace", "width"], "witness")?;
        exact(&root["format"], WITNESS_FORMAT, "format")?;
        let height = natural(&root["height"], WITNESS_CELL_LIMIT, "height")?;
        let width = natural(&root["width"], crate::model::MAX_WIDTH, "width")?;
        ensure(
            width > 0
                && height
                    .checked_mul(width)
                    .is_some_and(|c| c <= WITNESS_CELL_LIMIT),
            "plonky3-artifact-limit",
            || format!("trace of {height} rows and {width} columns"),
        )?;
        let rows = array(&root["trace"], "trace")?;
        ensure(rows.len() == height, "plonky3-artifact-schema", || {
            "trace row count differs from height".into()
        })?;
        let mut values = Vec::with_capacity(height * width);
        for row in rows {
            let row = parse_scalars(row, "trace row")?;
            ensure(row.len() == width, "plonky3-artifact-schema", || {
                "trace row width differs".into()
            })?;
            values.extend(row);
        }
        require_canonical(text, &value)?;
        Ok(Self {
            trace: RowMajorMatrix::new(values, width),
        })
    }
}
