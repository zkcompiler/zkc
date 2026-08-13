//! The canonical OIR verifier document: identity recomputation, the row
//! grammar, and the semantic-id erasure.
//!
//! The grammar is docs/spec/carrier.md §6.2, which states that a second
//! implementation must be derivable from that section alone — this is
//! such an implementation. Identity discipline is §6.1: recompute
//! `SHA256("zkc/oir\n" ‖ bytes)` before reading any semantics, and
//! derive the provenance-independent semantic id by dropping `source`
//! and emptying every row's `src` list under the tag
//! `"zkc/oir-semantic\n"`.

use crate::json::{self, Json};
use sha2::{Digest, Sha256};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Ref {
    /// `["a", n]` — entry argument n.
    Arg(usize),
    /// `["r", row, k]` — result k of program row `row`.
    Res(usize, usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Entry {
    Val(String),
    Stream,
}

#[derive(Debug, Clone)]
pub enum Row {
    Init {
        sponge: String,
        iv: String,
    },
    Absorb {
        sponge: Ref,
        value: Ref,
    },
    Squeeze {
        sponge: Ref,
        label: String,
        class: String,
        count: u64,
        domain: String,
        rule: String,
        space: String,
    },
    Read {
        stream: Ref,
        label: String,
        class: String,
    },
    Const {
        value: String,
        class: String,
    },
    FNeg {
        operand: Ref,
    },
    FAdd {
        lhs: Ref,
        rhs: Ref,
    },
    FMul {
        lhs: Ref,
        rhs: Ref,
    },
    GExp {
        lhs: Ref,
        rhs: Ref,
    },
    GMul {
        lhs: Ref,
        rhs: Ref,
    },
    AssertEq {
        lhs: Ref,
        rhs: Ref,
        label: String,
    },
    /// Recognized so the refusal can name its digest; never emitted.
    CheckCall {
        inputs: Vec<Ref>,
        label: String,
        kind: String,
        digest: String,
        params: Vec<String>,
    },
    ExpectEnd {
        stream: Ref,
    },
    Decide {
        sponge: Ref,
    },
    /// Prover-frame rows, recognized for the endpoint-kind refusal.
    ProverOnly {
        kind: String,
    },
}

pub struct Document {
    /// Recomputed `SHA256("zkc/oir\n" ‖ bytes)`, lowercase hex.
    pub artifact_id: String,
    /// The provenance-independent view, lowercase hex.
    pub semantic_id: String,
    pub endpoint: String,
    /// `class → codec name`, in stored (canonical) order.
    pub codecs: Vec<(String, String)>,
    pub entry: Vec<Entry>,
    /// `"tagged-name=sha256:<hex>"` pins, in stored order.
    pub param_digests: Vec<String>,
    pub rows: Vec<Row>,
    pub source: String,
    pub statement_labels: Vec<String>,
}

fn sha256_hex(domain_tag: &str, bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(domain_tag.as_bytes());
    hasher.update(bytes);
    hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn parse_ref(value: &Json) -> Result<Ref, String> {
    let items = value.as_array().ok_or("reference is not an array")?;
    match items {
        [Json::String(kind), Json::UInt(index)] if kind == "a" => Ok(Ref::Arg(*index as usize)),
        [Json::String(kind), Json::UInt(row), Json::UInt(result)] if kind == "r" => {
            Ok(Ref::Res(*row as usize, *result as usize))
        }
        _ => Err(format!("malformed reference {}", json::serialize(value))),
    }
}

fn expect_string(value: &Json, what: &str) -> Result<String, String> {
    value
        .as_str()
        .map(str::to_owned)
        .ok_or_else(|| format!("{what} is not a string"))
}

fn parse_row(index: usize, row: &Json) -> Result<Row, String> {
    let items = row
        .as_array()
        .ok_or_else(|| format!("row {index} is not an array"))?;
    let kind = items
        .first()
        .and_then(Json::as_str)
        .ok_or_else(|| format!("row {index} has no kind tag"))?;
    let fail = |message: &str| Err(format!("row {index} ({kind}): {message}"));
    match kind {
        "init" => match items {
            [_, sponge, iv] => Ok(Row::Init {
                sponge: expect_string(sponge, "sponge")?,
                iv: expect_string(iv, "iv")?,
            }),
            _ => fail("expected [\"init\", sponge, iv]"),
        },
        "absorb" => match items {
            [_, sponge, value, _src] => Ok(Row::Absorb {
                sponge: parse_ref(sponge)?,
                value: parse_ref(value)?,
            }),
            _ => fail("expected [\"absorb\", sponge, value, src]"),
        },
        "squeeze" => match items {
            [_, sponge, label, class, count, domain, rule, space, _src] => Ok(Row::Squeeze {
                sponge: parse_ref(sponge)?,
                label: expect_string(label, "label")?,
                class: expect_string(class, "class")?,
                count: expect_string(count, "count")?
                    .parse::<u64>()
                    .map_err(|_| format!("row {index}: count is not decimal"))?,
                domain: expect_string(domain, "domain")?,
                rule: expect_string(rule, "rule")?,
                space: expect_string(space, "space")?,
            }),
            _ => fail(
                "expected [\"squeeze\", sponge, label, class, count, domain, rule, space, src]",
            ),
        },
        "read" => match items {
            [_, stream, label, class, _src] => Ok(Row::Read {
                stream: parse_ref(stream)?,
                label: expect_string(label, "label")?,
                class: expect_string(class, "class")?,
            }),
            _ => fail("expected [\"read\", stream, label, class, src]"),
        },
        "const" => match items {
            [_, value, class, _src] => Ok(Row::Const {
                value: expect_string(value, "value")?,
                class: expect_string(class, "class")?,
            }),
            _ => fail("expected [\"const\", value, class, src]"),
        },
        "f_neg" => match items {
            [_, operand, _src] => Ok(Row::FNeg {
                operand: parse_ref(operand)?,
            }),
            _ => fail("expected [\"f_neg\", operand, src]"),
        },
        "f_add" | "f_mul" | "g_exp" | "g_mul" => match items {
            [_, lhs, rhs, _src] => {
                let lhs = parse_ref(lhs)?;
                let rhs = parse_ref(rhs)?;
                Ok(match kind {
                    "f_add" => Row::FAdd { lhs, rhs },
                    "f_mul" => Row::FMul { lhs, rhs },
                    "g_exp" => Row::GExp { lhs, rhs },
                    _ => Row::GMul { lhs, rhs },
                })
            }
            _ => fail("expected [op, lhs, rhs, src]"),
        },
        "assert_eq" => match items {
            [_, lhs, rhs, label, _src] => Ok(Row::AssertEq {
                lhs: parse_ref(lhs)?,
                rhs: parse_ref(rhs)?,
                label: expect_string(label, "label")?,
            }),
            _ => fail("expected [\"assert_eq\", lhs, rhs, label, src]"),
        },
        "check_call" => match items {
            [_, inputs, label, check_kind, digest, params, _src] => {
                let mut input_refs = Vec::new();
                for input in inputs
                    .as_array()
                    .ok_or_else(|| format!("row {index}: check inputs are not an array"))?
                {
                    input_refs.push(parse_ref(input)?);
                }
                let mut param_values = Vec::new();
                for param in params
                    .as_array()
                    .ok_or_else(|| format!("row {index}: check params are not an array"))?
                {
                    param_values.push(expect_string(param, "check parameter")?);
                }
                Ok(Row::CheckCall {
                    inputs: input_refs,
                    label: expect_string(label, "label")?,
                    kind: expect_string(check_kind, "kind")?,
                    digest: expect_string(digest, "contract digest")?,
                    params: param_values,
                })
            }
            _ => fail("expected [\"check_call\", inputs, label, kind, digest, params, src]"),
        },
        "expect_end" => match items {
            [_, stream] => Ok(Row::ExpectEnd {
                stream: parse_ref(stream)?,
            }),
            _ => fail("expected [\"expect_end\", stream]"),
        },
        "decide" => match items {
            [_, sponge] => Ok(Row::Decide {
                sponge: parse_ref(sponge)?,
            }),
            _ => fail("expected [\"decide\", sponge]"),
        },
        "write" | "end_stream" | "finish" | "hole_call" => Ok(Row::ProverOnly {
            kind: kind.to_owned(),
        }),
        other => Err(format!(
            "row {index}: '{other}' is outside the canonical row grammar"
        )),
    }
}

/// The semantic-id erasure (carrier.md §6.1): drop `source`, empty every
/// row's `src` list. Rows without a `src` field — init, expect_end,
/// decide, end_stream, finish, hole_call — pass unchanged.
fn semantic_view(document: &Json) -> Result<Json, String> {
    let entries = document.as_object().ok_or("document is not an object")?;
    let mut erased = Vec::new();
    for (key, value) in entries {
        if key == "source" {
            continue;
        }
        if key != "program" {
            erased.push((key.clone(), value.clone()));
            continue;
        }
        let rows = value.as_array().ok_or("program is not an array")?;
        let mut erased_rows = Vec::new();
        for row in rows {
            let items = row.as_array().ok_or("row is not an array")?;
            let kind = items.first().and_then(Json::as_str).unwrap_or("");
            let carries_src = !matches!(
                kind,
                "init" | "expect_end" | "decide" | "end_stream" | "finish" | "hole_call"
            );
            let mut copied = items.to_vec();
            if carries_src {
                let last = copied.len() - 1;
                copied[last] = Json::Array(Vec::new());
            }
            erased_rows.push(Json::Array(copied));
        }
        erased.push((key.clone(), Json::Array(erased_rows)));
    }
    Ok(Json::Object(erased))
}

impl Document {
    pub fn parse(bytes: &[u8]) -> Result<Document, String> {
        // Identity before semantics: the consumer discipline of §6.1.
        let artifact_id = sha256_hex("zkc/oir\n", bytes);
        let document = json::parse(bytes)?;

        // The writer must agree with the canonical form before any
        // derived view is trusted: re-serialization is byte-identity.
        if json::serialize(&document).as_bytes() != bytes {
            return Err("document is not in canonical serialization; \
                        re-serialization does not reproduce the input bytes"
                .into());
        }
        let semantic_id = sha256_hex(
            "zkc/oir-semantic\n",
            json::serialize(&semantic_view(&document)?).as_bytes(),
        );

        let endpoint = expect_string(
            document.get("endpoint").ok_or("document has no endpoint")?,
            "endpoint",
        )?;

        let mut codecs = Vec::new();
        for (class, codec) in document
            .get("codecs")
            .and_then(Json::as_object)
            .ok_or("document has no codecs object")?
        {
            codecs.push((class.clone(), expect_string(codec, "codec name")?));
        }

        let mut entry = Vec::new();
        for element in document
            .get("entry")
            .and_then(Json::as_array)
            .ok_or("document has no entry")?
        {
            let items = element.as_array().ok_or("entry element is not an array")?;
            match items {
                [Json::String(kind), Json::String(class)] if kind == "val" => {
                    entry.push(Entry::Val(class.clone()))
                }
                [Json::String(kind)] if kind == "stream" => entry.push(Entry::Stream),
                [Json::String(kind), ..] if kind == "handle" => {
                    return Err("handle entry argument: this is a prover document".into())
                }
                _ => {
                    return Err(format!(
                        "malformed entry element {}",
                        json::serialize(element)
                    ))
                }
            }
        }

        let mut param_digests = Vec::new();
        for pin in document
            .get("param_digests")
            .and_then(Json::as_array)
            .ok_or("document has no param_digests")?
        {
            param_digests.push(expect_string(pin, "param digest")?);
        }

        let mut rows = Vec::new();
        for (index, row) in document
            .get("program")
            .and_then(Json::as_array)
            .ok_or("document has no program")?
            .iter()
            .enumerate()
        {
            rows.push(parse_row(index, row)?);
        }

        let source = expect_string(
            document.get("source").ok_or("document has no source")?,
            "source",
        )?;

        let mut statement_labels = Vec::new();
        for label in document
            .get("statement_labels")
            .and_then(Json::as_array)
            .ok_or("document has no statement_labels")?
        {
            statement_labels.push(expect_string(label, "statement label")?);
        }

        Ok(Document {
            artifact_id,
            semantic_id,
            endpoint,
            codecs,
            entry,
            param_digests,
            rows,
            source,
            statement_labels,
        })
    }
}
