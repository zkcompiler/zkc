//! The canonical OIR document — both endpoint frames: identity
//! recomputation, the row grammar, and the semantic-id erasure.
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

/// A typed slot: an entry argument, or one hole-call result. `stream`
/// appears only in an entry; `sponge` only on a hole that threads the
/// transcript through its fill (the `pow_search` peek).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Entry {
    Val(String),
    /// A counted vector value of the named class: the whole vector is
    /// one slot, exactly as a vector squeeze's.
    ValVec(String, u64),
    /// An opaque linear witness payload of the named handle class.
    Handle(String),
    Stream,
    Sponge,
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
        /// 1 for the scalar row family; the read_vec family's declared
        /// element count otherwise (docs/spec/carrier.md §7).
        count: u64,
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

    //== the prover frame ==//
    /// The dual of `read`: a fill's value leaves on the wire.
    Write {
        stream: Ref,
        value: Ref,
        label: String,
        class: String,
        /// 1 for the scalar row family; write_vec's count otherwise.
        count: u64,
    },
    /// A supplier call. Result indices run positionally across the mixed
    /// value/handle list, in declaration order.
    HoleCall {
        inputs: Vec<Ref>,
        results: Vec<Entry>,
        label: String,
        kind: String,
        digest: String,
        params: Vec<String>,
        semantic_params: Vec<String>,
    },
    EndStream {
        stream: Ref,
    },
    Finish {
        sponge: Ref,
    },
}

/// The two endpoint frames the grammar admits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endpoint {
    Verifier,
    ProverSkeleton,
}

impl Endpoint {
    fn from_name(name: &str) -> Option<Endpoint> {
        match name {
            "verifier" => Some(Endpoint::Verifier),
            "prover_skeleton" => Some(Endpoint::ProverSkeleton),
            _ => None,
        }
    }
}

pub struct Document {
    /// Recomputed `SHA256("zkc/oir\n" ‖ bytes)`, lowercase hex.
    pub artifact_id: String,
    /// The provenance-independent view, lowercase hex.
    pub semantic_id: String,
    pub endpoint: Endpoint,
    /// The `endpoint` field verbatim, for diagnostics.
    pub endpoint_name: String,
    /// `class → codec name`, in stored (canonical) order.
    pub codecs: Vec<(String, String)>,
    pub entry: Vec<Entry>,
    /// `"tagged-name=sha256:<hex>"` pins, in stored order.
    pub param_digests: Vec<String>,
    pub rows: Vec<Row>,
    pub source: String,
    pub statement_labels: Vec<String>,
    /// The statement, paired with the payload class of the entry
    /// argument that carries it, in ABI order. The grammar puts the
    /// statement values first, so this is established once at parse
    /// rather than re-derived wherever the pair is needed.
    pub statement: Vec<(String, String)>,
    /// Prover only: ordered `[label, handle class]` pairs. Empty on a
    /// verifier document, where the key is absent.
    pub witness_labels: Vec<(String, String)>,
    /// Prover only: `[event position, discharge kind]` rows — the checks
    /// this endpoint delegates to its counterparty.
    pub counterparty: Vec<(u64, String)>,
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

fn expect_strings(value: &Json, what: &str) -> Result<Vec<String>, String> {
    let items = value
        .as_array()
        .ok_or_else(|| format!("{what} is not an array"))?;
    items.iter().map(|item| expect_string(item, what)).collect()
}

fn parse_refs(value: &Json, what: &str) -> Result<Vec<Ref>, String> {
    let items = value
        .as_array()
        .ok_or_else(|| format!("{what} is not an array"))?;
    items.iter().map(parse_ref).collect()
}

/// A counted element count, under the carrier's own grammar: a
/// canonical decimal (no leading zeros) from 2 through 2^20 — the
/// scalar form spells 1 through its own row or slot shape
/// (docs/spec/carrier.md §6.2).
fn parse_count(value: &Json, context: &str) -> Result<u64, String> {
    let text = value
        .as_str()
        .ok_or_else(|| format!("{context}: count is not a string"))?;
    if text.is_empty() || !text.chars().all(|c| c.is_ascii_digit()) || text.starts_with('0') {
        return Err(format!(
            "{context}: count '{text}' is not a canonical decimal"
        ));
    }
    let count = text
        .parse::<u64>()
        .map_err(|_| format!("{context}: count '{text}' is not a canonical decimal"))?;
    if !(2..=1 << 20).contains(&count) {
        return Err(format!(
            "{context}: a counted shape declares 2 through 2^20 elements; the \
             scalar form spells 1 through its own shape"
        ));
    }
    Ok(count)
}

/// One typed slot: `["val", class]`, `["val", class, count]`,
/// `["handle", class]`, `["stream"]`, `["sponge"]`. Which of them a
/// position admits is the caller's rule.
fn parse_slot(value: &Json, what: &str) -> Result<Entry, String> {
    match value.as_array() {
        Some([Json::String(kind), Json::String(class)]) if kind == "val" => {
            Ok(Entry::Val(class.clone()))
        }
        Some([Json::String(kind), Json::String(class), count]) if kind == "val" => {
            Ok(Entry::ValVec(class.clone(), parse_count(count, what)?))
        }
        Some([Json::String(kind), Json::String(class)]) if kind == "handle" => {
            Ok(Entry::Handle(class.clone()))
        }
        Some([Json::String(kind)]) if kind == "stream" => Ok(Entry::Stream),
        Some([Json::String(kind)]) if kind == "sponge" => Ok(Entry::Sponge),
        _ => Err(format!("malformed {what} {}", json::serialize(value))),
    }
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
                count: 1,
            }),
            _ => fail("expected [\"read\", stream, label, class, src]"),
        },
        "read_vec" => match items {
            [_, stream, label, class, count, _src] => Ok(Row::Read {
                stream: parse_ref(stream)?,
                label: expect_string(label, "label")?,
                class: expect_string(class, "class")?,
                count: parse_count(count, &format!("row {index}"))?,
            }),
            _ => fail("expected [\"read_vec\", stream, label, class, count, src]"),
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
            [_, inputs, label, check_kind, digest, params, _src] => Ok(Row::CheckCall {
                inputs: parse_refs(inputs, "check inputs")?,
                label: expect_string(label, "label")?,
                kind: expect_string(check_kind, "kind")?,
                digest: expect_string(digest, "contract digest")?,
                params: expect_strings(params, "check parameter")?,
            }),
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
        "write" => match items {
            [_, stream, value, label, class, _src] => Ok(Row::Write {
                stream: parse_ref(stream)?,
                value: parse_ref(value)?,
                label: expect_string(label, "label")?,
                class: expect_string(class, "class")?,
                count: 1,
            }),
            _ => fail("expected [\"write\", stream, value, label, class, src]"),
        },
        "write_vec" => match items {
            [_, stream, value, label, class, count, _src] => Ok(Row::Write {
                stream: parse_ref(stream)?,
                value: parse_ref(value)?,
                label: expect_string(label, "label")?,
                class: expect_string(class, "class")?,
                count: parse_count(count, &format!("row {index}"))?,
            }),
            _ => fail("expected [\"write_vec\", stream, value, label, class, count, src]"),
        },
        "hole_call" => match items {
            [_, inputs, results, label, hole_kind, digest, params, semantic_params] => {
                let mut typed = Vec::new();
                for result in results
                    .as_array()
                    .ok_or_else(|| format!("row {index}: hole results are not an array"))?
                {
                    match parse_slot(result, "hole result")? {
                        Entry::Stream => {
                            return fail("a hole result cannot be the proof stream");
                        }
                        slot => typed.push(slot),
                    }
                }
                Ok(Row::HoleCall {
                    inputs: parse_refs(inputs, "hole inputs")?,
                    results: typed,
                    label: expect_string(label, "label")?,
                    kind: expect_string(hole_kind, "kind")?,
                    digest: expect_string(digest, "contract digest")?,
                    params: expect_strings(params, "hole parameter")?,
                    semantic_params: expect_strings(semantic_params, "hole semantic parameter")?,
                })
            }
            _ => fail(
                "expected [\"hole_call\", inputs, results, label, kind, digest, params, \
                 semantic_params]",
            ),
        },
        "end_stream" => match items {
            [_, stream] => Ok(Row::EndStream {
                stream: parse_ref(stream)?,
            }),
            _ => fail("expected [\"end_stream\", stream]"),
        },
        "finish" => match items {
            [_, sponge] => Ok(Row::Finish {
                sponge: parse_ref(sponge)?,
            }),
            _ => fail("expected [\"finish\", sponge]"),
        },
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
            // The erasure runs before the grammar is checked, so it
            // cannot assume a row has a kind tag and a trailing src.
            if carries_src && copied.len() > 1 {
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

        let endpoint_name = expect_string(
            document.get("endpoint").ok_or("document has no endpoint")?,
            "endpoint",
        )?;
        let endpoint = Endpoint::from_name(&endpoint_name).ok_or_else(|| {
            format!("endpoint '{endpoint_name}' is outside the canonical grammar's two frames")
        })?;

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
            entry.push(parse_slot(element, "entry element")?);
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

        // `witness_labels` and `counterparty` are present exactly on a
        // prover document and absent exactly on a verifier one (§6.2);
        // a document carrying the wrong set is not the frame it claims.
        let prover = endpoint == Endpoint::ProverSkeleton;
        let mut witness_labels = Vec::new();
        let mut counterparty = Vec::new();
        for key in ["witness_labels", "counterparty"] {
            if document.get(key).is_some() != prover {
                return Err(format!(
                    "'{key}' is {} on a '{endpoint_name}' document",
                    if prover { "required" } else { "not admitted" }
                ));
            }
        }
        if prover {
            for pair in document
                .get("witness_labels")
                .and_then(Json::as_array)
                .ok_or("witness_labels is not an array")?
            {
                match pair.as_array() {
                    Some([Json::String(label), Json::String(class)]) => {
                        witness_labels.push((label.clone(), class.clone()))
                    }
                    _ => return Err(format!("malformed witness label {}", json::serialize(pair))),
                }
            }
            // Schema, uniqueness, and the closed discharge table are what
            // a source-free consumer can establish; coverage against the
            // source obligation set is authenticated only where the
            // sealed PIR is also present (endpoints.md §6.1), and the
            // emitted README repeats that nonclaim.
            for row in document
                .get("counterparty")
                .and_then(Json::as_array)
                .ok_or("counterparty is not an array")?
            {
                let (position, kind) = match row.as_array() {
                    Some([Json::UInt(position), Json::String(kind)]) => (*position, kind.clone()),
                    _ => {
                        return Err(format!(
                            "malformed counterparty row {}",
                            json::serialize(row)
                        ))
                    }
                };
                if !matches!(kind.as_str(), "assert_eq" | "check_call") {
                    return Err(format!(
                        "counterparty row cites discharge kind '{kind}', which no verifier-local \
                         check realizes"
                    ));
                }
                if counterparty
                    .iter()
                    .any(|(seen, _): &(u64, String)| *seen == position)
                {
                    return Err(format!(
                        "counterparty rows name event position {position} twice"
                    ));
                }
                counterparty.push((position, kind));
            }
        }

        let mut statement = Vec::new();
        for (index, label) in statement_labels.iter().enumerate() {
            match entry.get(index) {
                Some(Entry::Val(class)) => statement.push((label.clone(), class.clone())),
                _ => {
                    return Err(format!(
                        "statement label '{label}' is argument {index}, which is not a value \
                         entry; the statement occupies the first arguments"
                    ))
                }
            }
        }

        Ok(Document {
            artifact_id,
            semantic_id,
            endpoint,
            endpoint_name,
            codecs,
            entry,
            param_digests,
            rows,
            source,
            statement_labels,
            statement,
            witness_labels,
            counterparty,
        })
    }
}
