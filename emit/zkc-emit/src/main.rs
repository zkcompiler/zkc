//! zkc-emit: consume one canonical OIR document plus one supplier
//! binding, and write a standalone Rust crate for the endpoint the
//! document declares — a verifier, or a prover.
//!
//! Drivers own IO; the emitter owns nothing but the walk. Identity is
//! recomputed from the document bytes before any semantics are read, and
//! every supplier gap refuses here — at emit time — naming what is
//! missing, so the emitted crate has no "cannot judge" arm.

mod binding;
mod doc;
mod emit;
mod json;

use std::path::{Path, PathBuf};
use std::process::ExitCode;

struct Args {
    doc: PathBuf,
    binding: PathBuf,
    rt_path: String,
    out: PathBuf,
    vectors: Option<PathBuf>,
    crate_name: Option<String>,
}

fn usage() -> String {
    "usage: zkc-emit --doc <canonical-oir.json> --binding <binding.json> \
     --rt-path <path-to-zkc-rt> --out <dir> [--vectors <vectors.json>] \
     [--crate-name <name>]"
        .into()
}

fn parse_args() -> Result<Args, String> {
    let mut doc = None;
    let mut binding = None;
    let mut rt_path = None;
    let mut out = None;
    let mut vectors = None;
    let mut crate_name = None;
    let mut arguments = std::env::args().skip(1);
    while let Some(flag) = arguments.next() {
        let mut value = || {
            arguments
                .next()
                .ok_or_else(|| format!("{flag} needs a value"))
        };
        match flag.as_str() {
            "--doc" => doc = Some(PathBuf::from(value()?)),
            "--binding" => binding = Some(PathBuf::from(value()?)),
            "--rt-path" => rt_path = Some(value()?),
            "--out" => out = Some(PathBuf::from(value()?)),
            "--vectors" => vectors = Some(PathBuf::from(value()?)),
            "--crate-name" => crate_name = Some(value()?),
            other => return Err(format!("unknown flag '{other}'\n{}", usage())),
        }
    }
    Ok(Args {
        doc: doc.ok_or_else(usage)?,
        binding: binding.ok_or_else(usage)?,
        rt_path: rt_path.ok_or_else(usage)?,
        out: out.ok_or_else(usage)?,
        vectors,
        crate_name,
    })
}

fn read(path: &Path) -> Result<Vec<u8>, String> {
    std::fs::read(path).map_err(|error| format!("cannot read {}: {error}", path.display()))
}

/// A `label → text` object, in stored order.
fn labelled(case: &json::Json, key: &str) -> Result<Vec<(String, String)>, String> {
    let mut pairs = Vec::new();
    for (label, value) in case
        .get(key)
        .and_then(json::Json::as_object)
        .ok_or_else(|| format!("vector has no '{key}' object"))?
    {
        pairs.push((
            label.clone(),
            value
                .as_str()
                .ok_or_else(|| format!("'{key}' value is not a string"))?
                .to_owned(),
        ));
    }
    Ok(pairs)
}

fn strings(case: &json::Json, key: &str) -> Result<Vec<String>, String> {
    let mut items = Vec::new();
    for entry in case
        .get(key)
        .and_then(json::Json::as_array)
        .ok_or_else(|| format!("vector has no '{key}' array"))?
    {
        items.push(
            entry
                .as_str()
                .ok_or_else(|| format!("'{key}' entry is not a string"))?
                .to_owned(),
        );
    }
    Ok(items)
}

/// The corpus is endpoint-shaped and says so in its top-level key:
/// `vectors` describes verifier replays, `prover_vectors` prover runs.
/// Reading one as the other is the mismatch the emitter refuses.
fn parse_vectors(bytes: &[u8]) -> Result<emit::Vectors, String> {
    let root = json::parse(bytes)?;
    let artifact_id = root
        .get("artifact_id")
        .and_then(json::Json::as_str)
        .ok_or("vectors file has no artifact_id")?
        .to_owned();
    let field = |case: &json::Json, key: &str| -> Result<String, String> {
        case.get(key)
            .and_then(json::Json::as_str)
            .map(str::to_owned)
            .ok_or_else(|| format!("vector has no string field '{key}'"))
    };

    let cases = match (root.get("vectors"), root.get("prover_vectors")) {
        (Some(list), None) => {
            let mut cases = Vec::new();
            for case in list
                .as_array()
                .ok_or("vectors file's 'vectors' is not an array")?
            {
                cases.push(emit::VectorCase {
                    name: field(case, "name")?,
                    statement: labelled(case, "statement")?,
                    proof_hex: field(case, "proof")?,
                    expect: field(case, "expect")?,
                    challenges: strings(case, "challenges")?,
                });
            }
            emit::Cases::Verifier(cases)
        }
        (None, Some(list)) => {
            let mut cases = Vec::new();
            for case in list
                .as_array()
                .ok_or("vectors file's 'prover_vectors' is not an array")?
            {
                let expect = field(case, "expect")?;
                cases.push(emit::ProverCase {
                    name: field(case, "name")?,
                    statement: labelled(case, "statement")?,
                    witness: labelled(case, "witness")?,
                    label: if expect == "ok" {
                        String::new()
                    } else {
                        field(case, "label")?
                    },
                    message: if expect == "ok" {
                        String::new()
                    } else {
                        field(case, "message")?
                    },
                    expect,
                    proof_hex: field(case, "proof")?,
                    challenges: strings(case, "challenges")?,
                });
            }
            emit::Cases::Prover(cases)
        }
        _ => {
            return Err(
                "a vectors file carries exactly one of 'vectors' (verifier) and \
                 'prover_vectors' (prover)"
                    .into(),
            )
        }
    };
    Ok(emit::Vectors { artifact_id, cases })
}

fn write(path: &Path, contents: &str) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|error| format!("cannot create {}: {error}", parent.display()))?;
    }
    std::fs::write(path, contents)
        .map_err(|error| format!("cannot write {}: {error}", path.display()))
}

fn run() -> Result<(), String> {
    let args = parse_args()?;
    let document = doc::Document::parse(&read(&args.doc)?)?;
    let binding = binding::Binding::parse(&read(&args.binding)?)?;
    let vectors = match &args.vectors {
        None => None,
        Some(path) => Some(parse_vectors(&read(path)?)?),
    };

    let emitted = emit::emit(
        &document,
        &binding,
        &args.rt_path,
        args.crate_name.as_deref(),
        vectors.as_ref(),
    )?;

    write(&args.out.join("Cargo.toml"), &emitted.cargo_toml)?;
    write(&args.out.join("README.md"), &emitted.readme)?;
    write(&args.out.join("src/lib.rs"), &emitted.lib_rs)?;
    if let Some(conformance) = &emitted.conformance {
        write(&args.out.join("tests/conformance.rs"), conformance)?;
    }

    println!("artifact id: {}", document.artifact_id);
    println!("semantic id: {}", document.semantic_id);
    println!(
        "emitted: {} (crate {}, binding {})",
        args.out.display(),
        emitted.crate_name,
        binding.name
    );
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("zkc-emit: {message}");
            ExitCode::FAILURE
        }
    }
}
