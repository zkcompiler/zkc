//! zkc-emit: consume one canonical OIR verifier document plus one
//! supplier binding, and write a standalone Rust verifier crate.
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

fn parse_vectors(bytes: &[u8]) -> Result<emit::Vectors, String> {
    let root = json::parse(bytes)?;
    let artifact_id = root
        .get("artifact_id")
        .and_then(json::Json::as_str)
        .ok_or("vectors file has no artifact_id")?
        .to_owned();
    let mut cases = Vec::new();
    for case in root
        .get("vectors")
        .and_then(json::Json::as_array)
        .ok_or("vectors file has no vectors array")?
    {
        let field = |key: &str| -> Result<String, String> {
            case.get(key)
                .and_then(json::Json::as_str)
                .map(str::to_owned)
                .ok_or_else(|| format!("vector has no string field '{key}'"))
        };
        let mut statement = Vec::new();
        for (label, value) in case
            .get("statement")
            .and_then(json::Json::as_object)
            .ok_or("vector has no statement object")?
        {
            statement.push((
                label.clone(),
                value
                    .as_str()
                    .ok_or("statement value is not a string")?
                    .to_owned(),
            ));
        }
        let mut challenges = Vec::new();
        for entry in case
            .get("challenges")
            .and_then(json::Json::as_array)
            .ok_or("vector has no challenges array")?
        {
            challenges.push(
                entry
                    .as_str()
                    .ok_or("challenge entry is not a string")?
                    .to_owned(),
            );
        }
        cases.push(emit::VectorCase {
            name: field("name")?,
            statement,
            proof_hex: field("proof")?,
            expect: field("expect")?,
            challenges,
        });
    }
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
