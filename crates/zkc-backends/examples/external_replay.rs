//! `cargo run -p zkc-backends --example external_replay --offline -- FILE.json`
//! A missing path or `-` reads stdin. Writes one JSON result; failure exits 1.
use std::io::{Read, Write};
use zkc_backends::external::replay::{Limits, replay_json};
fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let path = args.next();
    if args.next().is_some() {
        return Err("expected at most one JSON path".into());
    }
    let input: Box<dyn Read> = match path.as_deref() {
        None | Some("-") => Box::new(std::io::stdin()),
        Some(path) => Box::new(std::fs::File::open(path)?),
    };
    let limits = Limits::default();
    let mut bytes = Vec::new();
    input
        .take(limits.input_bytes as u64 + 1)
        .read_to_end(&mut bytes)?;
    let output = replay_json(&bytes, limits)?;
    let mut stdout = std::io::stdout().lock();
    serde_json::to_writer(&mut stdout, &output)?;
    writeln!(stdout)?;
    Ok(())
}
