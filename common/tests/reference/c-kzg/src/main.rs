//! Evaluate EIP-4844 functions with c-kzg-4844 for the zkc vector corpus.
//!
//! Usage: `zkc-c-kzg-reference TRUSTED_SETUP < cases > results`. Each input
//! line is a function name followed by its arguments in hexadecimal; a list
//! argument separates elements with commas and writes the empty list as `-`.
//! Each output line is `true`, `false`, `error`, or the hexadecimal outputs.
use c_kzg::{Blob, Bytes32, Bytes48, KzgSettings};
use std::io::{BufRead, Write};
use std::path::Path;

fn hex(text: &str) -> Vec<u8> {
    assert!(text.len().is_multiple_of(2), "odd hexadecimal length");
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).expect("hexadecimal digit"))
        .collect()
}
fn encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn list(text: &str) -> Vec<Vec<u8>> {
    if text == "-" {
        Vec::new()
    } else {
        text.split(',').map(hex).collect()
    }
}
fn verdict(result: Result<bool, c_kzg::Error>) -> String {
    match result {
        Ok(true) => "true".into(),
        Ok(false) => "false".into(),
        Err(_) => "error".into(),
    }
}

/// Typed conversions refuse wrong lengths, as the upstream API does.
fn evaluate(settings: &KzgSettings, words: &[&str]) -> Result<String, c_kzg::Error> {
    let blob = |text: &str| Blob::from_bytes(&hex(text));
    let b48 = |text: &str| Bytes48::from_bytes(&hex(text));
    let b32 = |text: &str| Bytes32::from_bytes(&hex(text));
    Ok(match words {
        ["blob_to_kzg_commitment", b] => encode(
            settings
                .blob_to_kzg_commitment(&blob(b)?)?
                .to_bytes()
                .as_slice(),
        ),
        ["compute_kzg_proof", b, z] => {
            let (proof, y) = settings.compute_kzg_proof(&blob(b)?, &b32(z)?)?;
            format!(
                "{} {}",
                encode(proof.to_bytes().as_slice()),
                encode(y.as_slice())
            )
        }
        ["compute_blob_kzg_proof", b, c] => encode(
            settings
                .compute_blob_kzg_proof(&blob(b)?, &b48(c)?)?
                .to_bytes()
                .as_slice(),
        ),
        ["verify_kzg_proof", c, z, y, p] => {
            verdict(settings.verify_kzg_proof(&b48(c)?, &b32(z)?, &b32(y)?, &b48(p)?))
        }
        ["verify_blob_kzg_proof", b, c, p] => {
            verdict(settings.verify_blob_kzg_proof(&blob(b)?, &b48(c)?, &b48(p)?))
        }
        ["verify_blob_kzg_proof_batch", bs, cs, ps] => {
            let blobs = list(bs)
                .iter()
                .map(|b| Blob::from_bytes(b))
                .collect::<Result<Vec<_>, _>>()?;
            let commitments = list(cs)
                .iter()
                .map(|c| Bytes48::from_bytes(c))
                .collect::<Result<Vec<_>, _>>()?;
            let proofs = list(ps)
                .iter()
                .map(|p| Bytes48::from_bytes(p))
                .collect::<Result<Vec<_>, _>>()?;
            verdict(settings.verify_blob_kzg_proof_batch(&blobs, &commitments, &proofs))
        }
        _ => panic!("unknown request {:?}", words.first()),
    })
}

fn main() {
    let setup = std::env::args().nth(1).expect("trusted setup path");
    let settings =
        KzgSettings::load_trusted_setup_file(Path::new(&setup), 0).expect("trusted setup");
    let mut out = std::io::stdout().lock();
    for line in std::io::stdin().lock().lines() {
        let line = line.expect("input line");
        let words: Vec<&str> = line.split_whitespace().collect();
        let answer = evaluate(&settings, &words).unwrap_or_else(|_| "error".into());
        writeln!(out, "{answer}").expect("output");
    }
}
