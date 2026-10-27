//! Native counterpart for the browser round trip, using the same facade.
use serde_json::{Value as Json, json};
use std::{fs, path::Path, time::Instant};
use zkc_web::{ProofResult, ProofSession};
fn observation(result: Result<ProofResult, String>) -> Json {
    match result {
        Err(e) => json!({"error":e}),
        Ok(result) => {
            json!({"report":serde_json::from_str::<Json>(&result.report()).unwrap(), "proof_bytes":result.proof().len(), "has_outputs":result.outputs().is_some()})
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 3 {
        return Err("usage: memory FIXTURE_DIRECTORY AUTHORIZED_SHA256 OUTPUT_DIRECTORY".into());
    }
    let dir = Path::new(&args[0]);
    if args[1].len() != 64 || !args[1].is_ascii() {
        return Err("expected 64 hexadecimal pin characters".into());
    }
    let pin = (0..32)
        .map(|i| u8::from_str_radix(&args[1][2 * i..2 * i + 2], 16))
        .collect::<Result<Vec<_>, _>>()?;
    let out = Path::new(&args[2]);
    fs::create_dir_all(out)?;
    let package = fs::read(dir.join("entry.zkpkg"))?;
    let start = Instant::now();
    let mut session = ProofSession::new(&package, &pin, "{}", &[])?;
    let admission_ms = start.elapsed().as_secs_f64() * 1000.;
    let public = fs::read(dir.join("public.json"))?;
    let witness = fs::read(dir.join("witness.json"))?;
    let start = Instant::now();
    let result = session.prove(&public, &witness, &[], None)?;
    let prove_ms = start.elapsed().as_secs_f64() * 1000.;
    let produced: Json = serde_json::from_str(&result.report())?;
    if produced["success"] != true {
        return Err(format!("proof production failed: {produced}").into());
    }
    fs::write(out.join("native.proof"), result.proof())?;
    let start = Instant::now();
    let verified = session.verify(&public, &result.proof(), &[], None)?;
    let verify_ms = start.elapsed().as_secs_f64() * 1000.;
    let checked: Json = serde_json::from_str(&verified.report())?;
    if checked["success"] != true || checked["accepted"] != true {
        return Err(format!("proof verification failed: {checked}").into());
    }
    let browser = out.join("browser.proof");
    let cross = if browser.exists() {
        Some(
            session
                .verify(&public, &fs::read(browser)?, &[], None)?
                .report(),
        )
    } else {
        None
    };
    let mut unfilled: Json = serde_json::from_slice(&witness)?;
    let first = unfilled
        .as_object()
        .ok_or("witness map")?
        .keys()
        .next()
        .ok_or("witness field")?
        .clone();
    unfilled[&first] = Json::Null;
    let mut reference: Json = serde_json::from_slice(&public)?;
    let first = reference
        .as_object()
        .ok_or("public map")?
        .keys()
        .next()
        .ok_or("public field")?
        .clone();
    reference[&first] = json!({"file":"forbidden.bin","sha256":"00".repeat(32)});
    let controls = json!({
        "malformed": observation(session.prove(b"{", &witness, &[], None)),
        "unfilled": observation(session.prove(&public, &serde_json::to_vec(&unfilled)?, &[], None)),
        "reference": observation(session.prove(&serde_json::to_vec(&reference)?, &witness, &[], None)),
        "truncated": observation(session.verify(&public, &result.proof()[..5], &[], None)),
        "limited": observation(session.prove(&public, &witness, &[], Some(0))),
    });
    session.dispose();
    if session.describe().err().as_deref() != Some("web-session-disposed") {
        return Err("dispose failed".into());
    }
    println!(
        "{}",
        serde_json::json!({"admission_ms":admission_ms,"prove_ms":prove_ms,"verify_ms":verify_ms,"prove":produced,"verify":checked,"browser_cross_verify":cross,"controls":controls})
    );
    Ok(())
}
