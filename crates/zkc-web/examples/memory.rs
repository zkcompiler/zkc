//! Native counterpart for the browser round trip, using the same facade.
use serde_json::{Value as Json, json};
use std::{fs, path::Path, time::Instant};
use zkc_web::{ProofResult, ProofSession};
fn observation(result: Result<ProofResult, String>) -> Json {
    match result {
        Err(e) => match serde_json::from_str::<Json>(&e)
            .ok()
            .and_then(|v| v.get("sdk_refusal").cloned())
        {
            Some(refusal) => json!({"error":refusal["code"], "refusal":refusal}),
            None => json!({"error":e}),
        },
        Ok(result) => {
            json!({"report":serde_json::from_str::<Json>(&result.report()).unwrap(), "proof_bytes":result.proof().len(), "has_outputs":result.outputs().is_some()})
        }
    }
}

fn optional_json(path: &Path, default: Json) -> Result<Json, Box<dyn std::error::Error>> {
    match fs::read(path) {
        Ok(bytes) => Ok(serde_json::from_slice(&bytes)?),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(default),
        Err(error) => Err(error.into()),
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
    let options = optional_json(&dir.join("options.json"), json!({}))?;
    let authority = optional_json(&dir.join("authority.json"), Json::Null)?;
    let authority = if authority.is_null() {
        Vec::new()
    } else {
        serde_json::to_vec(&authority)?
    };
    let mut session = ProofSession::new(&package, &pin, &options.to_string(), &authority)?;
    for binding in optional_json(&dir.join("setups.json"), json!([]))?
        .as_array()
        .ok_or("setup bindings")?
    {
        session.set_setup(
            binding["slot"].as_str().ok_or("setup slot")?,
            &fs::read(dir.join(binding["path"].as_str().ok_or("setup path")?))?,
        )?;
    }
    for binding in optional_json(&dir.join("inputs.json"), json!([]))?
        .as_array()
        .ok_or("input bindings")?
    {
        session.set_input(
            binding["name"].as_str().ok_or("input name")?,
            &fs::read(dir.join(binding["path"].as_str().ok_or("input path")?))?,
        )?;
    }
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
    let mut controls = json!({
        "malformed": observation(session.prove(b"{", &witness, &[], None)),
        "truncated": observation(session.verify(&public, &result.proof()[..result.proof().len().min(5)], &[], None)),
        "limited": observation(session.prove(&public, &witness, &[], Some(0))),
    });
    let mut trailing = result.proof();
    trailing.push(0);
    controls["trailing"] = observation(session.verify(&public, &trailing, &[], None));
    controls["context"] = observation(session.verify(&public, &result.proof(), &[1], None));
    let mut unfilled: Json = serde_json::from_slice(&witness)?;
    if let Some(first) = unfilled
        .as_object()
        .and_then(|object| object.keys().next())
        .cloned()
    {
        unfilled[&first] = Json::Null;
        controls["unfilled"] =
            observation(session.prove(&public, &serde_json::to_vec(&unfilled)?, &[], None));
    }
    let mut reference: Json = serde_json::from_slice(&public)?;
    if let Some(first) = reference
        .as_object()
        .and_then(|object| object.keys().next())
        .cloned()
    {
        reference[&first] = json!({"file":"forbidden.bin","sha256":"00".repeat(32)});
        controls["reference"] =
            observation(session.prove(&serde_json::to_vec(&reference)?, &witness, &[], None));
    }
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
