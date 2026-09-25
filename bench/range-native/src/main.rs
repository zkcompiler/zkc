use std::{env, fs, io::Read, path::Path};
use zkc_range_native_research::{Generators, Statement, VerifierMode, experiment, validate};

fn unhex(s: &str) -> Result<Vec<u8>, String> {
    if !s.is_ascii() || !s.len().is_multiple_of(2) {
        return Err("invalid hex".into());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|_| "invalid hex".into()))
        .collect()
}
fn bounded_read(path: &str, limit: usize) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut out = Vec::new();
    fs::File::open(path)?
        .take((limit + 1) as u64)
        .read_to_end(&mut out)?;
    if out.len() > limit {
        return Err("input exceeds research profile limit".into());
    }
    Ok(out)
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    if args.first().map(String::as_str) == Some("verify") {
        if args.len() != 3 {
            return Err("usage: range-native verify statement.json proof.bin".into());
        }
        // Reads actual proof bytes, never an in-process prover object.
        let bytes = bounded_read(&args[2], 32 * (9 + 2 * 14))?;
        let v: serde_json::Value = serde_json::from_slice(&bounded_read(&args[1], 1 << 20)?)?;
        let bits = usize::try_from(v["bits"].as_u64().ok_or("bits")?)?;
        let count = usize::try_from(v["count"].as_u64().ok_or("count")?)?;
        let context = unhex(v["context_hex"].as_str().ok_or("context_hex")?)?;
        let commitments = v["commitments_hex"]
            .as_array()
            .ok_or("commitments_hex")?
            .iter()
            .map(|x| {
                unhex(x.as_str().ok_or("commitment")?)
                    .and_then(|b| b.try_into().map_err(|_| "commitment length".into()))
            })
            .collect::<Result<Vec<[u8; 32]>, String>>()?;
        let s = Statement {
            bits,
            count,
            context,
            commitments,
        };
        let gens = Generators::new(bits, count)?;
        for mode in [
            VerifierMode::Folding,
            VerifierMode::FlatMaterialized,
            VerifierMode::FlatPulledBack,
        ] {
            validate(&gens, &s, &bytes, mode)?;
        }
        println!("accepted: range equation and full IPA terminal equation; three exact validators");
        return Ok(());
    }
    let repeats = args.first().map(|s| s.parse()).transpose()?.unwrap_or(9);
    let result = experiment::run(repeats);
    // Fixture exports are confined to this crate's records directory, which is
    // a build output: it is created on demand and never committed.
    let records = Path::new(env!("CARGO_MANIFEST_DIR")).join("records");
    fs::create_dir_all(&records)?;
    for case in result["cases"].as_array().unwrap() {
        let stem = format!("n{}-m{}", case["bits"], case["count"]);
        let statement = serde_json::json!({"bits":case["bits"],"count":case["count"],"context_hex":case["public_context_hex"],"commitments_hex":case["commitments_hex"]});
        fs::write(
            records.join(format!("{stem}.statement.json")),
            serde_json::to_vec_pretty(&statement)?,
        )?;
        fs::write(
            records.join(format!("{stem}.native.proof")),
            unhex(case["native_proof_hex"].as_str().unwrap())?,
        )?;
        fs::write(
            records.join(format!("{stem}.upstream.proof")),
            unhex(case["upstream_proof_hex"].as_str().unwrap())?,
        )?;
    }
    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}
