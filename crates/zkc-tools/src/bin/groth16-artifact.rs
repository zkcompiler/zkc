//! Command-line host for the explicit compiled PIR Groth16 program.
use serde_json::json;
use std::{collections::BTreeMap, path::PathBuf, time::Instant};
use zkc_tools::{
    groth16::{
        self, MAX_JSON_BYTES, PreparedProtocol, PreparedRelation, ProverKey, Randomness, Statement,
        VerifyingKey,
    },
    snarkjs::{self, Limits},
};

const HELP: &str = "groth16-artifact prove|verify|bench OPTIONS
Required:
  --compiler PATH        installed native zkc-compile
  --lean PATH            installed interactive-protocol correspondence checker
  --vk PATH              application-selected snarkjs verification key
  --public PATH          expected snarkjs public signals
  --context TEXT         application-selected relation/key context
Code (choose one):
  --source PATH          Groth16 PIR with the maintained Core view/port contract
                         (default: embedded groth16.pir)
  --r1cs PATH            actual relation, required when compiling or proving
  --common PATH --endpoints PATH --relation-id HEX
                         application-authenticated cached source/endpoints and
                         declared relation context; does not rederive the R1CS
  --save-code PREFIX     save .common.json, .endpoints.json and .relation-id
Prove/bench:
  --zkey PATH --witness PATH
  --proof PATH           output snarkjs JSON (required for prove)
  --artifact PATH        optional output bound ZKCPRF01
  --test-randomness R,S   explicit canonical scalars; requires test-utils feature
Verify:
  --proof PATH           snarkjs JSON candidate
  --artifact PATH        bound ZKCPRF01 candidate (choose exactly one)
Bench:
  --iterations N         repeated prepared invocations, default 5, maximum 1000
Outputs one JSON timing record. Preparation includes compilation and Lean
admission; key_import and statement_binding are separate. Repeated prove and
verify measurements exclude those phases and process startup. Test fixtures
have public trapdoors and do not constitute a secure setup.";
fn required<'a>(options: &'a BTreeMap<String, String>, key: &str) -> Result<&'a str, String> {
    options
        .get(key)
        .map(String::as_str)
        .ok_or_else(|| format!("missing --{key}"))
}
fn read(path: &str) -> Result<Vec<u8>, String> {
    groth16::read_bounded(path, MAX_JSON_BYTES).map_err(|e| e.to_string())
}
fn ms(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1000.0
}
fn run() -> Result<serde_json::Value, String> {
    let mut args = std::env::args().skip(1);
    let command = args.next().ok_or_else(|| HELP.to_owned())?;
    if command == "--help" || command == "-h" {
        println!("{HELP}");
        return Ok(json!({"status":"help"}));
    }
    if !["prove", "verify", "bench"].contains(&command.as_str()) {
        return Err(HELP.into());
    }
    let mut options = BTreeMap::new();
    while let Some(flag) = args.next() {
        let name = flag
            .strip_prefix("--")
            .ok_or_else(|| format!("unexpected {flag}"))?;
        if ![
            "r1cs",
            "relation-id",
            "save-code",
            "compiler",
            "lean",
            "vk",
            "public",
            "context",
            "source",
            "common",
            "endpoints",
            "zkey",
            "witness",
            "proof",
            "artifact",
            "test-randomness",
            "iterations",
        ]
        .contains(&name)
        {
            return Err(format!("unknown {flag}"));
        }
        let value = args
            .next()
            .ok_or_else(|| format!("missing value for {flag}"))?;
        if options.insert(name.to_owned(), value).is_some() {
            return Err(format!("duplicate {flag}"));
        }
    }
    let compiler = required(&options, "compiler")?;
    let lean = required(&options, "lean")?;
    let context = required(&options, "context")?;
    let vk_path = required(&options, "vk")?;
    let public_path = required(&options, "public")?;
    let iterations = options
        .get("iterations")
        .map(|n| n.parse::<usize>().map_err(|_| "invalid iterations"))
        .transpose()?
        .unwrap_or(5);
    if iterations == 0
        || iterations > 1000
        || (command != "bench" && options.contains_key("iterations"))
    {
        return Err("invalid iterations".into());
    }
    if command == "verify" {
        for name in ["zkey", "witness", "test-randomness"] {
            if options.contains_key(name) {
                return Err(format!("--{name} is not a verifier input"));
            }
        }
        if options.contains_key("proof") == options.contains_key("artifact") {
            return Err("verify needs exactly one of --proof or --artifact".into());
        }
    }
    if command == "prove" {
        required(&options, "proof")?;
    }
    let random = if let Some(value) = options.get("test-randomness") {
        #[cfg(feature = "test-utils")]
        {
            let (r, s) = value.split_once(',').ok_or("expected R,S")?;
            Randomness::Test {
                r: zkc_arkworks::bn254::parse_decimal(r).map_err(|e| e.to_string())?,
                s: zkc_arkworks::bn254::parse_decimal(s).map_err(|e| e.to_string())?,
            }
        }
        #[cfg(not(feature = "test-utils"))]
        {
            let _ = value;
            return Err("--test-randomness requires the test-utils feature".into());
        }
    } else {
        Randomness::Os
    };
    let preparation = Instant::now();
    let protocol = match (options.get("common"), options.get("endpoints")) {
        (Some(common), Some(endpoints)) if !options.contains_key("source") => {
            PreparedProtocol::prepare(
                &read(common)?,
                &read(endpoints)?,
                lean,
                required(&options, "relation-id")?,
            )
        }
        (None, None) => {
            let source = options
                .get("source")
                .map(|p| groth16::read_bounded(p, 1_048_576))
                .transpose()
                .map_err(|e| e.to_string())?
                .unwrap_or_else(|| {
                    include_bytes!("../../../../examples/protocols/groth16.pir").to_vec()
                });
            PreparedProtocol::compile(
                compiler,
                lean,
                &source,
                &groth16::read_bounded(required(&options, "r1cs")?, 64 * 1024 * 1024)
                    .map_err(|e| e.to_string())?,
            )
        }
        _ => return Err("choose --source or both --common and --endpoints".into()),
    }
    .map_err(|e| e.to_string())?;
    let preparation_ms = ms(preparation);
    if let Some(prefix) = options.get("save-code") {
        for (suffix, bytes) in [
            ("common.json", protocol.source()),
            ("endpoints.json", protocol.endpoints()),
            ("relation-id", protocol.relation_identity().as_bytes()),
        ] {
            std::fs::write(format!("{prefix}.{suffix}"), bytes).map_err(|e| e.to_string())?;
        }
    }
    let import = Instant::now();
    let vk = VerifyingKey::from_json(&read(vk_path)?).map_err(|e| e.to_string())?;
    let statement = Statement::from_json(&read(public_path)?).map_err(|e| e.to_string())?;
    let proving = if command != "verify" {
        let key = snarkjs::read_zkey(
            required(&options, "zkey")?,
            &Limits::default(),
            &groth16::policy(),
        )
        .map_err(|e| e.to_string())?;
        let witness = snarkjs::read_wtns(
            required(&options, "witness")?,
            &Limits::default(),
            &groth16::policy(),
        )
        .map_err(|e| e.to_string())?;
        let relation = if let Some(relation) = protocol.relation() {
            relation.clone()
        } else {
            PreparedRelation::read(compiler, required(&options, "r1cs")?)
                .map_err(|e| e.to_string())?
        };
        Some((
            ProverKey::new(&key, &vk, &relation).map_err(|e| e.to_string())?,
            witness,
        ))
    } else {
        None
    };
    let key_import_ms = ms(import);
    let binding = Instant::now();
    let invocation = protocol
        .bind(vk, statement, context.as_bytes())
        .map_err(|e| e.to_string())?;
    let statement_binding_ms = ms(binding);
    let mut prove_ms = Vec::new();
    let mut verify_ms = Vec::new();
    let mut json_ms = Vec::new();
    let mut last = None;
    let loops = if command == "bench" { iterations } else { 1 };
    for _ in 0..loops {
        if let Some((key, witness)) = &proving {
            let start = Instant::now();
            let produced = invocation
                .prove(key, witness, random.clone())
                .map_err(|e| e.to_string())?;
            prove_ms.push(ms(start));
            let start = Instant::now();
            invocation
                .verify_artifact(&produced.artifact)
                .map_err(|e| e.to_string())?;
            verify_ms.push(ms(start));
            let start = Instant::now();
            let json = produced.proof.to_json().map_err(|e| e.to_string())?;
            json_ms.push(ms(start));
            last = Some((json, produced.artifact));
        } else {
            let start = Instant::now();
            if let Some(path) = options.get("proof") {
                invocation
                    .verify_json(&read(path)?)
                    .map_err(|e| e.to_string())?;
            } else {
                invocation
                    .verify_artifact(&read(required(&options, "artifact")?)?)
                    .map_err(|e| e.to_string())?;
            }
            verify_ms.push(ms(start));
        }
    }
    if let Some((json, artifact)) = &last {
        if let Some(path) = options.get("proof") {
            std::fs::write(PathBuf::from(path), json).map_err(|e| e.to_string())?;
        }
        if let Some(path) = options.get("artifact") {
            std::fs::write(PathBuf::from(path), artifact).map_err(|e| e.to_string())?;
        }
    }
    Ok(
        json!({"status":"accepted", "command":command, "iterations":loops,
        "relation_identity":protocol.relation_identity(), "key_binding":proving.as_ref().map(|(k,_)|k.binding_record()),
        "relation_identity_basis":if protocol.relation().is_some() {"computed-from-imported-r1cs"} else {"application-declared-cached-source-context"},
        "preparation_ms":preparation_ms, "key_import_ms":key_import_ms, "statement_binding_ms":statement_binding_ms,
        "prove_ms":prove_ms, "verify_ms":verify_ms, "proof_json_ms":json_ms,
        "randomness":if options.contains_key("test-randomness") {"explicit-test-tape"} else {"os"},
        "artifact_bytes":last.as_ref().map(|(_,a)| a.len()),
        "snarkjs_json_bytes":last.as_ref().map(|(j,_)| j.len()) }),
    )
}
fn main() {
    match run() {
        Ok(value) => println!("{value}"),
        Err(error) => {
            eprintln!("{}", json!({"status":"refused", "error":error}));
            std::process::exit(1);
        }
    }
}
