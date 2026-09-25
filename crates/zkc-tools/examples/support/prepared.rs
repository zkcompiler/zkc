//! Repeat the same complete artifact in one process, using production randomness.
//! Caller requirements can be retained with the admitted artifact. Application
//! wrappers must still authorize each invocation's actual context and inputs.
//! Example flags are named; no additional artifact JSON format is introduced.
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, time::Instant};
use zkc_tools::artifact::{
    ArtifactPaths, CacheLimits, CheckerInstallation, ClaimRequirements, InvocationInputs,
    InvocationOptions, PhysicalChoices, TraceMode, hex,
};

pub fn run(mut memory: impl FnMut(bool) -> serde_json::Value) -> Result<(), String> {
    let mut args = BTreeMap::new();
    let mut iter = std::env::args().skip(1);
    while let Some(flag) = iter.next() {
        if ![
            "--source",
            "--descriptor",
            "--construction",
            "--participants",
            "--compiler",
            "--lean",
            "--producer-inputs",
            "--validator-inputs",
            "--transcript-budget",
            "--repetitions",
            "--trace",
            "--cache-bytes",
            "--cache-entries",
            "--contract",
            "--certificate",
            "--implementations",
            "--linear-contractions",
            "--release-storage",
            "--live-value-bytes",
            "--total-value-bytes",
            "--proof-output",
        ]
        .contains(&flag.as_str())
        {
            return Err(format!("unknown flag {flag}"));
        }
        let value = iter
            .next()
            .ok_or_else(|| format!("missing value for {flag}"))?;
        if args.insert(flag.clone(), value).is_some() {
            return Err(format!("duplicate {flag}"));
        }
    }
    let get = |name: &str| {
        args.get(name)
            .map(String::as_str)
            .ok_or_else(|| format!("missing {name}"))
    };
    let repeats: usize = get("--repetitions")?
        .parse()
        .map_err(|_| "invalid repetitions")?;
    if repeats == 0 {
        return Err("repetitions must be positive".into());
    }
    let installation = CheckerInstallation::new(get("--compiler")?, get("--lean")?);
    let mut limits = CacheLimits::default();
    if let Some(bytes) = args.get("--cache-bytes") {
        limits.bytes = bytes.parse().map_err(|_| "invalid cache bytes")?;
    }
    if let Some(entries) = args.get("--cache-entries") {
        limits.entries = entries.parse().map_err(|_| "invalid cache entries")?;
    }
    memory(true);
    let start = Instant::now();
    let mut prepared = installation.prepare(
        ArtifactPaths {
            source: get("--source")?,
            descriptor: get("--descriptor")?,
            construction: get("--construction")?,
            participants: get("--participants")?,
        },
        limits,
    )?;
    let admission = start.elapsed();
    let start = Instant::now();
    let mut choices = PhysicalChoices::default();
    if let Some(value) = args.get("--linear-contractions") {
        choices.linear_contractions = value.parse().map_err(|_| "invalid linear contractions")?;
    }
    if let Some(value) = args.get("--release-storage") {
        choices.release_storage = value.parse().map_err(|_| "invalid release storage")?;
    }
    if let Some(path) = args.get("--implementations") {
        choices = choices.with_implementations(&std::fs::read(path).map_err(|e| e.to_string())?)?;
    }
    match (args.get("--contract"), args.get("--certificate")) {
        (Some(contract), Some(certificate)) => {
            let read = |path| std::fs::read(path).map_err(|e| format!("{e}"));
            let requirements =
                ClaimRequirements::from_slices(&read(contract)?, &read(certificate)?)?;
            prepared = prepared.with_requirements(&installation, requirements, choices)?;
        }
        (None, None)
            if !args.contains_key("--implementations")
                && !choices.linear_contractions
                && !choices.release_storage => {}
        _ => return Err("contract and certificate required together with physical choices".into()),
    }
    let claims = start.elapsed();
    let start = Instant::now();
    let producer = InvocationInputs::read(get("--producer-inputs")?)?;
    let validator = InvocationInputs::read(get("--validator-inputs")?)?;
    let input_parse = start.elapsed();
    let mut options = InvocationOptions::new(
        get("--transcript-budget")?
            .parse()
            .map_err(|_| "invalid transcript budget")?,
    );
    options.trace = match args.get("--trace").map(String::as_str).unwrap_or("none") {
        "none" => TraceMode::None,
        "full" => TraceMode::Full,
        _ => return Err("invalid trace".into()),
    };
    if let Some(value) = args.get("--live-value-bytes") {
        options.value_budget.live_bytes = value.parse().map_err(|_| "invalid live value bytes")?;
    }
    if let Some(value) = args.get("--total-value-bytes") {
        options.value_budget.total_bytes =
            value.parse().map_err(|_| "invalid total value bytes")?;
    }
    println!(
        "{}",
        json!({"memory":memory(false), "phase":"prepared", "admission_seconds":admission.as_secs_f64(),
        "claim_admission_seconds":claims.as_secs_f64(),
        "input_parse_seconds":input_parse.as_secs_f64(),
        "claim_contract_admitted":prepared.checked_requirements().is_some(),
        "application_authorization_included":false,
        "trace":format!("{:?}", options.trace),
        "value_budget":{"live_bytes":options.value_budget.live_bytes,"total_bytes":options.value_budget.total_bytes},
        "cache_entries_limit":limits.entries.min(64),
        "cache_bytes_limit":limits.bytes.min(64 << 20)})
    );
    let mut previous = None;
    for repetition in 0..repeats {
        memory(true);
        let p = prepared
            .produce(&installation, &producer, options)
            .map_err(|e| e.to_string())?;
        let proof = p.execution.outcome.map_err(|e| format!("produce: {e:?}"))?;
        let producer_memory = memory(false);
        memory(true);
        let v = prepared
            .validate(&installation, &validator, &proof, options)
            .map_err(|e| e.to_string())?;
        v.execution
            .outcome
            .map_err(|e| format!("validate: {e:?}"))?;
        let validator_memory = memory(false);
        let cache = prepared.cache_usage();
        println!(
            "{}",
            json!({"phase":"accepted", "repetition":repetition,
            "producer_memory":producer_memory, "validator_memory":validator_memory,
            "binding_sha256":hex(&p.binding), "proof_bytes":proof.len(),
            "proof_sha256":hex(&Sha256::digest(&proof)),
            "differs_from_previous":previous.as_ref().map(|p| p != &proof),
            "producer_bind_seconds":p.bind_time.as_secs_f64(),
            "producer_run_seconds":p.run_time.as_secs_f64(),
            "validator_bind_seconds":v.bind_time.as_secs_f64(),
            "validator_run_seconds":v.run_time.as_secs_f64(),
            "producer_total_value_bytes":p.usage.total_value_bytes,
            "validator_total_value_bytes":v.usage.total_value_bytes,
            "cache_entries":cache.entries, "cache_bytes":cache.bytes})
        );
        previous = Some(proof);
    }
    // Export outside both run timers; callers can independently validate the
    // last produced proof under a different host resource policy.
    if let (Some(path), Some(proof)) = (args.get("--proof-output"), previous) {
        std::fs::write(path, proof).map_err(|e| format!("write proof: {e}"))?;
    }
    Ok(())
}
