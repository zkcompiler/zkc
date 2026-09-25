//! Separate production/validation processes with an application-owned root.
use super::observe::TraceMode;
use super::{ArtifactFailure, CheckedBundle, Observed, io::*, produce, validate_with_decoder};
use serde_json::{Value as Json, json};
use std::{io::Write, path::Path, time::Instant};
use zkc_backends::Value;
use zkc_runtime::interactive::{Runner, StopKind};

fn failure(error: &ArtifactFailure) -> String {
    match error {
        ArtifactFailure::Format(e) => e.to_string(),
        ArtifactFailure::Backend(e) => e.code.clone(),
        ArtifactFailure::Runtime(e) => e.to_string(),
        ArtifactFailure::Stopped(stop) => match &stop.kind {
            StopKind::Backend(e) => e.code.clone(),
            _ => format!("artifact-stopped:{:?}", stop.kind),
        },
        ArtifactFailure::UnexpectedCommunication => "artifact-unexpected-communication".into(),
        ArtifactFailure::AcceptanceType => "artifact-acceptance-type".into(),
        ArtifactFailure::Rejected => "artifact-rejected".into(),
    }
}
fn publish(path: &str, bytes: &[u8]) -> Result<()> {
    let path = Path::new(path);
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let mut file = tempfile::NamedTempFile::new_in(parent).map_err(|_| "artifact-publish-io")?;
    file.write_all(bytes).map_err(|_| "artifact-publish-io")?;
    file.as_file()
        .sync_all()
        .map_err(|_| "artifact-publish-io")?;
    file.persist(path).map_err(|_| "artifact-publish-io")?;
    Ok(())
}
/// Always returns a structured report, including the last reached phase on
/// admission/binding failures. Exit policy belongs to the CLI.
pub fn run(producer: bool, args: &[String]) -> Json {
    let mut report = json!({"status":"refused", "phase":"arguments", "code":"artifact-usage",
        "timings":{"admission_seconds":0.0,"key_load_seconds":0.0,"run_seconds":0.0},
        "proof_bytes":0,"messages":0,"events":[],"trace":"full"});
    let result = (|| -> Result<()> {
        let (args, trace) = match args.last().map(String::as_str) {
            Some("--trace=none") => (&args[..args.len() - 1], TraceMode::None),
            Some("--trace=full") => (&args[..args.len() - 1], TraceMode::Full),
            _ => (args, TraceMode::Full),
        };
        if trace == TraceMode::None {
            report["trace"] = json!("none");
            report["events"] = Json::Null;
        }
        let [
            source,
            descriptor,
            construction,
            physical,
            inputs,
            compiler,
            lean,
            proof_path,
            budget,
        ] = args
        else {
            return Err("usage: zkc produce-artifact|validate-artifact SOURCE DESCRIPTOR CONSTRUCTION PARTICIPANTS INPUTS COMPILER_CHECKER LEAN_CHECKER PROOF TRANSCRIPT_BUDGET [--trace=full|none]".into());
        };
        let budget = zkc_runtime::logical::natural_index(budget).map_err(|e| e.to_string())?;
        report["phase"] = json!("admission");
        let start = Instant::now();
        let bundle =
            CheckedBundle::load(source, descriptor, construction, physical, compiler, lean);
        report["timings"]["admission_seconds"] = json!(start.elapsed().as_secs_f64());
        let bundle = bundle?;
        report["phase"] = json!("key-load");
        let start = Instant::now();
        let bound = (|| {
            let input = parse(&read(inputs, INPUT_LIMIT)?, INPUT_LIMIT)?;
            let role = bundle.role(producer)?;
            bundle.bind(&input, &role, budget)
        })();
        report["timings"]["key_load_seconds"] = json!(start.elapsed().as_secs_f64());
        let bound = bound?;
        report["binding_sha256"] = json!(hex(&bound.binding));
        report["phase"] = json!("run");
        let start = Instant::now();
        let execution = (|| -> Result<()> {
            let backend = Observed::new(bound.backend, &bundle, trace)?;
            let role = if producer {
                &bundle.producer
            } else {
                &bundle.validator
            };
            let mut runner = Runner::new(
                &bundle.admitted,
                &bundle.entry,
                role,
                "artifact",
                backend,
                bound.values,
            )
            .map_err(|e| e.error.to_string())?;
            let (result, bytes, messages, candidate) = if producer {
                let r = produce(&mut runner, &bound.binding);
                match r.outcome {
                    Ok(p) => (Ok(()), r.bytes, r.messages, Some(p.proof)),
                    Err(e) => (Err(failure(&e)), r.bytes, r.messages, None),
                }
            } else {
                let proof = read(proof_path, super::MAX_PROOF_BYTES)?;
                report["candidate_bytes"] = json!(proof.len());
                let r = validate_with_decoder(
                    &mut runner,
                    &proof,
                    &bound.binding,
                    bundle.acceptance,
                    |v| {
                        if let Value::Bool(b) = v {
                            Some(*b)
                        } else {
                            None
                        }
                    },
                    &bound.decoder,
                );
                (
                    r.outcome.map(|_| ()).map_err(|e| failure(&e)),
                    r.bytes,
                    r.messages,
                    None,
                )
            };
            report["proof_bytes"] = json!(bytes);
            report["messages"] = json!(messages);
            if trace == TraceMode::Full {
                report["events"] = json!(runner.backend().events());
            }
            let usage = runner.usage();
            report["runtime"] = json!({"instructions":usage.instructions,"calls":usage.calls,"iterations":usage.iterations,
                "total_value_bytes":usage.total_value_bytes,"active_frames":runner.backend().inner().active_frames()});
            report["resources"] = json!(bound.resources.iter().map(|(name, token)| {
                match runner.backend().inner().observe(token) {
                    Ok(o) => json!({"port":name,"generation":o.generation,"transitions":o.draw_count,"budget":o.budget,"stage":o.stage}),
                    Err(_) => json!({"port":name,"status":"observation-unavailable"}),
                }
            }).collect::<Vec<_>>());
            result?;
            if let Some(candidate) = candidate {
                publish(proof_path, &candidate)?;
            }
            Ok(())
        })();
        report["timings"]["run_seconds"] = json!(start.elapsed().as_secs_f64());
        execution?;
        report["status"] = json!(if producer { "produced" } else { "accepted" });
        report["phase"] = json!("complete");
        report["code"] = Json::Null;
        Ok(())
    })();
    if let Err(code) = result {
        report["code"] = json!(code);
    }
    report
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trace_policy_is_explicit_and_invalid_arguments_do_not_load_artifacts() {
        for producer in [false, true] {
            for (flag, trace, events) in [
                (None, "full", json!([])),
                (Some("--trace=full"), "full", json!([])),
                (Some("--trace=none"), "none", Json::Null),
            ] {
                let args = flag.into_iter().map(str::to_owned).collect::<Vec<_>>();
                let report = run(producer, &args);
                assert_eq!(report["status"], "refused");
                assert_eq!(report["phase"], "arguments");
                assert_eq!(report["trace"], trace);
                assert_eq!(report["events"], events);
            }
            for flags in [
                vec!["--trace=unknown"],
                vec!["--trace=none", "--trace=full"],
                vec!["--trace=full", "--trace=none"],
            ] {
                let mut args = vec!["unopened".to_owned(); 9];
                args.extend(flags.into_iter().map(str::to_owned));
                let report = run(producer, &args);
                assert_eq!(report["status"], "refused");
                assert_eq!(report["phase"], "arguments");
            }
        }
    }
}
