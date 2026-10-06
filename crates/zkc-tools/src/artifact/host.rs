//! Separate production/validation processes with an application-owned root.
use super::observe::TraceMode;
use super::{
    ArtifactFailure, ArtifactPaths, CacheLimits, CheckerInstallation, InvocationInputs,
    InvocationOptions, io::*,
};
use serde_json::{Value as Json, json};
use std::{io::Write, path::Path, time::Instant};
use zkc_runtime::interactive::StopKind;

pub(super) fn failure(error: &ArtifactFailure) -> String {
    match error {
        ArtifactFailure::StartedRunner => "artifact-runner-started".into(),
        ArtifactFailure::UnsupportedNativeProfile => {
            "native-participant-artifact-unsupported".into()
        }
        ArtifactFailure::Format(e) => e.to_string(),
        ArtifactFailure::Backend(e) => e.code.clone(),
        ArtifactFailure::NativeWire(e) => e.to_string(),
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
pub(super) fn publish(path: &str, bytes: &[u8]) -> Result<()> {
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
        "timings":{"scope":"prepared-execution","admission_seconds":0.0,"key_load_seconds":0.0,"run_seconds":0.0,
            "input_read_seconds":0.0,"proof_read_seconds":0.0,"publish_seconds":0.0},
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
        let installation = CheckerInstallation::new(compiler, lean);
        let prepared = installation.prepare(
            ArtifactPaths {
                source,
                descriptor,
                construction,
                participants: physical,
            },
            CacheLimits::default(),
        );
        report["timings"]["admission_seconds"] = json!(start.elapsed().as_secs_f64());
        let mut prepared = prepared?;
        report["phase"] = json!("key-load");
        let start = Instant::now();
        let input = InvocationInputs::read(inputs);
        report["timings"]["input_read_seconds"] = json!(start.elapsed().as_secs_f64());
        let input = input?;
        // Read candidate proof bytes before issuing any execution resources.
        let proof = if producer {
            None
        } else {
            let start = Instant::now();
            let bytes = read(proof_path, super::MAX_PROOF_BYTES);
            report["timings"]["proof_read_seconds"] = json!(start.elapsed().as_secs_f64());
            let bytes = bytes?;
            report["candidate_bytes"] = json!(bytes.len());
            Some(bytes)
        };
        let mut options = InvocationOptions::new(budget);
        options.trace = trace;
        let result = prepared
            .execute(&installation, &input, options, proof.as_deref())
            .map_err(|e| e.to_string())?;
        report["phase"] = json!(result.phase);
        report["binding_sha256"] = json!(hex(&result.binding));
        report["timings"]["key_load_seconds"] = json!(result.bind_time.as_secs_f64());
        report["timings"]["run_seconds"] = json!(result.run_time.as_secs_f64());
        report["proof_bytes"] = json!(result.execution.bytes);
        report["messages"] = json!(result.execution.messages);
        report["events"] = json!(result.events);
        report["resources"] = json!(result.resources);
        report["cleanup_errors"] = json!(result.cleanup_errors);
        let usage = result.usage;
        report["runtime"] = json!({"instructions":usage.instructions,"calls":usage.calls,"iterations":usage.iterations,
            "total_value_bytes":usage.total_value_bytes,"active_frames":result.active_frames});
        let candidate = result.execution.outcome.map_err(|e| failure(&e))?;
        if !result.cleanup_errors.is_empty() {
            return Err("artifact-cleanup".into());
        }
        if producer {
            let start = Instant::now();
            let published = publish(proof_path, &candidate);
            report["timings"]["publish_seconds"] = json!(start.elapsed().as_secs_f64());
            published?;
        }
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
