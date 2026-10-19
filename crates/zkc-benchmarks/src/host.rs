//! Generic source Entry benchmark. No protocol-specific interpretation.
use crate::{
    Failure, Operation, Report, Request, Result,
    measure::measure,
    observation::{Call, Lifecycle, Limits, Preparation},
};
use serde::Deserialize;
use serde_json::json;
use std::{
    cell::{Cell, RefCell},
    path::{Path, PathBuf},
    time::Instant,
};
use zkc_runtime::vm::StopKind;
use zkc_tools::entry::{
    BindingPolicy, Package, ProofEntry, ProofOptions, ProofRequest, inputs::Decoder,
};

fn rejection(error: Option<&str>, stop: Option<&StopKind>) -> Option<&'static str> {
    if matches!(stop, None | Some(StopKind::Cancelled)) {
        match error {
            Some("proof-header") => return Some("binding"),
            Some("proof-truncated" | "proof-trailing") => return Some("format"),
            // The proof driver assigns this only to a returned false acceptance.
            Some("artifact-rejected") => return Some("verification"),
            _ => {}
        }
    }
    match stop {
        Some(StopKind::Explicit(reason)) if reason == "reject" => Some("verification"),
        _ => None,
    }
}
fn preparation_stats(entry: &ProofEntry) -> Preparation {
    let stats = entry.preparation_stats();
    Preparation {
        entries: stats.entries,
        retained_bytes: stats.bytes,
        hits: stats.hits,
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Input {
    pub public: PathBuf,
    pub witness: Option<PathBuf>,
    pub proof: Option<PathBuf>,
}

/// File reads are outside capture and admission; those two phases are distinct.
pub fn capture(path: &Path, sha256: &str) -> Result<(Package, u128)> {
    let bytes = std::fs::read(path).map_err(|e| e.to_string())?;
    if sha256.len() != 64 {
        return Err("expected package SHA-256".into());
    }
    let mut pin = [0; 32];
    for (i, b) in pin.iter_mut().enumerate() {
        *b = u8::from_str_radix(sha256.get(i * 2..i * 2 + 2).ok_or("invalid digest")?, 16)
            .map_err(|e| e.to_string())?;
    }
    let start = Instant::now();
    let package = Package::capture(&bytes, &pin, Package::MAX_BYTES).map_err(|e| e.to_string())?;
    Ok((package, start.elapsed().as_nanos()))
}

pub fn run(
    job: &Request,
    path: &Path,
    sha256: &str,
    inputs: &[Input],
    preparation: bool,
    preparation_entries: Option<usize>,
    preparation_bytes: Option<usize>,
) -> Result<Report> {
    if job.operation == Operation::Run || inputs.is_empty() {
        return Err("proof worker requires proof inputs and a proof operation".into());
    }
    if inputs.len() > 1
        && (job.plan.iterations != 1
            || !job.plan.warmups.is_multiple_of(inputs.len())
            || !job.plan.samples.is_multiple_of(inputs.len()))
    {
        return Err(
            "changing inputs require one call per sample and complete warmup/sample cycles".into(),
        );
    }
    let (package, capture_ns) = capture(path, sha256)?;
    let start = Instant::now();
    let options = ProofOptions {
        binding: BindingPolicy::AllowAuthored,
        ..Default::default()
    };
    let mut entry =
        ProofEntry::admit(package, options, Default::default()).map_err(|e| e.to_string())?;
    let admit_ns = start.elapsed().as_nanos();
    let defaults = zkc_runtime::vm::PreparationLimits::default();
    let mut limits = defaults;
    if let Some(entries) = preparation_entries {
        limits.entries = entries;
    }
    if let Some(bytes) = preparation_bytes {
        limits.bytes = bytes;
    }
    if !preparation {
        limits.entries = 0;
        limits.bytes = 0;
    }
    entry = entry.with_preparation_limits(limits);
    let observed_limits = Limits {
        entries: limits.entries,
        bytes: limits.bytes,
        default_entries: defaults.entries,
        default_bytes: defaults.bytes,
    };
    let data = inputs
        .iter()
        .map(|input| {
            let public = std::fs::read(&input.public).map_err(|e| e.to_string())?;
            let witness = input
                .witness
                .as_ref()
                .map(std::fs::read)
                .transpose()
                .map_err(|e| e.to_string())?;
            let proof = if job.operation == Operation::Verify {
                std::fs::read(input.proof.as_ref().unwrap_or(&job.proof))
                    .map_err(|e| e.to_string())?
            } else {
                Vec::new()
            };
            Ok((public, witness, proof))
        })
        .collect::<Result<Vec<_>>>()?;
    let groups = entry.interface().input_groups();
    let public_group = groups
        .iter()
        .find(|group| group.name() == "public")
        .ok_or("missing public input group")?;
    let witness_group = groups
        .iter()
        .find(|group| group.name() == "witness")
        .ok_or("missing witness input group")?;
    let total = (job.plan.warmups + job.plan.samples) * job.plan.iterations;
    let calls = RefCell::new(Vec::with_capacity(total));
    let completed = Cell::new(0);
    let prior = RefCell::new(Preparation::default());
    let mut next = 0;
    let prepare = || {
        let index = next % data.len();
        next += 1;
        let (public, witness, _) = &data[index];
        let start = Instant::now();
        let mut decoder = Decoder::new(options.capacity)?;
        let public = decoder
            .decode(public_group, public, None)
            .map_err(|e| e.to_string())?;
        let mut request = ProofRequest {
            public,
            ..Default::default()
        };
        if job.operation == Operation::Prove {
            request.private.inputs = decoder
                .decode(witness_group, witness.as_deref().unwrap_or(b"{}"), None)
                .map_err(|e| e.to_string())?;
        }
        calls
            .borrow_mut()
            .push(Call::decoded(index, start.elapsed().as_nanos()));
        Ok((index, request))
    };
    let mut last = None;
    let mut proofs = Vec::new();
    let samples = measure(
        job.plan,
        prepare,
        |(index, input)| {
            (if job.operation == Operation::Prove {
                entry.prove(input)
            } else {
                entry.verify(input, &data[index].2)
            })
            .map(|report| (index, report))
            .map_err(|error| Failure::Failed(error.to_string()))
        },
        |(index, report)| {
            if !report.is_success() {
                let clean = job.operation == Operation::Verify
                    && report.native.cleanup_errors.is_empty()
                    && report.output_error.is_none();
                let stop = report.native.stop.as_ref().map(|stop| &stop.kind);
                let rejected = if clean { rejection(
                        report.native.outcome.as_ref().err().map(String::as_str),
                        stop,
                    ) } else { None };
                let detail = format!(
                    "{:?}; {}",
                    report.native.outcome.as_ref().err(),
                    report.native.diagnostics()
                );
                return Err(if let Some(class) = rejected {
                    Failure::Refusal {class, code: report.native.outcome.as_ref().err().cloned(), stop: stop.map(|v|format!("{v:?}")), detail}
                } else if clean
                    && !report.native.cancelled
                    && matches!(stop, Some(StopKind::Backend(error)) if error.code == "refused:bytes-bounds")
                {
                    // This code alone does not identify a proof read. Keep it
                    // distinct: only the harness's truncation control permits it.
                    Failure::InputBounds(detail)
                } else {
                    Failure::Failed(detail)
                });
            }
            if job.operation == Operation::Prove {
                crate::retain_proof(
                    &job.proof,
                    report.native.outcome.as_ref().unwrap(),
                    &mut proofs,
                )?;
            }
            if let Some(proof) = proofs.last_mut() {
                proof["input_index"] = json!(index);
            }
            calls.borrow_mut().last_mut().unwrap().execution_counts = report.native.execution_counts.json();
            let stats = preparation_stats(&entry);
            *prior.borrow_mut() = stats.clone();
            calls.borrow_mut().last_mut().unwrap().preparation = Some(stats);
            completed.set(completed.get() + 1);
            if calls.borrow().len() == total {
                last = Some((index, report));
            }
            Ok(())
        },
    )
    .map_err(|cause| Failure::Invocation {
        completed: completed.get(),
        cause: Box::new(cause),
        preparation_before: prior.into_inner(),
        preparation_after: preparation_stats(&entry),
        preparation_limits: observed_limits,
    })?;
    let (index, last) = last.unwrap();
    let mut report = Report::new(
        "admitted_entry_call",
        samples,
        if job.operation == Operation::Prove {
            last.native.outcome.as_ref().unwrap().len()
        } else {
            data[index].2.len()
        },
    );
    report.admission_ns = Some(capture_ns + admit_ns);
    let before = crate::peak_rss();
    let start = Instant::now();
    report.diagnostics = last.native.diagnostics();
    let diagnostics_ns = start.elapsed().as_nanos();
    report.lifecycle = Some(Lifecycle {
        preparation_limits: Some(observed_limits),
        capture_ns,
        admit_ns,
        calls: calls.into_inner(),
        diagnostics_ns,
        peak_rss_before_diagnostics: before,
        peak_rss_after_diagnostics: crate::peak_rss(),
    });
    let prepared = entry.preparation_stats();
    report.diagnostics["preparation"] = serde_json::json!({
        "entries": prepared.entries, "retained_bytes": prepared.bytes, "hits": prepared.hits,
    });
    report.proofs = proofs;
    if job.operation == Operation::Prove {
        std::fs::write(&job.proof, last.native.outcome.unwrap()).map_err(|e| e.to_string())?;
    }
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn refusals_preserve_the_layer_that_rejected() {
        use zkc_runtime::vm::BackendError;
        assert_eq!(
            rejection(Some("artifact-rejected"), None),
            Some("verification")
        );
        assert_eq!(
            rejection(None, Some(&StopKind::Explicit("reject".into()))),
            Some("verification")
        );
        assert_eq!(
            rejection(Some("proof-header"), Some(&StopKind::Cancelled)),
            Some("binding")
        );
        for code in ["proof-truncated", "proof-trailing"] {
            assert_eq!(
                rejection(Some(code), Some(&StopKind::Cancelled)),
                Some("format")
            );
            assert_eq!(rejection(Some(code), Some(&StopKind::Limit)), None);
        }
        for stop in [
            StopKind::Limit,
            StopKind::Cancelled,
            StopKind::Explicit("other".into()),
            StopKind::Backend(BackendError::new("refused:bytes-bounds")),
        ] {
            assert_eq!(rejection(None, Some(&stop)), None);
        }
        assert_eq!(rejection(Some("native-proof-cleanup"), None), None);
        assert_eq!(
            rejection(Some("proof-limit"), Some(&StopKind::Cancelled)),
            None
        );
    }
}
