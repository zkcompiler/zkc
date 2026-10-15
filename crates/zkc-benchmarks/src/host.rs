//! Generic source Entry benchmark. No protocol-specific interpretation.
use crate::{Failure, Operation, Report, Request, Result, measure::measure};
use std::{path::Path, time::Instant};
use zkc_runtime::interactive::StopKind;
use zkc_tools::entry::{
    BindingPolicy, Package, ProofEntry, ProofOptions, ProofRequest, inputs::Decoder,
};

fn rejection(error: Option<&str>, stop: Option<&StopKind>) -> bool {
    match stop {
        Some(StopKind::Explicit(reason)) => reason == "reject",
        None => error == Some("artifact-rejected"),
        _ => false,
    }
}

pub fn run(
    job: &Request,
    path: &Path,
    sha256: &str,
    public: &Path,
    witness: Option<&Path>,
) -> Result<Report> {
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
    let options = ProofOptions {
        binding: BindingPolicy::AllowAuthored,
        ..Default::default()
    };
    let entry =
        ProofEntry::admit(package, options, Default::default()).map_err(|e| e.to_string())?;
    let admission = start.elapsed().as_nanos();
    let public = std::fs::read(public).map_err(|e| e.to_string())?;
    let witness = witness
        .map(std::fs::read)
        .transpose()
        .map_err(|e| e.to_string())?;
    let proof = if job.operation == Operation::Verify {
        std::fs::read(&job.proof).map_err(|e| e.to_string())?
    } else {
        Vec::new()
    };
    let groups = entry.interface().input_groups();
    let public_group = groups
        .iter()
        .find(|group| group.name() == "public")
        .ok_or("missing public input group")?;
    let witness_group = groups
        .iter()
        .find(|group| group.name() == "witness")
        .ok_or("missing witness input group")?;
    let prepare = || {
        let mut decoder = Decoder::new(options.capacity)?;
        let public = decoder
            .decode(public_group, &public, None)
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
        Ok(request)
    };
    let mut last = None;
    let mut proofs = Vec::new();
    let samples = measure(
        job.plan,
        prepare,
        |input| {
            (if job.operation == Operation::Prove {
                entry.prove(input)
            } else {
                entry.verify(input, &proof)
            })
            .map_err(|error| Failure::Failed(error.to_string()))
        },
        |report| {
            if !report.is_success() {
                let clean = job.operation == Operation::Verify
                    && !report.native.cancelled
                    && report.native.cleanup_errors.is_empty()
                    && report.output_error.is_none();
                let stop = report.native.stop.as_ref().map(|stop| &stop.kind);
                let rejected = clean
                    && rejection(
                        report.native.outcome.as_ref().err().map(String::as_str),
                        stop,
                    );
                let detail = format!(
                    "{:?}; {}",
                    report.native.outcome.as_ref().err(),
                    report.native.diagnostics()
                );
                return Err(if rejected {
                    Failure::Rejected(detail)
                } else if clean
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
            last = Some(report);
            Ok(())
        },
    )?;
    let last = last.unwrap();
    let mut report = Report::new(
        "admitted_entry_call",
        samples,
        if job.operation == Operation::Prove {
            last.native.outcome.as_ref().unwrap().len()
        } else {
            proof.len()
        },
    );
    report.admission_ns = Some(admission);
    report.diagnostics = last.native.diagnostics();
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
    fn a_limit_or_unrelated_stop_is_not_proof_rejection() {
        use zkc_runtime::interactive::BackendError;
        assert!(rejection(Some("artifact-rejected"), None));
        assert!(rejection(None, Some(&StopKind::Explicit("reject".into()))));
        assert!(!rejection(Some("native-proof-cleanup"), None));
        assert!(!rejection(None, Some(&StopKind::Limit)));
        assert!(!rejection(None, Some(&StopKind::Cancelled)));
        assert!(!rejection(None, Some(&StopKind::Explicit("other".into()))));
        assert!(!rejection(
            None,
            Some(&StopKind::Backend(BackendError::new(
                "refused:bytes-bounds"
            )))
        ));
        assert!(!rejection(
            None,
            Some(&StopKind::Backend(BackendError::new("external-work-limit")))
        ));
    }
}
