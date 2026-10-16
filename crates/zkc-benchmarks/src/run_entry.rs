//! Ordinary source programs use the same admitted Host as application callers.
use crate::{
    Failure, Operation, Report, Request, Result,
    host::capture,
    measure::measure,
    observation::{Call, Lifecycle},
};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    time::Instant,
};
use zkc_tools::{
    entry::{RoleInputs, RunEntry, RunRequest, Value, inputs::Decoder},
    execution::InputValue,
};

fn accepted(value: Option<&Value>) -> bool {
    matches!(value, Some(Value::Leaf(InputValue::Native(value))) if matches!(value.as_ref(), zkc_backends::Value::Bool(true)))
}

pub fn run(
    job: &Request,
    path: &Path,
    sha256: &str,
    roles: &BTreeMap<String, PathBuf>,
    accept_role: &str,
) -> Result<Report> {
    if job.operation != Operation::Run {
        return Err("run worker requires a run operation".into());
    }
    let (package, capture_ns) = capture(path, sha256)?;
    let start = Instant::now();
    let entry = RunEntry::admit(package, Default::default(), Default::default())
        .map_err(|e| e.to_string())?;
    let admit_ns = start.elapsed().as_nanos();
    let data = roles
        .iter()
        .map(|(role, path)| {
            Ok((
                role.clone(),
                std::fs::read(path).map_err(|e| e.to_string())?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>>>()?;
    let groups = entry.interface().input_groups();
    let calls = std::cell::RefCell::new(Vec::with_capacity(
        (job.plan.warmups + job.plan.samples) * job.plan.iterations,
    ));
    let mut last = None;
    let mut observed = 0;
    let samples = measure(
        job.plan,
        || {
            let start = Instant::now();
            let mut decoder = Decoder::new(entry.limits().capacity)?;
            let mut roles = BTreeMap::new();
            for (role, bytes) in &data {
                let group = groups
                    .iter()
                    .find(|g| g.name() == role)
                    .ok_or("unknown input role")?;
                let inputs = decoder
                    .decode(group, bytes, None)
                    .map_err(|e| e.to_string())?;
                roles.insert(
                    role.clone(),
                    RoleInputs {
                        inputs,
                        ..Default::default()
                    },
                );
            }
            calls
                .borrow_mut()
                .push(Call::decoded(0, start.elapsed().as_nanos()));
            Ok(RunRequest {
                session: "benchmark".into(),
                roles,
                setups: BTreeMap::new(),
            })
        },
        |input| Ok(entry.prepare(input).map_err(|e| e.to_string())?.execute()),
        |report| {
            if !report.is_success() {
                return Err(format!("run failed: {}", report.native.diagnostics()).into());
            }
            if !accepted(
                report
                    .outputs
                    .as_ref()
                    .and_then(|r| r.get(accept_role))
                    .and_then(|r| r.get("accepted")),
            ) {
                return Err(Failure::IncorrectResult);
            }
            let mut counts = zkc_runtime::vm::ExecutionCounts::default();
            for role in &report
                .native
                .execution
                .as_ref()
                .expect("successful execution")
                .roles
            {
                counts.merge(&role.execution_counts);
            }
            calls.borrow_mut().last_mut().unwrap().execution_counts = counts.json();
            observed += 1;
            if observed == (job.plan.warmups + job.plan.samples) * job.plan.iterations {
                last = Some(report);
            }
            Ok(())
        },
    )?;
    let mut report = Report::new("admitted_run_call", samples, 0);
    report.admission_ns = Some(capture_ns + admit_ns);
    let last = last.unwrap();
    let before = crate::peak_rss();
    let start = Instant::now();
    report.diagnostics = last.native.diagnostics();
    let diagnostics_ns = start.elapsed().as_nanos();
    report.lifecycle = Some(Lifecycle {
        preparation_limits: None,
        capture_ns,
        admit_ns,
        calls: calls.into_inner(),
        diagnostics_ns,
        peak_rss_before_diagnostics: before,
        peak_rss_after_diagnostics: crate::peak_rss(),
    });
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn acceptance_is_a_typed_boolean() {
        assert!(accepted(Some(&Value::from(zkc_backends::Value::Bool(
            true
        )))));
        assert!(!accepted(Some(&Value::from(zkc_backends::Value::Bool(
            false
        )))));
        assert!(!accepted(Some(&Value::Unit)));
        assert!(!accepted(None));
    }
}
