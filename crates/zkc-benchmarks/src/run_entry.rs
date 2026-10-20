//! Ordinary source programs use the same admitted Host as application callers.
use crate::{
    Failure, Operation, Report, Request, Result,
    host::capture,
    ingress::{Ingress, Owner},
    measure::measure,
    observation::{Call, InputSetup, Lifecycle},
};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    time::Instant,
};
use zkc_tools::{
    entry::{NamedValues, RoleInputs, RunEntry, RunRequest, Value, inputs::Decoder},
    execution::InputValue,
};

fn accepted(value: Option<&Value>) -> bool {
    matches!(value, Some(Value::Leaf(InputValue::Native(value))) if matches!(value.as_ref(), zkc_backends::Value::Bool(true)))
}

fn make_request(values: BTreeMap<String, NamedValues>) -> RunRequest {
    RunRequest {
        session: "benchmark".into(),
        roles: values
            .into_iter()
            .map(|(role, inputs)| {
                (
                    role,
                    RoleInputs {
                        inputs,
                        ..Default::default()
                    },
                )
            })
            .collect(),
        setups: BTreeMap::new(),
    }
}
fn share(owners: &BTreeMap<String, Owner>) -> Result<BTreeMap<String, NamedValues>> {
    owners
        .iter()
        .map(|(role, owner)| Ok((role.clone(), owner.share()?)))
        .collect()
}

pub fn run(
    job: &Request,
    path: &Path,
    sha256: &str,
    roles: &BTreeMap<String, PathBuf>,
    accept_role: &str,
) -> Result<Report> {
    let ingress = job.ingress()?;
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
    let decode = || {
        let mut decoder = Decoder::new(entry.limits().capacity)?;
        data.iter()
            .map(|(role, bytes)| {
                let group = groups
                    .iter()
                    .find(|g| g.name() == role)
                    .ok_or("unknown input role")?;
                let inputs = decoder
                    .decode(group, bytes, None)
                    .map_err(|e| e.to_string())?;
                Ok((role.clone(), inputs))
            })
            .collect::<Result<BTreeMap<_, _>>>()
    };
    let mut input_setup = Vec::new();
    let owners = if ingress == Ingress::Json {
        None
    } else {
        let start = Instant::now();
        let owners = decode()?
            .into_iter()
            .map(|(role, values)| {
                let group = groups
                    .iter()
                    .find(|g| g.name() == role)
                    .ok_or("unknown input role")?;
                Ok((
                    role,
                    Owner::new(
                        values,
                        group,
                        entry.interface(),
                        ingress,
                        entry.limits().capacity,
                    )?,
                ))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        // Public Host admission confirms the exact physical ABI and complete
        // loading limits. This issues no resources; every timed call checks again.
        entry
            .check_inputs(make_request(share(&owners)?))
            .map_err(|e| format!("benchmark-ingress: input admission: {e}"))?;
        input_setup.push(InputSetup {
            input_index: 0,
            construction_ns: start.elapsed().as_nanos(),
            retained_payload_bytes: owners.values().map(|o| o.retained_payload_bytes).sum(),
        });
        Some(owners)
    };
    let calls = std::cell::RefCell::new(Vec::with_capacity(
        (job.plan.warmups + job.plan.samples) * job.plan.iterations,
    ));
    let mut last = None;
    let mut observed = 0;
    let samples = measure(
        job.plan,
        || {
            let (decoded, decode_ns) = if owners.is_none() {
                let start = Instant::now();
                let values = decode()?;
                (Some(values), Some(start.elapsed().as_nanos()))
            } else {
                (None, None)
            };
            let start = Instant::now();
            let values = if let Some(owners) = &owners {
                share(owners)?
            } else {
                decoded.unwrap()
            };
            let input = make_request(values);
            let request_ns = start.elapsed().as_nanos();
            calls
                .borrow_mut()
                .push(Call::constructed(0, decode_ns, request_ns));
            Ok(input)
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
        ingress,
        input_setup,
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
