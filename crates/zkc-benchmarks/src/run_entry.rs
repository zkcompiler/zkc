//! Ordinary source programs use the same admitted Function Host as applications.
use crate::{
    Failure, Operation, Report, Request, Result,
    host::capture,
    ingress::{Ingress, Owner},
    measure::measure,
    observation::{Call, InputSetup, Lifecycle},
};
use serde::Deserialize;
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    time::Instant,
};
use zkc::{
    entry::{
        FunctionEntry, FunctionInterface, FunctionOptions, FunctionRequest, InvocationBinding,
        InvocationContext, NamedValues, RunContext, Value, files::Documents,
    },
    execution::InputValue,
};

fn accepted(value: Option<&Value>) -> bool {
    matches!(value, Some(Value::Leaf(InputValue::Native(value))) if matches!(value.as_ref(), zkc_native::Value::Bool(true)))
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Check {
    Acceptance { role: String },
    Output { expected: PathBuf },
}

fn check_output(
    value: &Value,
    check: &Check,
    expected: Option<&serde_json::Value>,
    options: FunctionOptions,
) -> Result<()> {
    let correct = match check {
        Check::Acceptance { role } => {
            let output = match value {
                Value::Record(roles) => roles.get(role),
                _ => None,
            };
            let acceptance = match output {
                Some(Value::Record(outputs)) => outputs.get("accepted"),
                _ => None,
            };
            accepted(acceptance)
        }
        Check::Output { .. } => {
            let bytes = zkc::entry::files::function_output(
                value,
                options.limits.capacity,
                Default::default(),
            )?;
            let actual: serde_json::Value =
                serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
            Some(&actual) == expected
        }
    };
    if correct {
        Ok(())
    } else {
        Err(Failure::IncorrectResult)
    }
}

fn context(entry: &FunctionEntry) -> InvocationContext {
    InvocationContext {
        deployments: entry
            .deployments()
            .map(|(id, _)| {
                (
                    id.into(),
                    InvocationBinding::Run(RunContext {
                        session: Some("benchmark".into()),
                        ..Default::default()
                    }),
                )
            })
            .collect(),
    }
}

fn make_request(entry: &FunctionEntry, arguments: NamedValues) -> FunctionRequest {
    FunctionRequest {
        arguments,
        context: context(entry),
    }
}

pub fn run(
    job: &Request,
    path: &Path,
    sha256: &str,
    arguments: &Path,
    check: &Check,
) -> Result<Report> {
    let ingress = job.ingress()?;
    if job.operation != Operation::Run {
        return Err("function worker requires a run operation".into());
    }
    let (package, capture_ns) = capture(path, sha256)?;
    let start = Instant::now();
    // This inventory is checked by the common Host owner, before executable
    // admission. Setup authority is never inferred from a child package.
    let children = FunctionInterface::deployment_interfaces(&package).map_err(|e| e.to_string())?;
    let mut authority = BTreeMap::new();
    for child in children {
        if child.operation() != "run" || child.interface().setup_names().len() != 0 {
            return Err("benchmark Function requires setup-free run children".into());
        }
        authority.insert(child.id().into(), Default::default());
    }
    let options = FunctionOptions::default();
    let entry = FunctionEntry::admit(package, options, authority).map_err(|e| e.to_string())?;
    let admit_ns = start.elapsed().as_nanos();
    let expected = match check {
        Check::Output { expected } => Some(
            serde_json::from_slice::<serde_json::Value>(
                &std::fs::read(expected).map_err(|e| e.to_string())?,
            )
            .map_err(|e| e.to_string())?,
        ),
        _ => None,
    };
    let group = entry.interface().input_group();
    let decode = || -> Result<NamedValues> {
        Documents::new(options.limits.capacity)?
            .load(&group, Some(arguments))
            .map_err(|e| e.to_string().into())
    };
    let mut input_setup = Vec::new();
    let owner = if ingress == Ingress::Json {
        None
    } else {
        let start = Instant::now();
        let owner = Owner::function(
            decode()?,
            &group,
            entry.interface(),
            ingress,
            options.limits.capacity,
        )?;
        entry
            .check_inputs(make_request(&entry, owner.share()?))
            .map_err(|e| format!("benchmark-ingress: input admission: {e}"))?;
        input_setup.push(InputSetup {
            input_index: 0,
            construction_ns: start.elapsed().as_nanos(),
            retained_payload_bytes: owner.retained_payload_bytes,
        });
        Some(owner)
    };
    let total = (job.plan.warmups + job.plan.samples) * job.plan.iterations;
    let calls = std::cell::RefCell::new(Vec::with_capacity(total));
    let mut last = None;
    let mut observed = 0;
    let samples = measure(
        job.plan,
        || {
            let (decoded, decode_ns) = if owner.is_none() {
                let start = Instant::now();
                let values = decode()?;
                (Some(values), Some(start.elapsed().as_nanos()))
            } else {
                (None, None)
            };
            let start = Instant::now();
            let values = if let Some(owner) = &owner {
                owner.share()?
            } else {
                decoded.unwrap()
            };
            let input = make_request(&entry, values);
            let request_ns = start.elapsed().as_nanos();
            calls
                .borrow_mut()
                .push(Call::constructed(0, decode_ns, request_ns));
            Ok(input)
        },
        // Time the complete Function call, including native child invocation,
        // input adaptation, cleanup and construction of its typed source return.
        |input| Ok(entry.prepare(input).map_err(|e| e.to_string())?.execute()),
        |report| {
            calls
                .borrow_mut()
                .last_mut()
                .expect("constructed call")
                .execution_counts = report.execution_counts.json();
            if !report.is_success() {
                return Err(format!("function failed: {}", report.diagnostics()).into());
            }
            let value = report.value.as_ref().unwrap().clone().into_value();
            check_output(&value, check, expected.as_ref(), options)?;
            observed += 1;
            if observed == total {
                last = Some(report);
            }
            Ok(())
        },
    )?;
    let mut report = Report::new("admitted_function_call", samples, 0);
    report.admission_ns = Some(capture_ns + admit_ns);
    let last = last.unwrap();
    let before = crate::peak_rss();
    let start = Instant::now();
    report.diagnostics = last.diagnostics();
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
    use zkc_runtime::vm::Value as _;
    #[test]
    fn acceptance_is_a_typed_boolean() {
        assert!(accepted(Some(&Value::from(zkc_native::Value::Bool(true)))));
        assert!(!accepted(Some(&Value::from(zkc_native::Value::Bool(
            false
        )))));
        assert!(!accepted(Some(&Value::Unit)));
        assert!(!accepted(None));
    }

    // Independently authored Function carrier: acceptance is ordinary source
    // data and the worker acceptance gate checks publication. No native protocol exists.
    #[test]
    fn function_worker_calls_the_host_with_every_ingress_and_checks_every_result() {
        use serde_json::json;
        use sha2::{Digest, Sha256};
        use std::sync::atomic::{AtomicUsize, Ordering};
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        fn hash(bytes: &[u8]) -> String {
            Sha256::digest(bytes)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect()
        }
        let directory = std::env::temp_dir().join(format!(
            "zkc-benchmark-function-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&directory).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(directory.clone());
        let boolean = json!({"kind":"boolean","type":"bool","identity":hash(b"bool"),
            "custody":false,"constructible":true,"permissions":["Copy","Drop"],
            "fields":[],"alternatives":[],"leaves":["bool"]});
        let product = |name: &str, member: &str, child: &serde_json::Value| {
            json!({
            "kind":"record","type":name,"identity":hash(name.as_bytes()),
            "custody":false,"constructible":true,"permissions":["Copy","Drop"],
            "fields":[{"name":member,"offset":0,"schema":child}],"alternatives":[],"leaves":["bool"]})
        };
        let outputs = product("example::Outputs", "accepted", &boolean);
        let result = product("example::Result", "P", &outputs);
        let definition = |id, schema: &serde_json::Value| json!({"id":id,"schema":schema});
        let signature = json!({"symbol":"example::Main",
            "parameters":[{"name":"accepted","schema":boolean}],"result":result});
        let artifact = json!({"format":"zkc.host/0","original":hash(b"original"),"entry":"example::Main",
            "functions":[{"signature":signature,"body":{
                "arguments":[definition(0,&boolean)],"operations":[
                    {"op":"construct","alternative":"","operands":[0],"results":[definition(1,&outputs)]},
                    {"op":"construct","alternative":"","operands":[1],"results":[definition(2,&result)]}],"returns":[2]}}],
            "calculations":[],"deployments":[]});
        let interface = json!({"format":"zkc.language-interface/0","capture":hash(b"capture"),
            "original":hash(b"original"),"toolchain":"test","entry":"example::Main",
            "selection":{"kind":"function","function":"example::Main"},
            "functions":[signature],"protocols":[],"relations":[],"setups":[]});
        let package = json!({"format":"zkc.entry/0","original":"original",
            "interface":interface.to_string(),"artifact":artifact.to_string(),"assets":[],
            "options":{"simplify":true,"release_storage":false,"finite_bulk":true,
                "fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true}}).to_string();
        let path = directory.join("function.zkpkg");
        std::fs::write(&path, &package).unwrap();
        let arguments = directory.join("arguments.json");
        let payload = zkc_native::readable_wire(
            &zkc_native::Value::Bool(true).physical_type(),
            &json!(true),
            128,
        )
        .unwrap();
        std::fs::write(directory.join("input.zkcv"), &payload).unwrap();
        for ingress in ["json", "wire", "native", "prepared"] {
            for file_backed in [false, true] {
                let job: Request = serde_json::from_value(json!({"format":"zkc.benchmark-job/0",
                "backend":{"kind":"run","ingress":ingress,"package":path,"sha256":hash(package.as_bytes()),
                    "arguments":arguments,"check":{"kind":"acceptance","role":"P"}},"operation":"run",
                "plan":{"warmups":1,"samples":2,"iterations":2},"proof":directory.join("unused")})).unwrap();
                let input = if file_backed {
                    json!({"accepted":{"file":"input.zkcv","sha256":hash(&payload)}}).to_string()
                } else {
                    json!({"accepted":true}).to_string()
                };
                std::fs::write(&arguments, input).unwrap();
                let report = run(
                    &job,
                    &path,
                    &hash(package.as_bytes()),
                    &arguments,
                    &Check::Acceptance { role: "P".into() },
                );
                let report = report.unwrap();
                assert_eq!(report.boundary, "admitted_function_call");
                assert_eq!(report.diagnostics["completed"], true);
                assert!(
                    report.diagnostics["usage"]["instructions"]
                        .as_u64()
                        .unwrap()
                        > 0
                );
                let life = report.lifecycle.unwrap();
                assert_eq!(life.calls.len(), 6);
                assert!(
                    life.calls.iter().all(|c| c.execution_counts.is_some()
                        == zkc_runtime::vm::ExecutionCounts::ENABLED)
                );
                assert_eq!(life.input_setup.len(), usize::from(ingress != "json"));
                assert!(
                    life.calls
                        .iter()
                        .all(|c| c.decode_ns.is_some() == (ingress == "json"))
                );
                let expected = directory.join("expected.json");
                let output_check = Check::Output {
                    expected: expected.clone(),
                };
                std::fs::write(
                    &expected,
                    json!({"format":"zkc.entry-outputs/0", "value":{"P":{"accepted":true}}})
                        .to_string(),
                )
                .unwrap();
                assert!(
                    run(
                        &job,
                        &path,
                        &hash(package.as_bytes()),
                        &arguments,
                        &output_check
                    )
                    .is_ok()
                );
                std::fs::write(
                    &expected,
                    json!({"format":"zkc.entry-outputs/0", "value":{"P":{"accepted":false}}})
                        .to_string(),
                )
                .unwrap();
                assert!(matches!(
                    run(
                        &job,
                        &path,
                        &hash(package.as_bytes()),
                        &arguments,
                        &output_check
                    ),
                    Err(Failure::IncorrectResult)
                ));
                assert!(matches!(
                    run(
                        &job,
                        &path,
                        &hash(package.as_bytes()),
                        &arguments,
                        &Check::Acceptance {
                            role: "absent".into()
                        }
                    ),
                    Err(Failure::IncorrectResult)
                ));
                std::fs::write(&arguments, r#"{"accepted":false}"#).unwrap();
                assert!(matches!(
                    run(
                        &job,
                        &path,
                        &hash(package.as_bytes()),
                        &arguments,
                        &Check::Acceptance { role: "P".into() }
                    ),
                    Err(Failure::IncorrectResult)
                ));
                std::fs::write(&arguments, r#"{"accepted":true,"extra":false}"#).unwrap();
                assert!(
                    run(
                        &job,
                        &path,
                        &hash(package.as_bytes()),
                        &arguments,
                        &Check::Acceptance { role: "P".into() }
                    )
                    .is_err()
                );
            }
        }
    }
}
