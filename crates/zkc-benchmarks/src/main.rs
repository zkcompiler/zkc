//! Development-only benchmark client. Production execution stays in the Host.
mod evidence;
mod host;
mod ingress;
mod kernel;
mod measure;
mod observation;
mod run_entry;
mod schnorr;
mod sumcheck;

use measure::{Plan, Sample};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub enum Failure {
    Ingress {
        policy: ingress::Ingress,
        cause: Box<Failure>,
    },
    Failed(String),
    Rejected(String),
    InputBounds(String),
    IncorrectResult,
    Refusal {
        class: &'static str,
        code: Option<String>,
        stop: Option<String>,
        detail: String,
    },
    Invocation {
        completed: usize,
        cause: Box<Failure>,
        preparation_before: observation::Preparation,
        preparation_after: observation::Preparation,
        preparation_limits: observation::Limits,
    },
}
type Result<T, E = Failure> = std::result::Result<T, E>;
impl From<String> for Failure {
    fn from(message: String) -> Self {
        Self::Failed(message)
    }
}
impl From<&str> for Failure {
    fn from(message: &str) -> Self {
        Self::Failed(message.into())
    }
}

#[derive(Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Operation {
    Prove,
    Verify,
    Run,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum Backend {
    Host {
        ingress: ingress::Ingress,
        package: PathBuf,
        sha256: String,
        inputs: Vec<host::Input>,
        preparation: bool,
        preparation_entries: Option<usize>,
        preparation_bytes: Option<usize>,
    },
    Run {
        ingress: ingress::Ingress,
        package: PathBuf,
        sha256: String,
        arguments: PathBuf,
        check: run_entry::Check,
    },
    Kernel {
        provider: kernel::Provider,
        group: kernel::Group,
        kernel: kernel::Kernel,
        boundary: kernel::Boundary,
        elements: usize,
        #[serde(default = "kernel::single_call")]
        chain_length: usize,
    },
    Schnorr {
        public: PathBuf,
        witness: Option<PathBuf>,
    },
    Sumcheck {
        public: PathBuf,
    },
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    format: String,
    backend: Backend,
    operation: Operation,
    plan: Plan,
    proof: PathBuf,
}

impl Request {
    fn ingress(&self) -> Result<ingress::Ingress> {
        match &self.backend {
            Backend::Host { ingress, .. } | Backend::Run { ingress, .. } => Ok(*ingress),
            _ => Err("backend has no Host ingress policy".into()),
        }
    }
}

#[derive(Serialize)]
pub struct Report {
    format: &'static str,
    status: &'static str,
    pub boundary: &'static str,
    pub admission_ns: Option<u128>,
    pub samples: Vec<Sample>,
    pub proof_bytes: usize,
    pub diagnostics: Value,
    pub lifecycle: Option<observation::Lifecycle>,
    pub process_peak_rss_bytes: Option<u64>,
    pub proofs: Vec<Value>,
    pub build: Value,
    pub process: Value,
    pub timer_floor_ns: u128,
}
impl Report {
    fn new(boundary: &'static str, samples: Vec<Sample>, proof_bytes: usize) -> Self {
        Self {
            format: "zkc.benchmark-worker/0",
            status: "passed",
            boundary,
            admission_ns: None,
            samples,
            proof_bytes,
            diagnostics: Value::Null,
            lifecycle: None,
            process_peak_rss_bytes: None,
            proofs: Vec::new(),
            build: {
                let mut facts = evidence::build();
                facts["execution_counts"] = json!(zkc_runtime::vm::ExecutionCounts::ENABLED);
                facts
            },
            process: Value::Null,
            timer_floor_ns: 0,
        }
    }
}

/// Retain every produced proof for independent post-worker validation.
fn retain_proof(path: &Path, proof: &[u8], outputs: &mut Vec<Value>) -> Result<()> {
    let path = path.with_extension(format!("{}.proof", outputs.len()));
    std::fs::write(&path, proof).map_err(|e| e.to_string())?;
    outputs.push(json!({"path":path, "bytes":proof.len(), "sha256":Sha256::digest(proof).iter().map(|b|format!("{b:02x}")).collect::<String>()}));
    Ok(())
}

use evidence::peak_rss;

fn run() -> Result<Report> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 1 {
        return Err("usage: zkc-benchmarks REQUEST.json".into());
    }
    let request: Request =
        serde_json::from_slice(&std::fs::read(&args[0]).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    if request.format != "zkc.benchmark-job/0" {
        return Err("unknown benchmark job format".into());
    }
    request.plan.validate()?;
    if zkc_runtime::vm::ExecutionCounts::ENABLED
        && (request.plan.warmups + request.plan.samples) * request.plan.iterations > 128
    {
        return Err("execution counts permit at most 128 calls per worker".into());
    }
    let mut report = (match &request.backend {
        Backend::Host {
            ingress: _,
            package,
            sha256,
            inputs,
            preparation,
            preparation_entries,
            preparation_bytes,
        } => host::run(
            &request,
            package,
            sha256,
            inputs,
            *preparation,
            *preparation_entries,
            *preparation_bytes,
        ),
        Backend::Run {
            ingress: _,
            package,
            sha256,
            arguments,
            check,
        } => run_entry::run(&request, package, sha256, arguments, check),
        Backend::Kernel {
            provider,
            group,
            kernel,
            boundary,
            elements,
            chain_length,
        } => kernel::run(
            &request,
            *provider,
            *group,
            *kernel,
            *boundary,
            *elements,
            *chain_length,
        ),
        Backend::Schnorr { public, witness } if request.operation != Operation::Run => {
            schnorr::run(&request, public, witness.as_deref())
        }
        Backend::Sumcheck { public } if request.operation != Operation::Run => {
            sumcheck::run(&request, public)
        }
        _ => Err("backend does not support this operation".into()),
    })
    .map_err(|cause| match request.ingress() {
        Ok(policy) => Failure::Ingress {
            policy,
            cause: Box::new(cause),
        },
        Err(_) => cause,
    })?;
    report.process_peak_rss_bytes = peak_rss();
    report.process = evidence::process();
    report.timer_floor_ns = evidence::timer_floor_ns();
    Ok(report)
}
fn main() {
    match run() {
        Ok(report) => println!("{}", serde_json::to_string(&report).unwrap()),
        Err(error) => {
            let (ingress, error) = match error {
                Failure::Ingress { policy, cause } => (Some(policy), *cause),
                other => (None, other),
            };
            let (completed_calls, preparation, preparation_limits, error) = match error {
                Failure::Invocation {
                    completed,
                    cause,
                    preparation_before,
                    preparation_after,
                    preparation_limits,
                } => (
                    Some(completed),
                    json!({"before":preparation_before,"after":preparation_after}),
                    Some(preparation_limits),
                    *cause,
                ),
                error => (None, Value::Null, None, error),
            };
            let mut refusal = Value::Null;
            let (status, error) = match error {
                Failure::Failed(error) => ("failed", error),
                Failure::Rejected(error) => ("rejected", error),
                Failure::Refusal {
                    class,
                    code,
                    stop,
                    detail,
                } => {
                    refusal = json!({"class":class,"code":code,"stop":stop});
                    ("rejected", detail)
                }
                Failure::InputBounds(error) => ("input-bounds", error),
                Failure::IncorrectResult => (
                    "incorrect-result",
                    "run did not return the expected true acceptance output".into(),
                ),
                Failure::Invocation { .. } | Failure::Ingress { .. } => {
                    unreachable!("failures are attributed once")
                }
            };
            println!(
                "{}",
                json!({"format":"zkc.benchmark-worker/0", "ingress":ingress, "status":status, "error":error, "completed_calls":completed_calls,"refusal":refusal,"preparation":preparation,"preparation_limits":preparation_limits})
            );
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod request_tests {
    use super::*;

    #[test]
    fn ingress_is_explicit_in_the_current_backend_contract() {
        for kind in ["host", "run"] {
            let mut backend = if kind == "host" {
                json!({"kind":kind,"package":"package","sha256":"pin","inputs":[],
                    "preparation":true,"preparation_entries":null,"preparation_bytes":null})
            } else {
                json!({"kind":kind,"package":"package","sha256":"pin","arguments":"arguments.json","check":{"kind":"acceptance","role":"P"}})
            };
            assert!(serde_json::from_value::<Backend>(backend.clone()).is_err());
            for ingress in ["json", "wire", "native", "prepared"] {
                backend["ingress"] = json!(ingress);
                assert!(serde_json::from_value::<Backend>(backend.clone()).is_ok());
            }
            backend["ingress"] = json!("both");
            assert!(serde_json::from_value::<Backend>(backend.clone()).is_err());
            backend["ingress"] = json!("json");
            backend["unknown"] = json!(true);
            assert!(serde_json::from_value::<Backend>(backend).is_err());
        }
    }
}
