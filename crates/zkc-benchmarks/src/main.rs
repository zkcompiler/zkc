//! Development-only benchmark client. Production execution stays in the Host.
mod host;
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
        package: PathBuf,
        sha256: String,
        inputs: Vec<host::Input>,
        preparation: bool,
        preparation_entries: Option<usize>,
    },
    Run {
        package: PathBuf,
        sha256: String,
        roles: std::collections::BTreeMap<String, PathBuf>,
        accept_role: String,
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
            build: json!({"compiler":env!("BENCH_RUSTC"), "profile":env!("BENCH_PROFILE"),
                "opt_level":env!("BENCH_OPT_LEVEL"), "target":env!("BENCH_TARGET"),
                "debug_assertions":cfg!(debug_assertions),
                "execution_counts":zkc_runtime::vm::ExecutionCounts::ENABLED}),
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

// This is the worker's lifetime high-water mark, including setup and warmups.
fn peak_rss() -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        let line = status.lines().find(|s| s.starts_with("VmHWM:"))?;
        line.split_whitespace()
            .nth(1)?
            .parse::<u64>()
            .ok()?
            .checked_mul(1024)
    }
    #[cfg(not(target_os = "linux"))]
    {
        None
    }
}

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
    let mut report = match &request.backend {
        Backend::Host {
            package,
            sha256,
            inputs,
            preparation,
            preparation_entries,
        } => host::run(
            &request,
            package,
            sha256,
            inputs,
            *preparation,
            *preparation_entries,
        )?,
        Backend::Run {
            package,
            sha256,
            roles,
            accept_role,
        } => run_entry::run(&request, package, sha256, roles, accept_role)?,
        Backend::Schnorr { public, witness } if request.operation != Operation::Run => {
            schnorr::run(&request, public, witness.as_deref())?
        }
        Backend::Sumcheck { public } if request.operation != Operation::Run => {
            sumcheck::run(&request, public)?
        }
        _ => return Err("backend does not support this operation".into()),
    };
    report.process_peak_rss_bytes = peak_rss();
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let status_value = |key: &str| {
        status
            .lines()
            .find_map(|line| line.strip_prefix(key).map(str::trim))
    };
    report.process = json!({"threads_at_exit":status_value("Threads:"), "affinity":status_value("Cpus_allowed_list:"),
        "rayon_num_threads":std::env::var("RAYON_NUM_THREADS").ok()});
    report.timer_floor_ns = (0..1000)
        .map(|_| {
            let start = std::time::Instant::now();
            std::hint::black_box(());
            start.elapsed().as_nanos()
        })
        .min()
        .unwrap();
    Ok(report)
}
fn main() {
    match run() {
        Ok(report) => println!("{}", serde_json::to_string(&report).unwrap()),
        Err(error) => {
            let (completed_calls, preparation, error) = match error {
                Failure::Invocation {
                    completed,
                    cause,
                    preparation_before,
                    preparation_after,
                } => (
                    Some(completed),
                    json!({"before":preparation_before,"after":preparation_after}),
                    *cause,
                ),
                error => (None, Value::Null, error),
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
                Failure::Invocation { .. } => unreachable!("invocations are attributed once"),
            };
            println!(
                "{}",
                json!({"format":"zkc.benchmark-worker/0", "status":status, "error":error, "completed_calls":completed_calls,"refusal":refusal,"preparation":preparation})
            );
            std::process::exit(1);
        }
    }
}
