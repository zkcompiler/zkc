//! Closed-source checker command and exact response interpretation.
use serde_json::{Value, json};
use std::{
    path::{Path, PathBuf},
    process::{Command, ExitStatus},
    time::Duration,
};
use zkc_runtime::{CheckFailure, CheckRequest, Checker};

const RESPONSE_LIMIT: u64 = 4096;

pub struct LeanChecker {
    executable: PathBuf,
    timeout: Duration,
}
impl LeanChecker {
    pub fn new(executable: impl AsRef<Path>) -> std::io::Result<Self> {
        Ok(Self {
            executable: executable.as_ref().canonicalize()?,
            timeout: Duration::from_secs(30),
        })
    }
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
}

fn response(
    bytes: &[u8],
    status: ExitStatus,
    request: CheckRequest<'_>,
) -> Result<(), CheckFailure> {
    if bytes.len() as u64 > RESPONSE_LIMIT {
        return Err(CheckFailure::MalformedResponse);
    }
    let text = std::str::from_utf8(bytes)
        .map_err(|_| CheckFailure::MalformedResponse)?
        .trim();
    let mut expected = json!({"claim":"complete-logical-execution",
        "realization":request.realization.name(),"status":"checked"});
    if let Some(phase) = request.phase {
        expected["phase-profile"] = json!(phase.profile);
        if let Some(entry) = &phase.entry {
            expected["entry"] = entry.json();
        }
    }
    let expected = expected.to_string();
    if text == expected {
        return if status.success() {
            Ok(())
        } else {
            Err(CheckFailure::ProcessFailed)
        };
    }
    // The installed tool emits canonical whole records. Requiring exactly that
    // encoding rejects duplicate keys, extra claims and trailing records.
    if let Ok(value) = serde_json::from_str::<Value>(text)
        && let Some(code) = value.get("code").and_then(Value::as_str)
        && let canonical = json!({"code":code,"status":"refused"}).to_string()
        && text == canonical
        && status.code() == Some(1)
    {
        return Err(match code {
            "unresolved-dependency"
            | "unsupported-phase-profile"
            | "unsupported-phase-role"
            | "unsupported-format-version"
            | "unsupported-semantics-version"
            | "unsupported-capability"
            | "unsupported-realization"
            | "unsupported-rule"
            | "unsupported-claim"
            | "unsupported-requirement" => CheckFailure::Unsupported(code.to_owned()),
            "unapproved-requirement" => CheckFailure::UnresolvedRequirements(code.to_owned()),
            _ => CheckFailure::NotEstablished(code.to_owned()),
        });
    }
    Err(if status.success() {
        CheckFailure::MalformedResponse
    } else {
        CheckFailure::ProcessFailed
    })
}

impl Checker for LeanChecker {
    fn check(&self, request: CheckRequest<'_>) -> Result<(), CheckFailure> {
        let dir = tempfile::tempdir().map_err(|_| CheckFailure::Io)?;
        let source = dir.path().join("source.json");
        let plan = dir.path().join("plan.json");
        let certificate = dir.path().join("certificate.json");
        let entry_file = dir.path().join("entry.json");
        std::fs::write(&source, request.source).map_err(|_| CheckFailure::Io)?;
        std::fs::write(&plan, request.candidate).map_err(|_| CheckFailure::Io)?;
        let mut command = Command::new(&self.executable);
        command
            .arg(if request.phase.and_then(|p| p.entry.as_ref()).is_some() {
                "admit-entry"
            } else if request.phase.is_some() {
                "admit"
            } else {
                "check"
            })
            .arg(source)
            .arg(plan);
        if let Some(phase) = request.phase {
            std::fs::write(&certificate, &phase.certificate).map_err(|_| CheckFailure::Io)?;
            command.arg(&phase.profile).arg(certificate);
            if let Some(entry) = &phase.entry {
                std::fs::write(&entry_file, entry.json().to_string())
                    .map_err(|_| CheckFailure::Io)?;
                command.arg(&entry_file);
            }
        }
        let output = crate::host::process::capture(
            &mut command,
            dir.path(),
            |elapsed| elapsed >= self.timeout,
            RESPONSE_LIMIT as usize,
            false,
        )
        .map_err(|error| match error {
            crate::host::process::Error::Process(_) | crate::host::process::Error::Io(_) => {
                CheckFailure::Io
            }
            crate::host::process::Error::Timeout => CheckFailure::BudgetExceeded,
            crate::host::process::Error::OutputLimit => CheckFailure::MalformedResponse,
        })?;
        let bytes = crate::host::io::read_bounded(output.stdout.path(), RESPONSE_LIMIT as usize)
            .map_err(|error| match error {
                crate::host::io::ReadError::Io(_) => CheckFailure::Io,
                crate::host::io::ReadError::Limit => CheckFailure::MalformedResponse,
            })?;
        response(&bytes, output.status, request)
    }
}
