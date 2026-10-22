use super::{CheckedInterface, Project, selection};
use crate::entry::{CompileOptions, Package};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    path::{Path, PathBuf},
    process::Command,
    time::Duration,
};
const DIAGNOSTIC_BYTES: usize = 65536;
pub(super) fn trim_diagnostics(text: &mut String) -> bool {
    let end = text.floor_char_boundary(DIAGNOSTIC_BYTES);
    let truncated = end < text.len();
    text.truncate(end);
    truncated
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum EntryKind {
    Function,
    Proof,
}
impl EntryKind {
    fn name(self) -> &'static str {
        match self {
            Self::Function => "function",
            Self::Proof => "proof",
        }
    }
}
#[derive(Clone, Copy, Debug, Default)]
pub struct Selection<'a> {
    pub name: Option<&'a str>,
    pub kind: Option<EntryKind>,
}
impl Selection<'_> {
    pub fn matches(self, view: &CheckedInterface) -> bool {
        selection::matches(self.name, view.entry()) && self.kind.is_none_or(|k| k == view.kind())
    }
}
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Entry {
    pub name: String,
    pub kind: EntryKind,
}
/// Optional compiler-owned diagnostic inventories. These do not affect semantics.
#[derive(Clone, Copy, Debug, Default)]
pub struct CheckOptions {
    pub declarations: bool,
    pub api: bool,
    pub notations: Option<NotationOptions>,
}
#[derive(Clone, Copy, Debug, Default)]
pub struct NotationOptions {
    pub include_private: bool,
    pub include_installation: bool,
}
/// Definition-check results; inventories are the compiler's diagnostic views.
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Checked {
    pub capture: String,
    pub installation: String,
    pub entries: Vec<Entry>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub entry: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub original: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub declarations: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub notations: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub api: Option<serde_json::Value>,
}
#[derive(Debug)]
pub struct Error {
    pub code: String,
    pub diagnostics: Option<String>,
    pub diagnostics_truncated: bool,
    pub structured: Option<serde_json::Value>,
}
impl From<String> for Error {
    fn from(code: String) -> Self {
        Self {
            code,
            diagnostics: None,
            diagnostics_truncated: false,
            structured: None,
        }
    }
}
impl From<&str> for Error {
    fn from(code: &str) -> Self {
        code.to_owned().into()
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.code)
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

/// The selected executable is resolved once from an explicit path or trusted PATH.
pub struct Compiler {
    path: PathBuf,
}
impl Compiler {
    pub fn new(name: &str) -> Result<Self> {
        let candidates =
            if Path::new(name).is_absolute() || Path::new(name).components().count() > 1 {
                vec![name.into()]
            } else {
                std::env::split_paths(&std::env::var_os("PATH").ok_or("source-compiler-missing")?)
                    .filter(|p| p.is_absolute())
                    .map(|p| p.join(name))
                    .collect()
            };
        for path in candidates {
            if !path.is_file() {
                continue;
            }
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if path
                    .metadata()
                    .map_err(|_| "source-compiler-io")?
                    .permissions()
                    .mode()
                    & 0o111
                    == 0
                {
                    continue;
                }
            }
            return Ok(Self {
                path: path.canonicalize().map_err(|_| "source-compiler-io")?,
            });
        }
        Err("source-compiler-missing".into())
    }
    pub fn path(&self) -> &Path {
        &self.path
    }
    fn invoke(
        &self,
        project: &Project,
        command: &str,
        selection: Selection<'_>,
        extra: &[&str],
    ) -> Result<Vec<u8>> {
        self.invoke_observed(project, command, selection, extra, None)
            .map(|r| r.bytes)
    }
    fn invoke_observed(
        &self,
        project: &Project,
        command: &str,
        selection: Selection<'_>,
        extra: &[&str],
        observations: Option<&ObservationRequest>,
    ) -> Result<Invocation> {
        let toolchain = observations.map(|_| self.capabilities()).transpose()?;
        for source in project.paths() {
            crate::host::io::open_regular(source).map_err(|_| "artifact-io")?;
        }
        let mut process = Command::new(&self.path);
        process.args([command, "--source-format=zkc"]);
        if let Some(name) = selection.name {
            if name.is_empty() {
                return Err("source-entry-selection".into());
            }
            process.arg(format!("--entry={name}"));
        }
        if let Some(kind) = selection.kind {
            process.arg(format!("--entry-kind={}", kind.name()));
        }
        let directory = tempfile::tempdir().map_err(|_| "source-compiler-io")?;
        let observation_path = directory.path().join("observations.json");
        process.arg(format!(
            "--{}={}",
            if observations.is_some() {
                "observations"
            } else {
                "diagnostics"
            },
            observation_path.display()
        ));
        let trace_path = directory.path().join("time-trace.json");
        if let Some(request) = observations {
            process.arg(format!("--time-trace={}", trace_path.display()));
            if !request.dumps.is_empty() {
                process.arg(format!("--dump={}", request.dumps.join(",")));
            }
        }
        process.args(&project.flags).args(extra);
        let captured = crate::host::process::capture(
            &mut process,
            directory.path(),
            |elapsed| elapsed >= Duration::from_secs(300),
            Package::MAX_BYTES,
            true,
        )
        .map_err(|e| match e {
            crate::host::process::Error::Timeout => "source-compiler-timeout",
            crate::host::process::Error::OutputLimit => "source-compiler-limit",
            _ => "source-compiler-io",
        })?;
        use std::io::Read;
        let mut diagnostics = Vec::new();
        captured
            .stderr
            .as_ref()
            .unwrap()
            .reopen()
            .map_err(|_| "source-compiler-io")?
            .take((DIAGNOSTIC_BYTES + 1) as u64)
            .read_to_end(&mut diagnostics)
            .map_err(|_| "source-compiler-io")?;
        let mut truncated = diagnostics.len() > DIAGNOSTIC_BYTES;
        diagnostics.truncate(DIAGNOSTIC_BYTES);
        let mut diagnostics =
            (!diagnostics.is_empty()).then(|| String::from_utf8_lossy(&diagnostics).into_owned());
        if let Some(text) = &mut diagnostics {
            truncated |= trim_diagnostics(text);
        }
        let mut observation: Option<serde_json::Value> =
            crate::host::inputs::read_regular(&observation_path, 32 * 1024 * 1024)
                .ok()
                .and_then(|bytes| serde_json::from_slice::<serde_json::Value>(&bytes).ok())
                .filter(|record| {
                    record.is_object()
                        && record["format"] == "zkc.compilation-observation/0"
                        && record["completed"] == captured.status.success()
                });
        if let Some(observation) = &mut observation
            && observations.is_some()
        {
            if Some(self.capabilities()?) != toolchain {
                return Err("source-compiler-changed".into());
            }
            observation["toolchain"] = toolchain.unwrap();
            let trace = crate::host::inputs::read_regular(&trace_path, 8 * 1024 * 1024)
                .ok()
                .and_then(|bytes| serde_json::from_slice::<serde_json::Value>(&bytes).ok());
            observation["time_trace_status"] = serde_json::json!(if trace.is_some() {
                "collected"
            } else {
                "unavailable-invalid-or-over-limit"
            });
            observation["time_trace"] = trace.unwrap_or(serde_json::Value::Null);
        }
        if !captured.status.success() {
            return Err(Error {
                code: "source-compilation".into(),
                diagnostics,
                diagnostics_truncated: truncated,
                structured: observation,
            });
        }
        if observations.is_some() && observation.is_none() {
            return Err("source-observation-format".into());
        }
        let bytes = crate::host::inputs::read_regular(captured.stdout.path(), Package::MAX_BYTES)?;
        Ok(Invocation {
            bytes,
            diagnostics,
            diagnostics_truncated: truncated,
            observation,
        })
    }
    pub fn check(
        &self,
        project: &Project,
        entry: Option<&str>,
        options: CheckOptions,
    ) -> Result<Checked> {
        let mut flags = Vec::new();
        if options.declarations {
            flags.push("--declarations");
        }
        if options.api {
            flags.push("--api");
        }
        if let Some(notations) = options.notations {
            flags.push("--notations");
            if notations.include_private {
                flags.push("--notation-private");
            }
            if notations.include_installation {
                flags.push("--notation-installation");
            }
        }
        let bytes = self.invoke(
            project,
            "language-check",
            Selection {
                name: entry,
                kind: None,
            },
            &flags,
        )?;
        let mut report: serde_json::Value =
            serde_json::from_slice(&bytes).map_err(|_| "source-check-format")?;
        if report["format"] != "zkc.source-check/0"
            || report["status"] != "checked"
            || report["phase"] != "complete"
            || report["scope"]
                != if entry.is_some() {
                    "entry"
                } else {
                    "definitions"
                }
            || !selection::valid_check(&report, entry)
            || report.get("declarations").is_some() != options.declarations
            || report.get("notations").is_some() != options.notations.is_some()
            || report.get("api").is_some() != options.api
            || (options.api && report["api"]["format"] != "zkc.source-api/0")
        {
            return Err("source-check-format".into());
        }
        let object = report.as_object_mut().ok_or("source-check-format")?;
        for key in ["format", "status", "phase", "scope"] {
            object.remove(key);
        }
        serde_json::from_value(report).map_err(|_| "source-check-format".into())
    }
    /// A checked logical view, obtained before executable lowering. It cannot bind a Host.
    pub fn inspect(&self, project: &Project, selection: Selection<'_>) -> Result<CheckedInterface> {
        let bytes = self.invoke(project, "language-interface", selection, &[])?;
        let view = CheckedInterface::from_compiler(&bytes)?;
        if !selection.matches(&view) {
            return Err("source-entry-selection".into());
        }
        Ok(view)
    }
    /// Captures exactly the locally compiled bytes. Trust rests on source and compiler.
    pub fn compile(
        &self,
        project: &Project,
        selection: Selection<'_>,
        options: CompileOptions,
    ) -> Result<Package> {
        self.build(CompilationRequest {
            project,
            selection,
            options,
            observations: None,
            cache: None,
        })
        .map(|r| r.package)
    }
    pub fn build(&self, request: CompilationRequest<'_>) -> Result<CompilationResult> {
        if let Some(cache) = request.cache {
            return cache.build(self, request);
        }
        let CompilationRequest {
            project,
            selection,
            options,
            observations,
            ..
        } = request;
        let flags = options.flags();
        let invocation =
            self.invoke_observed(project, "language-package", selection, &flags, observations)?;
        let mut result = Self::captured(&invocation.bytes, selection, options)?;
        result.observation = invocation.observation;
        result.diagnostics = invocation.diagnostics;
        result.diagnostics_truncated = invocation.diagnostics_truncated;
        Ok(result)
    }
    pub(super) fn captured(
        bytes: &[u8],
        selection: Selection<'_>,
        options: CompileOptions,
    ) -> Result<CompilationResult> {
        let pin = Sha256::digest(bytes).into();
        let package =
            Package::capture(bytes, &pin, Package::MAX_BYTES).map_err(|e| e.to_string())?;
        let view = CheckedInterface::read(&package)?;
        if !selection.matches(&view) || package.options() != options {
            return Err("source-entry-selection".into());
        }
        Ok(CompilationResult {
            package,
            observation: None,
            diagnostics: None,
            diagnostics_truncated: false,
            cache: None,
        })
    }
    /// Query the actual selected executable, even outside a project.
    pub fn capabilities(&self) -> Result<serde_json::Value> {
        let directory = tempfile::tempdir().map_err(|_| "source-compiler-io")?;
        let captured = crate::host::process::capture(
            Command::new(&self.path).arg("--capabilities"),
            directory.path(),
            |elapsed| elapsed >= Duration::from_secs(30),
            65536,
            true,
        )
        .map_err(|_| "source-compiler-io")?;
        if !captured.status.success() {
            return Err("source-compiler-capabilities".into());
        }
        let bytes = crate::host::inputs::read_regular(captured.stdout.path(), 65536)?;
        let mut result: serde_json::Value =
            serde_json::from_slice(&bytes).map_err(|_| "source-compiler-capabilities")?;
        if result["format"] != "zkc.compiler-capabilities/0" {
            return Err("source-compiler-capabilities".into());
        }
        let mut binary = std::fs::File::open(&self.path).map_err(|_| "source-compiler-io")?;
        let mut hash = Sha256::new();
        use std::io::Read;
        let mut buffer = [0u8; 65536];
        loop {
            let size = binary.read(&mut buffer).map_err(|_| "source-compiler-io")?;
            if size == 0 {
                break;
            }
            hash.update(&buffer[..size]);
        }
        result["binary_sha256"] = serde_json::json!(crate::host::inputs::hex(&hash.finalize()));
        result["path"] = serde_json::json!(self.path);
        result["execution_counts"] = serde_json::json!(zkc_runtime::vm::ExecutionCounts::ENABLED);
        Ok(result)
    }
}
/// Sidecars are opt-in and never become part of executable identity.
#[derive(Clone, Debug, Default)]
pub struct ObservationRequest {
    pub dumps: Vec<String>,
}
pub struct CompilationRequest<'a> {
    pub project: &'a Project,
    pub selection: Selection<'a>,
    pub options: CompileOptions,
    pub observations: Option<&'a ObservationRequest>,
    pub cache: Option<&'a super::CompilationCache>,
}
pub struct CompilationResult {
    pub cache: Option<serde_json::Value>,
    pub package: Package,
    pub observation: Option<serde_json::Value>,
    pub diagnostics: Option<String>,
    pub diagnostics_truncated: bool,
}
struct Invocation {
    bytes: Vec<u8>,
    diagnostics: Option<String>,
    diagnostics_truncated: bool,
    observation: Option<serde_json::Value>,
}
