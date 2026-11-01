use super::{CheckedInterface, Project, selection};
use crate::entry::{CompileOptions, Package};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    ffi::OsString,
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
    /// Compiler-owned diagnostics only; these entries do not authorize claims.
    pub source_claim_inventory: Vec<serde_json::Value>,
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
    #[cfg(feature = "evm")]
    immutable_image: Option<crate::io::executable::Executable>,
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
                #[cfg(feature = "evm")]
                immutable_image: None,
            });
        }
        Err("source-compiler-missing".into())
    }
    pub fn path(&self) -> &Path {
        &self.path
    }
    /// Compile a selected proof Entry through the common checked compiler
    /// boundary. This produces EVM source, never a native Entry package.
    #[cfg(feature = "evm")]
    pub fn evm_source(
        &self,
        project: &Project,
        selection: Selection<'_>,
        options: &crate::evm::Options,
    ) -> Result<crate::evm::Source> {
        let executable = compiler_snapshot(&self.path)?;
        let compiler = Self {
            path: self.path.clone(),
            immutable_image: Some(executable),
        };
        let source = compiler.evm_source_from(project, selection, options)?;
        check_compiler_path(compiler.immutable_image.as_ref().unwrap(), &self.path)?;
        Ok(source)
    }
    #[cfg(feature = "evm")]
    fn evm_source_from(
        &self,
        project: &Project,
        selection: Selection<'_>,
        options: &crate::evm::Options,
    ) -> Result<crate::evm::Source> {
        if selection.kind == Some(EntryKind::Function) {
            return Err("source-entry-selection".into());
        }
        if options.compile.release_storage {
            return Err("evm-option-unsupported".into());
        }
        let mut flags = options.compile.flags().map_err(|e| e.to_string())?;
        flags.push(format!("--evm-version={}", options.fork.as_str()));
        let flags: Vec<_> = flags.iter().map(String::as_str).collect();
        let bytes = self.invoke(project, "language-evm", selection, &flags)?;
        let source = crate::evm::Source::capture(&bytes).map_err(|e| Error::from(e.to_string()))?;
        if !selection::matches(selection.name, source.entry()) {
            return Err("source-entry-selection".into());
        }
        if source.fork() != options.fork
            || source.options() != &options.compile
            || source.metadata()["options"]["numerical_expressions"] != "prefer-native"
        {
            return Err("evm-source-options".into());
        }
        Ok(source)
    }
    /// Reuse requires an immutable authenticated artifact with an exact build
    /// key. Both compiler and solc identities are rechecked on this path.
    #[cfg(feature = "evm")]
    pub fn build_evm(
        &self,
        project: &Project,
        selection: Selection<'_>,
        options: &crate::evm::Options,
        solc: &crate::evm::Solc,
        reuse: Option<&crate::evm::Artifact>,
    ) -> Result<crate::evm::Artifact> {
        let executable = compiler_snapshot(&self.path)?;
        let compiler = Self {
            path: self.path.clone(),
            immutable_image: Some(executable),
        };
        let executable = compiler.immutable_image.as_ref().unwrap();
        let source = compiler.evm_source_from(project, selection, options)?;
        check_compiler_path(executable, &self.path)?;
        let artifact = solc
            .compile(crate::evm::Build {
                source: &source,
                compiler_sha256: executable.sha256(),
                reuse,
            })
            .map_err(|e| Error::from(e.to_string()))?;
        check_compiler_path(executable, &self.path)?;
        Ok(artifact)
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
            crate::io::open_regular(source).map_err(|_| "artifact-io")?;
        }
        let mut arguments = vec![OsString::from(command), "--source-format=zkc".into()];
        if let Some(name) = selection.name {
            if name.is_empty() {
                return Err("source-entry-selection".into());
            }
            arguments.push(format!("--entry={name}").into());
        }
        if let Some(kind) = selection.kind {
            arguments.push(format!("--entry-kind={}", kind.name()).into());
        }
        let directory = tempfile::tempdir().map_err(|_| "source-compiler-io")?;
        let observation_path = directory.path().join("observations.json");
        arguments.push(
            format!(
                "--{}={}",
                if observations.is_some() {
                    "observations"
                } else {
                    "diagnostics"
                },
                observation_path.display()
            )
            .into(),
        );
        let trace_path = directory.path().join("time-trace.json");
        if let Some(request) = observations {
            arguments.push(format!("--time-trace={}", trace_path.display()).into());
            if !request.dumps.is_empty() {
                arguments.push(format!("--dump={}", request.dumps.join(",")).into());
            }
        }
        arguments.extend(project.flags.iter().map(OsString::from));
        arguments.extend(extra.iter().map(OsString::from));
        let captured = self
            .capture(
                &arguments,
                directory.path(),
                Duration::from_secs(300),
                Package::MAX_BYTES,
            )
            .map_err(|e| match e {
                crate::io::process::Error::Timeout => "source-compiler-timeout",
                crate::io::process::Error::OutputLimit => "source-compiler-limit",
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
            crate::io::bytes::read_regular(&observation_path, 32 * 1024 * 1024)
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
            let trace = crate::io::bytes::read_regular(&trace_path, 8 * 1024 * 1024)
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
        let bytes = crate::io::bytes::read_regular(captured.stdout.path(), Package::MAX_BYTES)?;
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
        let flags = options.flags().map_err(|e| e.to_string())?;
        let flags: Vec<_> = flags.iter().map(String::as_str).collect();
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
        let captured = self
            .capture(
                &["--capabilities".into()],
                directory.path(),
                Duration::from_secs(30),
                65536,
            )
            .map_err(|_| "source-compiler-io")?;
        if !captured.status.success() {
            return Err("source-compiler-capabilities".into());
        }
        let bytes = crate::io::bytes::read_regular(captured.stdout.path(), 65536)?;
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
        result["binary_sha256"] = serde_json::json!(crate::io::bytes::hex(&hash.finalize()));
        result["path"] = serde_json::json!(self.path);
        #[cfg(feature = "cpu")]
        let execution_counts = crate::EXECUTION_COUNTS_ENABLED;
        #[cfg(not(feature = "cpu"))]
        let execution_counts = false;
        result["execution_counts"] = serde_json::json!(execution_counts);
        Ok(result)
    }

    fn capture(
        &self,
        arguments: &[OsString],
        directory: &Path,
        timeout: Duration,
        limit: usize,
    ) -> std::result::Result<crate::io::process::Captured, crate::io::process::Error> {
        #[cfg(feature = "evm")]
        if let Some(image) = &self.immutable_image {
            let mut command = image
                .command(&self.path)
                .map_err(crate::io::process::Error::Process)?;
            if let Some(libraries) =
                compiler_library_path(&self.path, std::env::var_os("LD_LIBRARY_PATH").as_deref())
                    .map_err(crate::io::process::Error::Process)?
            {
                command.env("LD_LIBRARY_PATH", libraries);
            }
            return command
                .args(arguments)
                .capture(directory, timeout, limit, None);
        }
        crate::io::process::capture(
            Command::new(&self.path).args(arguments),
            directory,
            |elapsed| elapsed >= timeout,
            limit,
            true,
        )
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

/// The compiler installer owns the bin/../lib layout. A memfd has no installed
/// ELF $ORIGIN, so supply that directory explicitly for snapshot execution.
/// Installed libraries precede trusted ambient fallback; both remain mutable
/// host toolchain inputs, outside the executable image's authentication.
#[cfg(feature = "evm")]
fn compiler_library_path(
    executable: &Path,
    ambient: Option<&std::ffi::OsStr>,
) -> std::io::Result<Option<OsString>> {
    let Some(bin) = executable.parent().filter(|bin| bin.ends_with("bin")) else {
        return Ok(None);
    };
    let library = bin.parent().unwrap().join("lib");
    // ld.so accepts both separators, expands $ tokens and has no escaping.
    // Refuse an ambiguous installation rather than search unintended paths.
    if !library.is_absolute()
        || library
            .as_os_str()
            .as_encoded_bytes()
            .iter()
            .any(|byte| matches!(byte, b':' | b';' | b'$'))
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "compiler installation cannot be represented in LD_LIBRARY_PATH",
        ));
    }
    let mut libraries = library.into_os_string();
    if let Some(ambient) = ambient.filter(|value| !value.is_empty()) {
        libraries.push(":");
        libraries.push(ambient);
    }
    Ok(Some(libraries))
}

#[cfg(feature = "evm")]
fn compiler_snapshot(path: &Path) -> Result<crate::io::executable::Executable> {
    crate::io::executable::Executable::capture(path, 512 * 1024 * 1024)
        .map_err(compiler_snapshot_error)
}

#[cfg(feature = "evm")]
fn check_compiler_path(executable: &crate::io::executable::Executable, path: &Path) -> Result<()> {
    if !executable
        .matches_path(path)
        .map_err(compiler_snapshot_error)?
    {
        return Err("source-compiler-changed".into());
    }
    Ok(())
}

#[cfg(feature = "evm")]
fn compiler_snapshot_error(error: crate::io::ReadError) -> Error {
    match error {
        crate::io::ReadError::Limit => "source-compiler-limit",
        crate::io::ReadError::Io(error) if error.kind() == std::io::ErrorKind::Unsupported => {
            "source-compiler-snapshot-unsupported"
        }
        crate::io::ReadError::Io(_) => "source-compiler-io",
    }
    .into()
}

#[cfg(test)]
mod tests {
    use super::Checked;
    use serde_json::{Value, json};

    #[cfg(unix)]
    #[test]
    fn capabilities_report_the_linked_execution_instrumentation() {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("compiler");
        std::fs::write(
            &path,
            "#!/bin/sh\nprintf '%s\\n' '{\"format\":\"zkc.compiler-capabilities/0\"}'\n",
        )
        .unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
        let compiler = super::Compiler::new(path.to_str().unwrap()).unwrap();
        let capabilities = compiler.capabilities().unwrap();
        #[cfg(feature = "cpu")]
        assert_eq!(
            capabilities["execution_counts"],
            zkc_runtime::vm::ExecutionCounts::ENABLED
        );
        #[cfg(not(feature = "cpu"))]
        assert_eq!(capabilities["execution_counts"], false);
    }

    #[test]
    fn checked_inventory_is_required_and_preserved_without_weakening_the_envelope() {
        let baseline = json!({
            "capture": "capture", "installation": "installation", "entries": [],
            "source_claim_inventory": [{"label": "sound", "node": {"kind": "source-claim"}}]
        });
        let checked: Checked = serde_json::from_value(baseline.clone()).unwrap();
        assert_eq!(serde_json::to_value(checked).unwrap(), baseline);

        let mut missing = baseline.clone();
        missing
            .as_object_mut()
            .unwrap()
            .remove("source_claim_inventory");
        assert!(serde_json::from_value::<Checked>(missing).is_err());
        for invalid in [Value::Null, json!({}), json!("inventory")] {
            let mut changed = baseline.clone();
            changed["source_claim_inventory"] = invalid;
            assert!(serde_json::from_value::<Checked>(changed).is_err());
        }
        let mut unknown = baseline;
        unknown["unrecognized"] = json!([]);
        assert!(serde_json::from_value::<Checked>(unknown).is_err());
    }

    #[cfg(all(feature = "evm", target_os = "linux"))]
    mod evm {
        use super::super::*;
        use serde_json::Value;
        use std::{collections::BTreeMap, os::unix::fs::PermissionsExt};

        fn script(path: &Path, text: &str) {
            std::fs::write(path, text).unwrap();
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).unwrap();
        }

        fn response(entry: &str) -> String {
            crate::evm::tests::source_record(entry, "object \"Verifier\" { code {} }").to_string()
        }

        fn fixture(directory: &Path, entry: &str) -> (Compiler, Project) {
            let path = directory.join("compiler");
            script(
                &path,
                &format!("#!/bin/sh\nprintf '%s' '{}'\n", response(entry)),
            );
            let module = directory.join("main.zkc");
            std::fs::write(&module, "module example;\n").unwrap();
            let project = Project::explicit(
                BTreeMap::from([("example".into(), module.to_str().unwrap().into())]),
                BTreeMap::new(),
            )
            .unwrap();
            (Compiler::new(path.to_str().unwrap()).unwrap(), project)
        }

        #[test]
        fn evm_invocation_passes_and_authenticates_shared_options_and_fork() {
            let directory = tempfile::tempdir().unwrap();
            let (compiler, project) = fixture(directory.path(), "example::Proof");
            let mut options = crate::evm::Options {
                fork: crate::evm::EvmFork::Prague,
                ..Default::default()
            };
            options.compile.simplify = false;
            options.compile.finite_bulk = false;
            options.compile.fuse_vector_reductions = true;
            options.compile.fuse_collect_fold = true;
            options.compile.calculation_batching = false;
            options.compile.oracle_realization.order =
                crate::entry::OracleQueryOrder::AfterFinalDraw;
            let mut record =
                crate::evm::tests::source_record("example::Proof", "invocation control");
            let mut selected = serde_json::to_value(&options.compile).unwrap();
            selected["numerical_expressions"] = serde_json::json!("prefer-native");
            record["options"] = selected.clone();
            record["manifest"]["options"] = selected;
            let mut normalized = options.compile.oracle_realization.clone();
            normalized.roots = crate::entry::OracleRoots::Exact(vec![]);
            record["descriptor"][8] = serde_json::json!(normalized.canonical_json().unwrap());
            record["fork"] = serde_json::json!(options.fork);
            record["manifest"]["fork"] = serde_json::json!(options.fork);
            let mut checks = String::new();
            for flag in options
                .compile
                .flags()
                .unwrap()
                .into_iter()
                .chain(["--evm-version=prague".to_owned()])
            {
                // Flags contain canonical controlled JSON and no shell quotes.
                assert!(!flag.contains('\''));
                checks.push_str(&format!("found=; for arg do if [ \"$arg\" = '{flag}' ]; then found=1; fi; done\n[ \"$found\" = 1 ] || exit 8\n"));
            }
            script(
                compiler.path(),
                &format!("#!/bin/sh\n{checks}printf '%s' '{record}'\n"),
            );
            let direct = compiler
                .evm_source_from(&project, Selection::default(), &options)
                .unwrap();
            let captured = compiler
                .evm_source(&project, Selection::default(), &options)
                .unwrap();
            assert_eq!(direct.bytes(), captured.bytes());
            assert_eq!(captured.fork(), options.fork);
            assert_eq!(captured.options(), &options.compile);

            // A compiler that ignores any selected setting cannot supply a
            // superficially valid response for that request.
            let mut ignored = vec![crate::evm::tests::source_record(
                "example::Proof",
                "ignored options",
            )];
            let mut wrong_fork = record.clone();
            wrong_fork["fork"] = serde_json::json!("cancun");
            wrong_fork["manifest"]["fork"] = serde_json::json!("cancun");
            ignored.push(wrong_fork);
            for field in [
                "simplify",
                "finite_bulk",
                "fuse_vector_reductions",
                "fuse_collect_fold",
                "calculation_batching",
            ] {
                let mut wrong = record.clone();
                wrong["options"][field] =
                    serde_json::json!(!wrong["options"][field].as_bool().unwrap());
                wrong["manifest"]["options"] = wrong["options"].clone();
                ignored.push(wrong);
            }
            let mut wrong_oracle = record.clone();
            wrong_oracle["options"]["oracle_realization"] =
                serde_json::to_value(crate::entry::OracleSelection::default()).unwrap();
            wrong_oracle["manifest"]["options"] = wrong_oracle["options"].clone();
            let normalized = crate::entry::OracleSelection {
                roots: crate::entry::OracleRoots::Exact(vec![]),
                ..Default::default()
            };
            wrong_oracle["descriptor"][8] = serde_json::json!(normalized.canonical_json().unwrap());
            ignored.push(wrong_oracle);
            for record in ignored {
                script(
                    compiler.path(),
                    &format!("#!/bin/sh\nprintf '%s' '{record}'\n"),
                );
                assert_eq!(
                    compiler
                        .evm_source(&project, Selection::default(), &options)
                        .unwrap_err()
                        .code,
                    "evm-source-options"
                );
                assert_eq!(
                    compiler
                        .evm_source_from(&project, Selection::default(), &options)
                        .unwrap_err()
                        .code,
                    "evm-source-options"
                );
            }
            options.compile.release_storage = true;
            assert_eq!(
                compiler
                    .evm_source(&project, Selection::default(), &options)
                    .unwrap_err()
                    .code,
                "evm-option-unsupported"
            );
        }

        #[test]
        fn installed_compiler_library_path_preserves_trusted_fallback_without_adding_cwd() {
            use std::{ffi::OsStr, os::unix::ffi::OsStrExt};

            let path = Path::new("/trusted compiler/安装/bin/zkc-compile");
            let library = OsStr::new("/trusted compiler/安装/lib");
            for ambient in [None, Some(OsStr::new(""))] {
                assert_eq!(
                    compiler_library_path(path, ambient).unwrap().unwrap(),
                    library
                );
            }
            // Preserve caller-supplied empty entries, tokens, separators and
            // non-UTF-8 bytes as trusted ambient policy, without parsing them.
            let ambient = OsStr::from_bytes(b":/ambient\xff;$ORIGIN/plugins:");
            let mut expected = library.to_os_string();
            expected.push(":");
            expected.push(ambient);
            assert_eq!(
                compiler_library_path(path, Some(ambient)).unwrap().unwrap(),
                expected
            );
            assert!(
                compiler_library_path(Path::new("/build/compiler/zkc-compile"), Some(ambient))
                    .unwrap()
                    .is_none()
            );
            let path = Path::new(OsStr::from_bytes(b"/trusted\xff/bin/zkc-compile"));
            assert_eq!(
                compiler_library_path(path, None).unwrap().unwrap(),
                OsStr::from_bytes(b"/trusted\xff/lib")
            );
            for prefix in ["colon:prefix", "semicolon;prefix", "token$ORIGIN"] {
                let directory = tempfile::tempdir().unwrap();
                let bin = directory.path().join(prefix).join("bin");
                std::fs::create_dir_all(&bin).unwrap();
                let (compiler, project) = fixture(&bin, "example::Proof");
                assert_eq!(
                    compiler
                        .evm_source(
                            &project,
                            Selection::default(),
                            &crate::evm::Options::default()
                        )
                        .unwrap_err()
                        .code,
                    "source-compiler-io"
                );
            }
        }

        #[test]
        fn shared_installed_compiler_runs_sealed_bytes_with_installation_libraries() {
            fn output(captured: crate::io::process::Captured) -> Vec<u8> {
                let stderr =
                    crate::io::read_regular(captured.stderr.as_ref().unwrap().path(), 65536)
                        .unwrap();
                assert!(
                    captured.status.success(),
                    "{}: {}",
                    captured.status,
                    String::from_utf8_lossy(&stderr)
                );
                crate::io::read_regular(captured.stdout.path(), 65536).unwrap()
            }
            fn build(directory: &Path, command: &mut Command) {
                output(
                    crate::io::process::capture(
                        command,
                        directory,
                        |elapsed| elapsed >= Duration::from_secs(30),
                        65536,
                        true,
                    )
                    .unwrap(),
                );
            }

            let directory = tempfile::tempdir().unwrap();
            let root = directory.path().join("shared compiler 安装");
            let cc = std::env::var_os("CC").unwrap_or_else(|| "cc".into());
            let bin = root.join("bin");
            let lib = root.join("lib");
            let ambient = root.join("ambient");
            for path in [&bin, &lib, &ambient] {
                std::fs::create_dir_all(path).unwrap();
            }
            // Wrappers may add every -L directory to RUNPATH. Link against a
            // disposable directory, then move only the fixture libraries into
            // the installation. Keep all toolchain/system search paths intact.
            let link_libraries = tempfile::tempdir_in(&root).unwrap();
            let (mut compiler, project) = fixture(&bin, "example::Proof");
            let source = root.join("response.c");
            std::fs::write(
                &source,
                format!(
                    "const char *compiler_response(void) {{ return {}; }}\n",
                    serde_json::to_string(&response("example::Proof")).unwrap()
                ),
            )
            .unwrap();
            let library_name = "libZkcLoaderFixture.so";
            build(
                &root,
                Command::new(&cc)
                    .args(["-shared", "-fPIC", "-Wl,-soname,libZkcLoaderFixture.so"])
                    .arg(&source)
                    .arg("-o")
                    .arg(link_libraries.path().join(library_name)),
            );
            let fallback_source = root.join("fallback.c");
            std::fs::write(
                &fallback_source,
                "int compiler_fallback(void) { return 0; }\n",
            )
            .unwrap();
            let fallback_name = "libZkcLoaderFallback.so";
            build(
                &root,
                Command::new(&cc)
                    .args(["-shared", "-fPIC", "-Wl,-soname,libZkcLoaderFallback.so"])
                    .arg(&fallback_source)
                    .arg("-o")
                    .arg(link_libraries.path().join(fallback_name)),
            );
            let main = root.join("main.c");
            std::fs::write(
                &main,
                "#include <stdio.h>\nextern const char *compiler_response(void);\nextern int compiler_fallback(void);\nint main(void) { puts(compiler_response()); return compiler_fallback(); }\n",
            )
            .unwrap();
            build(
                &root,
                Command::new(&cc)
                    .arg(&main)
                    .arg("-L")
                    .arg(link_libraries.path())
                    .args([
                        "-lZkcLoaderFixture",
                        "-lZkcLoaderFallback",
                        "-Wl,--enable-new-dtags,-rpath,$ORIGIN/../lib",
                        "-o",
                    ])
                    .arg(compiler.path()),
            );
            for name in [library_name, fallback_name] {
                std::fs::rename(link_libraries.path().join(name), lib.join(name)).unwrap();
            }
            let link_path = link_libraries.path().to_owned();
            link_libraries.close().unwrap();
            assert!(!link_path.exists());
            let original = std::fs::read(compiler.path()).unwrap();
            assert_eq!(&original[..4], b"\x7fELF");
            let image = compiler_snapshot(compiler.path()).unwrap();
            assert_eq!(
                image.sha256(),
                crate::io::bytes::hex(&Sha256::digest(&original))
            );
            let direct = compiler
                .evm_source_from(
                    &project,
                    Selection::default(),
                    &crate::evm::Options::default(),
                )
                .unwrap();
            // Control: argv0 alone cannot restore the original ELF $ORIGIN.
            let broken = image
                .command(compiler.path())
                .unwrap()
                .args(["language-evm"])
                .capture(&root, Duration::from_secs(5), 65536, None)
                .unwrap();
            assert_eq!(broken.status.code(), Some(127));
            let stderr =
                crate::io::read_regular(broken.stderr.as_ref().unwrap().path(), 65536).unwrap();
            assert!(String::from_utf8_lossy(&stderr).contains(library_name));
            let sealed = compiler
                .evm_source(
                    &project,
                    Selection::default(),
                    &crate::evm::Options::default(),
                )
                .unwrap();
            assert_eq!(sealed.bytes(), direct.bytes());

            compiler.immutable_image = Some(image);
            for replace_inode in [true, false] {
                if replace_inode {
                    let replacement = root.join("replacement");
                    script(&replacement, "#!/bin/sh\nexit 9\n");
                    std::fs::rename(replacement, compiler.path()).unwrap();
                } else {
                    script(compiler.path(), "#!/bin/sh\nexit 9\n");
                }
                let sealed = compiler
                    .evm_source_from(
                        &project,
                        Selection::default(),
                        &crate::evm::Options::default(),
                    )
                    .unwrap();
                assert_eq!(sealed.bytes(), direct.bytes());
                assert_eq!(
                    check_compiler_path(
                        compiler.immutable_image.as_ref().unwrap(),
                        compiler.path()
                    )
                    .unwrap_err()
                    .code,
                    "source-compiler-changed"
                );
                std::fs::write(compiler.path(), &original).unwrap();
                check_compiler_path(compiler.immutable_image.as_ref().unwrap(), compiler.path())
                    .unwrap();
            }

            // A colliding ambient library must lose to the installation, while
            // a dependency absent from the installation still uses fallback.
            std::fs::rename(lib.join(fallback_name), ambient.join(fallback_name)).unwrap();
            std::fs::write(
                &source,
                "const char *compiler_response(void) { return \"ambient replacement\"; }\n",
            )
            .unwrap();
            build(
                &root,
                Command::new(&cc)
                    .args(["-shared", "-fPIC", "-Wl,-soname,libZkcLoaderFixture.so"])
                    .arg(&source)
                    .arg("-o")
                    .arg(ambient.join(library_name)),
            );
            let libraries = compiler_library_path(compiler.path(), Some(ambient.as_os_str()))
                .unwrap()
                .unwrap();
            let captured = compiler
                .immutable_image
                .as_ref()
                .unwrap()
                .command(compiler.path())
                .unwrap()
                .env("LD_LIBRARY_PATH", libraries)
                .capture(&root, Duration::from_secs(5), 65536, None)
                .unwrap();
            assert_eq!(output(captured), direct.bytes());
        }

        #[test]
        fn evm_response_must_match_the_requested_entry_and_proof_kind() {
            let directory = tempfile::tempdir().unwrap();
            let (compiler, project) = fixture(directory.path(), "example::Proof<example::Fr>");
            for name in [
                None,
                Some("Proof<example::Fr>"),
                Some(" ::example::Proof < example::Fr > "),
            ] {
                assert_eq!(
                    compiler
                        .evm_source(
                            &project,
                            Selection {
                                name,
                                kind: Some(EntryKind::Proof)
                            },
                            &crate::evm::Options::default()
                        )
                        .unwrap()
                        .entry(),
                    "example::Proof<example::Fr>"
                );
            }
            for name in [
                "Other<example::Fr>",
                "Proof",
                "Proof<other::Fr>",
                "other::Proof<example::Fr>",
                "",
            ] {
                assert_eq!(
                    compiler
                        .evm_source(
                            &project,
                            Selection {
                                name: Some(name),
                                kind: None
                            },
                            &crate::evm::Options::default()
                        )
                        .unwrap_err()
                        .code,
                    "source-entry-selection"
                );
            }
            assert_eq!(
                compiler
                    .evm_source(
                        &project,
                        Selection {
                            name: None,
                            kind: Some(EntryKind::Function)
                        },
                        &crate::evm::Options::default()
                    )
                    .unwrap_err()
                    .code,
                "source-entry-selection"
            );
        }

        #[test]
        fn compiler_image_survives_path_changes_and_live_recheck_refuses_them() {
            let directory = tempfile::tempdir().unwrap();
            let (mut compiler, project) = fixture(directory.path(), "example::Proof");
            compiler.immutable_image = Some(compiler_snapshot(compiler.path()).unwrap());
            let original = std::fs::read(compiler.path()).unwrap();
            for replace_inode in [true, false] {
                let replacement = "#!/bin/sh\nexit 9\n";
                if replace_inode {
                    let other = directory.path().join("replacement");
                    script(&other, replacement);
                    std::fs::rename(other, compiler.path()).unwrap();
                } else {
                    script(compiler.path(), replacement);
                }
                let source = compiler
                    .evm_source_from(
                        &project,
                        Selection::default(),
                        &crate::evm::Options::default(),
                    )
                    .unwrap();
                assert_eq!(source.entry(), "example::Proof");
                assert_eq!(
                    check_compiler_path(
                        compiler.immutable_image.as_ref().unwrap(),
                        compiler.path()
                    )
                    .unwrap_err()
                    .code,
                    "source-compiler-changed"
                );
                std::fs::write(compiler.path(), &original).unwrap();
                check_compiler_path(compiler.immutable_image.as_ref().unwrap(), compiler.path())
                    .unwrap();
            }
        }

        #[test]
        fn evm_route_refuses_a_compiler_path_changed_during_execution() {
            let directory = tempfile::tempdir().unwrap();
            let (compiler, project) = fixture(directory.path(), "example::Proof");
            // $0 is the parent fd for scripts; pass the installed path as data.
            // The command executes admitted bytes even after mutating that path.
            script(
                compiler.path(),
                &format!(
                    "#!/bin/sh\nfor arg do\n case \"$arg\" in --replace=*) printf changed > \"${{arg#--replace=}}\";; esac\ndone\nprintf '%s' '{}'\n",
                    response("example::Proof")
                ),
            );
            let mut project = project;
            project
                .flags
                .push(format!("--replace={}", compiler.path().display()));
            assert_eq!(
                compiler
                    .evm_source(
                        &project,
                        Selection::default(),
                        &crate::evm::Options::default()
                    )
                    .unwrap_err()
                    .code,
                "source-compiler-changed"
            );
        }

        #[test]
        fn compiler_snapshot_refuses_oversized_installed_images() {
            let directory = tempfile::tempdir().unwrap();
            let path = directory.path().join("compiler");
            script(&path, "#!/bin/sh\nexit 0\n");
            let file = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
            file.set_len(512 * 1024 * 1024 + 1).unwrap();
            assert_eq!(
                compiler_snapshot(&path).unwrap_err().code,
                "source-compiler-limit"
            );
        }

        #[test]
        #[ignore = "requires explicitly pinned installed compiler and solc"]
        fn pinned_installed_compiler_builds_and_reuses_a_sealed_evm_artifact() {
            let path = std::env::var("ZKC_COMPILER_BIN").unwrap();
            let expected = std::env::var("ZKC_COMPILER_SHA256").unwrap();
            let compiler = Compiler::new(&path).unwrap();
            let image = compiler_snapshot(compiler.path()).unwrap();
            assert_eq!(image.sha256(), expected);
            let project = Project::load(
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../../examples/projects/sumcheck-keccak/zkc.toml"),
            )
            .unwrap();
            let selection = Selection {
                name: Some("example::Proof"),
                kind: Some(EntryKind::Proof),
            };
            // Compare installed catalog resolution and identities with ordinary
            // pathname execution, then use the public snapshot route end to end.
            let direct = compiler
                .evm_source_from(&project, selection, &crate::evm::Options::default())
                .unwrap();
            let sealed = compiler
                .evm_source(&project, selection, &crate::evm::Options::default())
                .unwrap();
            assert_eq!(direct.bytes(), sealed.bytes());
            // Replay the transport defects against a complete real compiler
            // response, before any solc or artifact operation can consume it.
            for key in ["descriptor", "policy", "limits"] {
                let mut malformed = sealed.metadata().clone();
                malformed.as_object_mut().unwrap().remove(key);
                assert_eq!(
                    crate::evm::Source::capture(&serde_json::to_vec(&malformed).unwrap())
                        .unwrap_err()
                        .0,
                    "evm-source-format",
                    "missing {key}"
                );
            }
            for (path, replacement) in [
                ("/unknown", Value::Bool(true)),
                ("/manifest/format", Value::String("wrong-format".into())),
                ("/manifest/limits", Value::Null),
            ] {
                let mut malformed = sealed.metadata().clone();
                if path == "/unknown" {
                    malformed["unknown"] = replacement;
                } else {
                    *malformed.pointer_mut(path).unwrap() = replacement;
                }
                assert!(
                    crate::evm::Source::capture(&serde_json::to_vec(&malformed).unwrap()).is_err(),
                    "{path}"
                );
            }
            let response = serde_json::to_string(sealed.metadata()).unwrap();
            let duplicate = format!("{{\"target\":\"cpu\",{}", &response[1..]);
            assert_eq!(
                crate::evm::Source::capture(duplicate.as_bytes())
                    .unwrap_err()
                    .0,
                "evm-json"
            );
            let solc = crate::evm::Solc::new(
                std::env::var("ZKC_SOLC").unwrap(),
                &std::env::var("ZKC_SOLC_SHA256").unwrap(),
            )
            .unwrap();
            let artifact = compiler
                .build_evm(
                    &project,
                    selection,
                    &crate::evm::Options::default(),
                    &solc,
                    None,
                )
                .unwrap();
            assert_eq!(artifact.manifest().compiler_sha256, expected);
            assert!(!artifact.runtime_bytecode().is_empty());
            let reused = compiler
                .build_evm(
                    &project,
                    selection,
                    &crate::evm::Options::default(),
                    &solc,
                    Some(&artifact),
                )
                .unwrap();
            assert_eq!(artifact.identity(), reused.identity());
            let directory = tempfile::tempdir().unwrap();
            artifact.publish(directory.path().join("artifact")).unwrap();
            let captured = crate::evm::Artifact::capture(
                directory.path().join("artifact"),
                &artifact.identity(),
            )
            .unwrap();
            assert_eq!(captured.runtime_bytecode(), artifact.runtime_bytecode());
            let mut prague = crate::evm::Options {
                fork: crate::evm::EvmFork::Prague,
                ..Default::default()
            };
            prague.compile.simplify = false;
            prague.compile.finite_bulk = false;
            prague.compile.fuse_vector_reductions = true;
            prague.compile.fuse_collect_fold = true;
            prague.compile.calculation_batching = false;
            let selected = compiler.evm_source(&project, selection, &prague).unwrap();
            assert_eq!(selected.fork(), crate::evm::EvmFork::Prague);
            assert_eq!(selected.options(), &prague.compile);
            assert_eq!(
                compiler
                    .build_evm(&project, selection, &prague, &solc, Some(&artifact))
                    .unwrap_err()
                    .code,
                "evm-cache-key"
            );
            let artifact_prague = compiler
                .build_evm(&project, selection, &prague, &solc, None)
                .unwrap();
            assert_eq!(
                artifact_prague.manifest().evm_version,
                crate::evm::EvmFork::Prague
            );
            assert_ne!(artifact_prague.identity(), artifact.identity());
            assert_eq!(
                compiler
                    .build_evm(&project, selection, &prague, &solc, Some(&artifact_prague))
                    .unwrap()
                    .identity(),
                artifact_prague.identity()
            );
            artifact_prague
                .publish(directory.path().join("prague"))
                .unwrap();
            let imported_prague = crate::evm::Artifact::capture(
                directory.path().join("prague"),
                &artifact_prague.identity(),
            )
            .unwrap();
            assert_eq!(
                imported_prague.manifest().evm_version,
                crate::evm::EvmFork::Prague
            );
            let authored_path = directory.path().join("authored.zkc");
            std::fs::write(
                &authored_path,
                r#"module authored;
domain Fr=field("bls12-381.fr");
protocol Echo roles(P,V)(value:Fr@(P,V))->(accepted:bool@V) {
  let received=send P->V(value);
  let accepted=received==value;
  return(accepted=accepted);
}
proof Proof=Echo{prover P;verifier V;public{value};accept accepted;construction authored;}
"#,
            )
            .unwrap();
            let authored = Project::explicit(
                BTreeMap::from([("authored".into(), authored_path.to_str().unwrap().into())]),
                BTreeMap::new(),
            )
            .unwrap();
            let authored_selection = Selection {
                name: Some("authored::Proof"),
                kind: Some(EntryKind::Proof),
            };
            let options = crate::evm::Options::default();
            let direct = compiler
                .evm_source_from(&authored, authored_selection, &options)
                .unwrap();
            let captured = compiler
                .evm_source(&authored, authored_selection, &options)
                .unwrap();
            assert_eq!(direct.bytes(), captured.bytes());
            assert_eq!(captured.metadata()["policy"][5], "");
            assert_eq!(captured.metadata()["policy"][6], serde_json::json!([]));
            assert_eq!(captured.metadata()["policy"][8], serde_json::json!([]));
            assert_eq!(captured.metadata()["policy"][9], "zkc.framed/0");
            let zero = compiler
                .build_evm(&authored, authored_selection, &options, &solc, None)
                .unwrap();
            assert!(!zero.runtime_bytecode().is_empty());
            assert_eq!(zero.source().unwrap().bytes(), captured.bytes());
            check_compiler_path(&image, compiler.path()).unwrap();
        }
    }
}
