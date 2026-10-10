use super::{Project, selection};
use crate::entry::{CompileOptions, Interface, Package};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    path::{Path, PathBuf},
    process::Command,
    time::Duration,
};

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum EntryKind {
    Run,
    Proof,
}
impl EntryKind {
    fn name(self) -> &'static str {
        match self {
            Self::Run => "run",
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
    fn matches(self, view: &Interface) -> bool {
        selection::matches(self.name, view.entry())
            && self
                .kind
                .is_none_or(|k| (k == EntryKind::Proof) == view.is_proof())
    }
}
#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Entry {
    pub name: String,
    pub kind: EntryKind,
}
/// Definition-check results; declarations are the compiler's diagnostic view.
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
}
#[derive(Debug)]
pub struct Error {
    pub code: String,
    pub diagnostics: Option<String>,
    pub diagnostics_truncated: bool,
}
impl From<String> for Error {
    fn from(code: String) -> Self {
        Self {
            code,
            diagnostics: None,
            diagnostics_truncated: false,
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
        process.args(&project.flags).args(extra);
        let directory = tempfile::tempdir().map_err(|_| "source-compiler-io")?;
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
        if !captured.status.success() {
            use std::io::Read;
            let mut bytes = Vec::new();
            captured
                .stderr
                .as_ref()
                .unwrap()
                .reopen()
                .map_err(|_| "source-compiler-io")?
                .take(65537)
                .read_to_end(&mut bytes)
                .map_err(|_| "source-compiler-io")?;
            let truncated = bytes.len() > 65536;
            bytes.truncate(65536);
            return Err(Error {
                code: "source-compilation".into(),
                diagnostics: Some(String::from_utf8_lossy(&bytes).into_owned()),
                diagnostics_truncated: truncated,
            });
        }
        crate::host::inputs::read_regular(captured.stdout.path(), Package::MAX_BYTES)
            .map_err(Into::into)
    }
    pub fn check(
        &self,
        project: &Project,
        entry: Option<&str>,
        declarations: bool,
    ) -> Result<Checked> {
        let bytes = self.invoke(
            project,
            "language-check",
            Selection {
                name: entry,
                kind: None,
            },
            if declarations {
                &["--declarations"]
            } else {
                &[]
            },
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
    pub fn inspect(&self, project: &Project, selection: Selection<'_>) -> Result<Interface> {
        let bytes = self.invoke(project, "language-interface", selection, &[])?;
        let view = Interface::from_compiler(&bytes).map_err(|e| e.to_string())?;
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
        let mut flags = Vec::new();
        if !options.simplify {
            flags.push("--no-simplify");
        }
        if options.release_storage {
            flags.push("--release-storage");
        }
        let bytes = self.invoke(project, "language-package", selection, &flags)?;
        let pin = Sha256::digest(&bytes).into();
        let package =
            Package::capture(&bytes, &pin, Package::MAX_BYTES).map_err(|e| e.to_string())?;
        let view = crate::entry::BoundInterface::read(&package).map_err(|e| e.to_string())?;
        if !selection.matches(&view) || package.options() != options {
            return Err("source-entry-selection".into());
        }
        Ok(package)
    }
}
