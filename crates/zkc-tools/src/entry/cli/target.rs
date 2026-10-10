//! Explicit trust roots for local compilation and pinned packages.
use super::*;
use crate::project::{
    EntryKind, Selection,
    cli::{Source, compiler_error},
};

pub(super) enum Target {
    Project(Source),
    Package {
        package: Package,
        path: String,
        pin: String,
    },
}
impl Target {
    pub fn validate(args: &Arguments<'_>) -> Result<()> {
        let package = args.has("--package");
        if package != args.has("--sha256") {
            return Err("cli-usage".into());
        }
        if package
            && (!args.positional.is_empty()
                || args.options.iter().any(|(k, _)| {
                    matches!(
                        *k,
                        "--project"
                            | "--module"
                            | "--asset"
                            | "--compiler"
                            | "--no-simplify"
                            | "--release-storage"
                    )
                }))
        {
            return Err("cli-usage".into());
        }
        Ok(())
    }
    pub fn load(args: &Arguments<'_>, outputs: &mut Outputs, report: &mut Json) -> Result<Self> {
        if let Some(path) = args.value("--package") {
            outputs.protect([path])?;
            let expected = args.value("--sha256").expect("validated package pin");
            let pin = digest(expected)?;
            let bytes = read(path, Package::MAX_BYTES)?;
            let package =
                Package::capture(&bytes, &pin, Package::MAX_BYTES).map_err(|e| e.to_string())?;
            report["mode"] = json!("package");
            report["package_sha256"] = json!(hex(package.identity()));
            Ok(Self::Package {
                package,
                path: path.into(),
                pin: expected.into(),
            })
        } else {
            let source = Source::load(args)?;
            source.protect(outputs)?;
            source.describe(report);
            Ok(Self::Project(source))
        }
    }
    pub fn inspect(&self, name: Option<&str>, report: &mut Json) -> Result<Interface> {
        match self {
            Self::Package { package, .. } => BoundInterface::read(package)
                .map(|v| v.into_view())
                .map_err(|e| e.to_string()),
            Self::Project(source) => source
                .compiler
                .inspect(&source.project, Selection { name, kind: None })
                .map_err(|e| compiler_error(report, e)),
        }
    }
    pub fn compile(
        &self,
        name: Option<&str>,
        kind: Option<EntryKind>,
        report: &mut Json,
    ) -> Result<Package> {
        let package = match self {
            Self::Package { package, .. } => package.clone(),
            Self::Project(source) => source
                .compiler
                .compile(&source.project, Selection { name, kind }, source.options)
                .map_err(|e| compiler_error(report, e))?,
        };
        report["package_sha256"] = json!(hex(package.identity()));
        Ok(package)
    }
    pub fn protect(&self, outputs: &mut Outputs) -> Result<()> {
        match self {
            Self::Project(source) => source.protect(outputs),
            Self::Package { path, .. } => outputs.protect([path.as_str()]),
        }
    }
}
