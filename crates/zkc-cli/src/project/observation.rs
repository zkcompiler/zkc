//! Immutable, local report publication. Executable publications keep their owner.
use serde_json::{Value, json};
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
};

pub(crate) struct ReportDirectory {
    path: PathBuf,
}
impl ReportDirectory {
    /// A fresh directory prevents overwriting source, inputs or prior evidence.
    pub fn create(path: &str) -> Result<Self, String> {
        let path = std::path::absolute(path).map_err(|_| "report-path")?;
        if path.try_exists().map_err(|_| "report-path")? {
            return Err("report-exists".into());
        }
        fs::create_dir_all(path.parent().ok_or("report-path")?).map_err(|_| "report-io")?;
        fs::create_dir(&path).map_err(|_| "report-io")?;
        Ok(Self { path })
    }
    pub fn publish(&self, report: &mut Value) -> Result<(), String> {
        let mut files = vec!["command.json".to_owned()];
        let field = if report.get("compilation").is_some() {
            "compilation"
        } else {
            "compiler_diagnostics"
        };
        if let Some(mut compilation) = report.get(field).cloned() {
            if let Some(trace) = compilation
                .as_object_mut()
                .and_then(|o| o.remove("time_trace"))
                && !trace.is_null()
            {
                write(
                    &self.path.join("time-trace.json"),
                    &serde_json::to_vec(&trace).map_err(|_| "report-encoding")?,
                )?;
                files.push("time-trace.json".to_owned());
                compilation["time_trace_file"] = json!("time-trace.json");
            }
            if let Some(phases) = compilation["phases"].as_array_mut() {
                for (index, phase) in phases.iter_mut().enumerate() {
                    let Some(name) = phase["phase"].as_str().map(str::to_owned) else {
                        continue;
                    };
                    if ![
                        "entry",
                        "protocol",
                        "participant",
                        "exec",
                        "execution",
                        "physical",
                    ]
                    .contains(&name.as_str())
                    {
                        continue;
                    }
                    if let Some(ir) = phase
                        .as_object_mut()
                        .and_then(|o| o.remove("ir"))
                        .and_then(|s| s.as_str().map(str::to_owned))
                    {
                        let file = format!("{index:03}-{name}.mlir");
                        write(&self.path.join(&file), ir.as_bytes())?;
                        files.push(file.clone());
                        phase["ir_file"] = json!(file);
                    }
                }
            }
            write(
                &self.path.join("compilation.json"),
                &serde_json::to_vec_pretty(&compilation).map_err(|_| "report-encoding")?,
            )?;
            files.push("compilation.json".to_owned());
            report[field] = compilation;
        }
        report["report"] = json!({"directory":self.path,"files":files});
        let bytes = serde_json::to_vec_pretty(report).map_err(|_| "report-encoding")?;
        if bytes.len() > 32 * 1024 * 1024 {
            return Err("report-limit".into());
        }
        write(&self.path.join("command.json"), &bytes)
    }
}
fn write(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = tempfile::NamedTempFile::new_in(path.parent().ok_or("report-path")?)
        .map_err(|_| "report-io")?;
    file.write_all(bytes).map_err(|_| "report-io")?;
    file.persist_noclobber(path).map_err(|_| "report-io")?;
    Ok(())
}
