//! Checked manifest recipe data; command execution belongs to the CLI.
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields, rename_all = "kebab-case")]
pub struct TestRecipe {
    pub entry: String,
    #[serde(default = "operation")]
    pub operation: String,
    #[serde(default)]
    pub args: Vec<String>,
    #[serde(default = "expected")]
    pub expect: String,
}
fn operation() -> String {
    "check".into()
}
fn expected() -> String {
    "success".into()
}
impl TestRecipe {
    pub(super) fn validate(&self) -> Result<(), String> {
        if self.entry.len() > 4096
            || self.entry.is_empty()
            || !["check", "run", "prove", "verify"].contains(&self.operation.as_str())
            || self.args.len() > 64
            || self.args.iter().any(|s| s.len() > 4096)
            || self.expect.is_empty()
            || self.expect.len() > 128
            || self.args.iter().any(|s| {
                [
                    "--project",
                    "--module",
                    "--asset",
                    "--compiler",
                    "--package",
                    "--sha256",
                    "--profile",
                    "--report",
                    "--cache",
                ]
                .iter()
                .any(|flag| s == flag || s.starts_with(&format!("{flag}=")))
            })
        {
            return Err("source-test-format".into());
        }
        Ok(())
    }
}
