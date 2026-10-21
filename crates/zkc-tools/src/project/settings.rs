//! Root-owned implementation settings, shared by the CLI and SDK.
use crate::entry::CompileOptions;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Partial settings never authorize skipping required compiler checks.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields, rename_all = "kebab-case")]
pub struct BuildSettings {
    pub simplify: Option<bool>,
    pub release_storage: Option<bool>,
    pub finite_bulk: Option<bool>,
    pub fuse_vector_reductions: Option<bool>,
    pub fuse_collect_fold: Option<bool>,
    pub calculation_batching: Option<bool>,
}
/// A resolved request records provenance independently of executable policy.
#[derive(Clone, Debug, Serialize)]
pub struct ResolvedSettings {
    pub(crate) profile: String,
    pub(crate) values: BTreeMap<&'static str, bool>,
    pub(crate) origins: BTreeMap<&'static str, String>,
}
impl Default for ResolvedSettings {
    fn default() -> Self {
        let mut result = Self {
            profile: "default".into(),
            values: BTreeMap::new(),
            origins: BTreeMap::new(),
        };
        result.apply(
            &BuildSettings {
                simplify: Some(true),
                release_storage: Some(false),
                finite_bulk: Some(true),
                fuse_vector_reductions: Some(false),
                fuse_collect_fold: Some(false),
                calculation_batching: Some(true),
            },
            "default",
        );
        result
    }
}
impl ResolvedSettings {
    pub fn profile(&self) -> &str {
        &self.profile
    }
    pub fn values(&self) -> &BTreeMap<&'static str, bool> {
        &self.values
    }
    pub fn origins(&self) -> &BTreeMap<&'static str, String> {
        &self.origins
    }
    pub fn apply(&mut self, settings: &BuildSettings, origin: &str) {
        for (name, value) in settings.values() {
            if let Some(value) = value {
                self.values.insert(name, value);
                self.origins.insert(name, origin.into());
            }
        }
    }
    pub fn options(&self) -> CompileOptions {
        CompileOptions {
            simplify: self.values["simplify"],
            release_storage: self.values["release-storage"],
            finite_bulk: self.values["finite-bulk"],
            fuse_vector_reductions: self.values["fuse-vector-reductions"],
            fuse_collect_fold: self.values["fuse-collect-fold"],
            calculation_batching: self.values["calculation-batching"],
        }
    }
}
impl BuildSettings {
    fn values(&self) -> [(&'static str, Option<bool>); 6] {
        [
            ("simplify", self.simplify),
            ("release-storage", self.release_storage),
            ("finite-bulk", self.finite_bulk),
            ("fuse-vector-reductions", self.fuse_vector_reductions),
            ("fuse-collect-fold", self.fuse_collect_fold),
            ("calculation-batching", self.calculation_batching),
        ]
    }
    pub(crate) fn set_flag(&mut self, flag: &str) {
        match flag {
            "--no-simplify" => self.simplify = Some(false),
            "--release-storage" => self.release_storage = Some(true),
            "--no-finite-bulk" => self.finite_bulk = Some(false),
            "--fuse-vector-reductions" => self.fuse_vector_reductions = Some(true),
            "--fuse-collect-fold" => self.fuse_collect_fold = Some(true),
            "--no-calculation-batching" => self.calculation_batching = Some(false),
            _ => (),
        }
    }
}
impl CompileOptions {
    pub fn flags(&self) -> Vec<&'static str> {
        [
            (self.simplify, false, "--no-simplify"),
            (self.release_storage, true, "--release-storage"),
            (self.finite_bulk, false, "--no-finite-bulk"),
            (
                self.fuse_vector_reductions,
                true,
                "--fuse-vector-reductions",
            ),
            (self.fuse_collect_fold, true, "--fuse-collect-fold"),
            (
                self.calculation_batching,
                false,
                "--no-calculation-batching",
            ),
        ]
        .into_iter()
        .filter_map(|(value, selected, flag)| (value == selected).then_some(flag))
        .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn resolution_preserves_request_precedence_and_explicit_false() {
        let mut resolved = ResolvedSettings::default();
        resolved.apply(
            &BuildSettings {
                finite_bulk: Some(false),
                release_storage: Some(true),
                ..Default::default()
            },
            "build",
        );
        resolved.apply(
            &BuildSettings {
                finite_bulk: Some(true),
                ..Default::default()
            },
            "profile.vector",
        );
        resolved.apply(
            &BuildSettings {
                release_storage: Some(false),
                ..Default::default()
            },
            "request",
        );
        let options = resolved.options();
        assert!(options.finite_bulk);
        assert!(!options.release_storage);
        assert_eq!(resolved.origins["finite-bulk"], "profile.vector");
        assert_eq!(resolved.origins["release-storage"], "request");
        assert!(options.flags().is_empty());
        assert!(toml::from_str::<BuildSettings>("unknown=true").is_err());
    }
}
