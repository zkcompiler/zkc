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
    #[serde(
        default,
        deserialize_with = "requested_selection",
        skip_serializing_if = "Option::is_none"
    )]
    pub oracle_realization: Option<crate::entry::OracleSelection>,
}
// Absence participates in precedence; an explicitly malformed/null request
// must fail instead of becoming an absent override and selecting the default.
fn requested_selection<'de, D: serde::Deserializer<'de>>(
    decoder: D,
) -> Result<Option<crate::entry::OracleSelection>, D::Error> {
    crate::entry::OracleSelection::deserialize(decoder).map(Some)
}
/// A resolved request records provenance independently of executable policy.
#[derive(Clone, Debug, Serialize)]
pub struct ResolvedSettings {
    pub(crate) profile: String,
    pub(crate) values: BTreeMap<&'static str, bool>,
    pub(crate) oracle_realization: crate::entry::OracleSelection,
    pub(crate) origins: BTreeMap<&'static str, String>,
}
impl Default for ResolvedSettings {
    fn default() -> Self {
        let mut result = Self {
            profile: "default".into(),
            oracle_realization: Default::default(),
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
                oracle_realization: Some(Default::default()),
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
        if let Some(selection) = &settings.oracle_realization {
            self.oracle_realization = selection.clone();
            self.origins.insert("oracle-realization", origin.into());
        }
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
            oracle_realization: self.oracle_realization.clone(),
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
}
impl CompileOptions {
    pub fn flags(&self) -> Result<Vec<String>, crate::entry::OracleSelectionError> {
        let mut flags: Vec<String> = [
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
        .filter_map(|(value, selected, flag)| (value == selected).then_some(flag.to_owned()))
        .collect();
        flags.push(format!(
            "--oracle-realization={}",
            self.oracle_realization.canonical_json()?
        ));
        Ok(flags)
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
        assert_eq!(
            options.flags().unwrap(),
            vec![format!(
                "--oracle-realization={}",
                options.oracle_realization.canonical_json().unwrap()
            )]
        );
        assert!(toml::from_str::<BuildSettings>("unknown=true").is_err());
    }
    #[test]
    fn typed_selection_preserves_precedence_provenance_and_compiler_arguments() {
        use crate::entry::{OracleRoots, OracleSelection, OracleTableRealization};
        let mut resolved = ResolvedSettings::default();
        assert_eq!(resolved.origins()["oracle-realization"], "default");
        let exact = OracleSelection {
            roots: OracleRoots::Exact(vec![]),
            ..Default::default()
        };
        let named = OracleSelection {
            roots: OracleRoots::Uniform(OracleTableRealization {
                scheme: "explicit/0".into(),
                ..Default::default()
            }),
            ..Default::default()
        };
        for (selection, origin) in [
            (exact.clone(), "build"),
            (named.clone(), "profile.selected"),
            (exact.clone(), "request"),
        ] {
            resolved.apply(
                &BuildSettings {
                    oracle_realization: Some(selection.clone()),
                    ..Default::default()
                },
                origin,
            );
            assert_eq!(resolved.options().oracle_realization, selection);
            assert_eq!(resolved.origins()["oracle-realization"], origin);
        }
        resolved.apply(&BuildSettings::default(), "absent");
        assert_eq!(resolved.origins()["oracle-realization"], "request");
        assert_eq!(
            resolved.options().flags().unwrap(),
            [format!(
                "--oracle-realization={}",
                exact.canonical_json().unwrap()
            )]
        );
        assert!(serde_json::from_str::<BuildSettings>(r#"{"oracle-realization":null}"#).is_err());
        assert!(serde_json::from_str::<BuildSettings>(r#"{"oracle-realization":[]}"#).is_err());
        assert!(
            serde_json::from_value::<BuildSettings>(
                serde_json::to_value(BuildSettings::default()).unwrap()
            )
            .is_ok()
        );
        let mut malformed = resolved.options();
        malformed.oracle_realization.roots = OracleRoots::Uniform(OracleTableRealization {
            grouping: crate::entry::OracleLeafGrouping::AntipodalPairs,
            ..Default::default()
        });
        assert!(malformed.flags().is_err());
        let text = r#"oracle-realization = { format = "zkc.oracle-selection/0", roots = {kind = "exact", entries = []}, order = "unrestricted", authentication = "per-query" }"#;
        let parsed: BuildSettings = toml::from_str(text).unwrap();
        assert_eq!(parsed.oracle_realization, Some(exact));
        assert!(toml::from_str::<BuildSettings>(&text.replace("exact", "inferred")).is_err());
        assert!(
            toml::from_str::<BuildSettings>(
                &text.replace("entries = []", "entries = [], unknown = false")
            )
            .is_err()
        );
    }
}
