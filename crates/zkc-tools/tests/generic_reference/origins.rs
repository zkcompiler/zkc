//! Check redundant native path metadata against original source before erasure.
//! This small test oracle follows only source instances and loop bounds; it does
//! not inspect candidate bodies or reuse the native driver's traversal.

use serde_json::Value as Json;
use zkc_runtime::interactive::{ArtifactFormat, Origin, PathElement};

pub(super) struct SourceOrigins(Json);
impl SourceOrigins {
    pub(super) fn new(bytes: &[u8]) -> Self {
        let source: Json = serde_json::from_slice(bytes).unwrap();
        Self(if source[0] == "zkc.library/1" {
            source[3].clone()
        } else {
            source
        })
    }
    pub(super) fn check(&self, origin: &Origin) -> Result<(), &'static str> {
        if origin.format != ArtifactFormat::ExplicitBindings {
            return Err("format");
        }
        let source = &self.0;
        let entry = row(&source[5], 1, &origin.entry)?;
        let mut instance = row(&source[4], 1, text(&entry[2])?)?;
        let mut body = &row(&source[3], 1, text(&instance[2])?)?[7];
        for frame in &origin.path {
            match frame {
                PathElement::Conditional { .. }
                | PathElement::For { .. }
                | PathElement::Match { .. } => {
                    return Err("local-control-origin-unsupported");
                }
                PathElement::Call {
                    site,
                    instance: actual,
                } => {
                    let instruction = row(body, 1, site)?;
                    if instruction[0] != "call" {
                        return Err("call-site");
                    }
                    let dependency = row(&instance[4], 0, text(&instruction[2])?)?;
                    if dependency[1] != actual.as_str() {
                        return Err("call-instance");
                    }
                    instance = row(&source[4], 1, actual)?;
                    body = &row(&source[3], 1, text(&instance[2])?)?[7];
                }
                PathElement::Loop { site, iteration } => {
                    let instruction = row(body, 1, site)?;
                    if instruction[0] != "loop" {
                        return Err("loop-site");
                    }
                    let count = &instruction[2];
                    let n = match count[0].as_str() {
                        Some("constant") => text(&count[1])?,
                        Some("parameter") => text(&row(&instance[3], 0, text(&count[1])?)?[1])?,
                        _ => return Err("loop-count"),
                    }
                    .parse::<u64>()
                    .map_err(|_| "loop-count")?;
                    if *iteration >= n {
                        return Err("loop-iteration");
                    }
                    body = &instruction[5];
                }
            }
        }
        if instance[1] != origin.instance {
            return Err("current-instance");
        }
        Ok(())
    }
}
fn text(value: &Json) -> Result<&str, &'static str> {
    value.as_str().ok_or("source-string")
}
fn row<'a>(values: &'a Json, key: usize, name: &str) -> Result<&'a Json, &'static str> {
    values
        .as_array()
        .ok_or("source-array")?
        .iter()
        .find(|row| row[key] == name)
        .ok_or("source-name")
}

/// The oracle these cases compare against is a test of its own: nothing in the
/// product is touched here, so a failure belongs under a name that says the
/// oracle is wrong rather than under whichever case happened to call it first.
#[test]
fn the_origin_oracle_rejects_instance_iteration_and_ordering_mutations() {
    check_mutations();
}

pub(super) fn check_mutations() {
    use serde_json::json;
    let source = json!([
        "zkc.protocol/1",
        [],
        [],
        [
            [
                "protocol",
                "Root",
                ["P"],
                [],
                [],
                [],
                [["middle", "Middle", []]],
                [["call", "enter", "middle", [], []], ["return", []]]
            ],
            [
                "protocol",
                "Middle",
                ["P"],
                [],
                [],
                [],
                [["leaf", "Leaf", []]],
                [
                    [
                        "loop",
                        "rounds",
                        ["constant", "2"],
                        [],
                        [],
                        [["call", "nested", "leaf", [], []], ["yield", []]],
                        []
                    ],
                    ["return", []]
                ]
            ],
            ["protocol", "Leaf", ["P"], [], [], [], [], [["return", []]]]
        ],
        [
            [
                "instance",
                "root",
                "Root",
                [],
                [["middle", "middle"]],
                [["P", "P"]]
            ],
            [
                "instance",
                "middle",
                "Middle",
                [],
                [["leaf", "leaf"]],
                [["P", "P"]]
            ],
            [
                "instance",
                "alias_middle",
                "Middle",
                [],
                [["leaf", "leaf"]],
                [["P", "P"]]
            ],
            ["instance", "leaf", "Leaf", [], [], [["P", "P"]]]
        ],
        [["entry", "main", "root"]]
    ]);
    let checker = SourceOrigins::new(&serde_json::to_vec(&source).unwrap());
    let origin = Origin {
        format: ArtifactFormat::ExplicitBindings,
        session: "test".into(),
        entry: "main".into(),
        instance: "leaf".into(),
        path: vec![
            PathElement::Call {
                site: "enter".into(),
                instance: "middle".into(),
            },
            PathElement::Loop {
                site: "rounds".into(),
                iteration: 1,
            },
            PathElement::Call {
                site: "nested".into(),
                instance: "leaf".into(),
            },
        ],
    };
    assert_eq!(checker.check(&origin), Ok(()));
    let mut changed = origin.clone();
    let PathElement::Call { instance, .. } = &mut changed.path[0] else {
        unreachable!()
    };
    *instance = "alias_middle".into();
    // Same normalized reference path and leaf; only the intermediate native
    // target changed. The previous erasing observer missed this distinction.
    assert_eq!(
        super::support::source_path(&origin),
        super::support::source_path(&changed)
    );
    assert_eq!(checker.check(&changed), Err("call-instance"));
    let mut changed = origin.clone();
    changed.instance = "middle".into();
    assert_eq!(checker.check(&changed), Err("current-instance"));
    let mut changed = origin.clone();
    changed.path[1] = PathElement::Loop {
        site: "rounds".into(),
        iteration: 2,
    };
    assert_eq!(checker.check(&changed), Err("loop-iteration"));
    let mut changed = origin;
    changed.path.swap(0, 1);
    assert_eq!(checker.check(&changed), Err("source-name"));
}
