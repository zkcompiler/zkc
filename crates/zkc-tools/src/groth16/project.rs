//! Project preparation keeps the captured relation descriptor across lowering.
use super::{
    Error, PreparedProtocol, PreparedRelation, Result, compiler_output,
    compiler_output_with_libraries, relation,
};
use serde_json::Value as Json;
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

impl PreparedProtocol {
    /// Capture a frontend project once, then compile its immutable snapshot.
    /// The dedicated Groth16 adapter requires one public-matrix rank-one view
    /// of the supplied R1CS, reached through `main`'s Products and Residuals
    /// calls, and the example's `main` participant contract. Other rank-one
    /// views must not be reached. This is a structural call-graph check, not a
    /// proof that arbitrary source implements the Groth16 verifier equation.
    /// Library aliases and generated symbols do not select relation identity.
    /// Setup/key-derivation premises remain those of `bind_checked`.
    pub fn compile_project(
        compiler: impl AsRef<Path>,
        lean: impl AsRef<Path>,
        source: impl AsRef<Path>,
        libraries: &[PathBuf],
        r1cs: impl AsRef<Path>,
    ) -> Result<Self> {
        // The compiler owns the project library limit and refuses beyond it.
        let relation = PreparedRelation::read(&compiler, r1cs)?;
        let snapshot = compiler_output_with_libraries(
            compiler.as_ref(),
            "protocol-resolve",
            source.as_ref(),
            libraries,
        )?;
        let (view, rank_one_views) = selected_view(&snapshot, &relation)?;
        let directory = tempfile::tempdir().map_err(|e| Error::detail("groth16-io", e))?;
        let path = directory.path().join("resolved.json");
        std::fs::write(&path, snapshot).map_err(|e| Error::detail("groth16-io", e))?;
        let common = compiler_output(compiler.as_ref(), "protocol-materialize", &path)?;
        let path = directory.path().join("materialized.json");
        std::fs::write(&path, &common).map_err(|e| Error::detail("groth16-io", e))?;
        let endpoints = compiler_output(compiler.as_ref(), "protocol-compile", &path)?;
        let mut result = Self::prepare_view(
            &common,
            &endpoints,
            lean.as_ref(),
            relation.identity(),
            &view,
            &rank_one_views,
        )?;
        result.relation = Some(relation::retained(relation));
        Ok(result)
    }
}

/// The snapshot's relation declarations and view records, each of the exact
/// shape the compiler writes. A malformed entry is refused rather than skipped,
/// since skipping could leave the selected view resting on an entry never read.
fn relation_tables(source: &Json) -> Result<(&Vec<Json>, &Vec<Json>)> {
    let malformed = || Error::new("groth16-relation-source");
    let declarations = source[1][0].as_array().ok_or_else(malformed)?;
    let views = source[1][1].as_array().ok_or_else(malformed)?;
    if declarations.iter().any(|d| {
        d.as_array()
            .is_none_or(|d| d.len() != 2 || !d[0].is_string())
    }) || views.iter().any(|v| {
        v.as_array()
            .is_none_or(|v| v.len() != 5 || !v.iter().all(Json::is_string))
    }) {
        return Err(malformed());
    }
    Ok((declarations, views))
}

fn selected_view(snapshot: &[u8], relation: &PreparedRelation) -> Result<(String, Vec<String>)> {
    let source: serde_json::Value =
        serde_json::from_slice(snapshot).map_err(|e| Error::detail("groth16-source", e))?;
    if source[0] != "zkc.relations/1" {
        return Err(Error::new("groth16-relation-source"));
    }
    let (declarations, views) = relation_tables(&source)?;
    let expected: serde_json::Value = serde_json::from_slice(relation.canonical_descriptor())
        .map_err(|e| Error::detail("groth16-relation-json", e))?;
    let mut selected = None;
    let mut rank_one_views = Vec::new();
    for view in views {
        if view[2] == "rank_one" {
            rank_one_views.push(name(&view[0])?.to_owned());
        }
        if view[2] != "rank_one" || view[3] != "public_matrices" || view[4] != "0" {
            continue;
        }
        let owner = declarations.iter().find(|d| d[0] == view[1]);
        if owner.is_some_and(|d| d[1] == expected) {
            let name = view[0]
                .as_str()
                .ok_or_else(|| Error::new("groth16-relation-source"))?;
            if selected.replace(name.to_owned()).is_some() {
                return Err(Error::new("groth16-relation-view-ambiguous"));
            }
        }
    }
    Ok((
        selected.ok_or_else(|| Error::new("groth16-relation-identity"))?,
        rank_one_views,
    ))
}

// A typed projection of the common carrier's call graph, before algorithm
// expansion erases `apply`. JSON coordinates belong only to this decoder;
// graph traversal uses callable, protocol and instance identities. Admission
// and the independent endpoint correspondence check still check the full code.
enum Call<'a> {
    Function(&'a str),
    Dependency(&'a str),
}
struct Function<'a> {
    origin: Option<&'a str>,
    calls: Vec<Call<'a>>,
}
struct Protocol<'a> {
    calls: Vec<Call<'a>>,
}
struct Instance<'a> {
    protocol: &'a str,
    dependencies: BTreeMap<&'a str, &'a str>,
}
struct CommonGraph<'a> {
    functions: BTreeMap<&'a str, Function<'a>>,
    protocols: BTreeMap<&'a str, Protocol<'a>>,
    instances: BTreeMap<&'a str, Instance<'a>>,
    entries: BTreeMap<&'a str, &'a str>,
}
fn graph_error() -> Error {
    Error::new("groth16-relation-call-graph")
}
fn list(value: &Json) -> Result<&[Json]> {
    value.as_array().map(Vec::as_slice).ok_or_else(graph_error)
}
fn record(value: &Json, size: usize) -> Result<&[Json]> {
    let row = list(value)?;
    if row.len() != size {
        return Err(graph_error());
    }
    Ok(row)
}
fn name(value: &Json) -> Result<&str> {
    value.as_str().ok_or_else(graph_error)
}
fn insert<'a, T>(map: &mut BTreeMap<&'a str, T>, key: &'a str, value: T) -> Result<()> {
    if map.insert(key, value).is_some() {
        return Err(graph_error());
    }
    Ok(())
}
fn calls(body: &Json) -> Result<Vec<Call<'_>>> {
    let mut result = Vec::new();
    let mut pending = vec![body];
    while let Some(body) = pending.pop() {
        for instruction in list(body)? {
            let row = list(instruction)?;
            match row.first().and_then(Json::as_str) {
                Some("local") => result.push(Call::Function(name(&record(instruction, 6)?[3])?)),
                Some("apply") => result.push(Call::Function(name(&record(instruction, 6)?[2])?)),
                Some("call") => result.push(Call::Dependency(name(&record(instruction, 5)?[2])?)),
                Some("if") => {
                    let row = record(instruction, 7)?;
                    pending.extend([&row[4], &row[5]]);
                }
                Some("match") => {
                    for arm in list(&record(instruction, 6)?[4])? {
                        pending.push(&record(arm, 3)?[2]);
                    }
                }
                Some("for") => {
                    let row = record(instruction, 9)?;
                    // Statically empty traversals cannot establish view use.
                    if row[3] != row[4] {
                        pending.push(&row[7]);
                    }
                }
                Some("loop") => {
                    let row = record(instruction, 7)?;
                    let count = record(&row[2], 2)?;
                    if count[0] != "constant" || count[1] != "0" {
                        pending.push(&row[5]);
                    }
                }
                Some("op" | "variant" | "message" | "return" | "yield" | "stop" | "incomplete") => {
                }
                _ => return Err(graph_error()),
            }
        }
    }
    Ok(result)
}
impl<'a> CommonGraph<'a> {
    fn decode(source: &'a Json) -> Result<Self> {
        let mut graph = Self {
            functions: BTreeMap::new(),
            protocols: BTreeMap::new(),
            instances: BTreeMap::new(),
            entries: BTreeMap::new(),
        };
        let mut common = source;
        if source[0] == "zkc.library/1" {
            let library = record(source, 4)?;
            for definition in list(&library[1])? {
                let row = record(definition, 7)?;
                if row[0] != "generic_function" {
                    return Err(graph_error());
                }
                insert(
                    &mut graph.functions,
                    name(&row[1])?,
                    Function {
                        origin: None,
                        calls: calls(&row[6])?,
                    },
                )?;
            }
            for configuration in list(&library[2])? {
                let row = record(configuration, 5)?;
                if row[0] != "configure" {
                    return Err(graph_error());
                }
                insert(
                    &mut graph.functions,
                    name(&row[1])?,
                    Function {
                        origin: None,
                        calls: vec![Call::Function(name(&row[2])?)],
                    },
                )?;
            }
            common = &library[3];
        }
        let common = record(common, 6)?;
        if common[0] != "zkc.protocol/1" {
            return Err(graph_error());
        }
        for function in list(&common[2])? {
            let row = record(function, 6)?;
            if row[0] != "function" {
                return Err(graph_error());
            }
            insert(
                &mut graph.functions,
                name(&row[1])?,
                Function {
                    origin: Some(name(&record(&row[5], 2)?[0])?),
                    calls: calls(&row[4])?,
                },
            )?;
        }
        for protocol in list(&common[3])? {
            let row = record(protocol, 8)?;
            if row[0] != "protocol" {
                return Err(graph_error());
            }
            insert(
                &mut graph.protocols,
                name(&row[1])?,
                Protocol {
                    calls: calls(&row[7])?,
                },
            )?;
        }
        for instance in list(&common[4])? {
            let row = record(instance, 6)?;
            if row[0] != "instance" {
                return Err(graph_error());
            }
            let mut dependencies = BTreeMap::new();
            for dependency in list(&row[4])? {
                let pair = record(dependency, 2)?;
                insert(&mut dependencies, name(&pair[0])?, name(&pair[1])?)?;
            }
            insert(
                &mut graph.instances,
                name(&row[1])?,
                Instance {
                    protocol: name(&row[2])?,
                    dependencies,
                },
            )?;
        }
        for entry in list(&common[5])? {
            let row = record(entry, 3)?;
            if row[0] != "entry" {
                return Err(graph_error());
            }
            insert(&mut graph.entries, name(&row[1])?, name(&row[2])?)?;
        }
        Ok(graph)
    }

    fn reachable(&self) -> Result<BTreeSet<&'a str>> {
        let mut instances = vec![*self.entries.get("main").ok_or_else(graph_error)?];
        let mut visited = BTreeSet::new();
        let mut functions = Vec::new();
        while let Some(name) = instances.pop() {
            if !visited.insert(name) {
                continue;
            }
            let instance = self.instances.get(name).ok_or_else(graph_error)?;
            let protocol = self
                .protocols
                .get(instance.protocol)
                .ok_or_else(graph_error)?;
            for call in &protocol.calls {
                match call {
                    Call::Function(name) => functions.push(*name),
                    Call::Dependency(alias) => {
                        instances.push(*instance.dependencies.get(alias).ok_or_else(graph_error)?)
                    }
                }
            }
        }
        let mut reached = BTreeSet::new();
        while let Some(name) = functions.pop() {
            if !reached.insert(name) {
                continue;
            }
            for call in &self.functions.get(name).ok_or_else(graph_error)?.calls {
                let Call::Function(name) = call else {
                    return Err(graph_error());
                };
                functions.push(*name);
            }
        }
        Ok(reached)
    }
}

pub(super) fn check_view_use(
    source: &Json,
    identity: &str,
    selected: &str,
    rank_one_views: &[String],
) -> Result<()> {
    let graph = CommonGraph::decode(source)?;
    let reached = graph.reachable()?;
    for view in rank_one_views
        .iter()
        .filter(|view| view.as_str() != selected)
    {
        for member in ["Assemble", "Products", "Residuals"] {
            if reached.contains(format!("{view}_{member}").as_str()) {
                return Err(Error::new("groth16-relation-view-mismatch"));
            }
        }
    }
    let origin = format!("Relation_{identity}");
    for member in ["Assemble", "Products", "Residuals"] {
        let helper = format!("{selected}_{member}");
        let function = graph
            .functions
            .get(helper.as_str())
            .ok_or_else(|| Error::new("groth16-relation-source"))?;
        if function.origin != Some(origin.as_str()) {
            return Err(Error::new("groth16-relation-identity"));
        }
        // The host provides the assembled assignment, so Assemble is optional.
        if member != "Assemble" && !reached.contains(helper.as_str()) {
            return Err(Error::new("groth16-relation-view-unused"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::relation_tables;
    use serde_json::json;

    #[test]
    fn malformed_relation_entries_are_refused_not_skipped() {
        let view = json!(["Core", "Circuit", "rank_one", "public_matrices", "0"]);
        let valid = json!(["zkc.relations/1", [[["Circuit", ["relation"]]], [view]], []]);
        assert!(relation_tables(&valid).is_ok());
        for broken in [
            json!(["zkc.relations/1", [[["Circuit"]], [view]], []]),
            json!(["zkc.relations/1", [[[7, ["relation"]]], [view]], []]),
            json!([
                "zkc.relations/1",
                [[["Circuit", ["relation"]]], [["Core", "Circuit"]]],
                []
            ]),
            json!([
                "zkc.relations/1",
                [
                    [["Circuit", ["relation"]]],
                    [["Core", "Circuit", "rank_one", "public_matrices", 0]]
                ],
                []
            ]),
            json!([
                "zkc.relations/1",
                [[["Circuit", ["relation"]]], ["Core"]],
                []
            ]),
        ] {
            assert_eq!(
                relation_tables(&broken).unwrap_err().code,
                "groth16-relation-source"
            );
        }
    }
}
