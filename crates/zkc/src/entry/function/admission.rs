use super::{carrier::*, *};
use crate::entry::interface::{preflight, schemas::Schemas};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8], limit: usize) -> Result<T> {
    preflight::check_carrier(bytes, limit)
        .map_err(|e| EntryError::new(EntryPhase::Admission, e))?;
    let mut decoder = serde_json::Deserializer::from_slice(bytes);
    decoder.disable_recursion_limit();
    let value =
        serde::Deserialize::deserialize(&mut decoder).map_err(|_| error("entry-host-format"))?;
    decoder.end().map_err(|_| error("entry-host-format"))?;
    Ok(value)
}
fn name(s: &str) -> Result<()> {
    require(!s.is_empty() && s.len() <= 256 * 1024, "entry-host-symbol")
}
fn inventory<'a>(names: impl Iterator<Item = &'a str>) -> Result<BTreeSet<&'a str>> {
    let mut seen = BTreeSet::new();
    for s in names {
        name(s)?;
        require(seen.insert(s), "entry-host-duplicate")?;
    }
    require(seen.len() <= 4096, "entry-host-limit")?;
    Ok(seen)
}
fn signature(s: &FunctionSignature) -> Result<()> {
    name(&s.symbol)?;
    let mut names = BTreeSet::new();
    for p in &s.parameters {
        require(
            crate::source_names::is_source_identifier(&p.name)
                && p.name.len() <= 128
                && names.insert(&p.name),
            "entry-host-parameter",
        )?;
    }
    require(s.parameters.len() <= 1024, "entry-host-limit")
}
pub(in crate::entry::function) fn check_schema<'a>(
    s: &'a Schema,
    schemas: &mut Schemas<'a>,
) -> Result<()> {
    schemas
        .check(s, 0)
        .map_err(|e| EntryError::new(EntryPhase::Interface, e))?;
    crate::entry::interface::schemas::check_export(s)
        .map_err(|e| EntryError::new(EntryPhase::Admission, e))
}
pub(in crate::entry::function) fn structure<'a>(
    document: &'a Document,
    interface: &'a FunctionInterface,
) -> Result<Validator<'a>> {
    let original = interface.original();
    require(
        interface.document.format == "zkc.language-interface/0" && document.format == "zkc.host/0",
        "entry-host-format",
    )?;
    require(
        interface.document.original == original && document.original == original,
        "entry-host-identity",
    )?;
    require(
        interface.document.selection.kind == "function"
            && interface.document.selection.function == document.entry,
        "entry-host-selection",
    )?;
    require(
        interface.document.protocols.is_empty()
            && interface.document.relations.is_empty()
            && interface.document.setups.is_empty(),
        "entry-host-stage",
    )?;
    name(&interface.document.capture)?;
    name(&interface.document.entry)?;
    name(&interface.document.toolchain)?;
    let functions = inventory(
        document
            .functions
            .iter()
            .map(|f| f.signature.symbol.as_str()),
    )?;
    let calculations = inventory(document.calculations.iter().map(|c| c.id.as_str()))?;
    let deployments = inventory(document.deployments.iter().map(|d| d.id.as_str()))?;
    require(
        functions.contains(document.entry.as_str()),
        "entry-host-selection",
    )?;
    let signatures = inventory(
        interface
            .document
            .functions
            .iter()
            .map(|s| s.symbol.as_str()),
    )?;
    require(signatures == functions, "entry-host-signature")?;
    for f in &document.functions {
        require(
            interface
                .document
                .functions
                .iter()
                .any(|s| s == &f.signature),
            "entry-host-signature",
        )?;
    }
    let mut schemas = Schemas::new();
    for s in &interface.document.functions {
        signature(s)?;
        for p in &s.parameters {
            check_schema(&p.schema, &mut schemas)?;
        }
        check_schema(&s.result, &mut schemas)?;
    }
    let mut validator = Validator {
        document,
        schemas,
        operations: 0,
        calls: BTreeMap::new(),
        calculations: BTreeSet::new(),
        deployments: BTreeSet::new(),
    };
    for f in &document.functions {
        signature(&f.signature)?;
        for p in &f.signature.parameters {
            check_schema(&p.schema, &mut validator.schemas)?;
        }
        check_schema(&f.signature.result, &mut validator.schemas)?;
        validator.block(
            &f.body,
            &f.signature
                .parameters
                .iter()
                .map(|p| &p.schema)
                .collect::<Vec<_>>(),
            &[&f.signature.result],
            &mut BTreeSet::new(),
            &f.signature.symbol,
            0,
        )?;
    }
    let mut heights = BTreeMap::new();
    visit(
        &document.entry,
        &validator.calls,
        &mut BTreeSet::new(),
        &mut heights,
        0,
    )?;
    require(
        heights.keys().copied().collect::<BTreeSet<_>>() == functions,
        "entry-host-coverage",
    )?;
    require(
        validator.calculations == calculations && validator.deployments == deployments,
        "entry-host-coverage",
    )?;
    Ok(validator)
}

fn visit<'a>(
    s: &'a str,
    graph: &BTreeMap<&'a str, BTreeSet<&'a str>>,
    active: &mut BTreeSet<&'a str>,
    heights: &mut BTreeMap<&'a str, usize>,
    depth: usize,
) -> Result<()> {
    require(depth <= 64, "entry-host-depth")?;
    require(!active.contains(s), "entry-host-cycle")?;
    // Reused callees retain their longest suffix: a previous shorter path
    // must not hide the full depth of a later caller.
    if let Some(height) = heights.get(s) {
        return require(depth + height <= 64, "entry-host-depth");
    }
    active.insert(s);
    let mut height = 0;
    if let Some(calls) = graph.get(s) {
        for c in calls {
            visit(c, graph, active, heights, depth + 1)?;
            height = height.max(heights[c] + 1);
        }
    }
    active.remove(s);
    heights.insert(s, height);
    Ok(())
}
pub(in crate::entry::function) struct Validator<'a> {
    document: &'a Document,
    pub(in crate::entry::function) schemas: Schemas<'a>,
    operations: usize,
    pub(in crate::entry::function) calls: BTreeMap<&'a str, BTreeSet<&'a str>>,
    calculations: BTreeSet<&'a str>,
    deployments: BTreeSet<&'a str>,
}
fn same(actual: &[&Schema], expected: &[&Schema]) -> Result<()> {
    require(actual == expected, "entry-host-signature")
}
impl<'a> Validator<'a> {
    fn block(
        &mut self,
        b: &'a Block,
        args: &[&Schema],
        returns: &[&Schema],
        seen: &mut BTreeSet<u32>,
        function: &'a str,
        depth: usize,
    ) -> Result<()> {
        require(depth <= 64, "entry-host-depth")?;
        same(
            &b.arguments.iter().map(|v| &v.schema).collect::<Vec<_>>(),
            args,
        )?;
        let mut env = BTreeMap::new();
        for v in &b.arguments {
            self.define(v, &mut env, seen)?;
        }
        for (position, op) in b.operations.iter().enumerate() {
            self.operations += 1;
            require(self.operations <= 100_000, "entry-host-limit")?;
            require(
                op.operands().len() <= 1024 && op.results().len() <= 1024,
                "entry-host-limit",
            )?;
            let operands = op
                .operands()
                .iter()
                .map(|i| {
                    env.get(i)
                        .copied()
                        .ok_or_else(|| error("entry-host-dominance"))
                })
                .collect::<Result<Vec<_>>>()?;
            let results = op.results().iter().map(|v| &v.schema).collect::<Vec<_>>();
            use Operation::*;
            match op {
                Construct { alternative, .. } => {
                    require(results.len() == 1, "entry-host-signature")?;
                    let s = results[0];
                    require(s.constructible && !s.custody, "entry-host-constructor")?;
                    let fields = if s.kind == SchemaKind::Variant {
                        &s.alternatives
                            .iter()
                            .find(|a| a.name == *alternative)
                            .ok_or_else(|| error("entry-host-alternative"))?
                            .fields
                    } else {
                        require(
                            alternative.is_empty()
                                && matches!(
                                    s.kind,
                                    SchemaKind::Record
                                        | SchemaKind::Array
                                        | SchemaKind::Tuple
                                        | SchemaKind::Unit
                                ),
                            "entry-host-constructor",
                        )?;
                        &s.fields
                    };
                    same(
                        &operands,
                        &fields.iter().map(|f| &f.schema).collect::<Vec<_>>(),
                    )?;
                }
                Unpack { .. } => {
                    require(
                        operands.len() == 1
                            && matches!(
                                operands[0].kind,
                                SchemaKind::Record
                                    | SchemaKind::Tuple
                                    | SchemaKind::Array
                                    | SchemaKind::Unit
                            ),
                        "entry-host-unpack",
                    )?;
                    same(
                        &results,
                        &operands[0]
                            .fields
                            .iter()
                            .map(|f| &f.schema)
                            .collect::<Vec<_>>(),
                    )?;
                }
                Stop { reason, .. } => {
                    require(
                        operands.is_empty()
                            && results.is_empty()
                            && reason.len() <= 4096
                            && position + 1 == b.operations.len()
                            && b.returns.is_empty(),
                        "entry-host-stop-shape",
                    )?;
                }
                Project { path, .. } => {
                    require(
                        operands.len() == 1 && results.len() == 1 && path.len() <= 32,
                        "entry-host-signature",
                    )?;
                    let mut s = operands[0];
                    for i in path {
                        require(s.kind != SchemaKind::Variant, "entry-host-projection")?;
                        s = &s
                            .fields
                            .get(*i as usize)
                            .ok_or_else(|| error("entry-host-projection"))?
                            .schema;
                    }
                    same(&results, &[s])?;
                }
                Call { callee, .. } => {
                    let f = self
                        .document
                        .functions
                        .iter()
                        .find(|f| f.signature.symbol == *callee)
                        .ok_or_else(|| error("entry-host-callee"))?;
                    same(
                        &operands,
                        &f.signature
                            .parameters
                            .iter()
                            .map(|p| &p.schema)
                            .collect::<Vec<_>>(),
                    )?;
                    same(&results, &[&f.signature.result])?;
                    self.calls.entry(function).or_default().insert(callee);
                }
                Numeric { calculation, .. } => {
                    let c = self
                        .document
                        .calculations
                        .iter()
                        .find(|c| c.id == *calculation)
                        .ok_or_else(|| error("entry-host-calculation"))?;
                    same(&operands, &c.parameters.iter().collect::<Vec<_>>())?;
                    same(&results, &c.results.iter().collect::<Vec<_>>())?;
                    self.calculations.insert(calculation);
                }
                Invoke { deployment, .. } => {
                    let d = self
                        .document
                        .deployments
                        .iter()
                        .find(|d| d.id == *deployment)
                        .ok_or_else(|| error("entry-host-deployment"))?;
                    same(&operands, &d.parameters.iter().collect::<Vec<_>>())?;
                    same(&results, &d.results.iter().collect::<Vec<_>>())?;
                    self.deployments.insert(deployment);
                }
                If { regions, .. } => {
                    require(
                        regions.len() == 2
                            && !operands.is_empty()
                            && operands[0].kind == SchemaKind::Boolean,
                        "entry-host-condition",
                    )?;
                    for r in regions {
                        self.block(r, &operands[1..], &results, seen, function, depth + 1)?;
                    }
                }
                Match {
                    alternatives,
                    regions,
                    ..
                } => {
                    require(
                        !operands.is_empty()
                            && operands[0].kind == SchemaKind::Variant
                            && alternatives.len() == regions.len(),
                        "entry-host-match",
                    )?;
                    let s = operands[0];
                    require(
                        alternatives.len() == s.alternatives.len()
                            && alternatives.iter().collect::<BTreeSet<_>>().len()
                                == alternatives.len(),
                        "entry-host-coverage",
                    )?;
                    for (a, r) in alternatives.iter().zip(regions) {
                        let arm = s
                            .alternatives
                            .iter()
                            .find(|arm| arm.name == *a)
                            .ok_or_else(|| error("entry-host-alternative"))?;
                        let mut args = arm.fields.iter().map(|f| &f.schema).collect::<Vec<_>>();
                        args.extend_from_slice(&operands[1..]);
                        self.block(r, &args, &results, seen, function, depth + 1)?;
                    }
                }
                For {
                    carried, regions, ..
                } => {
                    let n = *carried as usize;
                    require(
                        regions.len() == 1
                            && operands.len() >= 2 + n
                            && operands[..2].iter().all(|s| s.kind == SchemaKind::Index),
                        "entry-host-loop",
                    )?;
                    same(&results, &operands[2..2 + n])?;
                    let mut args = vec![operands[0]];
                    args.extend_from_slice(&operands[2..]);
                    self.block(&regions[0], &args, &results, seen, function, depth + 1)?;
                }
                Require { .. } => require(
                    operands.len() == 1
                        && operands[0].kind == SchemaKind::Boolean
                        && results.is_empty(),
                    "entry-host-condition",
                )?,
                Drop { .. } => require(
                    operands.len() == 1
                        && results.is_empty()
                        && operands[0].permissions.contains(&Permission::Drop),
                    "entry-host-drop",
                )?,
            }
            if let Operation::Drop { operands, .. } = op {
                env.remove(&operands[0]);
            }
            for v in op.results() {
                self.define(v, &mut env, seen)?;
            }
        }
        let actual = b
            .returns
            .iter()
            .map(|i| {
                env.get(i)
                    .copied()
                    .ok_or_else(|| error("entry-host-dominance"))
            })
            .collect::<Result<Vec<_>>>()?;
        if matches!(b.operations.last(), Some(Operation::Stop { .. })) {
            Ok(())
        } else {
            same(&actual, returns)
        }
    }
    fn define(
        &mut self,
        v: &'a Definition,
        env: &mut BTreeMap<u32, &'a Schema>,
        seen: &mut BTreeSet<u32>,
    ) -> Result<()> {
        require(seen.insert(v.id), "entry-host-ssa")?;
        check_schema(&v.schema, &mut self.schemas)?;
        env.insert(v.id, &v.schema);
        Ok(())
    }
}

/// Inspect static invocation requirements without importing setup authority.
/// Native code admission remains FunctionEntry::admit's separate obligation.
pub(super) fn interfaces(package: &Package) -> Result<Vec<super::DeploymentInterface>> {
    let interface = FunctionInterface::read(package)?;
    let document: Document = decode(package.artifact().as_bytes(), 16 * 1024 * 1024)?;
    let mut validator = structure(&document, &interface)?;
    let mut families = BTreeMap::new();
    let mut result = Vec::new();
    for c in &document.calculations {
        for s in c.parameters.iter().chain(&c.results) {
            check_schema(s, &mut validator.schemas)?;
        }
    }
    for d in &document.deployments {
        for s in d.parameters.iter().chain(&d.results) {
            check_schema(s, &mut validator.schemas)?;
        }
        let pin = Sha256::digest(d.package.as_bytes()).into();
        let child = Package::capture(d.package.as_bytes(), &pin, Package::MAX_BYTES)?;
        let view = crate::entry::BoundInterface::read(&child)
            .map_err(|e| EntryError::new(EntryPhase::Interface, e))?;
        super::deployment::check_interface(d, &view, &mut families)?;
        result.push(super::DeploymentInterface {
            id: d.id.clone(),
            operation: d.operation.clone(),
            interface: view.into_view(),
            parameters: d.parameters.clone(),
            result: d.results[0].clone(),
        });
    }
    Ok(result)
}
