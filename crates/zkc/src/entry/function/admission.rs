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
fn check_schema<'a>(s: &'a Schema, schemas: &mut Schemas<'a>) -> Result<()> {
    schemas
        .check(s, 0)
        .map_err(|e| EntryError::new(EntryPhase::Interface, e))?;
    crate::entry::value::check_export(s).map_err(|e| EntryError::new(EntryPhase::Admission, e))
}
pub(super) fn admit(
    package: &Package,
    options: FunctionOptions,
    mut authority: BTreeMap<String, SetupAuthority>,
) -> Result<EntryHost> {
    options
        .limits
        .validate()
        .map_err(|e| EntryError::new(EntryPhase::Admission, e))?;
    require(options.journal_events <= 4096, "entry-host-journal-limit")?;
    let interface = FunctionInterface::read(package)?;
    let document: Document = decode(package.artifact().as_bytes(), 16 * 1024 * 1024)?;
    let mut validator = structure(&document, &interface)?;
    let mut native_calculations = BTreeMap::new();
    let mut references = Vec::new();
    let backend = data::backend(options.limits.capacity)
        .map_err(|e| EntryError::new(EntryPhase::Admission, e))?;
    for c in &document.calculations {
        for s in c.parameters.iter().chain(&c.results) {
            check_schema(s, &mut validator.schemas)?;
        }
        let program = Program::decode(c.program.as_bytes(), zkc_native::native_contracts())
            .map_err(|e| EntryError::new(EntryPhase::Admission, e))?;
        require(
            program.entry_names().next().is_none(),
            "entry-host-numeric-stage",
        )?;
        let local = program
            .local_function(&c.function)
            .ok_or_else(|| error("entry-host-numeric-root"))?;
        require(
            local
                .inputs
                .iter()
                .map(|(_, t)| t.logical().spelling())
                .eq(c
                    .parameters
                    .iter()
                    .flat_map(|s| s.leaves.iter().map(String::as_str)))
                && local.outputs.iter().map(|t| t.logical().spelling()).eq(c
                    .results
                    .iter()
                    .flat_map(|s| s.leaves.iter().map(String::as_str))),
            "entry-host-numeric-signature",
        )?;
        require(
            local.inputs.iter().all(|(_, t)| t.is_duplicable())
                && local.outputs.iter().all(|t| t.is_duplicable()),
            "entry-host-numeric-custody",
        )?;
        require(
            local
                .inputs
                .iter()
                .map(|(_, t)| t)
                .chain(&local.outputs)
                .all(|t| {
                    zkc_runtime::vm::PhysicalType::default_for(t.logical().clone())
                        .as_ref()
                        .ok()
                        == Some(t)
                }),
            "entry-host-numeric-representation",
        )?;
        program
            .check_local_installation(&c.function, &backend)
            .map_err(|e| EntryError::new(EntryPhase::Admission, e))?;
        references.extend(
            program
                .local_asset_references(&c.function)
                .map_err(|e| EntryError::new(EntryPhase::Assets, e))?,
        );
        native_calculations.insert(
            c.id.clone(),
            super::Calculation {
                function: c.function.clone(),
                results: c.results.clone(),
                program,
            },
        );
    }
    let assets = super::super::EntryAssets::admit_references(package, references)
        .map_err(|e| EntryError::new(EntryPhase::Assets, e))?;
    require(
        authority.len() == document.deployments.len(),
        "entry-host-authority",
    )?;
    let mut native_deployments = BTreeMap::new();
    let mut families = BTreeMap::new();
    for d in &document.deployments {
        for s in d.parameters.iter().chain(&d.results) {
            check_schema(s, &mut validator.schemas)?;
        }
        let pin: [u8; 32] = Sha256::digest(d.package.as_bytes()).into();
        let child = Package::capture(d.package.as_bytes(), &pin, Package::MAX_BYTES)?;
        let authority = authority
            .remove(&d.id)
            .ok_or_else(|| error("entry-host-authority"))?;
        let native = match d.operation.as_str() {
            "run" => super::DeploymentKind::Run(Box::new(super::super::RunEntry::admit_host(
                child,
                options.limits,
                authority.clone(),
            )?)),
            "prove" | "verify" => {
                let operation = if d.operation == "prove" {
                    super::super::ProofOperation::Prove
                } else {
                    super::super::ProofOperation::Verify
                };
                super::DeploymentKind::Proof {
                    entry: Box::new(super::super::ProofEntry::admit_host_operation(
                        child,
                        super::super::ProofOptions {
                            capacity: options.limits.capacity,
                            external_work: options.limits.external_work,
                            binding: options.binding,
                        },
                        authority.clone(),
                        operation,
                    )?),
                    operation,
                }
            }
            _ => return Err(error("entry-host-stage")),
        };
        deployment::check(d, &native, &mut families)?;
        native_deployments.insert(
            d.id.clone(),
            super::Deployment {
                result: d.results[0].clone(),
                authority,
                kind: native,
            },
        );
    }
    let mut schema_pool = BTreeMap::new();
    fn intern(s: &Schema, pool: &mut BTreeMap<String, std::sync::Arc<Schema>>) {
        if pool.contains_key(&s.identity) {
            return;
        }
        for f in &s.fields {
            intern(&f.schema, pool);
        }
        for f in s.alternatives.iter().flat_map(|a| &a.fields) {
            intern(&f.schema, pool);
        }
        pool.insert(s.identity.clone(), std::sync::Arc::new(s.clone()));
    }
    fn block_schemas(b: &Block, pool: &mut BTreeMap<String, std::sync::Arc<Schema>>) {
        for v in &b.arguments {
            intern(&v.schema, pool);
        }
        for op in &b.operations {
            for v in op.results() {
                intern(&v.schema, pool);
            }
            match op {
                Operation::If { regions, .. }
                | Operation::Match { regions, .. }
                | Operation::For { regions, .. } => {
                    for b in regions {
                        block_schemas(b, pool);
                    }
                }
                _ => {}
            }
        }
    }
    for f in &document.functions {
        for p in &f.signature.parameters {
            intern(&p.schema, &mut schema_pool);
        }
        intern(&f.signature.result, &mut schema_pool);
        block_schemas(&f.body, &mut schema_pool);
    }
    for s in document
        .calculations
        .iter()
        .flat_map(|c| c.parameters.iter().chain(&c.results))
        .chain(
            document
                .deployments
                .iter()
                .flat_map(|d| d.parameters.iter().chain(&d.results)),
        )
    {
        intern(s, &mut schema_pool);
    }
    let types = validator.schemas.finish();
    drop(validator.calls);
    Ok(EntryHost {
        entry: document.entry,
        functions: document.functions,
        interface,
        types,
        schemas: schema_pool,
        calculations: native_calculations,
        deployments: native_deployments,
        options,
        assets,
    })
}
fn structure<'a>(
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
struct Validator<'a> {
    document: &'a Document,
    schemas: Schemas<'a>,
    operations: usize,
    calls: BTreeMap<&'a str, BTreeSet<&'a str>>,
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
        deployment::check_interface(d, &view, &mut families)?;
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
