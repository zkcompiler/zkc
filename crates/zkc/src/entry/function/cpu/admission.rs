use super::super::admission::{check_schema, decode, structure};
use super::super::carrier::*;
use super::*;
use sha2::{Digest, Sha256};
pub(super) fn admit(
    package: &Package,
    options: FunctionOptions,
    mut authority: BTreeMap<String, SetupAuthority>,
    cpu: CpuExecution,
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
    let backend = data::backend(
        options.limits.capacity,
        cpu.clone(),
        options.limits.installation.clone(),
    )
    .map_err(|e| EntryError::new(EntryPhase::Admission, e))?;
    for c in &document.calculations {
        for s in c.parameters.iter().chain(&c.results) {
            check_schema(s, &mut validator.schemas)?;
        }
        let program = Program::decode(
            c.program.as_bytes(),
            options.limits.installation.contracts(),
        )
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
    let assets = crate::entry::EntryAssets::admit_references(package, references)
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
            "run" => super::DeploymentKind::Run(Box::new(crate::entry::RunEntry::admit_host(
                child,
                options.limits.clone(),
                authority.clone(),
                cpu.clone(),
            )?)),
            "prove" | "verify" => {
                let operation = if d.operation == "prove" {
                    crate::entry::ProofOperation::Prove
                } else {
                    crate::entry::ProofOperation::Verify
                };
                super::DeploymentKind::Proof {
                    entry: Box::new(crate::entry::ProofEntry::admit_host_operation(
                        child,
                        crate::entry::ProofOptions {
                            capacity: options.limits.capacity,
                            external_work: options.limits.external_work,
                            binding: options.binding,
                            installation: options.limits.installation.clone(),
                        },
                        authority.clone(),
                        operation,
                        cpu.clone(),
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
    let types = validator
        .schemas
        .finish()
        .into_keys()
        .map(|spelling| {
            LogicalType::parse(&spelling)
                .map(|ty| (spelling, ty))
                .map_err(|e| EntryError::new(EntryPhase::Admission, e))
        })
        .collect::<Result<_>>()?;
    drop(validator.calls);
    Ok(EntryHost {
        cpu,
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
