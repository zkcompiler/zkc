use super::syntax::{Leaf, block_transcript, service_field, transcript_field};
use super::{
    InterfaceError as E, Result, hash, identifier, raw::*, require, schemas::Schemas, text,
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) struct Checked {
    pub selected: usize,
    pub common: Vec<super::common::Requirement>,
    pub types: BTreeMap<String, Leaf>,
    pub setups: Vec<super::Setup>,
}
pub(super) fn check(document: &Interface, original: &str) -> Result<Checked> {
    require(document.format == "zkc.language-interface/0", E::Format)?;
    require(
        hash(&document.capture) && document.original == original,
        E::Identity,
    )?;
    text(&document.toolchain, 256 * 1024)?;
    text(&document.protocol, 4096)?;
    let (module, _) = document.entry.rsplit_once("::").ok_or(E::Identity)?;
    require(
        module.len() <= 2048 && document.entry.split("::").all(identifier),
        E::Identity,
    )?;
    let mut schemas = Schemas::new();
    let mut relations = BTreeMap::new();
    for relation in &document.relations {
        schemas.charge(1 + relation.symbol.len())?;
        text(&relation.symbol, 4096)?;
        require(
            matches!(relation.definition, Definition::Opaque {})
                || relation.static_arguments.is_empty(),
            E::Schema,
        )?;
        require(
            relations
                .insert(relation.symbol.as_str(), relation)
                .is_none(),
            E::Schema,
        )?;
        let mut names = BTreeSet::new();
        let mut flat = 0;
        for input in &relation.inputs {
            schemas.charge(1 + input.name.len())?;
            require(
                identifier(&input.name) && names.insert(&input.name) && !input.native.is_empty(),
                E::Schema,
            )?;
            schema_port(&input.schema, &input.native, &mut flat, &mut schemas)?;
            require(
                !input.schema.is_logical()
                    && input.schema.permissions.contains(&Permission::Copy)
                    && input.schema.permissions.contains(&Permission::Drop),
                E::Schema,
            )?;
        }
        match &relation.definition {
            Definition::Formula { function } => text(function, 4096)?,
            Definition::Opaque {} => (),
            Definition::R1cs { asset } | Definition::Air { asset } => {
                require(
                    hash(asset)
                        && relation.inputs.len() == 2
                        && relation.inputs[0].purpose == Purpose::Statement
                        && relation.inputs[1].purpose == Purpose::Witness
                        && relation
                            .inputs
                            .iter()
                            .all(|p| p.schema.kind == Kind::Builtin && p.native.len() == 1),
                    E::Schema,
                )?;
            }
            // The Host does not hold the bundle, so only the shape every
            // derived formal has is checked: one native leaf that is a field,
            // Boolean, index or vector. Exact derivation is the compiler's.
            Definition::Bundle { asset } => {
                require(hash(asset), E::Schema)?;
                for input in &relation.inputs {
                    let scalar =
                        matches!(input.schema.kind, Kind::Boolean | Kind::Index | Kind::Field);
                    let vector = input.schema.kind == Kind::Builtin
                        && schemas.setup_properties(&input.schema.leaves[0])?.0 == "vector";
                    require(input.native.len() == 1 && (scalar || vector), E::Schema)?;
                }
            }
        }
    }
    let mut symbols = BTreeSet::new();
    let mut selected = None;
    let mut common = Vec::new();
    for (index, protocol) in document.protocols.iter().enumerate() {
        schemas.charge(1 + protocol.symbol.len())?;
        text(&protocol.symbol, 4096)?;
        require(symbols.insert(&protocol.symbol), E::Schema)?;
        if protocol.symbol == document.protocol {
            selected = Some(index);
        }
        let mut roles = BTreeMap::new();
        require(
            !protocol.roles.is_empty() && protocol.roles.len() <= 1024,
            E::Schema,
        )?;
        for (index, role) in protocol.roles.iter().enumerate() {
            schemas.charge(1 + role.len())?;
            require(
                identifier(role) && roles.insert(role, index).is_none(),
                E::Schema,
            )?;
        }
        let input_count = ports(&protocol.inputs, &roles, &mut schemas)?;
        ports(&protocol.outputs, &roles, &mut schemas)?;
        let local = super::common::check(protocol, &mut schemas)?;
        if protocol.symbol == document.protocol {
            common = local;
        }
        let mut names: BTreeSet<_> = protocol.inputs.iter().map(|p| &p.name).collect();
        for (index, service) in protocol.services.iter().enumerate() {
            schemas
                .charge(1 + service.name.len() + service.contract.len() + service.owner.len())?;
            require(
                identifier(&service.name)
                    && names.insert(&service.name)
                    && roles.contains_key(&service.owner)
                    && service.native as usize == input_count + index,
                E::Schema,
            )?;
            service_field(&service.contract).ok_or(E::Schema)?;
        }
        let mut names = BTreeSet::new();
        for clause in &protocol.clauses {
            schemas.charge(1 + clause.name.len())?;
            require(
                identifier(&clause.name) && names.insert(&clause.name),
                E::Schema,
            )?;
            application(protocol, &clause.subject, &relations, &mut schemas)?;
            let output =
                |a: &Application| a.operands.iter().any(|s| s.direction == Direction::Output);
            require(
                match clause.kind {
                    ClauseKind::Input | ClauseKind::Continuation => !output(&clause.subject),
                    ClauseKind::Output => output(&clause.subject),
                    ClauseKind::Target => true,
                },
                E::Selection,
            )?;
            match (&clause.residual, clause.kind) {
                (Some(residual), ClauseKind::Continuation) => {
                    application(protocol, residual, &relations, &mut schemas)?;
                    require(output(residual), E::Selection)?;
                }
                (None, kind) if kind != ClauseKind::Continuation => (),
                _ => return Err(E::Selection),
            }
            if let Some(decision) = &clause.decision {
                require(clause.kind != ClauseKind::Input, E::Selection)?;
                schemas.charge(1 + decision.path.len())?;
                check_decision(
                    protocol,
                    decision,
                    decision.role.as_deref().ok_or(E::Selection)?,
                )?;
            } else {
                require(clause.kind != ClauseKind::Target, E::Selection)?;
            }
        }
    }
    let selected = selected.ok_or(E::Selection)?;
    job(
        &document.job,
        &document.protocols[selected],
        &relations,
        &mut schemas,
    )?;
    let setups = super::setups::check(document, &document.protocols[selected], &mut schemas)?;
    Ok(Checked {
        common,
        selected,
        types: schemas.finish(),
        setups,
    })
}
fn schema_port<'a>(
    schema: &'a Schema,
    native: &[u32],
    flat: &mut usize,
    schemas: &mut Schemas<'a>,
) -> Result<()> {
    schemas.charge(1 + native.len())?;
    schemas.check(schema, 1)?;
    let width = super::schemas::native_width(schema);
    require(width <= 1024, E::Limit)?;
    require(
        native.len() == width
            && native
                .iter()
                .enumerate()
                .all(|(i, n)| *n as usize == *flat + i),
        E::Schema,
    )?;
    *flat += native.len();
    Ok(())
}
fn ports<'a>(
    ports: &'a [Port],
    roles: &BTreeMap<&String, usize>,
    schemas: &mut Schemas<'a>,
) -> Result<usize> {
    let mut names = BTreeSet::new();
    let mut flat = 0;
    for (index, port) in ports.iter().enumerate() {
        schemas.charge(1 + port.name.len() + port.display_type.len())?;
        require(
            identifier(&port.name)
                && names.insert(&port.name)
                && port.index as usize == index
                && port.display_type == port.schema.display_type,
            E::Schema,
        )?;
        schema_port(&port.schema, &port.native, &mut flat, schemas)?;
        require(
            port.maximum_rows.get().is_some() == port.schema.kind.is_handle(),
            E::Schema,
        )?;
        if port.schema.kind.is_handle() {
            super::schemas::row_bound(&port.schema, port.maximum_rows.get().copied().flatten())?;
        }
        super::placement::check(&port.schema, &port.placement, roles.len(), schemas)?;
        let derived = super::placement::components(port, schemas)?;
        schemas.charge(port.components.len())?;
        require(port.components == derived, E::Schema)?;
    }
    Ok(flat)
}
pub(super) fn select<'a>(
    protocol: &'a Protocol,
    selector: &Selector,
) -> Result<(&'a Schema, &'a [u32])> {
    let ports = if selector.direction == Direction::Input {
        &protocol.inputs
    } else {
        &protocol.outputs
    };
    let port = ports.get(selector.port as usize).ok_or(E::Selection)?;
    let role = selector
        .role
        .as_ref()
        .map(|role| {
            protocol
                .roles
                .iter()
                .position(|r| r == role)
                .map(|r| r as u32)
                .ok_or(E::Selection)
        })
        .transpose()?;
    project_selector(
        port,
        &selector.path,
        role,
        selector.role.is_none(),
        super::SelectionPurpose::SpecificationObservation,
    )
}
pub(super) fn project<'a>(port: &'a Port, path: &[u32]) -> Result<(&'a Schema, &'a [u32])> {
    project_selector(
        port,
        path,
        None,
        false,
        super::SelectionPurpose::SetupAssociation,
    )
}
pub(super) fn project_role<'a>(
    port: &'a Port,
    path: &[u32],
    role: u32,
) -> Result<(&'a Schema, &'a [u32])> {
    project_selector(
        port,
        path,
        Some(role),
        false,
        super::SelectionPurpose::OrdinarySupply,
    )
}
/// Resolve semantic selection authority without traversing physical prefixes.
pub(super) fn selected_schema<'a>(
    port: &'a Port,
    path: &[u32],
    purpose: super::SelectionPurpose,
) -> Result<(&'a Schema, &'a Placement)> {
    let specification = purpose == super::SelectionPurpose::SpecificationObservation;
    let mut schema = &port.schema;
    let mut placement = &port.placement;
    require(path.len() <= 32, E::Limit)?;
    for &index in path {
        require(
            (schema.custody == 0 || specification && !schema.is_logical())
                && (specification
                    || !schema.sealed && (schema.is_logical() || schema.constructible))
                && !matches!(schema.kind, Kind::Variant | Kind::Associated),
            E::Selection,
        )?;
        let field = schema.fields.get(index as usize).ok_or(E::Selection)?;
        require(specification || field.public, E::Selection)?;
        if let Placement::Product { fields, .. } = placement {
            placement = fields
                .get(if schema.kind == Kind::Array {
                    0
                } else {
                    index as usize
                })
                .ok_or(E::Selection)?;
        }
        schema = &field.schema;
    }
    Ok((schema, placement))
}
fn project_selector<'a>(
    port: &'a Port,
    path: &[u32],
    role: Option<u32>,
    anchor: bool,
    purpose: super::SelectionPurpose,
) -> Result<(&'a Schema, &'a [u32])> {
    let specification = purpose == super::SelectionPurpose::SpecificationObservation;
    let (schema, placement) = selected_schema(port, path, purpose)?;
    let mut current = &port.schema;
    let mut offset = 0usize;
    for &index in path {
        let field = &current.fields[index as usize];
        let prefix = if current.is_logical() {
            current.custody as usize
                + current.fields[..index as usize]
                    .iter()
                    .map(|f| super::schemas::native_width(&f.schema))
                    .sum::<usize>()
        } else {
            field.offset as usize
        };
        offset = offset.checked_add(prefix).ok_or(E::Limit)?;
        current = &field.schema;
    }
    if anchor {
        require(
            matches!(placement, Placement::Oracle { .. }) && schema.kind == Kind::Oracle,
            E::Selection,
        )?;
        let native = port
            .native
            .get(offset + 1..offset + 2)
            .ok_or(E::Selection)?;
        return Ok((schema.data_schema.get().ok_or(E::Selection)?, native));
    }
    if purpose == super::SelectionPurpose::SetupAssociation {
        require(
            !schema.sealed && schema.custody == 0 && !schema.kind.is_handle(),
            E::Selection,
        )?;
        return Ok((
            schema,
            &port.native[offset..offset + super::schemas::native_width(schema)],
        ));
    }
    require(
        !schema.is_logical() && (specification || !schema.sealed),
        E::Selection,
    )?;
    let roles = super::placement::ordinary_roles(schema, placement).ok_or(E::Selection)?;
    require(role.is_none_or(|r| roles.contains(&r)), E::Selection)?;
    let native = port
        .native
        .get(offset..offset + schema.leaves.len())
        .ok_or(E::Selection)?;
    Ok((schema, native))
}
fn application(
    protocol: &Protocol,
    application: &Application,
    relations: &BTreeMap<&str, &Relation>,
    schemas: &mut Schemas<'_>,
) -> Result<()> {
    schemas.charge(1 + application.relation.len() + application.operands.len())?;
    let relation = relations
        .get(application.relation.as_str())
        .ok_or(E::Selection)?;
    require(
        application.operands.len() == relation.inputs.len(),
        E::Selection,
    )?;
    for (operand, input) in application.operands.iter().zip(&relation.inputs) {
        schemas.charge(1 + operand.path.len())?;
        let (schema, _) = select(protocol, operand)?;
        require(schema.identity == input.schema.identity, E::Selection)?;
    }
    Ok(())
}
fn check_decision(protocol: &Protocol, selected: &Selector, role: &str) -> Result<()> {
    let (schema, native) = select(protocol, selected)?;
    require(
        selected.direction == Direction::Output
            && selected.role.as_deref() == Some(role)
            && schema.kind == Kind::Boolean
            && native.len() == 1,
        E::Selection,
    )
}
fn job(
    job: &Job,
    protocol: &Protocol,
    relations: &BTreeMap<&str, &Relation>,
    schemas: &mut Schemas<'_>,
) -> Result<()> {
    let Job::Proof {
        prover,
        verifier,
        public,
        acceptance,
        completion,
        target,
        construction,
        gates,
    } = job
    else {
        return Ok(());
    };
    schemas.charge(1 + protocol.inputs.len() + protocol.services.len() + protocol.clauses.len())?;
    require(
        protocol.roles.len() == 2
            && prover != verifier
            && protocol.roles.contains(prover)
            && protocol.roles.contains(verifier),
        E::Selection,
    )?;
    super::boundary::check_public(protocol, public, verifier, schemas)?;
    schemas.charge(1 + acceptance.path.len())?;
    check_decision(protocol, acceptance, verifier)?;
    if let Some(completion) = completion {
        schemas.charge(1 + completion.path.len())?;
        check_decision(protocol, completion, prover)?;
    }
    schemas.charge(gates.len())?;
    require(gates.len() <= 64, E::Selection)?;
    let mut selected_gates = BTreeSet::new();
    for gate in gates {
        require(
            !gate.path.is_empty() && gate.path.len() <= 64 && gate.bits <= 64,
            E::Selection,
        )?;
        let mut bytes = 0;
        for part in &gate.path {
            schemas.charge(part.len() + 1)?;
            bytes += part.len() + 1;
            require(
                crate::source_names::is_source_identifier(part) && bytes <= 4096,
                E::Selection,
            )?;
        }
        require(selected_gates.insert(&gate.path), E::Selection)?;
    }
    if !gates.is_empty() {
        let Construction::FiatShamir { suite, .. } = construction.as_ref() else {
            return Err(E::Selection);
        };
        require(block_transcript(suite), E::Selection)?;
    }
    match construction.as_ref() {
        Construction::Authored { .. } => (),
        Construction::Derived {
            symbol,
            suite,
            services,
            ..
        } => {
            schemas.charge(symbol.len() + suite.as_ref().map_or(0, String::len))?;
            require(!symbol.is_empty() && symbol.len() <= 4096, E::Selection)?;
            require(!services.is_empty(), E::Selection)?;
            require(
                services.windows(2).all(|pair| pair[0] < pair[1]),
                E::Selection,
            )?;
            schemas.charge(services.len())?;
            for &service in services {
                let selected = protocol
                    .services
                    .get(service as usize)
                    .ok_or(E::Selection)?;
                require(&selected.owner == verifier, E::Selection)?;
            }
            if let Some(suite) = suite {
                transcript_field(suite).ok_or(E::Selection)?;
            }
        }
        Construction::FiatShamir {
            suite,
            services,
            format,
        } => {
            require(
                *format == zkc_format::proof::ProofFormat::Native && services.len() == 1,
                E::Selection,
            )?;
            let selected = protocol
                .services
                .get(services[0] as usize)
                .ok_or(E::Selection)?;
            let ty = transcript_field(suite).ok_or(E::Selection)?;
            let contract = service_field(&selected.contract).ok_or(E::Selection)?;
            require(&selected.owner == verifier && ty == contract, E::Selection)?;
        }
    };
    if let Some(target) = target {
        let clause = protocol
            .clauses
            .iter()
            .find(|c| c.name == *target)
            .ok_or(E::Selection)?;
        require(
            clause.kind == ClauseKind::Target
                && clause.decision.as_ref().is_some_and(|s| {
                    s.direction == acceptance.direction
                        && s.port == acceptance.port
                        && s.role == acceptance.role
                        && s.path == acceptance.path
                }),
            E::Selection,
        )?;
        let relation = relations[clause.subject.relation.as_str()];
        for (operand, input) in clause.subject.operands.iter().zip(&relation.inputs) {
            require(operand.direction == Direction::Input, E::Selection)?;
            let port = &protocol.inputs[operand.port as usize];
            let verifier_role = protocol
                .roles
                .iter()
                .position(|r| r == verifier)
                .ok_or(E::Selection)? as u32;
            let (selected, placed) = selected_schema(
                port,
                &operand.path,
                super::SelectionPurpose::SpecificationObservation,
            )?;
            let visible = if operand.role.is_none() {
                matches!(placed, Placement::Oracle { holder, .. } if *holder == verifier_role)
            } else {
                super::placement::ordinary_roles(selected, placed)
                    .is_some_and(|roles| roles.contains(&verifier_role))
            };
            require((input.purpose == Purpose::Witness) != visible, E::Selection)?;
        }
    }
    Ok(())
}

pub(super) fn public_data(schema: &Schema, work: &mut Schemas<'_>) -> Result<()> {
    work.charge(1 + schema.fields.len() + schema.alternatives.len())?;
    require(
        !schema.is_logical() && !schema.sealed && schema.custody == 0,
        E::Selection,
    )?;
    for field in schema
        .fields
        .iter()
        .chain(schema.alternatives.iter().flat_map(|a| &a.fields))
    {
        work.charge(1)?;
        require(field.public, E::Selection)?;
        public_data(&field.schema, work)?;
    }
    if let Some(element) = &schema.element {
        public_data(element, work)?;
    }
    Ok(())
}
