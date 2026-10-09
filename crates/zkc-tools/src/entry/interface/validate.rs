use super::{
    InterfaceError as E, Result, hash, identifier, raw::*, require, schemas::Schemas, text,
};
use std::collections::{BTreeMap, BTreeSet};
use zkc_runtime::interactive::{LogicalType, ServiceContract, Type};

pub(super) struct Checked {
    pub selected: usize,
    pub types: BTreeMap<String, LogicalType>,
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
                input.schema.permissions.contains(&Permission::Copy)
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
                        && schemas.setup_properties(&input.schema.leaves[0])?.0 == Type::Vector;
                    require(input.native.len() == 1 && (scalar || vector), E::Schema)?;
                }
            }
        }
    }
    let mut symbols = BTreeSet::new();
    let mut selected = None;
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
            ServiceContract::parse(&service.contract).map_err(|_| E::Schema)?;
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
                check_decision(protocol, decision, &decision.role)?;
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
    require(
        native.len() == schema.leaves.len()
            && native
                .iter()
                .enumerate()
                .all(|(i, n)| *n as usize == *flat + i),
        E::Schema,
    )?;
    schemas.check(schema, 1)?;
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
        schemas.charge(1 + port.name.len() + port.display_type.len() + port.roles.len())?;
        require(
            identifier(&port.name)
                && names.insert(&port.name)
                && port.index as usize == index
                && port.display_type == port.schema.display_type
                && !port.roles.is_empty(),
            E::Schema,
        )?;
        let mut previous = None;
        for role in &port.roles {
            let index = *roles.get(role).ok_or(E::Schema)?;
            require(previous.is_none_or(|p| p < index), E::Schema)?;
            previous = Some(index);
        }
        if port.roles.len() > 1 {
            require(
                [Permission::Copy, Permission::Drop, Permission::Share]
                    .iter()
                    .all(|p| port.schema.permissions.contains(p)),
                E::Schema,
            )?;
        }
        schema_port(&port.schema, &port.native, &mut flat, schemas)?;
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
    require(port.roles.contains(&selector.role), E::Selection)?;
    project(port, &selector.path)
}
pub(super) fn project<'a>(port: &'a Port, path: &[u32]) -> Result<(&'a Schema, &'a [u32])> {
    let mut schema = &port.schema;
    let mut offset = 0usize;
    require(path.len() <= 32, E::Limit)?;
    for &index in path {
        require(
            !schema.custody && !matches!(schema.kind, Kind::Variant | Kind::Associated),
            E::Selection,
        )?;
        let field = schema.fields.get(index as usize).ok_or(E::Selection)?;
        offset = offset.checked_add(field.offset as usize).ok_or(E::Limit)?;
        schema = &field.schema;
    }
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
            && selected.role == role
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
    let required: Vec<_> = protocol
        .inputs
        .iter()
        .filter(|p| p.roles.contains(verifier))
        .map(|p| p.index)
        .collect();
    require(public == &required, E::Selection)?;
    schemas.charge(1 + acceptance.path.len())?;
    check_decision(protocol, acceptance, verifier)?;
    if let Some(completion) = completion {
        schemas.charge(1 + completion.path.len())?;
        check_decision(protocol, completion, prover)?;
    }
    let derived = match construction {
        Construction::Authored {} => None,
        Construction::FiatShamir { suite, service } => {
            let selected = protocol
                .services
                .get(*service as usize)
                .ok_or(E::Selection)?;
            let ty =
                LogicalType::parse(&format!("transcript:{suite}")).map_err(|_| E::Selection)?;
            let contract = ServiceContract::parse(&selected.contract).map_err(|_| E::Selection)?;
            require(
                &selected.owner == verifier
                    && ty.identity().scalar_field() == Some(contract.field()),
                E::Selection,
            )?;
            Some(*service as usize)
        }
    };
    for (index, service) in protocol.services.iter().enumerate() {
        require(
            &service.owner != verifier || Some(index) == derived,
            E::Selection,
        )?;
    }
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
            let visible = protocol.inputs[operand.port as usize]
                .roles
                .contains(verifier);
            require((input.purpose == Purpose::Witness) != visible, E::Selection)?;
        }
    }
    Ok(())
}
