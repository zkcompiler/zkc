//! Reconstruct placements and typed component coverage without trusting the cache.
use super::{
    InterfaceError as E, Result, hash,
    raw::*,
    require,
    schemas::{Schemas, native_width},
};
use std::collections::BTreeSet;

fn set(roles: &[u32], participants: usize) -> Result<()> {
    require(
        !roles.is_empty()
            && roles.iter().all(|&r| (r as usize) < participants)
            && roles.windows(2).all(|p| p[0] < p[1]),
        E::Schema,
    )
}
impl Placement {
    pub(super) fn roles(&self) -> Vec<u32> {
        match self {
            Self::Data { roles } => roles.clone(),
            Self::Oracle { holder, receivers } => {
                let mut roles = receivers.clone();
                roles.push(*holder);
                roles.sort_unstable();
                roles
            }
            Self::Product { arguments, .. } => {
                let mut roles = arguments.clone();
                roles.sort_unstable();
                roles
            }
        }
    }
    pub(in crate::entry) fn describe(&self) -> serde_json::Value {
        use serde_json::json;
        match self {
            Self::Data { roles } => json!({"kind":"data","roles":roles}),
            Self::Oracle { holder, receivers } => {
                json!({"kind":"oracle","holder":holder,"receivers":receivers})
            }
            Self::Product {
                instance,
                arguments,
                fields,
            } => json!({"kind":"product","instance":instance,
                "arguments":arguments,"fields":fields.iter().map(Self::describe).collect::<Vec<_>>()}),
        }
    }
}
fn substitute(
    schema: &Schema,
    p: &Placement,
    mapping: &[u32],
    budget: &mut Schemas<'_>,
) -> Result<Placement> {
    budget.charge(1)?;
    let map = |r: &u32| mapping.get(*r as usize).copied().ok_or(E::Schema);
    let set = |roles: &[u32]| -> Result<Vec<u32>> {
        let mut mapped = roles.iter().map(map).collect::<Result<Vec<_>>>()?;
        mapped.sort_unstable();
        Ok(mapped)
    };
    Ok(match p {
        Placement::Data { roles } => {
            budget.charge(roles.len())?;
            Placement::Data { roles: set(roles)? }
        }
        Placement::Oracle { holder, receivers } => {
            budget.charge(receivers.len())?;
            Placement::Oracle {
                holder: map(holder)?,
                receivers: set(receivers)?,
            }
        }
        Placement::Product {
            instance,
            arguments,
            fields,
        } => {
            budget.charge(instance.len() + arguments.len())?;
            let mut arguments: Vec<_> = arguments.iter().map(map).collect::<Result<_>>()?;
            // Structural applications are sets; nominal applications retain the
            // declaration telescope order under the same substitution.
            if matches!(schema.kind, Kind::Tuple | Kind::Array) {
                arguments.sort_unstable();
            }
            let fields = fields
                .iter()
                .enumerate()
                .map(|(index, field)| {
                    let child = if schema.kind == Kind::Array {
                        schema.element.as_deref().ok_or(E::Schema)?
                    } else {
                        &schema.fields.get(index).ok_or(E::Schema)?.schema
                    };
                    substitute(child, field, mapping, budget)
                })
                .collect::<Result<_>>()?;
            Placement::Product {
                instance: instance.clone(),
                arguments,
                fields,
            }
        }
    })
}
pub(super) fn check(
    schema: &Schema,
    placement: &Placement,
    participants: usize,
    budget: &mut Schemas<'_>,
) -> Result<()> {
    budget.charge(1)?;
    match placement {
        Placement::Data { roles } => {
            budget.charge(roles.len())?;
            set(roles, participants)?;
            require(!schema.is_logical(), E::Schema)?;
            if roles.len() > 1 {
                budget.participants(schema)?;
            }
        }
        Placement::Oracle { holder, receivers } => {
            budget.charge(receivers.len())?;
            set(receivers, participants)?;
            require(
                schema.kind.is_handle()
                    && (*holder as usize) < participants
                    && !receivers.contains(holder),
                E::Schema,
            )?;
        }
        Placement::Product {
            instance,
            arguments,
            fields,
        } => {
            budget.charge(instance.len() + arguments.len() + fields.len())?;
            require(
                matches!(schema.kind, Kind::LogicalRecord | Kind::Tuple | Kind::Array)
                    && hash(instance)
                    && instance == &schema.identity,
                E::Schema,
            )?;
            let unique: BTreeSet<_> = arguments.iter().collect();
            require(
                !arguments.is_empty()
                    && arguments.len() <= participants
                    && unique.len() == arguments.len()
                    && arguments.iter().all(|&r| (r as usize) < participants),
                E::Schema,
            )?;
            if schema.kind == Kind::LogicalRecord && !schema.roles.is_empty() {
                require(
                    arguments.len() == schema.roles.len() && fields.len() == schema.fields.len(),
                    E::Schema,
                )?;
                for (field, actual) in schema.fields.iter().zip(fields) {
                    let expected = substitute(
                        &field.schema,
                        field.placement.as_ref().ok_or(E::Schema)?,
                        arguments,
                        budget,
                    )?;
                    require(&expected == actual, E::Schema)?;
                    check(&field.schema, actual, participants, budget)?;
                }
            } else {
                let children: Vec<_> = if schema.kind == Kind::Array {
                    vec![schema.element.as_deref().ok_or(E::Schema)?]
                } else {
                    schema.fields.iter().map(|f| &f.schema).collect()
                };
                require(children.len() == fields.len(), E::Schema)?;
                let mut union = BTreeSet::new();
                for (child, actual) in children.into_iter().zip(fields) {
                    check(child, actual, participants, budget)?;
                    union.extend(actual.roles());
                }
                require(arguments.iter().copied().eq(union), E::Schema)?;
                if schema.kind == Kind::LogicalRecord {
                    let mut family = None;
                    for (field, actual) in schema.fields.iter().zip(fields) {
                        budget.charge(1 + arguments.len())?;
                        if field.schema.kind.is_handle() {
                            let Placement::Oracle { holder, receivers } = actual else {
                                return Err(E::Schema);
                            };
                            let current = (*holder, receivers);
                            require(family.is_none_or(|previous| previous == current), E::Schema)?;
                            family = Some(current);
                        } else {
                            let Placement::Data { roles } = actual else {
                                return Err(E::Schema);
                            };
                            require(roles == arguments, E::Schema)?;
                        }
                    }
                    let (holder, receivers) = family.ok_or(E::Schema)?;
                    let mut roles = receivers.clone();
                    roles.push(holder);
                    roles.sort_unstable();
                    require(&roles == arguments, E::Schema)?;
                }
            }
        }
    }
    Ok(())
}

/// Derive the exact native map in field/body/participant order. Native coordinates
/// may repeat across participants; typed component coordinates may never repeat.
pub(super) fn components(port: &Port, budget: &mut Schemas<'_>) -> Result<Vec<Component>> {
    let mut result = Vec::new();
    visit(
        &port.schema,
        &port.placement,
        &mut Vec::new(),
        0,
        &mut result,
        budget,
    )?;
    for component in &mut result {
        component.native = *port
            .native
            .get(component.native as usize)
            .ok_or(E::Schema)?;
    }
    Ok(result)
}
fn visit(
    s: &Schema,
    p: &Placement,
    path: &mut Vec<u32>,
    base: usize,
    result: &mut Vec<Component>,
    budget: &mut Schemas<'_>,
) -> Result<()> {
    budget.charge(1 + path.len())?;
    let mut append = |leaf, role, facet, native| -> Result<()> {
        budget.charge(1 + path.len())?;
        require(result.len() < 1024 * 1024, E::Limit)?;
        result.push(Component {
            path: path.clone(),
            leaf,
            role,
            facet,
            native: native as u32,
        });
        Ok(())
    };
    match p {
        Placement::Oracle { holder, .. } => {
            // Components are participant ordered within each body leaf; ABI
            // coordinates still put holder data before receiver anchors.
            let roles = p.roles();
            for role in roles {
                if role == *holder {
                    append(0, role, Facet::OracleData, base)?;
                } else {
                    append(0, role, Facet::OracleAnchor, base + 1)?;
                }
            }
        }
        Placement::Data { roles } => {
            for leaf in 0..s.custody {
                for &role in roles {
                    append(leaf, role, Facet::Custody, base + leaf as usize)?;
                }
            }
            if s.fields.is_empty() {
                for leaf in s.custody as usize..s.leaves.len() {
                    for &role in roles {
                        append(leaf as u32, role, Facet::Data, base + leaf)?;
                    }
                }
            } else {
                for (i, field) in s.fields.iter().enumerate() {
                    path.push(i as u32);
                    visit(
                        &field.schema,
                        p,
                        path,
                        base + field.offset as usize,
                        result,
                        budget,
                    )?;
                    path.pop();
                }
            }
        }
        Placement::Product {
            arguments, fields, ..
        } => {
            for leaf in 0..s.custody {
                append(
                    leaf,
                    arguments[leaf as usize],
                    Facet::Custody,
                    base + leaf as usize,
                )?;
            }
            let mut next = base + s.custody as usize;
            for (i, field) in s.fields.iter().enumerate() {
                path.push(i as u32);
                visit(
                    &field.schema,
                    &fields[if s.kind == Kind::Array { 0 } else { i }],
                    path,
                    next,
                    result,
                    budget,
                )?;
                path.pop();
                next += native_width(&field.schema);
            }
        }
    }
    Ok(())
}

/// Resolve a component's terminal spelling. Custody and anchors remain unavailable
/// to ordinary ingress, even if their physical representation could be decoded.
pub(super) fn component_type<'a>(port: &'a Port, c: &Component) -> Result<&'a str> {
    let mut s = &port.schema;
    for &step in &c.path {
        s = &s.fields.get(step as usize).ok_or(E::Schema)?.schema;
    }
    require(
        matches!(c.facet, Facet::Data | Facet::Custody),
        E::Selection,
    )?;
    s.leaves
        .get(c.leaf as usize)
        .map(String::as_str)
        .ok_or(E::Schema)
}

/// Roles that can supply every component of an ordinary structural subtree.
/// Intersect child authority (including zero-array templates); never use a union.
/// The result is strictly increasing, like the data placements it intersects.
pub(super) fn ordinary_roles(schema: &Schema, placement: &Placement) -> Option<Vec<u32>> {
    if schema.is_logical() {
        return None;
    }
    match placement {
        Placement::Data { roles } => Some(roles.clone()),
        Placement::Product { fields, .. } => {
            let mut roles: Option<Vec<u32>> = None;
            for (i, p) in fields.iter().enumerate() {
                let child = if schema.kind == Kind::Array {
                    schema.element.as_deref()?
                } else {
                    &schema.fields.get(i)?.schema
                };
                let next = ordinary_roles(child, p)?;
                roles = Some(match roles {
                    Some(previous) => previous
                        .into_iter()
                        .filter(|r| next.binary_search(r).is_ok())
                        .collect(),
                    None => next,
                });
            }
            roles
        }
        _ => None,
    }
}
