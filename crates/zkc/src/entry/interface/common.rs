//! Validate owner-associated common observations using the existing component map.
#![cfg_attr(not(feature = "cpu"), allow(dead_code))]
use super::{InterfaceError as E, Result, raw::*, require, schemas::Schemas};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug)]
pub(super) struct Requirement {
    pub components: Vec<Component>,
    pub spelling: String,
    pub observation: CommonObservation,
}
#[derive(Debug)]
pub(super) struct Component {
    pub role: u32,
    pub original: u32,
    pub path: Vec<(usize, usize)>,
}

pub(super) fn check(protocol: &Protocol, work: &mut Schemas<'_>) -> Result<Vec<Requirement>> {
    require(protocol.common_input_requirements.len() <= 1024, E::Limit)?;
    // Index once, including zero-width ports in work accounting. Repeated scans
    // per requirement would make wide, mostly empty interfaces quadratic.
    let mut map = BTreeMap::new();
    for (input, port) in protocol.inputs.iter().enumerate() {
        work.charge(1 + port.components.len())?;
        for c in &port.components {
            work.charge(1 + c.path.len())?;
            require(
                map.insert((input as u32, c.path.as_slice(), c.role, c.leaf), c)
                    .is_none(),
                E::Schema,
            )?;
        }
    }
    let mut result = Vec::new();
    let mut seen = BTreeSet::new();
    let mut previous = None;
    let mut count = 0usize;
    for requirement in &protocol.common_input_requirements {
        count = count
            .checked_add(requirement.components.len())
            .ok_or(E::Limit)?;
        require(count <= 32768, E::Limit)?;
        work.charge(1 + requirement.components.len())?;
        let mut components = Vec::new();
        let mut keys = Vec::new();
        let mut roles = BTreeSet::new();
        let mut identity = None;
        let mut spelling = None;
        for c in &requirement.components {
            require(c.path.len() <= 32, E::Limit)?;
            work.charge(1 + c.path.len() + c.role.len())?;
            let role = protocol
                .roles
                .iter()
                .position(|r| r == &c.role)
                .ok_or(E::Selection)? as u32;
            let key = (c.input, c.path.clone(), role);
            require(keys.last().is_none_or(|prior| prior < &key), E::Selection)?;
            roles.insert(role);
            let port = protocol.inputs.get(c.input as usize).ok_or(E::Selection)?;
            let mut schema = &port.schema;
            let mut root = Vec::new();
            let mut path: Vec<(usize, usize)> = Vec::new();
            let mut steps = c.path.iter();
            while let Some(step) = steps.next() {
                // Ancestor custody belongs to separate native components. The
                // endpoint and exact component facet below decide whether this
                // observation selects ordinary data.
                match *step {
                    CommonStep::Field { index } => {
                        require(
                            !matches!(schema.kind, Kind::Variant | Kind::Associated)
                                && !schema.kind.is_handle(),
                            E::Selection,
                        )?;
                        let field = schema.fields.get(index as usize).ok_or(E::Selection)?;
                        if let Some((_, offset)) = path.last_mut() {
                            *offset = offset.checked_add(field.offset as usize).ok_or(E::Limit)?;
                        } else {
                            root.push(index);
                        }
                        schema = &field.schema;
                    }
                    CommonStep::Alternative { index } => {
                        require(
                            schema.kind == Kind::Variant
                                && !schema.is_logical()
                                && schema.leaves.len() == 1,
                            E::Selection,
                        )?;
                        let Some(CommonStep::Payload { index: payload }) = steps.next() else {
                            return Err(E::Selection);
                        };
                        let field = schema
                            .alternatives
                            .get(index as usize)
                            .and_then(|a| a.fields.get(*payload as usize))
                            .ok_or(E::Selection)?;
                        path.push((index as usize, field.offset as usize));
                        schema = &field.schema;
                    }
                    CommonStep::Payload { .. } => return Err(E::Selection),
                }
            }
            require(
                !schema.is_logical()
                    && schema.custody == 0
                    && schema.fields.is_empty()
                    && schema.leaves.len() == 1,
                E::Selection,
            )?;
            let leaf = schema.leaves[0].as_str();
            match requirement.observation {
                CommonObservation::Value {} => {
                    require(schema.permissions.contains(&Permission::Copy), E::Selection)?
                }
                CommonObservation::Tag {} => require(schema.kind == Kind::Variant, E::Selection)?,
                CommonObservation::Extent { axis } => {
                    let head = work.setup_properties(leaf)?.0;
                    let rank = match head {
                        "bytes" | "sequence" | "vector" | "groups" | "indices" | "field_array"
                        | "fixed_vector" => 1,
                        "matrix" => 2,
                        _ => 0,
                    };
                    require(
                        axis < rank && schema.permissions.contains(&Permission::Copy),
                        E::Selection,
                    )?;
                }
            }
            require(
                identity.is_none_or(|id| id == schema.identity.as_str())
                    && spelling.is_none_or(|s| s == leaf),
                E::Selection,
            )?;
            identity = Some(schema.identity.as_str());
            spelling = Some(leaf);
            let mapped = map
                .get(&(c.input, root.as_slice(), role, 0))
                .ok_or(E::Selection)?;
            require(mapped.facet == Facet::Data, E::Selection)?;
            // Shared vertices would mean the serialized classes were not maximal.
            // Keep nominal identity and each observation separate.
            require(
                seen.insert((
                    schema.identity.as_str(),
                    requirement.observation,
                    key.clone(),
                )),
                E::Selection,
            )?;
            keys.push(key);
            components.push(Component {
                role,
                original: mapped.native,
                path,
            });
        }
        require(roles.len() >= 2, E::Selection)?;
        let order = (keys, requirement.observation);
        require(
            previous.as_ref().is_none_or(|prior| prior < &order),
            E::Selection,
        )?;
        previous = Some(order);
        let spelling = spelling.ok_or(E::Selection)?;
        work.charge(1 + spelling.len())?;
        result.push(Requirement {
            components,
            spelling: spelling.to_owned(),
            observation: requirement.observation,
        });
    }
    Ok(result)
}

#[cfg(feature = "cpu")]
impl super::BoundInterface {
    /// Resolve the selected original's inventory against this exact admitted Run.
    /// Package authentication does not independently prove source completeness.
    pub(in crate::entry) fn common_input_requirements(
        &self,
        bundle: &zkc_runtime::host::joint::Bundle,
    ) -> Result<Vec<zkc_runtime::host::input_binding::InputRequirement>> {
        use zkc_runtime::host::input_binding::{InputComponent, InputRequirement, Observation};
        // Callers have authenticated these bundle bytes during Run admission.
        // Recheck its ABI before adapting the actual Program types.
        self.check_run_bundle(bundle, &self.artifact)?;
        let mut positions = BTreeMap::new();
        for role in self.roles() {
            // The same checked ordering used by native_input_position, computed
            // once per role instead of rescanning all ports per component.
            for (position, original) in self.role_native_inputs(role).into_iter().enumerate() {
                positions.insert((role.name.as_str(), original), position);
            }
        }
        let mut result = Vec::new();
        for required in &self.common {
            // Parse once per class. Formatting the actual type once for every
            // component would repeatedly allocate wide variant spellings.
            let logical = zkc_runtime::vm::LogicalType::parse(&required.spelling)
                .map_err(|_| E::NativeBinding)?;
            let mut components = Vec::new();
            let mut physical = None;
            for c in &required.components {
                let role = &self.roles()[c.role as usize];
                let input = *positions
                    .get(&(role.name.as_str(), c.original))
                    .ok_or(E::NativeBinding)?;
                let actual = bundle
                    .roles()
                    .get(c.role as usize)
                    .ok_or(E::NativeBinding)?;
                let mut ty = &actual.entry.inputs.get(input).ok_or(E::NativeBinding)?.1;
                for &(alternative, payload) in &c.path {
                    ty = ty
                        .variant_payload(alternative)
                        .and_then(|p| p.get(payload))
                        .ok_or(E::NativeBinding)?;
                }
                require(
                    ty.logical() == &logical && physical.as_ref().is_none_or(|prior| prior == ty),
                    E::NativeBinding,
                )?;
                physical = Some(ty.clone());
                components.push(InputComponent {
                    role: role.native_name.clone(),
                    input,
                    path: c.path.clone(),
                });
            }
            let observation = match required.observation {
                CommonObservation::Value {} => Observation::Value,
                CommonObservation::Tag {} => Observation::Tag,
                CommonObservation::Extent { axis } => Observation::Extent {
                    axis: axis as usize,
                },
            };
            result.push(InputRequirement {
                components,
                ty: physical.ok_or(E::NativeBinding)?,
                observation,
            });
        }
        Ok(result)
    }
}
