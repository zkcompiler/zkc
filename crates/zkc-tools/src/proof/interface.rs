//! Deployment policy and original source-port correspondence. These checks bind
//! the Host interface to independently admitted participant signatures; they do
//! not establish source/compiler correspondence or grant setup authority.
use super::{Port, RoleMap, index, input_kind, wire_codec, wire_type};
use crate::host::inputs::{Result, array, list, text};
use serde_json::Value as Json;
use std::collections::BTreeMap;
use zkc_runtime::interactive::{Admitted, LogicalType, PhysicalType, Type};

/// Borrowed policy fields after syntactic checks. Public selection is checked
/// later against the actual validator inputs, after message and role checks.
pub(super) struct DeploymentPolicy<'a> {
    pub(super) entry: &'a str,
    pub(super) producer: &'a str,
    pub(super) validator: &'a str,
    pub(super) original_acceptance: usize,
    pub(super) suite: Option<&'a str>,
    public_selection: &'a Json,
    pub(super) draw_count: usize,
}
impl<'a> DeploymentPolicy<'a> {
    pub(super) fn read(value: &'a Json) -> Result<Self> {
        let policy = array(value, 9)?;
        if text(&policy[0])? != "zkc.native-proof-policy/4" {
            return Err("native-proof-policy".into());
        }
        let (entry, producer, validator) =
            (text(&policy[1])?, text(&policy[2])?, text(&policy[3])?);
        if producer == validator {
            return Err("native-proof-interface".into());
        }
        let original_acceptance = index(&policy[4])?;
        let suite = text(&policy[5])?;
        let suite = (!suite.is_empty()).then_some(suite);
        let draws = list(&policy[8])?;
        if draws.len() > 64
            || (suite.is_some() != !draws.is_empty())
            || suite.is_some() != !text(&policy[6])?.is_empty()
        {
            return Err("native-proof-policy".into());
        }
        if suite.is_some() {
            index(&policy[6])?;
        }
        let mut selected_sites = std::collections::BTreeSet::new();
        for draw in draws {
            for site in array(draw, 2)? {
                let site = text(site)?;
                if site.is_empty()
                    || site.len() > 4096
                    || !site.bytes().all(|b| (33..=126).contains(&b))
                    || !selected_sites.insert(site)
                {
                    return Err("native-proof-policy".into());
                }
            }
        }
        Ok(Self {
            entry,
            producer,
            validator,
            original_acceptance,
            suite,
            public_selection: &policy[7],
            draw_count: draws.len(),
        })
    }
}

pub(super) struct RoleInterface {
    pub(super) maps: BTreeMap<String, RoleMap>,
    pub(super) public: Vec<Port>,
    // Preserve the final acceptance-presence check after setup authority.
    pub(super) acceptance: Option<usize>,
}
impl RoleInterface {
    pub(super) fn read(
        admitted: &Admitted,
        policy: &DeploymentPolicy<'_>,
        role_map: &Json,
        public_map: &Json,
    ) -> Result<Self> {
        let (entry, producer, validator) = (policy.entry, policy.producer, policy.validator);
        let suite = policy.suite;
        let original_acceptance = policy.original_acceptance;
        let roles = admitted.entry(entry).ok_or("native-proof-entry")?;
        let mut acceptance = None;
        let mut maps = BTreeMap::new();
        for row in list(role_map)? {
            let row = array(row, 6)?;
            let role_name = text(&row[0])?;
            let role = roles
                .iter()
                .find(|r| r.role == role_name)
                .ok_or("native-proof-role-map")?;
            if role.participant != text(&row[1])? {
                return Err("native-proof-role-map".into());
            }
            let extra = usize::from(suite.is_some());
            if role.inputs.len() < extra || role.outputs.len() < extra {
                return Err("native-proof-port-map".into());
            }
            let input_types = role.inputs[..role.inputs.len() - extra]
                .iter()
                .map(|(_, t)| t.clone())
                .collect::<Vec<_>>();
            let data = ports(&row[2], &input_types)?;
            for ty in &input_types {
                input_kind(ty)?;
            }
            let outputs = ports(&row[3], &role.outputs[..role.outputs.len() - extra])?;
            // This host returns proof bytes and retires its issued roots. It
            // has no caller-owned backend in which other affine outputs could
            // remain live, unlike the general bundle host.
            if role.outputs.iter().any(|ty| {
                ty.is_affine() && !matches!(ty.kind(), Type::Rng | Type::Nonce | Type::Transcript)
            }) {
                return Err("native-proof-output-kind".into());
            }
            let service_rows = list(&row[4])?;
            if service_rows.len() != role.services.len() {
                return Err("native-proof-service-map".into());
            }
            let mut services = Vec::new();
            for (row, service) in service_rows.iter().zip(&role.services) {
                let row = array(row, 4)?;
                let original = index(&row[0])?;
                if text(&row[1])? != service.name
                    || text(&row[2])? != service.contract.name()
                    || index(&row[3])? != service.input_index
                    || data.iter().any(|p| p.original == original)
                    || services.contains(&original)
                {
                    return Err("native-proof-service-map".into());
                }
                services.push(original);
            }
            if role_name == validator {
                let decision = index(&row[5])?;
                if outputs
                    .get(decision)
                    .is_none_or(|p| p.original != original_acceptance)
                {
                    return Err("native-proof-acceptance-map".into());
                }
                acceptance = Some(decision);
            } else if !text(&row[5])?.is_empty() {
                return Err("native-proof-acceptance-map".into());
            }
            if maps
                .insert(
                    role_name.to_owned(),
                    RoleMap {
                        data,
                        services,
                        outputs,
                    },
                )
                .is_some()
            {
                return Err("native-proof-role-map".into());
            }
        }
        if maps.len() != 2 || !maps.contains_key(producer) || !maps.contains_key(validator) {
            return Err("native-proof-role-map".into());
        }
        for port in &maps[producer].data {
            if maps[validator]
                .data
                .iter()
                .any(|other| other.original == port.original && other.logical != port.logical)
            {
                return Err("native-proof-shared-port-type".into());
            }
        }
        let mut public = Vec::new();
        for row in list(public_map)? {
            let row = array(row, 4)?;
            let original = index(&row[1])?;
            let logical = wire_type(text(&row[2])?, true)?;
            if text(&row[0])? != validator
                || wire_codec(&logical).as_deref() != Some(text(&row[3])?)
                || public.last().is_some_and(|p: &Port| p.original >= original)
            {
                return Err("native-proof-public-map".into());
            }
            public.push(Port { original, logical });
        }
        let required = &maps[validator].data;
        let selected = list(policy.public_selection)?
            .iter()
            .map(index)
            .collect::<Result<Vec<_>>>()?;
        if public.len() != required.len()
            || selected != public.iter().map(|p| p.original).collect::<Vec<_>>()
            || public
                .iter()
                .zip(required)
                .any(|(p, a)| p.original != a.original || p.logical != a.logical)
        {
            return Err("native-proof-public-map".into());
        }
        Ok(Self {
            maps,
            public,
            acceptance,
        })
    }
}

fn ports(value: &Json, actual: &[PhysicalType]) -> Result<Vec<Port>> {
    let mut ports = Vec::new();
    if list(value)?.len() != actual.len() {
        return Err("native-proof-port-map".into());
    }
    for (row, ty) in list(value)?.iter().zip(actual) {
        let row = array(row, 2)?;
        let original = index(&row[0])?;
        let logical = LogicalType::parse(text(&row[1])?).map_err(|e| e.to_string())?;
        if logical != ty.logical() || ports.last().is_some_and(|p: &Port| p.original >= original) {
            return Err("native-proof-port-map".into());
        }
        ports.push(Port { original, logical });
    }
    Ok(ports)
}
