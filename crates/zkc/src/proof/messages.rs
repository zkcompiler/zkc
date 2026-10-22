//! Static transcript events and their correspondence to both roles' wire
//! actions. The Runtime independently checks transcript operands and custody.
use super::{interface::DeploymentPolicy, wire_codec, wire_type};
use crate::host::inputs::{Result, array, list, text};
use serde_json::Value as Json;
use std::collections::BTreeMap;
use zkc_runtime::{
    logical,
    vm::{LogicalType, NativeTranscriptEvent, Program, ProgramAction},
};

pub(super) struct MessageLayout<'a> {
    pub(super) payload_types: BTreeMap<&'a str, LogicalType>,
    pub(super) events: Vec<NativeTranscriptEvent>,
    wire_origins: Vec<&'a str>,
    format: super::ProofFormat,
    record_codec: bool,
}
impl<'a> MessageLayout<'a> {
    pub(super) fn read(descriptor: &'a [Json], policy: &DeploymentPolicy<'_>) -> Result<Self> {
        let (entry, producer, validator) = (policy.entry, policy.producer, policy.validator);
        let suite = policy.suite;
        let event_rows = list(&descriptor[3])?;
        let message_rows = list(&descriptor[5])?;
        if event_rows.len() > 2048 || message_rows.len() > 2048 {
            return Err("native-proof-event-map".into());
        }
        let mut messages = BTreeMap::new();
        for row in message_rows {
            let row = array(row, 3)?;
            let origin = text(&row[0])?;
            let ty = wire_type(text(&row[1])?, false)?;
            if wire_codec(&ty).as_deref() != Some(text(&row[2])?)
                || messages.insert(origin, ty).is_some()
            {
                return Err("native-proof-message-map".into());
            }
        }
        let mut events = Vec::new();
        let mut origins = std::collections::BTreeSet::new();
        let mut queries = 0;
        let mut observed_messages = 0;
        let mut wire_origins = Vec::new();
        for row in event_rows {
            // ["query", origin] draws a field challenge; ["index", origin,
            // bound] draws UniformIndex(bound); ["message", origin] observes.
            let row = list(row)?;
            let kind = text(row.first().ok_or("artifact-record")?)?;
            if row.len()
                != if kind == "index" || kind == "start" {
                    3
                } else {
                    2
                }
            {
                return Err("artifact-record".into());
            }
            let bound = if kind == "index" {
                Some(
                    logical::uniform_index_bound(text(&row[2])?)
                        .map_err(|_| "native-proof-index-bound")?,
                )
            } else {
                None
            };
            if policy.construction.is_empty() && bound.is_some_and(|b| !b.is_power_of_two()) {
                return Err("native-proof-index-bound".into());
            }
            let origin = text(&row[1])?;
            let start_inputs = if kind == "start" {
                let inputs = list(&row[2])?;
                if policy.construction.is_empty() || inputs.len() > 1024 {
                    return Err("native-proof-construction-start".into());
                }
                Some(
                    inputs
                        .iter()
                        .map(|input| {
                            LogicalType::parse(text(input)?)
                                .map_err(|_| "native-proof-helper-signature".into())
                        })
                        .collect::<Result<Vec<_>>>()?,
                )
            } else {
                None
            };
            let query = kind == "query" || kind == "index";
            let bytes = logical::native_origin_template(
                &[origin.into()],
                if query { "query" } else { kind },
            )
            .map_err(|e| e.to_string())?;
            let record = logical::decode_tree(&bytes).map_err(|e| e.to_string())?;
            if record[1].as_str() != Some(entry) || !origins.insert(origin) {
                return Err("native-proof-origin-map".into());
            }
            if policy.format == super::ProofFormat::RawBytes
                && policy.construction.is_empty()
                && record[2]
                    .as_array()
                    .ok_or("native-proof-origin-map")?
                    .iter()
                    .any(|s| s[0] == "repeat")
            {
                return Err("native-proof-format".into());
            }
            if query {
                queries += 1;
                let field = record[4][4]
                    .as_str()
                    .and_then(|c| zkc_runtime::vm::ServiceContract::parse(c).ok())
                    .map(|c| c.field());
                if field.is_none()
                    || policy.construction.is_empty()
                        && suite.is_some()
                        && field
                            != suite
                                .and_then(|s| LogicalType::parse(&format!("transcript:{s}")).ok())
                                .and_then(|t| t.identity().scalar_field())
                    || record[4][5].as_str() != Some(if bound.is_some() { "index" } else { "draw" })
                    || record[4][6].as_str() != Some(validator)
                {
                    return Err("native-proof-query-origin".into());
                }
            } else if kind == "message" {
                observed_messages += 1;
                if record[4][4].as_str() == Some(producer)
                    && record[4][5].as_str() == Some(validator)
                {
                    wire_origins.push(origin);
                } else if record[4][4].as_str() != Some(validator)
                    || record[4][5].as_str() != Some(producer)
                {
                    return Err("native-proof-message-origin".into());
                }
            }
            let payload = if kind == "message" {
                Some(
                    messages
                        .get(origin)
                        .ok_or("native-proof-message-map")?
                        .clone(),
                )
            } else {
                None
            };
            let contract = match kind {
                "query" => "transcript.native.indexed.challenge".to_owned(),
                "index" => "transcript.native.indexed.index".to_owned(),
                "message" => "transcript.native.indexed.observe.data".to_owned(),
                "start" => "construction.start".to_owned(),
                _ => return Err("native-proof-event".into()),
            };
            if suite.is_some() || !policy.construction.is_empty() {
                events.push(NativeTranscriptEvent {
                    contract,
                    origin: origin.into(),
                    payload,
                    bound,
                    start_inputs,
                });
            }
        }
        if queries != policy.draw_count || observed_messages != messages.len() {
            return Err("native-proof-event-map".into());
        }
        if policy.format == super::ProofFormat::RawBytes
            && policy.construction.is_empty()
            && (observed_messages != 1
                || wire_origins.len() != 1
                || messages
                    .values()
                    .any(|t| t.kind() != zkc_runtime::vm::Type::Bytes))
        {
            return Err("native-proof-format".into());
        }
        Ok(Self {
            payload_types: messages,
            events,
            wire_origins,
            format: policy.format,
            record_codec: policy.format == super::ProofFormat::RawBytes
                && !policy.construction.is_empty(),
        })
    }

    /// Wire sites are excluded from the root but must match each participant's
    /// actual ordered sends/receives, including schema and nominal payload type.
    pub(super) fn check_wire(&self, value: &Json, admitted: &Program, entry: &str) -> Result<()> {
        let wire_rows = list(value)?;
        let origins = if self.record_codec {
            &[]
        } else {
            self.wire_origins.as_slice()
        };
        if wire_rows.len() != origins.len() {
            return Err("native-proof-wire-map".into());
        }
        let mut wire_layout = Vec::new();
        let mut wire_sites = std::collections::BTreeSet::new();
        for (row, origin) in wire_rows.iter().zip(origins.iter().copied()) {
            let row = array(row, 2)?;
            let site = text(&row[1])?;
            if text(&row[0])? != origin
                || site.is_empty()
                || site.len() > 4096
                || !wire_sites.insert(site)
            {
                return Err("native-proof-wire-map".into());
            }
            wire_layout.push((
                site,
                self.payload_types
                    .get(origin)
                    .ok_or("native-proof-message-map")?,
            ));
        }
        for role in admitted.program_entry(entry).map_err(|e| e.to_string())? {
            if self.format == super::ProofFormat::RawBytes {
                // Program admission already validates loop boundaries. The
                // flattened action order lets us check nesting in one pass.
                let mut inside_until = 0;
                for (index, action) in role.actions.iter().enumerate() {
                    match action {
                        ProgramAction::Loop { end, .. } => inside_until = inside_until.max(*end),
                        ProgramAction::Send { .. } | ProgramAction::Receive { .. }
                            if index < inside_until =>
                        {
                            return Err("native-proof-format".into());
                        }
                        _ => (),
                    }
                }
            }
            let actual: Vec<_> = role
                .actions
                .iter()
                .filter_map(|action| match action {
                    ProgramAction::Send {
                        site, schema, ty, ..
                    }
                    | ProgramAction::Receive {
                        site, schema, ty, ..
                    } => Some((site, schema, ty)),
                    _ => None,
                })
                .collect();
            if actual.len() != wire_layout.len()
                || actual.iter().zip(&wire_layout).any(
                    |((site, schema, ty), (expected, logical))| {
                        site.as_str() != *expected
                            || schema.as_str() != *expected
                            || ty.logical() != **logical
                    },
                )
            {
                return Err("native-proof-wire-map".into());
            }
        }
        Ok(())
    }
}
