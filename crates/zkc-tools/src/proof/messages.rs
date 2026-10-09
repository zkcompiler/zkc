//! Static transcript events and their correspondence to both roles' wire
//! actions. The Runtime independently checks transcript operands and custody.
use super::{interface::DeploymentPolicy, wire_codec, wire_type};
use crate::host::inputs::{Result, array, list, text};
use serde_json::Value as Json;
use std::collections::BTreeMap;
use zkc_runtime::{
    interactive::{Admitted, LogicalType, NativeTranscriptEvent, ProgramAction},
    logical,
};

pub(super) struct MessageLayout<'a> {
    pub(super) payload_types: BTreeMap<&'a str, LogicalType>,
    pub(super) events: Vec<NativeTranscriptEvent>,
    wire_origins: Vec<&'a str>,
}
impl<'a> MessageLayout<'a> {
    pub(super) fn read(descriptor: &'a [Json], policy: &DeploymentPolicy<'_>) -> Result<Self> {
        let (entry, producer, validator) = (policy.entry, policy.producer, policy.validator);
        let suite = policy.suite;
        let mut messages = BTreeMap::new();
        for row in list(&descriptor[5])? {
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
        for row in list(&descriptor[3])? {
            let row = array(row, 2)?;
            let (kind, origin) = (text(&row[0])?, text(&row[1])?);
            let bytes = logical::native_origin_template(&[origin.into()], kind)
                .map_err(|e| e.to_string())?;
            let record = logical::decode_tree(&bytes).map_err(|e| e.to_string())?;
            if record[1].as_str() != Some(entry) || !origins.insert(origin) {
                return Err("native-proof-origin-map".into());
            }
            if kind == "query" {
                queries += 1;
                if record[4][4]
                    .as_str()
                    .and_then(|c| zkc_runtime::interactive::ServiceContract::parse(c).ok())
                    .map(|c| c.field())
                    != suite
                        .and_then(|s| LogicalType::parse(&format!("transcript:{s}")).ok())
                        .and_then(|t| t.identity().scalar_field())
                    || record[4][5].as_str() != Some("draw")
                    || record[4][6].as_str() != Some(validator)
                {
                    return Err("native-proof-query-origin".into());
                }
            } else {
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
                "message" => "transcript.native.indexed.observe.data".to_owned(),
                _ => return Err("native-proof-event".into()),
            };
            if suite.is_some() {
                events.push(NativeTranscriptEvent {
                    contract,
                    origin: origin.into(),
                    payload,
                });
            }
        }
        if queries != policy.draw_count
            || observed_messages != messages.len()
            || origins.len() > 2048
        {
            return Err("native-proof-event-map".into());
        }
        Ok(Self {
            payload_types: messages,
            events,
            wire_origins,
        })
    }

    /// Wire sites are excluded from the root but must match each participant's
    /// actual ordered sends/receives, including schema and nominal payload type.
    pub(super) fn check_wire(&self, value: &Json, admitted: &Admitted, entry: &str) -> Result<()> {
        let wire_rows = list(value)?;
        if wire_rows.len() != self.wire_origins.len() {
            return Err("native-proof-wire-map".into());
        }
        let mut wire_layout = Vec::new();
        let mut wire_sites = std::collections::BTreeSet::new();
        for (row, origin) in wire_rows.iter().zip(self.wire_origins.iter().copied()) {
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
