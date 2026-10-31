//! Static transcript events and their correspondence to both roles' wire
//! actions. The Runtime independently checks transcript operands and custody.
use super::{interface::DeploymentPolicy, wire_codec, wire_type};
use crate::io::bytes::{Result, array, list, text};
use serde_json::Value as Json;
use std::collections::BTreeMap;
use zkc_format::logical;
use zkc_runtime::vm::{LogicalType, NativeTranscriptEvent, Program, ProgramAction};

pub(super) struct MessageLayout<'a> {
    pub(super) payload_types: BTreeMap<&'a str, LogicalType>,
    pub(super) events: Vec<NativeTranscriptEvent>,
    wire_origins: Vec<&'a str>,
    witness_slots: BTreeMap<&'a str, String>,
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
        let witness_rows = list(&descriptor[7])?;
        if witness_rows.len() > 64 {
            return Err("native-proof-witness-map".into());
        }
        let mut expected_witnesses = Vec::new();
        let mut events = Vec::new();
        let mut origins = std::collections::BTreeSet::new();
        let mut queries = 0;
        let mut observed_messages = 0;
        let mut wire_origins = Vec::new();
        let mut witness_types = Vec::new();
        let mut pending_delivery = None;
        let mut used_gates = std::collections::BTreeSet::new();
        let mut source_sites = std::collections::BTreeSet::new();
        for row in event_rows {
            let row = list(row)?;
            let kind = text(row.first().ok_or("artifact-record")?)?;
            let reconstructed = kind == "reconstructed-message";
            let message = kind == "message" || reconstructed;
            let block = kind == "indices" || kind == "gated-indices";
            let gated = kind == "gated-indices";
            let query = block || kind == "query" || kind == "index";
            let arity = match kind {
                "query" | "message" | "reconstructed-message" => 2,
                "index" | "start" => 3,
                "indices" => 4,
                "gated-indices" => 5,
                _ => return Err("native-proof-event".into()),
            };
            if row.len() != arity {
                return Err("artifact-record".into());
            }
            if reconstructed && (suite.is_none() || !policy.construction.is_empty()) {
                return Err("native-proof-reconstructed-profile".into());
            }
            let origin_kind = if query {
                "query"
            } else if message {
                "message"
            } else {
                kind
            };
            let bound = if block || kind == "index" {
                Some(
                    logical::uniform_index_bound(text(&row[2])?)
                        .map_err(|_| "native-proof-index-bound")?,
                )
            } else {
                None
            };
            let count = if block {
                let value = logical::natural_index(text(&row[3])?)
                    .map_err(|_| "native-proof-index-block")?;
                if !(1..=1 << 20).contains(&value)
                    || bound.is_none_or(|b| !b.is_power_of_two() || b > 1 << 63)
                {
                    return Err("native-proof-index-block".into());
                }
                Some(value)
            } else {
                None
            };
            let difficulty = if gated {
                let value =
                    logical::natural_index(text(&row[4])?).map_err(|_| "native-proof-gates")?;
                if value > 64 {
                    return Err("native-proof-gates".into());
                }
                Some(value as u8)
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
            let bytes = logical::native_origin_template(&[origin.into()], origin_kind)
                .map_err(|e| e.to_string())?;
            let record = logical::decode_tree(&bytes).map_err(|e| e.to_string())?;
            if record[1].as_str() != Some(entry) || !origins.insert(origin) {
                return Err("native-proof-origin-map".into());
            }
            let expanded_site = zkc_runtime::vm::native_origin_site(origin, origin_kind)
                .map_err(|e| e.to_string())?;
            source_sites.insert(expanded_site.clone());
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
                let selected = policy.draws.get(queries).ok_or("native-proof-event-map")?;
                let site = expanded_site.as_str();
                let applied = record[2]
                    .as_array()
                    .ok_or("native-proof-origin-map")?
                    .iter()
                    .any(|step| step[0] == "apply");
                let source = record[4][3]
                    .as_str()
                    .and_then(|s| s.strip_prefix("input_"))
                    .and_then(|s| logical::natural_index(s).ok())
                    .and_then(|s| usize::try_from(s).ok());
                if selected.0 != site || pending_delivery.is_some() {
                    return Err("native-proof-state-chain".into());
                }
                // Applied origins name the callee's lexical service port.
                // The compiler checks its mapping to the selected root;
                // runtime admission checks the authenticated expanded site.
                if !applied
                    && !source.is_some_and(|source| policy.replaced_services.contains(&source))
                {
                    return Err("native-proof-query-origin".into());
                }
                if policy.gates.get(site).copied() != difficulty
                    || !block && policy.gates.contains_key(site)
                {
                    return Err("native-proof-gates".into());
                }
                pending_delivery = Some(selected.1);
                queries += 1;
                let field = record[4][4]
                    .as_str()
                    .and_then(|c| zkc_runtime::vm::ServiceContract::parse(c).ok())
                    .map(|c| c.field());
                let suite_type =
                    suite.and_then(|s| LogicalType::parse(&format!("transcript:{s}")).ok());
                if field.is_none()
                    || policy.construction.is_empty()
                        && suite.is_some()
                        && field
                            != suite_type
                                .as_ref()
                                .and_then(|t| t.identity().scalar_field())
                    || block
                        && !suite_type
                            .as_ref()
                            .is_some_and(|t| t.identity().has_index_block_transcript())
                    || record[4][5].as_str()
                        != Some(if block {
                            "indices"
                        } else if bound.is_some() {
                            "index"
                        } else {
                            "draw"
                        })
                    || record[4][6].as_str() != Some(validator)
                {
                    return Err("native-proof-query-origin".into());
                }
                if gated {
                    used_gates.insert(selected.0);
                    let slot = format!("gate.{site}");
                    if policy
                        .draws
                        .iter()
                        .any(|(query, delivery)| *query == slot || *delivery == slot)
                    {
                        return Err("native-proof-witness-map".into());
                    }
                    expected_witnesses.push((origin, slot));
                    wire_origins.push(origin);
                    witness_types.push((origin, LogicalType::parse("index").unwrap()));
                }
            } else if message {
                observed_messages += 1;
                if reconstructed {
                    if record[4][4].as_str() != Some(validator)
                        || record[4][5].as_str() != Some(producer)
                        || pending_delivery.is_some()
                    {
                        return Err("native-proof-reconstructed-message".into());
                    }
                } else if record[4][4].as_str() == Some(producer)
                    && record[4][5].as_str() == Some(validator)
                {
                    if pending_delivery.is_some() {
                        return Err("native-proof-event-map".into());
                    }
                    wire_origins.push(origin);
                } else if record[4][4].as_str() == Some(validator)
                    && record[4][5].as_str() == Some(producer)
                {
                    if pending_delivery.take() != Some(expanded_site.as_str()) {
                        return Err("native-proof-event-map".into());
                    }
                } else {
                    return Err("native-proof-message-origin".into());
                }
            }
            let payload = if message {
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
                "query" => "transcript.native.indexed.challenge",
                "index" => "transcript.native.indexed.index",
                "indices" => "transcript.native.indexed.indices",
                "gated-indices" => "transcript.native.indexed.indices.gated",
                "message" | "reconstructed-message" => "transcript.native.indexed.observe.data",
                "start" => "construction.start",
                _ => unreachable!(),
            }
            .to_owned();
            if suite.is_some() || !policy.construction.is_empty() {
                events.push(NativeTranscriptEvent {
                    reconstructed,
                    contract,
                    origin: origin.into(),
                    payload,
                    bound,
                    count,
                    difficulty,
                    start_inputs,
                });
            }
        }
        if queries != policy.draw_count
            || observed_messages != messages.len()
            || pending_delivery.is_some()
            || used_gates.len() != policy.gates.len()
        {
            return Err("native-proof-event-map".into());
        }
        if witness_rows.len() != expected_witnesses.len() {
            return Err("native-proof-witness-map".into());
        }
        let mut slots = std::collections::BTreeSet::new();
        for (row, (origin, slot)) in witness_rows.iter().zip(&expected_witnesses) {
            let row = array(row, 4)?;
            if text(&row[0])? != *origin
                || text(&row[1])? != slot
                || text(&row[2])? != "index"
                || text(&row[3])? != "native.index/0"
                || source_sites.contains(slot)
                || !slots.insert(slot.as_str())
            {
                return Err("native-proof-witness-map".into());
            }
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
        messages.extend(witness_types);
        Ok(Self {
            witness_slots: expected_witnesses.into_iter().collect(),
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
                || self
                    .witness_slots
                    .get(origin)
                    .is_some_and(|slot| slot != site)
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
                            || ty.logical() != *logical
                    },
                )
            {
                return Err("native-proof-wire-map".into());
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn descriptor(bits: Option<u8>) -> Json {
        let origin = |tail: Json| {
            logical::encode_tree(&json!([
                "zkc.native-origin-template/0",
                "main",
                [],
                [],
                tail
            ]))
            .unwrap()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
        };
        let query = origin(json!([
            "query",
            "Round",
            "draw",
            "input_2",
            "random.koala-bear.ext4-binomial3/0",
            "indices",
            "V"
        ]));
        let message = origin(json!(["message", "Round", "message", "message", "P", "V"]));
        let delivery = origin(json!([
            "message", "Round", "delivery", "delivery", "V", "P"
        ]));
        let block = if let Some(bits) = bits {
            json!([
                "gated-indices",
                query,
                "9223372036854775808",
                "3",
                bits.to_string()
            ])
        } else {
            json!(["indices", query, "9223372036854775808", "3"])
        };
        json!([
            "zkc.native-proof-descriptor/0",
            [
                "zkc.native-proof-policy/0",
                "main",
                "P",
                "V",
                "0",
                "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0",
                ["2"],
                ["0"],
                [["draw", "delivery"]],
                "zkc.framed/0",
                "",
                bits.map(|bits| vec![json!(["draw", bits.to_string()])])
                    .unwrap_or_default()
            ],
            "zkc.native-origin/0",
            [["message", message], block, ["message", delivery]],
            [["V", "0", "bool", "zkcv.bool/0"]],
            [
                [message, "bool", "zkcv.bool/0"],
                [delivery, "indices", "zkc.native-data/0"]
            ],
            [],
            if bits.is_some() {
                vec![json!([query, "gate.draw", "index", "native.index/0"])]
            } else {
                vec![]
            },
            r#"{"authentication":"per-query","format":"zkc.oracle-selection/0","order":"unrestricted","roots":{"entries":[],"kind":"exact"}}"#
        ])
    }
    fn check(value: &Json) -> Result<()> {
        let descriptor = array(value, 9)?;
        let policy = DeploymentPolicy::read(&descriptor[1])?;
        MessageLayout::read(descriptor, &policy).map(|_| ())
    }
    #[test]
    fn block_descriptors_authenticate_gate_and_witness_selection() {
        for bits in [None, Some(0), Some(4), Some(64)] {
            check(&descriptor(bits)).unwrap();
        }
        for mutation in 0..13 {
            let mut value = descriptor(Some(4));
            match mutation {
                0 => value[1][11][0][1] = json!("3"),
                1 => value[1][11][0][0] = json!("unknown"),
                2 => value[1][11]
                    .as_array_mut()
                    .unwrap()
                    .push(json!(["draw", "4"])),
                3 => value[3][1][4] = json!("65"),
                4 => value[3][1][2] = json!("3"),
                5 => value[3][1][3] = json!("0"),
                6 => value[7][0][1] = json!("gate.other"),
                7 => value[7][0][2] = json!("indices"),
                8 => value[7][0][3] = json!("zkcv.index/0"),
                9 => {
                    let duplicate = value[7][0].clone();
                    value[7].as_array_mut().unwrap().push(duplicate);
                }
                10 => {
                    value[7].as_array_mut().unwrap().clear();
                }
                11 => value[3][1].as_array_mut().unwrap().push(json!("unknown")),
                _ => value[7][0].as_array_mut().unwrap().push(json!("unknown")),
            }
            assert!(check(&value).is_err(), "mutation {mutation}");
        }
    }
    #[test]
    fn nested_block_sites_and_lexical_service_ports_follow_source_applications() {
        let mut value = descriptor(Some(0));
        for index in 0..3 {
            let old = value[3][index][1].as_str().unwrap().to_owned();
            let kind = if index == 1 { "query" } else { "message" };
            let mut origin = logical::decode_tree(
                &logical::native_origin_template(std::slice::from_ref(&old), kind).unwrap(),
            )
            .unwrap();
            origin[2] = json!([["apply", "Root", "a"], ["apply", "Middle", "b"]]);
            if index == 1 {
                origin[4][3] = json!("input_7");
            }
            let new: String = logical::encode_tree(&origin)
                .unwrap()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            value[3][index][1] = json!(new);
            for row in value[5].as_array_mut().unwrap() {
                if row[0] == old {
                    row[0] = json!(new);
                }
            }
            if index == 1 {
                value[7][0][0] = json!(new);
            }
        }
        value[1][8] = json!([["apply_11_apply_1_a_b_draw", "apply_11_apply_1_a_b_delivery"]]);
        value[1][11] = json!([["apply_11_apply_1_a_b_draw", "0"]]);
        value[7][0][1] = json!("gate.apply_11_apply_1_a_b_draw");
        check(&value).unwrap();
        value[7][0][1] = json!("gate.draw");
        assert!(check(&value).is_err());
    }
    #[test]
    fn policy_and_descriptor_reject_old_shapes_and_unknown_fields() {
        for (field, old) in [
            (Some(1), true),
            (Some(1), false),
            (None, true),
            (None, false),
        ] {
            let mut value = descriptor(Some(0));
            let values = if field.is_some() {
                value[1].as_array_mut().unwrap()
            } else {
                value.as_array_mut().unwrap()
            };
            if old {
                values.pop();
            } else {
                values.push(json!([]));
            }
            assert!(check(&value).is_err());
        }
        for bits in ["00", "-1", "65", "18446744073709551616"] {
            let mut value = descriptor(Some(0));
            value[1][11][0][1] = json!(bits);
            assert!(check(&value).is_err());
        }
        let mut value = descriptor(None);
        value[1][11] = json!([["draw", "0"]]);
        assert!(check(&value).is_err());
    }
}
