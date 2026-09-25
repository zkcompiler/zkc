//! Small explicit-event JSON replay for compiler/Lean schedule comparison.
//! See README.md for the schema. No full protocol or proof decoder is hidden here.
use super::{
    Error, Result, Work, monero, openvm,
    wire::{ItemValue, Unobserved, WireItem, WireMap},
};
use serde::de::{self, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer};
use serde_json::{Map, Value, json};
use std::collections::BTreeMap;

pub const MONERO_PROFILE: &str = "monero-hash-chain-v1";
pub const OPENVM_PROFILE: &str = "openvm-babybear-poseidon2-v1";

/// Replay-tool admission limits. Native runtime caps remain the caller's policy.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub input_bytes: usize,
    pub items: usize,
    pub events: usize,
    pub values_per_event: usize,
    pub hash_bytes: u64,
    pub permutations: u64,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            input_bytes: 16 * 1024 * 1024,
            items: 100_000,
            events: 100_000,
            values_per_event: 1_000_000,
            hash_bytes: 64 * 1024 * 1024,
            permutations: 1_000_000,
        }
    }
}

// Value's ordinary deserializer silently overwrites duplicate keys. Reject them
// recursively at ingress, before mapping/event admission.
struct UniqueJson(Value);
impl<'de> Deserialize<'de> for UniqueJson {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> std::result::Result<Self, D::Error> {
        struct UniqueVisitor;
        impl<'de> Visitor<'de> for UniqueVisitor {
            type Value = UniqueJson;
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("JSON without duplicate keys")
            }
            fn visit_bool<E: de::Error>(self, v: bool) -> std::result::Result<Self::Value, E> {
                Ok(UniqueJson(v.into()))
            }
            fn visit_u64<E: de::Error>(self, v: u64) -> std::result::Result<Self::Value, E> {
                Ok(UniqueJson(v.into()))
            }
            fn visit_i64<E: de::Error>(self, v: i64) -> std::result::Result<Self::Value, E> {
                Ok(UniqueJson(v.into()))
            }
            fn visit_f64<E: de::Error>(self, _: f64) -> std::result::Result<Self::Value, E> {
                Err(E::custom("integer JSON required"))
            }
            fn visit_str<E: de::Error>(self, v: &str) -> std::result::Result<Self::Value, E> {
                Ok(UniqueJson(v.into()))
            }
            fn visit_string<E: de::Error>(self, v: String) -> std::result::Result<Self::Value, E> {
                Ok(UniqueJson(v.into()))
            }
            fn visit_unit<E: de::Error>(self) -> std::result::Result<Self::Value, E> {
                Ok(UniqueJson(Value::Null))
            }
            fn visit_seq<A: SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> std::result::Result<Self::Value, A::Error> {
                let mut out = Vec::new();
                while let Some(UniqueJson(value)) = seq.next_element()? {
                    out.push(value);
                }
                Ok(UniqueJson(out.into()))
            }
            fn visit_map<A: MapAccess<'de>>(
                self,
                mut map: A,
            ) -> std::result::Result<Self::Value, A::Error> {
                let mut out = Map::new();
                while let Some((key, UniqueJson(value))) = map.next_entry::<String, UniqueJson>()? {
                    if out.insert(key, value).is_some() {
                        return Err(de::Error::custom("duplicate key"));
                    }
                }
                Ok(UniqueJson(out.into()))
            }
        }
        deserializer.deserialize_any(UniqueVisitor)
    }
}

/// Byte ingress rejects duplicate keys, floats, trailing data and oversized input.
pub fn replay_json(bytes: &[u8], limits: Limits) -> Result<Value> {
    if bytes.len() > limits.input_bytes {
        return Err(Error::ResourceLimit);
    }
    let UniqueJson(value) = serde_json::from_slice(bytes).map_err(|_| Error::MalformedReplay)?;
    replay(&value, limits)
}

fn object<'a>(value: &'a Value, allowed: &[&str]) -> Result<&'a Map<String, Value>> {
    let obj = value.as_object().ok_or(Error::MalformedReplay)?;
    if obj.keys().any(|key| !allowed.contains(&key.as_str())) {
        return Err(Error::UnknownMember);
    }
    Ok(obj)
}
fn required<'a>(obj: &'a Map<String, Value>, key: &str) -> Result<&'a Value> {
    obj.get(key).ok_or(Error::MalformedReplay)
}
fn string(value: &Value) -> Result<&str> {
    value.as_str().ok_or(Error::MalformedReplay)
}
fn array(value: &Value) -> Result<&[Value]> {
    value
        .as_array()
        .map(Vec::as_slice)
        .ok_or(Error::MalformedReplay)
}
fn number(value: &Value) -> Result<u32> {
    value
        .as_u64()
        .and_then(|n| u32::try_from(n).ok())
        .ok_or(Error::MalformedReplay)
}
fn index(value: &Value) -> Result<usize> {
    value
        .as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .ok_or(Error::MalformedReplay)
}
fn names(value: &Value) -> Result<Vec<String>> {
    array(value)?
        .iter()
        .map(|v| Ok(string(v)?.to_owned()))
        .collect()
}

pub fn encode_hex(bytes: &[u8]) -> String {
    use std::fmt::Write;
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(out, "{byte:02x}").expect("String formatting");
    }
    out
}
pub fn decode_hex(value: &str) -> Result<Vec<u8>> {
    if !value.len().is_multiple_of(2) {
        return Err(Error::MalformedReplay);
    }
    fn nibble(b: u8) -> Result<u8> {
        match b {
            b'0'..=b'9' => Ok(b - b'0'),
            b'a'..=b'f' => Ok(b - b'a' + 10),
            _ => Err(Error::MalformedReplay),
        }
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|b| Ok(nibble(b[0])? * 16 + nibble(b[1])?))
        .collect()
}
pub fn decode_word(value: &str) -> Result<monero::Word> {
    if value.len() != 64 {
        return Err(Error::MalformedReplay);
    }
    decode_hex(value)?
        .try_into()
        .map_err(|_| Error::MalformedReplay)
}
fn work_json(work: Work) -> Value {
    json!({"hash_calls":work.hash_calls,"hash_bytes":work.hash_bytes,"permutations":work.permutations,"observes":work.observes,"samples":work.samples})
}
fn state_json(state: openvm::Snapshot) -> Value {
    json!({"state":state.state,"absorb_index":state.absorb_index,"sample_index":state.sample_index})
}
fn charge(total: &mut Work, work: Work, limits: Limits) -> Result<()> {
    let next = total.checked_add(work)?;
    if next.hash_bytes > limits.hash_bytes || next.permutations > limits.permutations {
        return Err(Error::ResourceLimit);
    }
    *total = next;
    Ok(())
}

/// Replay a previously decoded value. Use replay_json for untrusted JSON bytes.
/// Successful output establishes event consistency only, not proof validity or
/// the correctness of declared guard/source identities.
pub fn replay(value: &Value, limits: Limits) -> Result<Value> {
    let root = object(
        value,
        &[
            "version",
            "profile",
            "initial",
            "items",
            "unobserved",
            "events",
        ],
    )?;
    if number(required(root, "version")?)? != 1 {
        return Err(Error::MalformedReplay);
    }
    let profile = string(required(root, "profile")?)?;
    let mut chain = match profile {
        MONERO_PROFILE => Some(monero::HashChain::new(decode_word(string(required(
            root, "initial",
        )?)?)?)),
        OPENVM_PROFILE if !root.contains_key("initial") => None,
        _ => return Err(Error::MalformedReplay),
    };
    let mut duplex = openvm::Duplex::new();
    let raw_items = array(required(root, "items")?)?;
    let events = array(required(root, "events")?)?;
    if raw_items.len() > limits.items || events.len() > limits.events {
        return Err(Error::ResourceLimit);
    }
    let mut items = Vec::with_capacity(raw_items.len());
    for value in raw_items {
        let obj = object(value, &["id", "origin", "wire_index", "kind", "values"])?;
        let raw = required(obj, "values")?;
        let kind = string(required(obj, "kind")?)?;
        let value = match kind {
            "words" => {
                let values = array(raw)?;
                if values.len() > limits.values_per_event {
                    return Err(Error::ResourceLimit);
                }
                ItemValue::Words(
                    values
                        .iter()
                        .map(|v| decode_word(string(v)?))
                        .collect::<Result<_>>()?,
                )
            }
            "fields" => {
                let values = array(raw)?;
                if values.len() > limits.values_per_event {
                    return Err(Error::ResourceLimit);
                }
                ItemValue::Fields(values.iter().map(number).collect::<Result<_>>()?)
            }
            "opaque" => {
                let text = string(raw)?;
                if text.len() / 2 > limits.values_per_event {
                    return Err(Error::ResourceLimit);
                }
                ItemValue::Opaque(decode_hex(text)?)
            }
            _ => return Err(Error::WrongItemType),
        };
        let raw_index = required(obj, "wire_index")?;
        items.push(WireItem {
            id: string(required(obj, "id")?)?.to_owned(),
            origin: string(required(obj, "origin")?)?.to_owned(),
            wire_index: if raw_index.is_null() {
                None
            } else {
                Some(index(raw_index)?)
            },
            value,
        });
    }
    let wire = WireMap::new(items)?;
    let mut unobserved = Vec::new();
    for value in array(required(root, "unobserved")?)? {
        let obj = object(value, &["item", "guard"])?;
        unobserved.push(Unobserved {
            item: string(required(obj, "item")?)?.to_owned(),
            guard: string(required(obj, "guard")?)?.to_owned(),
        });
    }
    let mut used = Vec::new();
    let mut derived = BTreeMap::<String, monero::Word>::new();
    let mut total = Work::default();
    let mut checkpoints = Vec::with_capacity(events.len());
    for (event_index, event) in events.iter().enumerate() {
        let op = string(event.get("op").ok_or(Error::MalformedReplay)?)?;
        let allowed: &[&str] = match op {
            "hash" => &["op", "items", "output", "expect", "expect_state"],
            "update" | "observe" => &["op", "items", "expect", "expect_state"],
            "sample" | "sample_ext" => &["op", "expect", "expect_state"],
            "sample_bits" => &["op", "bits", "expect", "expect_state"],
            "check_witness" | "trial_witness" => {
                &["op", "bits", "witness", "expect", "expect_state"]
            }
            _ => return Err(Error::MalformedReplay),
        };
        let obj = object(event, allowed)?;
        let (result, work) = match op {
            "hash" | "update" if chain.is_some() => {
                let mut words = Vec::new();
                for id in names(required(obj, "items")?)? {
                    let additional = if let Some(word) = derived.get(&id) {
                        vec![*word]
                    } else {
                        let item = wire.get(&id)?;
                        let ItemValue::Words(values) = &item.value else {
                            return Err(Error::WrongItemType);
                        };
                        used.push(id);
                        values.clone()
                    };
                    if additional.len() > limits.values_per_event.saturating_sub(words.len()) {
                        return Err(Error::ResourceLimit);
                    }
                    words.extend(additional);
                }
                let work = monero::hash_work(words.len(), op == "update")?;
                charge(&mut total, work, limits)?;
                let result = if op == "hash" {
                    let output = string(required(obj, "output")?)?;
                    if output.is_empty() || wire.get(output).is_ok() || derived.contains_key(output)
                    {
                        return Err(Error::DuplicateIdentity);
                    }
                    let hash = monero::hash_to_scalar(&words);
                    derived.insert(output.to_owned(), hash);
                    hash
                } else {
                    chain.as_mut().expect("profile checked").update(&words)
                };
                (json!(encode_hex(&result)), work)
            }
            "observe" if chain.is_none() => {
                let mut fields = Vec::new();
                for id in names(required(obj, "items")?)? {
                    let item = wire.get(&id)?;
                    let ItemValue::Fields(values) = &item.value else {
                        return Err(Error::WrongItemType);
                    };
                    if values.len() > limits.values_per_event.saturating_sub(fields.len()) {
                        return Err(Error::ResourceLimit);
                    }
                    fields.extend_from_slice(values);
                    used.push(id);
                }
                let work = duplex.observe_work(fields.len())?;
                charge(&mut total, work, limits)?;
                let actual = duplex.observe(&fields)?;
                debug_assert_eq!(actual, work);
                (Value::Null, work)
            }
            "sample" | "sample_ext" | "sample_bits" if chain.is_none() => {
                let bits = if op == "sample_bits" {
                    let bits = number(required(obj, "bits")?)?;
                    openvm::validate_bits(bits)?;
                    Some(bits)
                } else {
                    None
                };
                let work = duplex.sample_work(if op == "sample_ext" { 4 } else { 1 })?;
                charge(&mut total, work, limits)?;
                let result = if let Some(bits) = bits {
                    json!(duplex.sample_bits(bits)?.value)
                } else if op == "sample_ext" {
                    json!(duplex.sample_ext().value)
                } else {
                    json!(duplex.sample().value)
                };
                (result, work)
            }
            "check_witness" | "trial_witness" if chain.is_none() => {
                let bits = number(required(obj, "bits")?)?;
                let witness = number(required(obj, "witness")?)?;
                openvm::validate_field(witness)?;
                let work = duplex.witness_work(bits)?;
                charge(&mut total, work, limits)?;
                let result = if op == "trial_witness" {
                    duplex.trial_witness(bits, witness)?
                } else {
                    duplex.check_witness(bits, witness)?
                };
                debug_assert_eq!(result.work, work);
                (json!(result.value), work)
            }
            _ => return Err(Error::MalformedReplay),
        };
        let state = chain.as_ref().map_or_else(
            || state_json(duplex.snapshot()),
            |chain| json!(encode_hex(&chain.state())),
        );
        if obj
            .get("expect")
            .is_some_and(|expected| expected != &result)
            || obj
                .get("expect_state")
                .is_some_and(|expected| expected != &state)
        {
            return Err(Error::ExpectationMismatch);
        }
        checkpoints.push(json!({"index":event_index,"op":op,"value":result,"state":state,"work":work_json(work)}));
    }
    wire.validate_mapping(&used, &unobserved)?;
    Ok(json!({"version":1,"profile":profile,"checkpoints":checkpoints,"work":work_json(total)}))
}
