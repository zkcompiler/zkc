//! Bounded outer-object decoder. The embedded participant text has one owner:
//! Runtime admission; this parser never interprets its positional records.
use super::bundle::Segment;
use super::{BundleError, BundleLimits, Step};
use serde::{
    Deserialize, Deserializer,
    de::{self, DeserializeSeed, MapAccess, SeqAccess, Visitor},
};
use std::{cell::Cell, fmt};

pub(super) struct RawBundle {
    pub format: String,
    pub candidate: String,
    pub entry: String,
    pub roles: Vec<String>,
    pub steps: Vec<Step>,
    pub segments: Vec<Segment>,
}
struct RawStep {
    role: u32,
    instruction: u32,
    anchor: Anchor,
}
enum RawSegment {
    Action(RawStep),
    Loop {
        entries: Vec<RawStep>,
        body: Vec<RawSegment>,
        exits: Vec<RawStep>,
    },
}
#[derive(Clone, Copy)]
struct SegmentSeed<'a> {
    limits: BundleLimits,
    exceeded: &'a Cell<bool>,
    steps: &'a Cell<usize>,
    depth: usize,
    action_only: bool,
}
impl<'de> DeserializeSeed<'de> for SegmentSeed<'_> {
    type Value = RawSegment;
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<RawSegment, D::Error> {
        if self.depth >= zkc_runtime::interactive::Limits::STACK_DEPTH {
            return Err(limit_error(self.exceeded));
        }
        d.deserialize_map(self)
    }
}
impl<'de> Visitor<'de> for SegmentSeed<'_> {
    type Value = RawSegment;
    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("bounded schedule action or loop segment")
    }
    fn visit_map<A: MapAccess<'de>>(self, mut a: A) -> Result<Self::Value, A::Error> {
        let (mut role, mut instruction, mut anchor) = (None, None, None);
        let (mut entries, mut body, mut exits) = (None, None, None);
        let mut seen = 0u8;
        while let Some(key) = a.next_key_seed(Text(self.limits.string_bytes, self.exceeded))? {
            let bit = match key.as_str() {
                "role" => 1,
                "instruction" => 2,
                "anchor" => 4,
                "loop" => 8,
                "body" => 16,
                "yield" => 32,
                _ => return Err(de::Error::custom("unknown schedule field")),
            };
            if seen & bit != 0 {
                return Err(de::Error::custom("duplicate schedule field"));
            }
            if bit >= 8 && self.action_only {
                return Err(de::Error::custom("expected schedule action"));
            }
            seen |= bit;
            match bit {
                1 => role = Some(a.next_value()?),
                2 => instruction = Some(a.next_value()?),
                4 => anchor = Some(a.next_value()?),
                8 | 32 => {
                    let values = a.next_value_seed(List {
                        seed: Self {
                            action_only: true,
                            ..self
                        },
                        limit: self.limits.steps,
                        exceeded: self.exceeded,
                    })?;
                    let steps = values
                        .into_iter()
                        .map(|v| match v {
                            RawSegment::Action(step) => step,
                            RawSegment::Loop { .. } => unreachable!("action-only seed"),
                        })
                        .collect();
                    if bit == 8 {
                        entries = Some(steps);
                    } else {
                        exits = Some(steps);
                    }
                }
                16 => {
                    body = Some(a.next_value_seed(List {
                        seed: Self {
                            depth: self.depth + 1,
                            ..self
                        },
                        limit: self.limits.steps,
                        exceeded: self.exceeded,
                    })?)
                }
                _ => unreachable!(),
            }
        }
        match seen {
            7 => {
                if self.steps.get() >= self.limits.steps {
                    return Err(limit_error(self.exceeded));
                }
                self.steps.set(self.steps.get() + 1);
                Ok(RawSegment::Action(RawStep {
                    role: role.unwrap(),
                    instruction: instruction.unwrap(),
                    anchor: anchor.unwrap(),
                }))
            }
            56 => Ok(RawSegment::Loop {
                entries: entries.unwrap(),
                body: body.unwrap(),
                exits: exits.unwrap(),
            }),
            _ => Err(de::Error::custom("missing or mixed schedule fields")),
        }
    }
}
fn flatten(
    nodes: Vec<RawSegment>,
    steps: &mut Vec<Step>,
    limit: usize,
    depth: usize,
) -> Result<Vec<Segment>, BundleError> {
    if depth >= zkc_runtime::interactive::Limits::STACK_DEPTH {
        return Err(BundleError::Limit);
    }
    fn append(raw: RawStep, steps: &mut Vec<Step>, limit: usize) -> Result<usize, BundleError> {
        if steps.len() >= limit {
            return Err(BundleError::Limit);
        }
        let index = steps.len();
        steps.try_reserve(1).map_err(|_| BundleError::Limit)?;
        steps.push(Step {
            role: raw.role as usize,
            instruction: raw.instruction as usize,
            anchor: raw.anchor.0.map(|a| a as usize),
        });
        Ok(index)
    }
    let mut result = Vec::new();
    result
        .try_reserve_exact(nodes.len())
        .map_err(|_| BundleError::Limit)?;
    for node in nodes {
        result.push(match node {
            RawSegment::Action(step) => Segment::Action(append(step, steps, limit)?),
            RawSegment::Loop {
                entries,
                body,
                exits,
            } => Segment::Loop {
                entries: entries
                    .into_iter()
                    .map(|s| append(s, steps, limit))
                    .collect::<Result<_, _>>()?,
                body: flatten(body, steps, limit, depth + 1)?,
                exits: exits
                    .into_iter()
                    .map(|s| append(s, steps, limit))
                    .collect::<Result<_, _>>()?,
            },
        });
    }
    Ok(result)
}
// The wrapper makes the nullable anchor field mandatory in the object.
struct Anchor(Option<u32>);
impl<'de> Deserialize<'de> for Anchor {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct Nullable;
        impl Visitor<'_> for Nullable {
            type Value = Anchor;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("null or unsigned anchor")
            }
            fn visit_unit<E: de::Error>(self) -> Result<Anchor, E> {
                Ok(Anchor(None))
            }
            fn visit_u64<E: de::Error>(self, n: u64) -> Result<Anchor, E> {
                Ok(Anchor(Some(
                    u32::try_from(n).map_err(|_| E::custom("anchor bound"))?,
                )))
            }
        }
        d.deserialize_any(Nullable)
    }
}
#[derive(Clone, Copy)]
struct Text<'a>(usize, &'a Cell<bool>);
fn limit_error<E: de::Error>(exceeded: &Cell<bool>) -> E {
    exceeded.set(true);
    E::custom("run-limit")
}
impl<'de> DeserializeSeed<'de> for Text<'_> {
    type Value = String;
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<String, D::Error> {
        d.deserialize_str(self)
    }
}
impl Visitor<'_> for Text<'_> {
    type Value = String;
    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("bounded string")
    }
    fn visit_str<E: de::Error>(self, value: &str) -> Result<String, E> {
        if value.len() > self.0 {
            return Err(limit_error(self.1));
        }
        let mut owned = String::new();
        owned
            .try_reserve_exact(value.len())
            .map_err(|_| limit_error(self.1))?;
        owned.push_str(value);
        Ok(owned)
    }
}
struct List<'a, S> {
    seed: S,
    limit: usize,
    exceeded: &'a Cell<bool>,
}
impl<'de, S: DeserializeSeed<'de> + Clone> DeserializeSeed<'de> for List<'_, S> {
    type Value = Vec<S::Value>;
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<Self::Value, D::Error> {
        d.deserialize_seq(self)
    }
}
struct Refuse<'a>(&'a Cell<bool>);
impl<'de> DeserializeSeed<'de> for Refuse<'_> {
    type Value = ();
    fn deserialize<D: Deserializer<'de>>(self, _: D) -> Result<(), D::Error> {
        Err(limit_error(self.0))
    }
}
impl<'de, S: DeserializeSeed<'de> + Clone> Visitor<'de> for List<'_, S> {
    type Value = Vec<S::Value>;
    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("bounded array")
    }
    fn visit_seq<A: SeqAccess<'de>>(self, mut a: A) -> Result<Self::Value, A::Error> {
        let mut values = Vec::new();
        while values.len() < self.limit {
            let Some(value) = a.next_element_seed(self.seed.clone())? else {
                return Ok(values);
            };
            values
                .try_reserve(1)
                .map_err(|_| limit_error(self.exceeded))?;
            values.push(value);
        }
        a.next_element_seed(Refuse(self.exceeded))?;
        Ok(values)
    }
}
struct BundleSeed<'a>(BundleLimits, &'a Cell<bool>);
impl<'de> DeserializeSeed<'de> for BundleSeed<'_> {
    type Value = RawBundle;
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<RawBundle, D::Error> {
        d.deserialize_map(self)
    }
}
impl<'de> Visitor<'de> for BundleSeed<'_> {
    type Value = RawBundle;
    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("run bundle")
    }
    fn visit_map<A: MapAccess<'de>>(self, mut a: A) -> Result<RawBundle, A::Error> {
        let (mut format, mut candidate, mut entry, mut roles, mut steps) =
            (None, None, None, None, None);
        let mut seen = 0u8;
        let step_count = Cell::new(0);
        while let Some(key) = a.next_key_seed(Text(self.0.string_bytes, self.1))? {
            let bit = match key.as_str() {
                "format" => 1,
                "candidate" => 2,
                "entry" => 4,
                "roles" => 8,
                "steps" => 16,
                _ => {
                    return Err(de::Error::unknown_field(
                        &key,
                        &["format", "candidate", "entry", "roles", "steps"],
                    ));
                }
            };
            if seen & bit != 0 {
                return Err(de::Error::custom("duplicate bundle field"));
            }
            seen |= bit;
            match key.as_str() {
                "format" => format = Some(a.next_value_seed(Text(self.0.string_bytes, self.1))?),
                "candidate" => {
                    candidate = Some(a.next_value_seed(Text(self.0.candidate_bytes, self.1))?)
                }
                "entry" => entry = Some(a.next_value_seed(Text(self.0.string_bytes, self.1))?),
                "roles" => {
                    roles = Some(a.next_value_seed(List {
                        seed: Text(self.0.string_bytes, self.1),
                        limit: self.0.roles,
                        exceeded: self.1,
                    })?)
                }
                "steps" => {
                    steps = Some(a.next_value_seed(List {
                        seed: SegmentSeed {
                            limits: self.0,
                            exceeded: self.1,
                            steps: &step_count,
                            depth: 0,
                            action_only: false,
                        },
                        limit: self.0.steps,
                        exceeded: self.1,
                    })?)
                }
                _ => unreachable!(),
            }
        }
        if seen != 31 {
            return Err(de::Error::custom("missing bundle field"));
        }
        let mut flat = Vec::new();
        let segments = flatten(steps.unwrap(), &mut flat, self.0.steps, 0)
            .map_err(|_| limit_error::<A::Error>(self.1))?;
        Ok(RawBundle {
            format: format.unwrap(),
            candidate: candidate.unwrap(),
            entry: entry.unwrap(),
            roles: roles.unwrap(),
            steps: flat,
            segments,
        })
    }
}
pub(super) fn bundle(bytes: &[u8], limits: BundleLimits) -> Result<RawBundle, BundleError> {
    if bytes.len() > limits.bytes {
        return Err(BundleError::Limit);
    }
    let (mut depth, mut nodes, mut quoted, mut escape, mut atom) =
        (0usize, 0usize, false, false, false);
    for &b in bytes {
        if quoted {
            if escape {
                escape = false;
            } else if b == b'\\' {
                escape = true;
            } else if b == b'"' {
                quoted = false;
            }
            continue;
        }
        match b {
            b'"' => {
                nodes += 1;
                quoted = true;
                atom = false;
            }
            b'[' | b'{' => {
                depth += 1;
                nodes += 1;
                atom = false;
            }
            b']' | b'}' => {
                depth = depth.checked_sub(1).ok_or(BundleError::Json)?;
                atom = false;
            }
            b',' | b':' | b' ' | b'\n' | b'\r' | b'\t' => atom = false,
            _ if !atom => {
                nodes += 1;
                atom = true;
            }
            _ => {}
        }
        if depth > limits.depth || nodes > limits.nodes {
            return Err(BundleError::Limit);
        }
    }
    if quoted || depth != 0 {
        return Err(BundleError::Json);
    }
    let mut decoder = serde_json::Deserializer::from_slice(bytes);
    // The bounded lexical pass above owns depth and total node admission.
    decoder.disable_recursion_limit();
    let exceeded = Cell::new(false);
    let result = BundleSeed(limits, &exceeded)
        .deserialize(&mut decoder)
        .map_err(|_| {
            if exceeded.get() {
                BundleError::Limit
            } else {
                BundleError::Json
            }
        })?;
    decoder.end().map_err(|_| BundleError::Json)?;
    Ok(result)
}
