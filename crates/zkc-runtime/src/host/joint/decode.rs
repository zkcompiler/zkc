//! Bounded outer-object decoder. The embedded participant text has one owner:
//! Runtime admission; this parser never interprets its positional records.
use super::bundle::{BranchArm, CONTROL_LEVELS, Segment};
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
    Branch {
        entries: Vec<RawStep>,
        arms: Vec<RawArm>,
    },
    Loop {
        entries: Vec<RawStep>,
        body: Vec<RawSegment>,
        exits: Vec<RawStep>,
    },
}
struct RawArm {
    alternative: String,
    body: Vec<RawSegment>,
    exits: Vec<RawStep>,
}
#[derive(Clone, Copy)]
struct ArmSeed<'a>(SegmentSeed<'a>);
impl<'de> DeserializeSeed<'de> for ArmSeed<'_> {
    type Value = RawArm;
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<RawArm, D::Error> {
        d.deserialize_map(self)
    }
}
impl<'de> Visitor<'de> for ArmSeed<'_> {
    type Value = RawArm;
    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("exact branch arm")
    }
    fn visit_map<A: MapAccess<'de>>(self, mut a: A) -> Result<RawArm, A::Error> {
        let (mut alternative, mut body, mut exits) = (None, None, None);
        while let Some(key) = a.next_key_seed(Text(self.0.limits.string_bytes, self.0.exceeded))? {
            match key.as_str() {
                "alternative" if alternative.is_none() => {
                    alternative = Some(a.next_value_seed(Text(128, self.0.exceeded))?)
                }
                "body" if body.is_none() => {
                    body = Some(a.next_value_seed(List {
                        seed: SegmentSeed {
                            depth: self.0.depth + 1,
                            ..self.0
                        },
                        limit: self.0.limits.steps,
                        exceeded: self.0.exceeded,
                    })?)
                }
                "yield" if exits.is_none() => {
                    let values = a.next_value_seed(List {
                        seed: SegmentSeed {
                            action_only: true,
                            ..self.0
                        },
                        limit: self.0.limits.steps,
                        exceeded: self.0.exceeded,
                    })?;
                    exits = Some(
                        values
                            .into_iter()
                            .map(|v| match v {
                                RawSegment::Action(s) => s,
                                _ => unreachable!("action seed"),
                            })
                            .collect(),
                    );
                }
                _ => return Err(de::Error::custom("unknown or duplicate branch arm field")),
            }
        }
        Ok(RawArm {
            alternative: alternative.ok_or_else(|| de::Error::custom("missing alternative"))?,
            body: body.ok_or_else(|| de::Error::custom("missing arm body"))?,
            exits: exits.ok_or_else(|| de::Error::custom("missing arm yield"))?,
        })
    }
}
#[derive(Clone, Copy)]
struct SegmentSeed<'a> {
    limits: BundleLimits,
    exceeded: &'a Cell<bool>,
    steps: &'a Cell<usize>,
    /// Control segments enclosing this one: a control segment here is at
    /// level depth + 1, while a step segment adds no level.
    depth: usize,
    action_only: bool,
}
impl<'de> DeserializeSeed<'de> for SegmentSeed<'_> {
    type Value = RawSegment;
    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<RawSegment, D::Error> {
        // A level-65 control segment refuses at its first control field, so
        // no segment is read more than one step below the deepest level.
        if self.depth > CONTROL_LEVELS {
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
        let (mut branches, mut arms) = (None, None);
        let mut seen = 0u16;
        while let Some(key) = a.next_key_seed(Text(self.limits.string_bytes, self.exceeded))? {
            let bit = match key.as_str() {
                "role" => 1,
                "instruction" => 2,
                "anchor" => 4,
                "loop" => 8,
                "body" => 16,
                "yield" => 32,
                "branch" => 64,
                "arms" => 128,
                _ => return Err(de::Error::custom("unknown schedule field")),
            };
            if seen & bit != 0 {
                return Err(de::Error::custom("duplicate schedule field"));
            }
            if bit >= 8 && self.action_only {
                return Err(de::Error::custom("expected schedule action"));
            }
            // A control field makes this a control segment at level depth + 1;
            // refuse one beyond the deepest level before reading its body.
            if bit >= 8 && self.depth >= CONTROL_LEVELS {
                return Err(limit_error(self.exceeded));
            }
            seen |= bit;
            match bit {
                1 => role = Some(a.next_value()?),
                2 => instruction = Some(a.next_value()?),
                4 => anchor = Some(a.next_value()?),
                8 | 32 | 64 => {
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
                            _ => unreachable!("action-only seed"),
                        })
                        .collect();
                    if bit == 8 {
                        entries = Some(steps);
                    } else if bit == 32 {
                        exits = Some(steps);
                    } else {
                        branches = Some(steps);
                    }
                }
                128 => {
                    arms = Some(a.next_value_seed(List {
                        seed: ArmSeed(self),
                        limit: 32,
                        exceeded: self.exceeded,
                    })?);
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
            192 => Ok(RawSegment::Branch {
                entries: branches.unwrap(),
                arms: arms.unwrap(),
            }),
            56 => Ok(RawSegment::Loop {
                entries: entries.unwrap(),
                body: body.unwrap(),
                exits: exits.unwrap(),
            }),
            _ => Err(de::Error::custom("missing or mixed schedule fields")),
        }
    }
}
/// `depth` counts the control segments enclosing `nodes`, as in
/// [`SegmentSeed`].
fn flatten(
    nodes: Vec<RawSegment>,
    steps: &mut Vec<Step>,
    limit: usize,
    depth: usize,
) -> Result<Vec<Segment>, BundleError> {
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
        if !matches!(node, RawSegment::Action(_)) && depth >= CONTROL_LEVELS {
            return Err(BundleError::Limit);
        }
        result.push(match node {
            RawSegment::Action(step) => Segment::Action(append(step, steps, limit)?),
            RawSegment::Branch { entries, arms } => Segment::Branch {
                entries: entries
                    .into_iter()
                    .map(|s| append(s, steps, limit))
                    .collect::<Result<_, _>>()?,
                arms: arms
                    .into_iter()
                    .map(|arm| {
                        Ok(BranchArm {
                            alternative: arm.alternative,
                            body: flatten(arm.body, steps, limit, depth + 1)?,
                            exits: arm
                                .exits
                                .into_iter()
                                .map(|s| append(s, steps, limit))
                                .collect::<Result<_, _>>()?,
                        })
                    })
                    .collect::<Result<_, BundleError>>()?,
            },
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

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value as Json, json};

    fn step(instruction: u32) -> Json {
        json!({"role":0,"instruction":instruction,"anchor":null})
    }
    /// A schedule of `levels` control segments, each in the body of the one
    /// before, whose innermost body holds one step. The innermost segment is a
    /// branch when `branch` is set; the outer ones are loops, which keep the
    /// outer JSON within its own, separate depth bound.
    fn nested(levels: usize, branch: bool) -> Vec<u8> {
        let mut body = json!([step(0)]);
        for level in (1..=levels).rev() {
            body = if branch && level == levels {
                json!([{"branch":[step(1)],
                    "arms":[{"alternative":"then","body":body,"yield":[step(2)]}]}])
            } else {
                json!([{"loop":[step(1)],"body":body,"yield":[step(2)]}])
            };
        }
        serde_json::to_vec(&json!({"format":"zkc.run/0","candidate":"","entry":"main",
            "roles":["P"],"steps":body}))
        .unwrap()
    }
    fn deepest(segments: &[Segment]) -> usize {
        segments
            .iter()
            .map(|segment| match segment {
                Segment::Action(_) => 0,
                Segment::Loop { body, .. } => 1 + deepest(body),
                Segment::Branch { arms, .. } => {
                    1 + arms.iter().map(|arm| deepest(&arm.body)).max().unwrap_or(0)
                }
            })
            .max()
            .unwrap_or(0)
    }
    #[test]
    fn control_nesting_admits_level_64_with_a_body_and_refuses_level_65() {
        for branch in [false, true] {
            // Steps add no level: the step in the level-64 body is admitted.
            let admitted = bundle(&nested(CONTROL_LEVELS, branch), BundleLimits::default())
                .unwrap_or_else(|e| panic!("level {CONTROL_LEVELS} refused: {e}"));
            assert_eq!(deepest(&admitted.segments), CONTROL_LEVELS);
            assert_eq!(admitted.steps.len(), 2 * CONTROL_LEVELS + 1);
            assert!(matches!(
                bundle(&nested(CONTROL_LEVELS + 1, branch), BundleLimits::default()),
                Err(BundleError::Limit)
            ));
        }
        // A level-65 control segment refuses even with an empty body.
        let mut body = json!([{"loop":[step(1)],"body":[],"yield":[step(2)]}]);
        for _ in 0..CONTROL_LEVELS {
            body = json!([{"loop":[step(1)],"body":body,"yield":[step(2)]}]);
        }
        let bytes = serde_json::to_vec(&json!({"format":"zkc.run/0","candidate":"",
            "entry":"main","roles":["P"],"steps":body}))
        .unwrap();
        assert!(matches!(
            bundle(&bytes, BundleLimits::default()),
            Err(BundleError::Limit)
        ));
    }
    #[test]
    fn flattening_counts_control_segments_only() {
        fn raw(levels: usize) -> Vec<RawSegment> {
            let action = |instruction| {
                RawSegment::Action(RawStep {
                    role: 0,
                    instruction,
                    anchor: Anchor(None),
                })
            };
            let mut body = vec![action(0)];
            for _ in 0..levels {
                body = vec![RawSegment::Loop {
                    entries: vec![RawStep {
                        role: 0,
                        instruction: 1,
                        anchor: Anchor(None),
                    }],
                    body,
                    exits: vec![],
                }];
            }
            body
        }
        let mut steps = Vec::new();
        let flat = flatten(raw(CONTROL_LEVELS), &mut steps, 32768, 0).unwrap();
        assert_eq!(deepest(&flat), CONTROL_LEVELS);
        assert_eq!(steps.len(), CONTROL_LEVELS + 1);
        let mut steps = Vec::new();
        assert!(matches!(
            flatten(raw(CONTROL_LEVELS + 1), &mut steps, 32768, 0),
            Err(BundleError::Limit)
        ));
    }
}
