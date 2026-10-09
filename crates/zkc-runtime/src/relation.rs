//! Independent admission and reference semantics of the deterministic relation
//! bundle `zkc.relation-bundle/0`, its configuration, instance and witness
//! carriers, and the separate staged program `zkc.relation-staged/0`.
//!
//! Field arithmetic is supplied through [`Algebra`]; this module owns rows,
//! scopes, windows, authority, presence and interaction meaning. It makes no
//! claim about a proof protocol that consumes the relation.
use crate::interactive::Identity;
pub use crate::ring::Error;
use crate::ring::{Expression, Node};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

mod table;
pub use table::{TableData, TableLengths, TableView};

pub const BYTE_LIMIT: usize = 8 * 1024 * 1024;
pub const DATA_BYTE_LIMIT: usize = 256 * 1024 * 1024;
pub const TABLE_LIMIT: usize = 256;
pub const GROUP_LIMIT: usize = 256;
pub const WIDTH_LIMIT: u32 = 65_536;
pub const PUBLIC_LIMIT: usize = 65_536;
pub const CHANNEL_LIMIT: usize = 4_096;
pub const ARITY_LIMIT: usize = 64;
pub const CHECK_LIMIT: usize = 4_096;
pub const NAME_LIMIT: usize = 128;
pub const OFFSET_LIMIT: i32 = 65_536;
pub const HEIGHT_LIMIT: u32 = 1 << 20;
pub const COORDINATE_LIMIT: u64 = 1 << 22;
pub const WORK_LIMIT: u64 = 1 << 26;
pub const ANALYSIS_WORK_LIMIT: u64 = 1 << 26;
pub const ANALYSIS_INPUT_LIMIT: u64 = 1 << 22;
pub const CONTRIBUTION_LIMIT: u64 = 1 << 22;
pub const RESULT_RECORD_LIMIT: u64 = 1 << 20;
pub const RESULT_COORDINATE_LIMIT: u64 = 1 << 22;
pub const MULTIPLICITY_LIMIT: u64 = u32::MAX as u64;
pub const PHASE_LIMIT: usize = 16;
pub const SLOT_LIMIT: usize = 4_096;
pub const PREMISE_LIMIT: usize = 4_096;
type Result<T> = std::result::Result<T, Error>;

/// Bound repeated formation scans and retained input facts across all tables.
#[derive(Default)]
struct AnalysisBudget {
    work: u64,
    inputs: u64,
}
impl AnalysisBudget {
    fn account(
        &mut self,
        arena: &Expression,
        traversals: usize,
        retained_outputs: usize,
    ) -> Result<()> {
        let input_count = arena.inputs().len() as u64;
        let scan = arena.nodes().len() as u64 + input_count + 1;
        let traversals = traversals as u64;
        let retained_outputs = retained_outputs as u64;
        if traversals > (ANALYSIS_WORK_LIMIT - self.work) / scan
            || (input_count != 0
                && retained_outputs > (ANALYSIS_INPUT_LIMIT - self.inputs) / input_count)
        {
            return Err(Error("bundle-analysis-limit"));
        }
        self.work += traversals * scan;
        self.inputs += retained_outputs * input_count;
        Ok(())
    }
}

fn is_prime(field: Identity) -> bool {
    field.field_characteristic().is_some() && field != Identity::KoalaBearExt8
}
/// Coordinates per element: `koala-bear.ext8-binomial3` is F_p[X]/(X^8 - 3)
/// in the ascending basis (docs/spec/domains/values.md).
pub fn degree(field: Identity) -> Option<usize> {
    if is_prime(field) {
        Some(1)
    } else if field == Identity::KoalaBearExt8 {
        Some(8)
    } else {
        None
    }
}

fn below_modulus(field: Identity, n: u64) -> bool {
    let (m, n) = (field.field_characteristic().unwrap_or("0"), n.to_string());
    n.len() < m.len() || (n.len() == m.len() && n.as_str() < m)
}
fn identity_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Bounded scan before serde allocation: arrays, strings, canonical naturals,
/// `true`, `false` and `null` only; objects never occur in these carriers.
pub fn parse_json(
    text: &str,
    limit: usize,
    invalid: &'static str,
    too_large: &'static str,
) -> Result<Value> {
    if text.len() > limit {
        return Err(Error(too_large));
    }
    let bytes = text.as_bytes();
    let (mut i, mut depth) = (0, 0usize);
    while i < bytes.len() {
        match bytes[i] {
            b'[' => {
                depth += 1;
                if depth > 16 {
                    return Err(Error(too_large));
                }
                i += 1;
            }
            b']' => {
                depth = depth.checked_sub(1).ok_or(Error(invalid))?;
                i += 1;
            }
            b'"' => {
                i += 1;
                loop {
                    let b = *bytes.get(i).ok_or(Error(invalid))?;
                    i += 1;
                    if b == b'"' {
                        break;
                    }
                    if b == b'\\' {
                        i = i.checked_add(1).ok_or(Error(invalid))?;
                    }
                }
            }
            b'0'..=b'9' => {
                let start = i;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
                if (i - start > 1 && bytes[start] == b'0') || i - start > 20 {
                    return Err(Error(invalid));
                }
            }
            b't' if text[i..].starts_with("true") => i += 4,
            b'f' if text[i..].starts_with("false") => i += 5,
            b'n' if text[i..].starts_with("null") => i += 4,
            b',' | b' ' | b'\r' | b'\n' | b'\t' => i += 1,
            _ => return Err(Error(invalid)),
        }
    }
    if depth != 0 {
        return Err(Error(invalid));
    }
    serde_json::from_str(text).map_err(|_| Error(invalid))
}

fn array<'a>(value: &'a Value, code: &'static str) -> Result<&'a [Value]> {
    value.as_array().map(Vec::as_slice).ok_or(Error(code))
}
fn row<'a>(value: &'a Value, arity: usize, code: &'static str) -> Result<&'a [Value]> {
    let a = array(value, code)?;
    if a.len() != arity {
        return Err(Error(code));
    }
    Ok(a)
}
fn tag(value: &Value) -> Option<&str> {
    value.as_array()?.first()?.as_str()
}
fn natural(value: &Value, limit: u64, code: &'static str) -> Result<u64> {
    value.as_u64().filter(|n| *n <= limit).ok_or(Error(code))
}
fn text(value: &Value, code: &'static str) -> Result<String> {
    value.as_str().map(str::to_owned).ok_or(Error(code))
}
fn field(value: &Value) -> Result<Identity> {
    let name = value.as_str().ok_or(Error("bundle-schema"))?;
    let field = Identity::parse(name).map_err(|_| Error("bundle-field"))?;
    field.field_characteristic().ok_or(Error("bundle-field"))?;
    Ok(field)
}
fn signed_offset(value: &Value) -> Option<i32> {
    let text = value.as_str()?;
    let (negative, digits) = match text.strip_prefix('-') {
        Some(d) => (true, d),
        None => (false, text),
    };
    if digits.is_empty()
        || digits.len() > 6
        || !digits.bytes().all(|b| b.is_ascii_digit())
        || (digits.starts_with('0') && (digits.len() > 1 || negative))
    {
        return None;
    }
    let n: i32 = digits.parse().ok()?;
    (n <= OFFSET_LIMIT).then_some(if negative { -n } else { n })
}
fn valid_name(name: &str) -> bool {
    !name.is_empty() && name.len() <= NAME_LIMIT && !name.bytes().any(|b| b < 0x20 || b == 0x7f)
}
fn unique_names<'a>(names: impl IntoIterator<Item = &'a str>) -> Result<()> {
    let mut seen = BTreeSet::new();
    for name in names {
        if !valid_name(name) {
            return Err(Error("bundle-name"));
        }
        if !seen.insert(name) {
            return Err(Error("bundle-duplicate-name"));
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Authority {
    Witness,
    Config,
    Public,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeightAuthority {
    Fixed,
    Config,
    Instance,
}
/// A fixed height has `min == max`. Every present table has height `>= 1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Height {
    pub authority: HeightAuthority,
    pub min: u32,
    pub max: u32,
    pub power_of_two: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReadModel {
    Finite,
    Cyclic,
}
/// Contiguous row ranges: `Interior(l, r)` is `[l, h - r)`; `Interval(s, e)`
/// is `[s, e)` and requires `e <= h`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scope {
    All,
    First,
    Last,
    Interior(u32, u32),
    Interval(u32, u32),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Group {
    pub name: String,
    pub authority: Authority,
    pub field: Identity,
    pub width: u32,
}
/// Closed binding of one arena input. No challenge, claim or selector input
/// exists in the deterministic relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Input {
    Public(u32),
    Read {
        group: u32,
        offset: i32,
        column: u32,
    },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Assertion {
    pub output: usize,
    pub scope: Scope,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChannelKind {
    FieldBalance,
    Multiset,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Channel {
    pub name: String,
    pub kind: ChannelKind,
    pub tuple: Vec<Identity>,
    pub count: Identity,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Locality {
    Global,
    Local(u32),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    Push,
    Pull,
}
/// `declared` on a field balance is a recorded source premise, never part of
/// satisfaction. A multiset multiplicity must be a natural `<= bound`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Interaction {
    FieldBalance {
        channel: usize,
        locality: Locality,
        scope: Scope,
        tuple: Vec<usize>,
        count: usize,
        declared: Option<u64>,
    },
    Multiset {
        channel: usize,
        locality: Locality,
        scope: Scope,
        side: Side,
        tuple: Vec<usize>,
        multiplicity: usize,
        bound: u64,
    },
}
impl Interaction {
    fn parts(&self) -> (usize, Locality, Scope, &[usize], usize) {
        match self {
            Self::FieldBalance {
                channel,
                locality,
                scope,
                tuple,
                count,
                ..
            } => (*channel, *locality, *scope, tuple, *count),
            Self::Multiset {
                channel,
                locality,
                scope,
                tuple,
                multiplicity,
                ..
            } => (*channel, *locality, *scope, tuple, *multiplicity),
        }
    }
    fn outputs(&self) -> Vec<usize> {
        let (_, _, _, tuple, count) = self.parts();
        let mut outputs = tuple.to_vec();
        outputs.push(count);
        outputs
    }
}
#[derive(Clone, Debug)]
pub struct Table {
    pub name: String,
    pub optional: bool,
    pub height: Height,
    pub read_model: ReadModel,
    pub groups: Vec<Group>,
    pub arena: Expression,
    pub inputs: Vec<Input>,
    pub assertions: Vec<Assertion>,
    pub interactions: Vec<Interaction>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slot {
    pub name: String,
    pub field: Identity,
}
/// Degree weights: public slots 0, every read 1 regardless of authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutputFact {
    pub field: Identity,
    pub degree: u32,
    pub reads: Vec<(u32, i32, u32)>,
    pub publics: Vec<u32>,
}
#[derive(Clone, Debug)]
pub struct Bundle {
    publics: Vec<Slot>,
    channels: Vec<Channel>,
    tables: Vec<Table>,
    facts: Vec<Vec<OutputFact>>,
    identity: String,
}

fn check_scope(scope: Scope) -> Result<()> {
    match scope {
        Scope::Interior(a, b) if a > HEIGHT_LIMIT || b > HEIGHT_LIMIT => Err(Error("bundle-scope")),
        Scope::Interval(a, b) if a > HEIGHT_LIMIT || b > HEIGHT_LIMIT || a > b => {
            Err(Error("bundle-scope"))
        }
        _ => Ok(()),
    }
}
/// Active rows `[lo, hi)` on a present table; Interval's stop is checked first.
pub fn scope_rows(scope: Scope, height: u32) -> (u32, u32) {
    match scope {
        Scope::All => (0, height),
        Scope::First => (0, 1),
        Scope::Last => (height - 1, height),
        Scope::Interior(l, r) if u64::from(l) + u64::from(r) < u64::from(height) => (l, height - r),
        Scope::Interior(..) => (0, 0),
        Scope::Interval(s, e) => (s, e),
    }
}
/// Finite windows undefined at every height on which the scope is nonempty.
fn static_window(scope: Scope, offset: i32) -> bool {
    let o = i64::from(offset);
    match scope {
        Scope::All => o == 0,
        Scope::First => o >= 0,
        Scope::Last => o <= 0,
        Scope::Interior(l, r) => i64::from(l) + o >= 0 && o <= i64::from(r),
        Scope::Interval(s, e) => s >= e || i64::from(s) + o >= 0,
    }
}
fn window_at(scope: Scope, model: ReadModel, height: u32, offsets: &[i32]) -> Result<()> {
    if let Scope::Interval(_, e) = scope
        && e > height
    {
        return Err(Error("bundle-scope-height"));
    }
    if model == ReadModel::Cyclic {
        return Ok(());
    }
    let (lo, hi) = scope_rows(scope, height);
    if lo >= hi {
        return Ok(());
    }
    for &o in offsets {
        if i64::from(lo) + i64::from(o) < 0 || i64::from(hi) + i64::from(o) > i64::from(height) {
            return Err(Error("bundle-window"));
        }
    }
    Ok(())
}
/// Row index of `row + offset` for an admitted window.
pub fn read_row(model: ReadModel, height: u32, row: u32, offset: i32) -> u32 {
    let index = i64::from(row) + i64::from(offset);
    match model {
        ReadModel::Finite => index as u32,
        ReadModel::Cyclic => index.rem_euclid(i64::from(height)) as u32,
    }
}
fn check_height(h: Height) -> Result<()> {
    if h.min < 1
        || h.min > h.max
        || h.max > HEIGHT_LIMIT
        || (h.authority == HeightAuthority::Fixed && (h.min != h.max || h.power_of_two))
        || (h.power_of_two && !(0..=20).any(|k| (h.min..=h.max).contains(&(1u32 << k))))
    {
        return Err(Error("bundle-height"));
    }
    Ok(())
}
/// Every declared input used, every output referenced.
fn check_outputs_used(arena: &Expression, referenced: &[usize]) -> Result<()> {
    let mut used = vec![false; arena.outputs().len()];
    for &p in referenced {
        *used.get_mut(p).ok_or(Error("bundle-output"))? = true;
    }
    if used.iter().any(|u| !u) {
        return Err(Error("bundle-unused-output"));
    }
    let all: Vec<_> = (0..arena.outputs().len()).collect();
    if arena.used_inputs(&all)?.len() != arena.inputs().len() {
        return Err(Error("bundle-unused-input"));
    }
    Ok(())
}

impl Bundle {
    pub fn parse(text: &str) -> Result<Self> {
        Self::decode(&parse_json(
            text,
            BYTE_LIMIT,
            "bundle-schema",
            "bundle-limit",
        )?)
    }
    pub fn publics(&self) -> &[Slot] {
        &self.publics
    }
    pub fn channels(&self) -> &[Channel] {
        &self.channels
    }
    pub fn tables(&self) -> &[Table] {
        &self.tables
    }
    pub fn facts(&self) -> &[Vec<OutputFact>] {
        &self.facts
    }
    /// SHA-256 of the canonical compact encoding; structural identity only.
    pub fn identity(&self) -> &str {
        &self.identity
    }

    pub fn new(publics: Vec<Slot>, channels: Vec<Channel>, tables: Vec<Table>) -> Result<Self> {
        if publics.len() > PUBLIC_LIMIT
            || channels.len() > CHANNEL_LIMIT
            || tables.len() > TABLE_LIMIT
        {
            return Err(Error("bundle-limit"));
        }
        if tables.is_empty() {
            return Err(Error("bundle-tables"));
        }
        if publics.iter().any(|s| degree(s.field).is_none()) {
            return Err(Error("bundle-field"));
        }
        unique_names(publics.iter().map(|s| s.name.as_str()))?;
        for c in &channels {
            if c.tuple.len() > ARITY_LIMIT {
                return Err(Error("bundle-limit"));
            }
            if c.tuple
                .iter()
                .chain([&c.count])
                .any(|f| f.field_characteristic().is_none())
            {
                return Err(Error("bundle-field"));
            }
            if c.kind == ChannelKind::Multiset && !is_prime(c.count) {
                return Err(Error("bundle-multiset-field"));
            }
        }
        unique_names(channels.iter().map(|c| c.name.as_str()))?;
        unique_names(tables.iter().map(|t| t.name.as_str()))?;
        let mut facts = Vec::with_capacity(tables.len());
        let mut analysis_budget = AnalysisBudget::default();
        for table in &tables {
            check_height(table.height)?;
            if table.groups.len() > GROUP_LIMIT {
                return Err(Error("bundle-limit"));
            }
            for g in &table.groups {
                if degree(g.field).is_none() {
                    return Err(Error("bundle-field"));
                }
                if g.width < 1 || g.width > WIDTH_LIMIT {
                    return Err(Error("bundle-width"));
                }
                if g.authority == Authority::Config
                    && table.height.authority == HeightAuthority::Instance
                {
                    return Err(Error("bundle-config-height"));
                }
            }
            unique_names(table.groups.iter().map(|g| g.name.as_str()))?;
            let arena = &table.arena;
            if table.inputs.len() != arena.inputs().len() {
                return Err(Error("bundle-input-count"));
            }
            let mut bindings = BTreeSet::new();
            let mut weights = Vec::with_capacity(table.inputs.len());
            for (i, input) in table.inputs.iter().enumerate() {
                let field = match *input {
                    Input::Public(index) => {
                        weights.push(0);
                        publics
                            .get(index as usize)
                            .ok_or(Error("bundle-input"))?
                            .field
                    }
                    Input::Read {
                        group,
                        offset,
                        column,
                    } => {
                        let g = table
                            .groups
                            .get(group as usize)
                            .ok_or(Error("bundle-input"))?;
                        if column >= g.width || !(-OFFSET_LIMIT..=OFFSET_LIMIT).contains(&offset) {
                            return Err(Error("bundle-input"));
                        }
                        weights.push(1);
                        g.field
                    }
                };
                if arena.inputs()[i] != field {
                    return Err(Error("bundle-input-field"));
                }
                if !bindings.insert(*input) {
                    return Err(Error("bundle-duplicate-input"));
                }
            }
            if table.assertions.len() + table.interactions.len() > CHECK_LIMIT {
                return Err(Error("bundle-limit"));
            }
            let mut referenced = Vec::new();
            for a in &table.assertions {
                check_scope(a.scope)?;
                referenced.push(a.output);
            }
            for i in &table.interactions {
                check_scope(i.parts().2)?;
                referenced.extend(i.outputs());
            }
            analysis_budget.account(
                arena,
                arena.outputs().len() + referenced.len() + 1,
                arena.outputs().len(),
            )?;
            check_outputs_used(arena, &referenced)?;
            let degrees = arena.degrees(&weights)?;
            let mut outputs = Vec::with_capacity(arena.outputs().len());
            for position in 0..arena.outputs().len() {
                let node = arena.outputs()[position];
                let (mut reads, mut publics_used) = (Vec::new(), Vec::new());
                for input in arena.used_inputs(&[position])? {
                    match table.inputs[input] {
                        Input::Public(index) => publics_used.push(index),
                        Input::Read {
                            group,
                            offset,
                            column,
                        } => reads.push((group, offset, column)),
                    }
                }
                reads.sort();
                publics_used.sort();
                outputs.push(OutputFact {
                    field: arena.facts()[node].field,
                    degree: degrees[node],
                    reads,
                    publics: publics_used,
                });
            }
            let static_check = |scope: Scope, positions: &[usize]| -> Result<()> {
                if table.read_model == ReadModel::Cyclic {
                    return Ok(());
                }
                for p in positions {
                    if outputs[*p].reads.iter().any(|r| !static_window(scope, r.1)) {
                        return Err(Error("bundle-window"));
                    }
                }
                Ok(())
            };
            for a in &table.assertions {
                static_check(a.scope, &[a.output])?;
            }
            for interaction in &table.interactions {
                let (channel, locality, scope, tuple, count) = interaction.parts();
                let c = channels.get(channel).ok_or(Error("bundle-channel"))?;
                let kind = match interaction {
                    Interaction::FieldBalance { .. } => ChannelKind::FieldBalance,
                    _ => ChannelKind::Multiset,
                };
                if kind != c.kind {
                    return Err(Error("bundle-interaction-kind"));
                }
                if tuple.len() != c.tuple.len() {
                    return Err(Error("bundle-tuple-arity"));
                }
                if tuple
                    .iter()
                    .zip(&c.tuple)
                    .any(|(p, f)| outputs[*p].field != *f)
                {
                    return Err(Error("bundle-tuple-field"));
                }
                if outputs[count].field != c.count {
                    return Err(Error("bundle-count-field"));
                }
                if let Locality::Local(key) = locality
                    && key as usize > CHECK_LIMIT
                {
                    return Err(Error("bundle-locality"));
                }
                if let Interaction::Multiset { bound, .. } = interaction
                    && (*bound < 1
                        || *bound > MULTIPLICITY_LIMIT
                        || !below_modulus(c.count, *bound))
                {
                    return Err(Error("bundle-multiset-bound"));
                }
                static_check(scope, &interaction.outputs())?;
            }
            facts.push(outputs);
        }
        let mut bundle = Self {
            publics,
            channels,
            tables,
            facts,
            identity: String::new(),
        };
        let canonical = bundle.encode().to_string();
        if canonical.len() > BYTE_LIMIT {
            return Err(Error("bundle-limit"));
        }
        bundle.identity = identity_hex(canonical.as_bytes());
        Ok(bundle)
    }

    pub fn encode(&self) -> Value {
        let scope = encode_scope;
        let locality = |l: Locality| match l {
            Locality::Global => json!(["global"]),
            Locality::Local(k) => json!(["local", k]),
        };
        let tables: Vec<_> = self
            .tables
            .iter()
            .map(|t| {
                let height = match t.height.authority {
                    HeightAuthority::Fixed => json!(["fixed", t.height.min]),
                    HeightAuthority::Config => {
                        json!(["config", t.height.min, t.height.max, t.height.power_of_two])
                    }
                    HeightAuthority::Instance => json!([
                        "instance",
                        t.height.min,
                        t.height.max,
                        t.height.power_of_two
                    ]),
                };
                let groups: Vec<_> = t
                    .groups
                    .iter()
                    .map(|g| {
                        json!([
                            g.name,
                            match g.authority {
                                Authority::Witness => "witness",
                                Authority::Config => "config",
                                Authority::Public => "public",
                            },
                            g.field.name(),
                            g.width
                        ])
                    })
                    .collect();
                let inputs: Vec<_> = t
                    .inputs
                    .iter()
                    .map(|i| match *i {
                        Input::Public(index) => json!(["public", index]),
                        Input::Read {
                            group,
                            offset,
                            column,
                        } => json!(["read", group, offset.to_string(), column]),
                    })
                    .collect();
                let assertions: Vec<_> = t
                    .assertions
                    .iter()
                    .map(|a| json!([a.output, scope(a.scope)]))
                    .collect();
                let interactions: Vec<_> = t
                    .interactions
                    .iter()
                    .map(|i| match i {
                        Interaction::FieldBalance {
                            channel,
                            locality: l,
                            scope: s,
                            tuple,
                            count,
                            declared,
                        } => json!([
                            "field-balance",
                            channel,
                            locality(*l),
                            scope(*s),
                            tuple,
                            count,
                            declared
                        ]),
                        Interaction::Multiset {
                            channel,
                            locality: l,
                            scope: s,
                            side,
                            tuple,
                            multiplicity,
                            bound,
                        } => json!([
                            "multiset",
                            channel,
                            locality(*l),
                            scope(*s),
                            if *side == Side::Push { "push" } else { "pull" },
                            tuple,
                            multiplicity,
                            bound
                        ]),
                    })
                    .collect();
                json!([
                    t.name,
                    if t.optional { "optional" } else { "required" },
                    height,
                    if t.read_model == ReadModel::Cyclic {
                        "cyclic"
                    } else {
                        "finite"
                    },
                    groups,
                    t.arena.encode(),
                    inputs,
                    assertions,
                    interactions
                ])
            })
            .collect();
        let publics: Vec<_> = self
            .publics
            .iter()
            .map(|s| json!([s.name, s.field.name()]))
            .collect();
        let channels: Vec<_> = self
            .channels
            .iter()
            .map(|c| {
                json!([
                    c.name,
                    if c.kind == ChannelKind::Multiset {
                        "multiset"
                    } else {
                        "field-balance"
                    },
                    c.tuple.iter().map(|f| f.name()).collect::<Vec<_>>(),
                    c.count.name()
                ])
            })
            .collect();
        json!(["zkc.relation-bundle/0", publics, channels, tables])
    }

    pub fn decode(value: &Value) -> Result<Self> {
        let root = row(value, 4, "bundle-schema")?;
        if root[0].as_str() != Some("zkc.relation-bundle/0") {
            return Err(Error("bundle-schema"));
        }
        let (publics, channels, tables) = (
            array(&root[1], "bundle-schema")?,
            array(&root[2], "bundle-schema")?,
            array(&root[3], "bundle-schema")?,
        );
        if publics.len() > PUBLIC_LIMIT
            || channels.len() > CHANNEL_LIMIT
            || tables.len() > TABLE_LIMIT
        {
            return Err(Error("bundle-limit"));
        }
        let publics = publics
            .iter()
            .map(|p| {
                let p = row(p, 2, "bundle-schema")?;
                Ok(Slot {
                    name: text(&p[0], "bundle-schema")?,
                    field: field(&p[1])?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let channels = channels
            .iter()
            .map(|c| {
                let c = row(c, 4, "bundle-schema")?;
                let kind = match c[1].as_str() {
                    Some("field-balance") => ChannelKind::FieldBalance,
                    Some("multiset") => ChannelKind::Multiset,
                    _ => return Err(Error("bundle-schema")),
                };
                let tuple = array(&c[2], "bundle-schema")?;
                if tuple.len() > ARITY_LIMIT {
                    return Err(Error("bundle-limit"));
                }
                Ok(Channel {
                    name: text(&c[0], "bundle-schema")?,
                    kind,
                    tuple: tuple.iter().map(field).collect::<Result<_>>()?,
                    count: field(&c[3])?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let tables = tables
            .iter()
            .map(decode_table)
            .collect::<Result<Vec<_>>>()?;
        Self::new(publics, channels, tables)
    }
}

fn encode_scope(scope: Scope) -> Value {
    match scope {
        Scope::All => json!(["all"]),
        Scope::First => json!(["first"]),
        Scope::Last => json!(["last"]),
        Scope::Interior(l, r) => json!(["interior", l, r]),
        Scope::Interval(s, e) => json!(["interval", s, e]),
    }
}
fn decode_scope(value: &Value) -> Result<Scope> {
    let a = array(value, "bundle-scope")?;
    let scope = match (tag(value), a.len()) {
        (Some("all"), 1) => Scope::All,
        (Some("first"), 1) => Scope::First,
        (Some("last"), 1) => Scope::Last,
        (Some(t @ ("interior" | "interval")), 3) => {
            let first = natural(&a[1], HEIGHT_LIMIT.into(), "bundle-scope")? as u32;
            let second = natural(&a[2], HEIGHT_LIMIT.into(), "bundle-scope")? as u32;
            if t == "interior" {
                Scope::Interior(first, second)
            } else {
                Scope::Interval(first, second)
            }
        }
        _ => return Err(Error("bundle-scope")),
    };
    check_scope(scope)?;
    Ok(scope)
}
fn decode_locality(value: &Value) -> Result<Locality> {
    match (tag(value), value.as_array().map(Vec::len)) {
        (Some("global"), Some(1)) => Ok(Locality::Global),
        (Some("local"), Some(2)) => {
            Ok(Locality::Local(
                natural(&value[1], CHECK_LIMIT as u64, "bundle-locality")? as u32,
            ))
        }
        _ => Err(Error("bundle-locality")),
    }
}
fn positions(value: &Value, limit: usize) -> Result<Vec<usize>> {
    let a = array(value, "bundle-schema")?;
    if a.len() > limit {
        return Err(Error("bundle-schema"));
    }
    a.iter()
        .map(|p| natural(p, u32::MAX.into(), "bundle-schema").map(|p| p as usize))
        .collect()
}
fn decode_interaction(value: &Value) -> Result<Interaction> {
    let a = array(value, "bundle-schema")?;
    let multiset = match (tag(value), a.len()) {
        (Some("field-balance"), 7) => false,
        (Some("multiset"), 8) => true,
        _ => return Err(Error("bundle-interaction-kind")),
    };
    let channel = natural(&a[1], CHANNEL_LIMIT as u64, "bundle-channel")? as usize;
    let locality = decode_locality(&a[2])?;
    let scope = decode_scope(&a[3])?;
    if multiset {
        let side = match a[4].as_str() {
            Some("push") => Side::Push,
            Some("pull") => Side::Pull,
            _ => return Err(Error("bundle-side")),
        };
        let tuple = positions(&a[5], ARITY_LIMIT)?;
        let multiplicity = natural(&a[6], u32::MAX.into(), "bundle-schema")? as usize;
        let bound = a[7].as_u64().ok_or(Error("bundle-multiset-bound"))?;
        return Ok(Interaction::Multiset {
            channel,
            locality,
            scope,
            side,
            tuple,
            multiplicity,
            bound,
        });
    }
    let tuple = positions(&a[4], ARITY_LIMIT)?;
    let count = natural(&a[5], u32::MAX.into(), "bundle-schema")? as usize;
    let declared = if a[6].is_null() {
        None
    } else {
        Some(a[6].as_u64().ok_or(Error("bundle-schema"))?)
    };
    Ok(Interaction::FieldBalance {
        channel,
        locality,
        scope,
        tuple,
        count,
        declared,
    })
}
fn decode_table(value: &Value) -> Result<Table> {
    let a = row(value, 9, "bundle-schema")?;
    let name = text(&a[0], "bundle-schema")?;
    let optional = match a[1].as_str() {
        Some("required") => false,
        Some("optional") => true,
        _ => return Err(Error("bundle-schema")),
    };
    let read_model = match a[3].as_str() {
        Some("finite") => ReadModel::Finite,
        Some("cyclic") => ReadModel::Cyclic,
        _ => return Err(Error("bundle-schema")),
    };
    let (groups, inputs, assertions, interactions) = (
        array(&a[4], "bundle-schema")?,
        array(&a[6], "bundle-schema")?,
        array(&a[7], "bundle-schema")?,
        array(&a[8], "bundle-schema")?,
    );
    if groups.len() > GROUP_LIMIT
        || inputs.len() > crate::ring::NODE_LIMIT
        || assertions.len() + interactions.len() > CHECK_LIMIT
    {
        return Err(Error("bundle-limit"));
    }
    let h = array(&a[2], "bundle-height")?;
    let height = match (tag(&a[2]), h.len()) {
        (Some("fixed"), 2) => {
            let n = natural(&h[1], HEIGHT_LIMIT.into(), "bundle-height")? as u32;
            Height {
                authority: HeightAuthority::Fixed,
                min: n,
                max: n,
                power_of_two: false,
            }
        }
        (Some(t @ ("config" | "instance")), 4) => Height {
            authority: if t == "config" {
                HeightAuthority::Config
            } else {
                HeightAuthority::Instance
            },
            min: natural(&h[1], HEIGHT_LIMIT.into(), "bundle-height")? as u32,
            max: natural(&h[2], HEIGHT_LIMIT.into(), "bundle-height")? as u32,
            power_of_two: h[3].as_bool().ok_or(Error("bundle-height"))?,
        },
        _ => return Err(Error("bundle-height")),
    };
    let arena = Expression::decode(&a[5])?;
    let groups = groups
        .iter()
        .map(|g| {
            let g = row(g, 4, "bundle-schema")?;
            let authority = match g[1].as_str() {
                Some("witness") => Authority::Witness,
                Some("config") => Authority::Config,
                Some("public") => Authority::Public,
                _ => return Err(Error("bundle-schema")),
            };
            Ok(Group {
                name: text(&g[0], "bundle-schema")?,
                authority,
                field: field(&g[2])?,
                width: natural(&g[3], WIDTH_LIMIT.into(), "bundle-schema")? as u32,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let inputs = inputs
        .iter()
        .map(|i| match (tag(i), i.as_array().map(Vec::len)) {
            (Some("public"), Some(2)) => {
                Ok(Input::Public(
                    natural(&i[1], PUBLIC_LIMIT as u64, "bundle-input")? as u32,
                ))
            }
            (Some("read"), Some(4)) => Ok(Input::Read {
                group: natural(&i[1], GROUP_LIMIT as u64, "bundle-input")? as u32,
                offset: signed_offset(&i[2]).ok_or(Error("bundle-input"))?,
                column: natural(&i[3], WIDTH_LIMIT.into(), "bundle-input")? as u32,
            }),
            _ => Err(Error("bundle-input-kind")),
        })
        .collect::<Result<Vec<_>>>()?;
    let assertions = assertions
        .iter()
        .map(|x| {
            let x = row(x, 2, "bundle-schema")?;
            Ok(Assertion {
                output: natural(&x[0], u32::MAX.into(), "bundle-schema")? as usize,
                scope: decode_scope(&x[1])?,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let interactions = interactions
        .iter()
        .map(decode_interaction)
        .collect::<Result<Vec<_>>>()?;
    Ok(Table {
        name,
        optional,
        height,
        read_model,
        groups,
        arena,
        inputs,
        assertions,
        interactions,
    })
}

/// Canonical base coordinates: one per prime-field element, `degree` per
/// extension element, flattened row-major per group.
pub type Columns = Vec<String>;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Configuration {
    pub relation: String,
    pub tables: Vec<(Option<u32>, Vec<Columns>)>,
}
/// `None` marks an absent table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instance {
    pub relation: String,
    pub publics: Vec<Columns>,
    pub tables: Vec<Option<(Option<u32>, Vec<Columns>)>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Witness {
    pub relation: String,
    pub tables: Vec<Option<Vec<Columns>>>,
}

fn read_value(value: &Value, field: Identity, out: &mut Columns) -> Result<()> {
    if degree(field) == Some(1) {
        out.push(value.as_str().ok_or(Error("bundle-value"))?.to_owned());
        return Ok(());
    }
    let a = value
        .as_array()
        .filter(|a| Some(a.len()) == degree(field))
        .ok_or(Error("bundle-value"))?;
    for c in a {
        out.push(c.as_str().ok_or(Error("bundle-value"))?.to_owned());
    }
    Ok(())
}
fn encode_value(coordinates: &[String]) -> Value {
    if coordinates.len() == 1 {
        json!(coordinates[0])
    } else {
        json!(coordinates)
    }
}
fn read_group(value: &Value, field: Identity, budget: &mut u64) -> Result<Columns> {
    let a = array(value, "bundle-data-shape")?;
    let d = degree(field).ok_or(Error("bundle-field"))? as u64;
    let need = a.len() as u64 * d;
    if need > *budget {
        return Err(Error("bundle-data-limit"));
    }
    *budget -= need;
    let mut out = Vec::with_capacity(need as usize);
    for v in a {
        read_value(v, field, &mut out)?;
    }
    Ok(out)
}
fn encode_group(columns: &[String], field: Identity) -> Value {
    Value::Array(
        columns
            .chunks(degree(field).unwrap_or(1))
            .map(encode_value)
            .collect(),
    )
}
fn read_height(value: &Value) -> Result<Option<u32>> {
    if value.is_null() {
        return Ok(None);
    }
    Ok(Some(
        natural(value, HEIGHT_LIMIT.into(), "bundle-height")? as u32
    ))
}

impl Table {
    fn groups_with(&self, authority: Authority) -> impl Iterator<Item = (usize, &Group)> {
        self.groups
            .iter()
            .enumerate()
            .filter(move |(_, g)| g.authority == authority)
    }
    fn read_groups(
        &self,
        value: &Value,
        authority: Authority,
        budget: &mut u64,
    ) -> Result<Vec<Columns>> {
        let a = array(value, "bundle-data-schema")?;
        let groups: Vec<_> = self.groups_with(authority).collect();
        if a.len() != groups.len() {
            return Err(Error("bundle-group-count"));
        }
        groups
            .iter()
            .zip(a)
            .map(|((_, g), v)| read_group(v, g.field, budget))
            .collect()
    }
    fn encode_groups(&self, authority: Authority, groups: &[Columns]) -> Value {
        let fields: Vec<_> = self.groups_with(authority).map(|(_, g)| g.field).collect();
        Value::Array(
            groups
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    encode_group(c, fields.get(i).copied().unwrap_or(Identity::KoalaBear))
                })
                .collect(),
        )
    }
}

impl Bundle {
    fn data_root<'a>(
        &self,
        value: &'a Value,
        arity: usize,
        tag_name: &str,
    ) -> Result<(String, &'a [Value])> {
        let root = row(value, arity, "bundle-data-schema")?;
        if root[0].as_str() != Some(tag_name) {
            return Err(Error("bundle-data-schema"));
        }
        let tables = array(&root[arity - 1], "bundle-data-schema")?;
        if tables.len() != self.tables.len() {
            return Err(Error("bundle-data-schema"));
        }
        Ok((text(&root[1], "bundle-data-schema")?, tables))
    }
    pub fn decode_configuration(&self, value: &Value) -> Result<Configuration> {
        let (relation, rows) = self.data_root(value, 3, "zkc.relation-configuration/0")?;
        let mut budget = COORDINATE_LIMIT;
        let tables = self
            .tables
            .iter()
            .zip(rows)
            .map(|(t, v)| {
                let v = row(v, 2, "bundle-data-schema")?;
                Ok((
                    read_height(&v[0])?,
                    t.read_groups(&v[1], Authority::Config, &mut budget)?,
                ))
            })
            .collect::<Result<_>>()?;
        Ok(Configuration { relation, tables })
    }
    pub fn decode_instance(&self, value: &Value) -> Result<Instance> {
        let (relation, rows) = self.data_root(value, 4, "zkc.relation-instance/0")?;
        let values = array(&value[2], "bundle-public-shape")?;
        if values.len() != self.publics.len() {
            return Err(Error("bundle-public-shape"));
        }
        let publics = self
            .publics
            .iter()
            .zip(values)
            .map(|(s, v)| {
                let mut out = Vec::new();
                read_value(v, s.field, &mut out).map(|()| out)
            })
            .collect::<Result<_>>()?;
        let mut budget = COORDINATE_LIMIT;
        let tables = self
            .tables
            .iter()
            .zip(rows)
            .map(|(t, v)| match (tag(v), v.as_array().map(Vec::len)) {
                (Some("absent"), Some(1)) => Ok(None),
                (Some("present"), Some(3)) => Ok(Some((
                    read_height(&v[1])?,
                    t.read_groups(&v[2], Authority::Public, &mut budget)?,
                ))),
                _ => Err(Error("bundle-data-schema")),
            })
            .collect::<Result<_>>()?;
        Ok(Instance {
            relation,
            publics,
            tables,
        })
    }
    pub fn decode_witness(&self, value: &Value) -> Result<Witness> {
        let (relation, rows) = self.data_root(value, 3, "zkc.relation-witness/0")?;
        let mut budget = COORDINATE_LIMIT;
        let tables = self
            .tables
            .iter()
            .zip(rows)
            .map(|(t, v)| {
                if v.is_null() {
                    Ok(None)
                } else {
                    t.read_groups(v, Authority::Witness, &mut budget).map(Some)
                }
            })
            .collect::<Result<_>>()?;
        Ok(Witness { relation, tables })
    }
    pub fn encode_configuration(&self, c: &Configuration) -> Value {
        let tables: Vec<_> = self
            .tables
            .iter()
            .zip(&c.tables)
            .map(|(t, (h, g))| json!([h, t.encode_groups(Authority::Config, g)]))
            .collect();
        json!(["zkc.relation-configuration/0", c.relation, tables])
    }
    pub fn encode_instance(&self, i: &Instance) -> Value {
        let tables: Vec<_> = self
            .tables
            .iter()
            .zip(&i.tables)
            .map(|(t, e)| match e {
                None => json!(["absent"]),
                Some((h, g)) => json!(["present", h, t.encode_groups(Authority::Public, g)]),
            })
            .collect();
        let publics: Vec<_> = i.publics.iter().map(|v| encode_value(v)).collect();
        json!(["zkc.relation-instance/0", i.relation, publics, tables])
    }
    pub fn encode_witness(&self, w: &Witness) -> Value {
        let tables: Vec<_> = self
            .tables
            .iter()
            .zip(&w.tables)
            .map(|(t, e)| match e {
                None => Value::Null,
                Some(g) => t.encode_groups(Authority::Witness, g),
            })
            .collect();
        json!(["zkc.relation-witness/0", w.relation, tables])
    }

    /// Shape, presence, height authority, every read domain and resource
    /// preflight, then canonical values. No arithmetic is performed.
    pub fn admit(
        &self,
        config: &Configuration,
        instance: &Instance,
        witness: &Witness,
    ) -> Result<Admitted> {
        if [&config.relation, &instance.relation, &witness.relation]
            .iter()
            .any(|r| r.as_str() != self.identity)
        {
            return Err(Error("bundle-relation"));
        }
        let n = self.tables.len();
        if config.tables.len() != n || instance.tables.len() != n || witness.tables.len() != n {
            return Err(Error("bundle-data-shape"));
        }
        if instance.publics.len() != self.publics.len() {
            return Err(Error("bundle-public-shape"));
        }
        let mut admitted = Admitted {
            present: vec![false; n],
            heights: vec![0; n],
            work: 0,
        };
        let mut coordinates = 0u64;
        for slot in &self.publics {
            coordinates += degree(slot.field).ok_or(Error("bundle-field"))? as u64;
        }
        for (t, table) in self.tables.iter().enumerate() {
            let (cfg_height, cfg_groups) = &config.tables[t];
            let present = instance.tables[t].is_some();
            if !present && !table.optional {
                return Err(Error("bundle-table-missing"));
            }
            if present != witness.tables[t].is_some() {
                return Err(Error("bundle-witness-presence"));
            }
            let ins_height = instance.tables[t].as_ref().and_then(|e| e.0);
            let (height, config_height) = match table.height.authority {
                HeightAuthority::Fixed => {
                    if cfg_height.is_some() || ins_height.is_some() {
                        return Err(Error("bundle-height-authority"));
                    }
                    (table.height.min, table.height.min)
                }
                HeightAuthority::Config => {
                    let h = cfg_height.ok_or(Error("bundle-height-authority"))?;
                    if ins_height.is_some() {
                        return Err(Error("bundle-height-authority"));
                    }
                    (h, h)
                }
                HeightAuthority::Instance => {
                    if cfg_height.is_some() || (present && ins_height.is_none()) {
                        return Err(Error("bundle-height-authority"));
                    }
                    (if present { ins_height.unwrap_or(0) } else { 0 }, 0)
                }
            };
            let checked = table.height.authority != HeightAuthority::Instance || present;
            if checked
                && (height < table.height.min
                    || height > table.height.max
                    || (table.height.power_of_two && !height.is_power_of_two()))
            {
                return Err(Error("bundle-height"));
            }
            let config_groups: Vec<_> = table.groups_with(Authority::Config).collect();
            let public_groups: Vec<_> = table.groups_with(Authority::Public).collect();
            let witness_groups: Vec<_> = table.groups_with(Authority::Witness).collect();
            let public_data = instance.tables[t].as_ref().map(|e| &e.1);
            if cfg_groups.len() != config_groups.len()
                || (present
                    && (public_data.map_or(0, Vec::len) != public_groups.len()
                        || witness.tables[t].as_ref().map_or(0, Vec::len) != witness_groups.len()))
            {
                return Err(Error("bundle-group-count"));
            }
            let mut check =
                |groups: &[(usize, &Group)], data: &[Columns], rows: u32| -> Result<()> {
                    for ((_, g), c) in groups.iter().zip(data) {
                        let d = degree(g.field).ok_or(Error("bundle-field"))? as u64;
                        // The declared shape is bounded before data lengths.
                        let expected = u64::from(rows) * u64::from(g.width) * d;
                        coordinates += expected;
                        if coordinates > COORDINATE_LIMIT {
                            return Err(Error("bundle-data-limit"));
                        }
                        if c.len() as u64 != expected {
                            return Err(Error("bundle-group-shape"));
                        }
                    }
                    Ok(())
                };
            check(&config_groups, cfg_groups, config_height)?;
            if let (Some(p), Some(w)) = (public_data, &witness.tables[t]) {
                check(&public_groups, p, height)?;
                check(&witness_groups, w, height)?;
            }
            admitted.present[t] = present;
            admitted.heights[t] = if present { height } else { 0 };
        }
        let (mut work, mut contributions, mut result_records, mut result_coordinates) =
            (0u64, 0u64, 0u64, 0u64);
        for (t, table) in self.tables.iter().enumerate() {
            if !admitted.present[t] {
                continue;
            }
            let height = admitted.heights[t];
            let offsets = |outputs: &[usize]| -> Vec<i32> {
                outputs
                    .iter()
                    .flat_map(|p| self.facts[t][*p].reads.iter().map(|r| r.1))
                    .collect()
            };
            for a in &table.assertions {
                window_at(a.scope, table.read_model, height, &offsets(&[a.output]))?;
                let (lo, hi) = scope_rows(a.scope, height);
                let rows = u64::from(hi.saturating_sub(lo));
                result_records += rows;
                result_coordinates += rows
                    * degree(self.facts[t][a.output].field).ok_or(Error("bundle-field"))? as u64;
            }
            for i in &table.interactions {
                let scope = i.parts().2;
                window_at(scope, table.read_model, height, &offsets(&i.outputs()))?;
                let (lo, hi) = scope_rows(scope, height);
                contributions += u64::from(hi.saturating_sub(lo));
                let width = i.outputs().iter().try_fold(0u64, |sum, p| -> Result<u64> {
                    Ok(sum + degree(self.facts[t][*p].field).ok_or(Error("bundle-field"))? as u64)
                })?;
                result_records += u64::from(hi.saturating_sub(lo));
                result_coordinates += u64::from(hi.saturating_sub(lo)) * width;
            }
            let checks = table.assertions.len() + table.interactions.len();
            if checks > 0 {
                work += u64::from(height)
                    * (table.arena.nodes().len() + table.arena.inputs().len() + checks + 1) as u64;
            }
            if work > WORK_LIMIT {
                return Err(Error("bundle-work-limit"));
            }
            if contributions > CONTRIBUTION_LIMIT {
                return Err(Error("bundle-contribution-limit"));
            }
            if result_records > RESULT_RECORD_LIMIT || result_coordinates > RESULT_COORDINATE_LIMIT
            {
                return Err(Error("bundle-result-limit"));
            }
        }
        admitted.work = work;
        for (s, v) in self.publics.iter().zip(&instance.publics) {
            if v.len() != degree(s.field).unwrap_or(0)
                || !v.iter().all(|c| s.field.canonical_field_literal(c))
            {
                return Err(Error("bundle-value"));
            }
        }
        for (t, table) in self.tables.iter().enumerate() {
            let mut next = [0usize; 3];
            for g in &table.groups {
                let data = match g.authority {
                    Authority::Config => {
                        next[0] += 1;
                        Some(&config.tables[t].1[next[0] - 1])
                    }
                    Authority::Public => instance.tables[t].as_ref().map(|e| {
                        next[1] += 1;
                        &e.1[next[1] - 1]
                    }),
                    Authority::Witness => witness.tables[t].as_ref().map(|w| {
                        next[2] += 1;
                        &w[next[2] - 1]
                    }),
                };
                if let Some(data) = data
                    && !data.iter().all(|c| g.field.canonical_field_literal(c))
                {
                    return Err(Error("bundle-value"));
                }
            }
        }
        Ok(admitted)
    }
}

/// Admitted presence and heights, with the reference evaluator's work bound.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Admitted {
    pub present: Vec<bool>,
    pub heights: Vec<u32>,
    pub work: u64,
}

/// Field arithmetic supplied to the reference semantics. Values are already
/// canonical when `value` is called; `coordinates` returns canonical text.
pub trait Algebra {
    type Value: Clone;
    fn value(&self, field: Identity, coordinates: &[String]) -> Result<Self::Value>;
    fn constant(&self, field: Identity, literal: &str) -> Result<Self::Value>;
    fn add(&self, field: Identity, a: &Self::Value, b: &Self::Value) -> Self::Value;
    fn mul(&self, field: Identity, a: &Self::Value, b: &Self::Value) -> Self::Value;
    fn neg(&self, field: Identity, a: &Self::Value) -> Self::Value;
    fn embed(&self, from: Identity, to: Identity, a: &Self::Value) -> Result<Self::Value>;
    fn coordinates(&self, field: Identity, a: &Self::Value) -> Vec<String>;
}
fn is_zero(coordinates: &[String]) -> bool {
    coordinates.iter().all(|c| c == "0")
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Residual {
    pub table: usize,
    pub assertion: usize,
    pub row: u32,
    pub value: Columns,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Balance {
    pub kind: ChannelKind,
    pub channel: usize,
    pub local: Option<(usize, u32)>,
    pub tuple: Vec<Columns>,
    pub sum: Columns,
    pub push: u64,
    pub pull: u64,
    pub balanced: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evaluation {
    pub satisfied: bool,
    pub work: u64,
    pub residuals: Vec<Residual>,
    pub balances: Vec<Balance>,
    pub range_failures: Vec<(usize, usize, u32)>,
}

/// Interpret a selected arena for one row: nodes in order, inputs fetched once.
fn interpret<A: Algebra>(
    arena: &Expression,
    algebra: &A,
    fetch: &mut dyn FnMut(usize) -> Result<A::Value>,
) -> Result<Vec<A::Value>> {
    let mut values: Vec<A::Value> = Vec::with_capacity(arena.nodes().len());
    let mut inputs: BTreeMap<usize, A::Value> = BTreeMap::new();
    for (i, node) in arena.nodes().iter().enumerate() {
        let field = arena.facts()[i].field;
        let v = match node {
            Node::Constant(f, literal) => algebra.constant(*f, literal)?,
            Node::Input(j) => match inputs.get(j) {
                Some(v) => v.clone(),
                None => {
                    let v = fetch(*j)?;
                    inputs.insert(*j, v.clone());
                    v
                }
            },
            Node::Add(a, b) => algebra.add(field, &values[*a], &values[*b]),
            Node::Mul(a, b) => algebra.mul(field, &values[*a], &values[*b]),
            Node::Neg(a) => algebra.neg(field, &values[*a]),
            Node::Embed(to, a) => algebra.embed(arena.facts()[*a].field, *to, &values[*a])?,
        };
        values.push(v);
    }
    Ok(arena.outputs().iter().map(|o| values[*o].clone()).collect())
}

type BalanceKey = (usize, Option<(usize, u32)>, String);

/// Element `(row, column)` of a row-major group of canonical coordinates.
fn element<A: Algebra>(
    algebra: &A,
    field: Identity,
    width: u32,
    columns: &[String],
    row: u32,
    column: u32,
) -> Result<A::Value> {
    let d = degree(field).expect("admitted field");
    let base = (row as usize * width as usize + column as usize) * d;
    algebra.value(field, &columns[base..base + d])
}

impl Bundle {
    /// Columns of every group of an admitted present table, in group order,
    /// each from the carrier with authority over it.
    fn present_groups<'a>(
        &self,
        t: usize,
        config: &'a Configuration,
        instance: &'a Instance,
        witness: &'a Witness,
    ) -> Vec<&'a Columns> {
        let mut next = [0usize; 3];
        self.tables[t]
            .groups
            .iter()
            .map(|g| match g.authority {
                Authority::Config => {
                    next[0] += 1;
                    &config.tables[t].1[next[0] - 1]
                }
                Authority::Public => {
                    next[1] += 1;
                    &instance.tables[t].as_ref().expect("present").1[next[1] - 1]
                }
                Authority::Witness => {
                    next[2] += 1;
                    &witness.tables[t].as_ref().expect("present")[next[2] - 1]
                }
            })
            .collect()
    }

    /// Admission followed by the reference interpretation of every assertion,
    /// field-weighted balance and natural multiset equality.
    pub fn evaluate<A: Algebra>(
        &self,
        config: &Configuration,
        instance: &Instance,
        witness: &Witness,
        algebra: &A,
    ) -> Result<Evaluation> {
        let admitted = self.admit(config, instance, witness)?;
        let publics = self
            .publics
            .iter()
            .zip(&instance.publics)
            .map(|(s, v)| algebra.value(s.field, v))
            .collect::<Result<Vec<_>>>()?;
        let mut result = Evaluation {
            satisfied: true,
            work: admitted.work,
            residuals: vec![],
            balances: vec![],
            range_failures: vec![],
        };
        let mut balances: BTreeMap<BalanceKey, (Balance, Option<A::Value>)> = BTreeMap::new();
        for (t, table) in self.tables.iter().enumerate() {
            if !admitted.present[t] {
                continue;
            }
            let height = admitted.heights[t];
            let groups = self.present_groups(t, config, instance, witness);
            // Rows split into segments over which the active checks are fixed.
            let mut cuts = BTreeSet::from([0, height]);
            let ranges: Vec<(bool, usize, (u32, u32))> = table
                .assertions
                .iter()
                .enumerate()
                .map(|(i, a)| (true, i, scope_rows(a.scope, height)))
                .chain(
                    table
                        .interactions
                        .iter()
                        .enumerate()
                        .map(|(i, x)| (false, i, scope_rows(x.parts().2, height))),
                )
                .collect();
            for (_, _, (lo, hi)) in &ranges {
                if lo < hi {
                    cuts.insert(*lo);
                    cuts.insert(*hi);
                }
            }
            let cuts: Vec<_> = cuts.into_iter().collect();
            let mut residuals: Vec<Vec<Residual>> = vec![vec![]; table.assertions.len()];
            for segment in cuts.windows(2) {
                let (from, to) = (segment[0], segment[1]);
                let active: Vec<_> = ranges
                    .iter()
                    .filter(|(_, _, (lo, hi))| lo < hi && *lo <= from && to <= *hi)
                    .collect();
                if active.is_empty() {
                    continue;
                }
                let needed: BTreeSet<usize> = active
                    .iter()
                    .flat_map(|(assertion, i, _)| {
                        if *assertion {
                            vec![table.assertions[*i].output]
                        } else {
                            table.interactions[*i].outputs()
                        }
                    })
                    .collect();
                let positions: Vec<usize> = needed.into_iter().collect();
                let selected = table.arena.select(&positions)?;
                let slot =
                    |output: usize| positions.binary_search(&output).expect("selected output");
                for r in from..to {
                    let mut fetch = |input: usize| -> Result<A::Value> {
                        match table.inputs[input] {
                            Input::Public(index) => Ok(publics[index as usize].clone()),
                            Input::Read {
                                group,
                                offset,
                                column,
                            } => {
                                let g = &table.groups[group as usize];
                                element(
                                    algebra,
                                    g.field,
                                    g.width,
                                    groups[group as usize],
                                    read_row(table.read_model, height, r, offset),
                                    column,
                                )
                            }
                        }
                    };
                    let values = interpret(&selected, algebra, &mut fetch)?;
                    for (assertion, index, _) in &active {
                        if *assertion {
                            let a = &table.assertions[*index];
                            let value = algebra.coordinates(
                                self.facts[t][a.output].field,
                                &values[slot(a.output)],
                            );
                            result.satisfied &= is_zero(&value);
                            residuals[*index].push(Residual {
                                table: t,
                                assertion: *index,
                                row: r,
                                value,
                            });
                            continue;
                        }
                        let interaction = &table.interactions[*index];
                        let (channel, locality, _, tuple, count) = interaction.parts();
                        let c = &self.channels[channel];
                        let tuple: Vec<Columns> = tuple
                            .iter()
                            .zip(&c.tuple)
                            .map(|(p, f)| algebra.coordinates(*f, &values[slot(*p)]))
                            .collect();
                        let local = match locality {
                            Locality::Global => None,
                            Locality::Local(k) => Some((t, k)),
                        };
                        let key = (
                            channel,
                            local,
                            json!(tuple.iter().map(|v| encode_value(v)).collect::<Vec<_>>())
                                .to_string(),
                        );
                        let entry = balances.entry(key).or_insert_with(|| {
                            (
                                Balance {
                                    kind: c.kind,
                                    channel,
                                    local,
                                    tuple: tuple.clone(),
                                    sum: vec![],
                                    push: 0,
                                    pull: 0,
                                    balanced: true,
                                },
                                None,
                            )
                        });
                        let value = &values[slot(count)];
                        match interaction {
                            Interaction::FieldBalance { .. } => {
                                entry.1 = Some(match &entry.1 {
                                    Some(s) => algebra.add(c.count, s, value),
                                    None => value.clone(),
                                });
                            }
                            Interaction::Multiset { side, bound, .. } => {
                                let n = algebra.coordinates(c.count, value)[0]
                                    .parse::<u64>()
                                    .ok()
                                    .filter(|n| n <= bound);
                                let Some(n) = n else {
                                    result.satisfied = false;
                                    result.range_failures.push((t, *index, r));
                                    continue;
                                };
                                if *side == Side::Push {
                                    entry.0.push += n
                                } else {
                                    entry.0.pull += n
                                }
                            }
                        }
                    }
                }
            }
            result.residuals.extend(residuals.into_iter().flatten());
        }
        for (_, (mut balance, sum)) in balances {
            if balance.kind == ChannelKind::FieldBalance {
                let count = self.channels[balance.channel].count;
                balance.sum = sum.map_or_else(
                    || vec!["0".into(); degree(count).unwrap_or(1)],
                    |s| algebra.coordinates(count, &s),
                );
                balance.balanced = is_zero(&balance.sum);
            } else {
                balance.balanced = balance.push == balance.pull;
            }
            result.satisfied &= balance.balanced;
            result.balances.push(balance);
        }
        Ok(result)
    }
}

/// Inputs of a staged arena. Read phase 0 is the bundle's own groups.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum StagedInput {
    Public(u32),
    Read {
        phase: u32,
        group: u32,
        offset: i32,
        column: u32,
    },
    Challenge {
        phase: u32,
        index: u32,
    },
    Claim {
        phase: u32,
        index: u32,
    },
}
#[derive(Clone, Debug)]
pub struct StagedTable {
    pub groups: Vec<(String, Identity, u32)>,
    pub arena: Expression,
    pub inputs: Vec<StagedInput>,
    pub assertions: Vec<Assertion>,
}
#[derive(Clone, Debug)]
pub struct StagedPhase {
    pub challenges: Vec<Slot>,
    pub claims: Vec<Slot>,
    pub tables: Vec<StagedTable>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Premise {
    Boolean {
        phase: u32,
        table: u32,
        output: usize,
        scope: Scope,
    },
    AtMostOne {
        phase: u32,
        table: u32,
        outputs: Vec<usize>,
        scope: Scope,
    },
    Nonzero {
        phase: u32,
        table: u32,
        output: usize,
        scope: Scope,
    },
    CharacteristicExceeds {
        field: Identity,
        bound: u64,
    },
}
/// A challenge-indexed predicate over a bundle's data. Its premises are
/// recorded assumptions; it never changes the bundle relation.
#[derive(Clone, Debug)]
pub struct Staged {
    relation: String,
    phases: Vec<StagedPhase>,
    global: (Expression, Vec<StagedInput>, Vec<usize>),
    premises: Vec<Premise>,
    identity: String,
}

impl Staged {
    pub fn phases(&self) -> &[StagedPhase] {
        &self.phases
    }
    pub fn premises(&self) -> &[Premise] {
        &self.premises
    }
    pub fn identity(&self) -> &str {
        &self.identity
    }

    pub fn parse(bundle: &Bundle, text: &str) -> Result<Self> {
        Self::decode(
            bundle,
            &parse_json(text, BYTE_LIMIT, "staged-schema", "staged-limit")?,
        )
    }
    /// Carrier shapes in reading order before formation: the root, then per
    /// phase its slots and per table its arena, bindings, groups and
    /// assertions, then the global arena and premises.
    pub fn decode(bundle: &Bundle, value: &Value) -> Result<Self> {
        let root = row(value, 5, "staged-schema")?;
        if root[0].as_str() != Some("zkc.relation-staged/0") {
            return Err(Error("staged-schema"));
        }
        let relation = root[1].as_str().ok_or(Error("staged-schema"))?;
        let (phases, g, premises) = (
            array(&root[2], "staged-schema")?,
            row(&root[3], 3, "staged-schema")?,
            array(&root[4], "staged-schema")?,
        );
        if relation != bundle.identity() {
            return Err(Error("bundle-relation"));
        }
        if phases.len() > PHASE_LIMIT || premises.len() > PREMISE_LIMIT {
            return Err(Error("staged-limit"));
        }
        // A non-string field is a carrier shape error; an unknown one is a
        // formation refusal.
        let staged_field = |v: &Value| {
            v.as_str().ok_or(Error("staged-schema"))?;
            field(v)
        };
        let slots = |v: &Value| -> Result<Vec<Slot>> {
            let a = array(v, "staged-schema")?;
            if a.len() > SLOT_LIMIT {
                return Err(Error("staged-schema"));
            }
            a.iter()
                .map(|s| {
                    let s = row(s, 2, "staged-schema")?;
                    Ok(Slot {
                        name: text(&s[0], "staged-schema")?,
                        field: staged_field(&s[1])?,
                    })
                })
                .collect()
        };
        let phases = phases
            .iter()
            .map(|p| {
                let p = row(p, 3, "staged-schema")?;
                let tables = array(&p[2], "staged-schema")?;
                if tables.len() > TABLE_LIMIT {
                    return Err(Error("staged-schema"));
                }
                let (challenges, claims) = (slots(&p[0])?, slots(&p[1])?);
                let tables = tables
                    .iter()
                    .map(|t| {
                        let t = row(t, 4, "staged-schema")?;
                        let (groups, assertions) = (
                            array(&t[0], "staged-schema")?,
                            array(&t[3], "staged-schema")?,
                        );
                        if groups.len() > GROUP_LIMIT || assertions.len() > CHECK_LIMIT {
                            return Err(Error("staged-schema"));
                        }
                        let (arena, inputs) = (Expression::decode(&t[1])?, staged_inputs(&t[2])?);
                        let groups = groups
                            .iter()
                            .map(|g| {
                                let g = row(g, 3, "staged-schema")?;
                                Ok((
                                    text(&g[0], "staged-schema")?,
                                    staged_field(&g[1])?,
                                    natural(&g[2], WIDTH_LIMIT.into(), "staged-schema")? as u32,
                                ))
                            })
                            .collect::<Result<_>>()?;
                        let assertions = assertions
                            .iter()
                            .map(|x| {
                                let x = row(x, 2, "staged-schema")?;
                                Ok(Assertion {
                                    output: natural(&x[0], u32::MAX.into(), "staged-schema")?
                                        as usize,
                                    scope: decode_scope(&x[1])?,
                                })
                            })
                            .collect::<Result<_>>()?;
                        Ok(StagedTable {
                            groups,
                            arena,
                            inputs,
                            assertions,
                        })
                    })
                    .collect::<Result<_>>()?;
                Ok(StagedPhase {
                    challenges,
                    claims,
                    tables,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let global = (
            Expression::decode(&g[0])?,
            staged_inputs(&g[1])?,
            positions(&g[2], CHECK_LIMIT).map_err(|_| Error("staged-schema"))?,
        );
        let premises = premises
            .iter()
            .map(|p| {
                let a = array(p, "staged-premise")?;
                let index = |v: &Value, limit: usize| {
                    natural(v, limit as u64, "staged-premise").map(|n| n as u32)
                };
                Ok(match (tag(p), a.len()) {
                    (Some("characteristic-exceeds"), 3) => Premise::CharacteristicExceeds {
                        field: field(&a[1]).map_err(|_| Error("staged-premise"))?,
                        bound: a[2].as_u64().ok_or(Error("staged-premise"))?,
                    },
                    (Some("boolean"), 5) => Premise::Boolean {
                        phase: index(&a[1], PHASE_LIMIT)?,
                        table: index(&a[2], TABLE_LIMIT)?,
                        output: natural(&a[3], u32::MAX.into(), "staged-premise")? as usize,
                        scope: decode_scope(&a[4])?,
                    },
                    (Some("nonzero"), 5) => Premise::Nonzero {
                        phase: index(&a[1], PHASE_LIMIT)?,
                        table: index(&a[2], TABLE_LIMIT)?,
                        output: natural(&a[3], u32::MAX.into(), "staged-premise")? as usize,
                        scope: decode_scope(&a[4])?,
                    },
                    (Some("at-most-one"), 5) => Premise::AtMostOne {
                        phase: index(&a[1], PHASE_LIMIT)?,
                        table: index(&a[2], TABLE_LIMIT)?,
                        outputs: positions(&a[3], ARITY_LIMIT)
                            .map_err(|_| Error("staged-premise"))?,
                        scope: decode_scope(&a[4])?,
                    },
                    _ => return Err(Error("staged-premise")),
                })
            })
            .collect::<Result<Vec<_>>>()?;
        Self::new(bundle, phases, global, premises)
    }

    pub fn new(
        bundle: &Bundle,
        phases: Vec<StagedPhase>,
        global: (Expression, Vec<StagedInput>, Vec<usize>),
        premises: Vec<Premise>,
    ) -> Result<Self> {
        if phases.is_empty() {
            return Err(Error("staged-phases"));
        }
        if phases.len() > PHASE_LIMIT || premises.len() > PREMISE_LIMIT {
            return Err(Error("staged-limit"));
        }
        let mut names = BTreeSet::new();
        for p in &phases {
            if p.challenges.len() + p.claims.len() > SLOT_LIMIT {
                return Err(Error("staged-limit"));
            }
            for s in p.challenges.iter().chain(&p.claims) {
                if !valid_name(&s.name) {
                    return Err(Error("bundle-name"));
                }
                if !names.insert(s.name.as_str()) {
                    return Err(Error("bundle-duplicate-name"));
                }
                if degree(s.field).is_none() {
                    return Err(Error("bundle-field"));
                }
            }
            if p.tables.len() != bundle.tables.len() {
                return Err(Error("staged-tables"));
            }
        }
        let mut premise_outputs: BTreeMap<(u32, u32), Vec<usize>> = BTreeMap::new();
        for p in &premises {
            match p {
                Premise::Boolean {
                    phase,
                    table,
                    output,
                    ..
                }
                | Premise::Nonzero {
                    phase,
                    table,
                    output,
                    ..
                } => premise_outputs
                    .entry((*phase, *table))
                    .or_default()
                    .push(*output),
                Premise::AtMostOne {
                    phase,
                    table,
                    outputs,
                    ..
                } => premise_outputs
                    .entry((*phase, *table))
                    .or_default()
                    .extend(outputs),
                Premise::CharacteristicExceeds { .. } => {}
            }
        }
        let mut analysis_budget = AnalysisBudget::default();
        for (t, base) in bundle.tables.iter().enumerate() {
            let mut group_names: BTreeSet<&str> =
                base.groups.iter().map(|g| g.name.as_str()).collect();
            for (p, phase) in phases.iter().enumerate() {
                let table = &phase.tables[t];
                if table.groups.len() > GROUP_LIMIT || table.assertions.len() > CHECK_LIMIT {
                    return Err(Error("staged-limit"));
                }
                for (name, f, width) in &table.groups {
                    if !valid_name(name) {
                        return Err(Error("bundle-name"));
                    }
                    if !group_names.insert(name.as_str()) {
                        return Err(Error("bundle-duplicate-name"));
                    }
                    if degree(*f).is_none() {
                        return Err(Error("bundle-field"));
                    }
                    if *width < 1 || *width > WIDTH_LIMIT {
                        return Err(Error("bundle-width"));
                    }
                }
                staged_check_inputs(
                    bundle,
                    &phases,
                    t,
                    p + 1,
                    &table.arena,
                    &table.inputs,
                    false,
                )?;
                let mut referenced: Vec<usize> = Vec::new();
                for a in &table.assertions {
                    check_scope(a.scope)?;
                    referenced.push(a.output);
                }
                if let Some(extra) = premise_outputs.get(&(p as u32 + 1, t as u32)) {
                    referenced.extend(extra.iter().filter(|o| **o < table.arena.outputs().len()));
                }
                analysis_budget.account(&table.arena, referenced.len() + 1, 0)?;
                check_outputs_used(&table.arena, &referenced)?;
                if base.read_model == ReadModel::Finite {
                    for a in &table.assertions {
                        for o in staged_offsets(&table.arena, &table.inputs, a.output)? {
                            if !static_window(a.scope, o) {
                                return Err(Error("bundle-window"));
                            }
                        }
                    }
                }
            }
        }
        staged_check_inputs(bundle, &phases, 0, phases.len(), &global.0, &global.1, true)?;
        analysis_budget.account(&global.0, global.2.len() + 1, 0)?;
        check_outputs_used(&global.0, &global.2)?;
        for p in &premises {
            let (phase, table, outputs, scope) = match p {
                Premise::Boolean {
                    phase,
                    table,
                    output,
                    scope,
                }
                | Premise::Nonzero {
                    phase,
                    table,
                    output,
                    scope,
                } => (*phase, *table, std::slice::from_ref(output), *scope),
                Premise::AtMostOne {
                    phase,
                    table,
                    outputs,
                    scope,
                } => (*phase, *table, outputs.as_slice(), *scope),
                Premise::CharacteristicExceeds { field, bound } => {
                    if field.field_characteristic().is_none() || *bound < 1 {
                        return Err(Error("staged-premise"));
                    }
                    continue;
                }
            };
            let arena = bundle.tables.get(table as usize).and_then(|b| {
                if phase == 0 {
                    Some(&b.arena)
                } else {
                    phases
                        .get(phase as usize - 1)
                        .map(|ph| &ph.tables[table as usize].arena)
                }
            });
            let Some(arena) = arena else {
                return Err(Error("staged-premise"));
            };
            if outputs.is_empty()
                || outputs.len() > ARITY_LIMIT
                || outputs.iter().any(|o| *o >= arena.outputs().len())
            {
                return Err(Error("staged-premise"));
            }
            check_scope(scope)?;
        }
        let mut staged = Self {
            relation: bundle.identity.clone(),
            phases,
            global,
            premises,
            identity: String::new(),
        };
        let canonical = staged.encode().to_string();
        if canonical.len() > BYTE_LIMIT {
            return Err(Error("staged-limit"));
        }
        staged.identity = identity_hex(canonical.as_bytes());
        Ok(staged)
    }

    pub fn encode(&self) -> Value {
        let inputs = |inputs: &[StagedInput]| -> Vec<Value> {
            inputs
                .iter()
                .map(|i| match *i {
                    StagedInput::Public(index) => json!(["public", index]),
                    StagedInput::Read {
                        phase,
                        group,
                        offset,
                        column,
                    } => json!(["read", phase, group, offset.to_string(), column]),
                    StagedInput::Challenge { phase, index } => json!(["challenge", phase, index]),
                    StagedInput::Claim { phase, index } => json!(["claim", phase, index]),
                })
                .collect()
        };
        let slots = |s: &[Slot]| -> Vec<Value> {
            s.iter().map(|s| json!([s.name, s.field.name()])).collect()
        };
        let phases: Vec<_> = self
            .phases
            .iter()
            .map(|p| {
                json!([
                    slots(&p.challenges),
                    slots(&p.claims),
                    p.tables
                        .iter()
                        .map(|t| json!([
                            t.groups
                                .iter()
                                .map(|(n, f, w)| json!([n, f.name(), w]))
                                .collect::<Vec<_>>(),
                            t.arena.encode(),
                            inputs(&t.inputs),
                            t.assertions
                                .iter()
                                .map(|a| json!([a.output, encode_scope(a.scope)]))
                                .collect::<Vec<_>>()
                        ]))
                        .collect::<Vec<_>>()
                ])
            })
            .collect();
        let premises: Vec<_> = self
            .premises
            .iter()
            .map(|p| match p {
                Premise::Boolean {
                    phase,
                    table,
                    output,
                    scope,
                } => json!(["boolean", phase, table, output, encode_scope(*scope)]),
                Premise::Nonzero {
                    phase,
                    table,
                    output,
                    scope,
                } => json!(["nonzero", phase, table, output, encode_scope(*scope)]),
                Premise::AtMostOne {
                    phase,
                    table,
                    outputs,
                    scope,
                } => json!(["at-most-one", phase, table, outputs, encode_scope(*scope)]),
                Premise::CharacteristicExceeds { field, bound } => {
                    json!(["characteristic-exceeds", field.name(), bound])
                }
            })
            .collect();
        json!([
            "zkc.relation-staged/0",
            self.relation,
            phases,
            [
                self.global.0.encode(),
                inputs(&self.global.1),
                self.global.2
            ],
            premises
        ])
    }
}

fn staged_inputs(value: &Value) -> Result<Vec<StagedInput>> {
    let a = array(value, "staged-schema")?;
    if a.len() > crate::ring::NODE_LIMIT {
        return Err(Error("staged-schema"));
    }
    a.iter()
        .map(|i| {
            let n = |v: &Value, limit: u64| natural(v, limit, "staged-input").map(|n| n as u32);
            match (tag(i), i.as_array().map(Vec::len)) {
                (Some("public"), Some(2)) => {
                    Ok(StagedInput::Public(n(&i[1], PUBLIC_LIMIT as u64)?))
                }
                (Some("read"), Some(5)) => Ok(StagedInput::Read {
                    phase: n(&i[1], PHASE_LIMIT as u64)?,
                    group: n(&i[2], GROUP_LIMIT as u64)?,
                    offset: signed_offset(&i[3]).ok_or(Error("staged-input"))?,
                    column: n(&i[4], WIDTH_LIMIT.into())?,
                }),
                (Some("challenge"), Some(3)) => Ok(StagedInput::Challenge {
                    phase: n(&i[1], PHASE_LIMIT as u64)?,
                    index: n(&i[2], SLOT_LIMIT as u64)?,
                }),
                (Some("claim"), Some(3)) => Ok(StagedInput::Claim {
                    phase: n(&i[1], PHASE_LIMIT as u64)?,
                    index: n(&i[2], SLOT_LIMIT as u64)?,
                }),
                _ => Err(Error("staged-input")),
            }
        })
        .collect()
}
fn staged_check_inputs(
    bundle: &Bundle,
    phases: &[StagedPhase],
    table: usize,
    phase: usize,
    arena: &Expression,
    inputs: &[StagedInput],
    global: bool,
) -> Result<()> {
    if inputs.len() != arena.inputs().len() {
        return Err(Error("staged-input-count"));
    }
    let mut seen = BTreeSet::new();
    for (i, input) in inputs.iter().enumerate() {
        let f = match *input {
            StagedInput::Public(index) => {
                bundle
                    .publics
                    .get(index as usize)
                    .ok_or(Error("staged-input"))?
                    .field
            }
            StagedInput::Read {
                phase: p,
                group,
                offset,
                column,
            } => {
                if global {
                    return Err(Error("staged-global-read"));
                }
                if p as usize > phase {
                    return Err(Error("staged-phase-order"));
                }
                if !(-OFFSET_LIMIT..=OFFSET_LIMIT).contains(&offset) {
                    return Err(Error("staged-input"));
                }
                let (f, width) = if p == 0 {
                    let g = bundle.tables[table]
                        .groups
                        .get(group as usize)
                        .ok_or(Error("staged-input"))?;
                    (g.field, g.width)
                } else {
                    let g = phases[p as usize - 1].tables[table]
                        .groups
                        .get(group as usize)
                        .ok_or(Error("staged-input"))?;
                    (g.1, g.2)
                };
                if column >= width {
                    return Err(Error("staged-input"));
                }
                f
            }
            StagedInput::Challenge { phase: p, index } | StagedInput::Claim { phase: p, index } => {
                if p == 0 {
                    return Err(Error("staged-input"));
                }
                if p as usize > phase {
                    return Err(Error("staged-phase-order"));
                }
                let ph = &phases[p as usize - 1];
                let slots = if matches!(input, StagedInput::Challenge { .. }) {
                    &ph.challenges
                } else {
                    &ph.claims
                };
                slots
                    .get(index as usize)
                    .ok_or(Error("staged-input"))?
                    .field
            }
        };
        if arena.inputs()[i] != f {
            return Err(Error("staged-input-field"));
        }
        if !seen.insert(*input) {
            return Err(Error("staged-duplicate-input"));
        }
    }
    Ok(())
}
fn staged_offsets(arena: &Expression, inputs: &[StagedInput], output: usize) -> Result<Vec<i32>> {
    Ok(arena
        .used_inputs(&[output])?
        .into_iter()
        .filter_map(|i| match inputs[i] {
            StagedInput::Read { offset, .. } => Some(offset),
            _ => None,
        })
        .collect())
}

/// Supplied values of one staged phase: the actual challenge and claim
/// values, and per table `None` exactly when the table is absent, otherwise
/// the phase's groups for that table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StagedPhaseAssignment {
    pub challenges: Vec<Columns>,
    pub claims: Vec<Columns>,
    pub tables: Vec<Option<Vec<Columns>>>,
}
/// `zkc.relation-staged-assignment/0`: one entry per phase of the program it
/// names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StagedAssignment {
    pub program: String,
    pub phases: Vec<StagedPhaseAssignment>,
}
/// Value of a staged assertion's output on one row; `phase` counts from 1.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StagedResidual {
    pub phase: u32,
    pub table: usize,
    pub assertion: usize,
    pub row: u32,
    pub value: Columns,
}
/// The staged predicate only: staged assertions and global outputs. `work`
/// counts the staged tables, not the bundle's own checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StagedEvaluation {
    pub satisfied: bool,
    pub work: u64,
    pub residuals: Vec<StagedResidual>,
    pub global: Vec<Columns>,
}

/// Read values after the caller checks both challenge and claim list shapes.
fn read_values(values: &[Value], slots: &[Slot]) -> Result<Vec<Columns>> {
    slots
        .iter()
        .zip(values)
        .map(|(s, v)| {
            let mut out = Vec::new();
            read_value(v, s.field, &mut out).map(|()| out)
        })
        .collect()
}
fn output_field(arena: &Expression, output: usize) -> Identity {
    arena.facts()[arena.outputs()[output]].field
}
/// Materialized result records and their base coordinates.
fn check_results(records: u64, coordinates: u64) -> Result<()> {
    if records > RESULT_RECORD_LIMIT || coordinates > RESULT_COORDINATE_LIMIT {
        return Err(Error("bundle-result-limit"));
    }
    Ok(())
}

impl Staged {
    /// Exact carrier shape and one coordinate budget across all phases.
    /// The program identity, presence, heights and canonical values are
    /// checked by [`Staged::evaluate`].
    pub fn decode_assignment(&self, value: &Value) -> Result<StagedAssignment> {
        let root = row(value, 3, "staged-data-schema")?;
        if root[0].as_str() != Some("zkc.relation-staged-assignment/0") {
            return Err(Error("staged-data-schema"));
        }
        let program = text(&root[1], "staged-data-schema")?;
        let rows = array(&root[2], "staged-data-schema")?;
        if rows.len() != self.phases.len() {
            return Err(Error("staged-data-schema"));
        }
        let mut budget = COORDINATE_LIMIT;
        let mut phases = Vec::with_capacity(rows.len());
        for (phase, entry) in self.phases.iter().zip(rows) {
            let entry = row(entry, 3, "staged-data-schema")?;
            let tables = array(&entry[2], "staged-data-schema")?;
            if tables.len() != phase.tables.len() {
                return Err(Error("staged-data-schema"));
            }
            let challenge_values = array(&entry[0], "staged-slot-shape")?;
            let claim_values = array(&entry[1], "staged-slot-shape")?;
            if challenge_values.len() != phase.challenges.len()
                || claim_values.len() != phase.claims.len()
            {
                return Err(Error("staged-slot-shape"));
            }
            let challenges = read_values(challenge_values, &phase.challenges)?;
            let claims = read_values(claim_values, &phase.claims)?;
            let mut data = Vec::with_capacity(tables.len());
            for (table, value) in phase.tables.iter().zip(tables) {
                if value.is_null() {
                    data.push(None);
                    continue;
                }
                let groups = value
                    .as_array()
                    .filter(|g| g.len() == table.groups.len())
                    .ok_or(Error("bundle-group-count"))?;
                let mut columns = Vec::with_capacity(groups.len());
                for ((_, field, _), group) in table.groups.iter().zip(groups) {
                    columns.push(read_group(group, *field, &mut budget)?);
                }
                data.push(Some(columns));
            }
            phases.push(StagedPhaseAssignment {
                challenges,
                claims,
                tables: data,
            });
        }
        Ok(StagedAssignment { program, phases })
    }

    /// Encode an assignment admitted for this program and its base data.
    pub fn encode_assignment(&self, assignment: &StagedAssignment) -> Value {
        let values = |v: &[Columns]| -> Vec<Value> { v.iter().map(|c| encode_value(c)).collect() };
        let tables = self.phases[0].tables.len();
        let phases: Vec<_> = assignment
            .phases
            .iter()
            .enumerate()
            .map(|(p, data)| {
                let encoded: Vec<_> = data
                    .tables
                    .iter()
                    .take(tables)
                    .enumerate()
                    .map(|(t, groups)| match groups {
                        None => Value::Null,
                        Some(groups) => Value::Array(
                            groups
                                .iter()
                                .enumerate()
                                .map(|(g, columns)| {
                                    let field = self
                                        .phases
                                        .get(p)
                                        .and_then(|phase| phase.tables[t].groups.get(g))
                                        .map_or(Identity::KoalaBear, |group| group.1);
                                    encode_group(columns, field)
                                })
                                .collect(),
                        ),
                    })
                    .collect();
                json!([values(&data.challenges), values(&data.claims), encoded])
            })
            .collect();
        json!([
            "zkc.relation-staged-assignment/0",
            assignment.program,
            phases
        ])
    }

    /// The staged predicate for the supplied actual challenges and claims.
    /// The base data are admitted first. Shape, presence, windows, work and
    /// result size are then checked from the declared program and admitted
    /// heights before any staged value is read. Premises are recorded
    /// assumptions and are not evaluated; the bundle's own assertions and
    /// interactions are not part of this predicate.
    pub fn evaluate<A: Algebra>(
        &self,
        bundle: &Bundle,
        config: &Configuration,
        instance: &Instance,
        witness: &Witness,
        assignment: &StagedAssignment,
        algebra: &A,
    ) -> Result<StagedEvaluation> {
        if bundle.identity != self.relation {
            return Err(Error("bundle-relation"));
        }
        let admitted = bundle.admit(config, instance, witness)?;
        if assignment.program != self.identity {
            return Err(Error("staged-program"));
        }
        if assignment.phases.len() != self.phases.len() {
            return Err(Error("staged-data-shape"));
        }
        let (mut coordinates, mut work) = (0u64, 0u64);
        let (mut records, mut result_coordinates) = (0u64, 0u64);
        for (phase, data) in self.phases.iter().zip(&assignment.phases) {
            if data.challenges.len() != phase.challenges.len()
                || data.claims.len() != phase.claims.len()
            {
                return Err(Error("staged-slot-shape"));
            }
            if data.tables.len() != bundle.tables.len() {
                return Err(Error("staged-data-shape"));
            }
            for slot in phase.challenges.iter().chain(&phase.claims) {
                coordinates += degree(slot.field).ok_or(Error("bundle-field"))? as u64;
            }
            if coordinates > COORDINATE_LIMIT {
                return Err(Error("bundle-data-limit"));
            }
            for (t, (table, groups)) in phase.tables.iter().zip(&data.tables).enumerate() {
                if admitted.present[t] != groups.is_some() {
                    return Err(Error("staged-presence"));
                }
                let Some(groups) = groups else {
                    continue;
                };
                if groups.len() != table.groups.len() {
                    return Err(Error("bundle-group-count"));
                }
                let height = admitted.heights[t];
                for ((_, field, width), columns) in table.groups.iter().zip(groups) {
                    let d = degree(*field).ok_or(Error("bundle-field"))? as u64;
                    // The declared shape is bounded before data lengths.
                    let expected = u64::from(height) * u64::from(*width) * d;
                    coordinates += expected;
                    if coordinates > COORDINATE_LIMIT {
                        return Err(Error("bundle-data-limit"));
                    }
                    if columns.len() as u64 != expected {
                        return Err(Error("bundle-group-shape"));
                    }
                }
                let model = bundle.tables[t].read_model;
                for a in &table.assertions {
                    window_at(
                        a.scope,
                        model,
                        height,
                        &staged_offsets(&table.arena, &table.inputs, a.output)?,
                    )?;
                }
                if !table.assertions.is_empty() {
                    work += u64::from(height)
                        * (table.arena.nodes().len()
                            + table.arena.inputs().len()
                            + table.assertions.len()
                            + 1) as u64;
                }
                if work > WORK_LIMIT {
                    return Err(Error("bundle-work-limit"));
                }
                for a in &table.assertions {
                    let (lo, hi) = scope_rows(a.scope, height);
                    let rows = u64::from(hi.saturating_sub(lo));
                    records += rows;
                    result_coordinates +=
                        rows * degree(output_field(&table.arena, a.output)).unwrap_or(1) as u64;
                }
                check_results(records, result_coordinates)?;
            }
        }
        let (global, global_inputs, global_outputs) = &self.global;
        for &output in global_outputs {
            records += 1;
            result_coordinates += degree(output_field(global, output)).unwrap_or(1) as u64;
        }
        check_results(records, result_coordinates)?;
        for (phase, data) in self.phases.iter().zip(&assignment.phases) {
            for (slots, values) in [
                (&phase.challenges, &data.challenges),
                (&phase.claims, &data.claims),
            ] {
                for (s, v) in slots.iter().zip(values) {
                    if v.len() != degree(s.field).unwrap_or(0)
                        || !v.iter().all(|c| s.field.canonical_field_literal(c))
                    {
                        return Err(Error("bundle-value"));
                    }
                }
            }
            for (table, groups) in phase.tables.iter().zip(&data.tables) {
                for ((_, field, _), columns) in table.groups.iter().zip(groups.iter().flatten()) {
                    if !columns.iter().all(|c| field.canonical_field_literal(c)) {
                        return Err(Error("bundle-value"));
                    }
                }
            }
        }
        let publics = bundle
            .publics
            .iter()
            .zip(&instance.publics)
            .map(|(s, v)| algebra.value(s.field, v))
            .collect::<Result<Vec<_>>>()?;
        let slot_values = |slots: &[Slot], values: &[Columns]| {
            slots
                .iter()
                .zip(values)
                .map(|(s, v)| algebra.value(s.field, v))
                .collect::<Result<Vec<_>>>()
        };
        let (mut challenges, mut claims) = (Vec::new(), Vec::new());
        for (phase, data) in self.phases.iter().zip(&assignment.phases) {
            challenges.push(slot_values(&phase.challenges, &data.challenges)?);
            claims.push(slot_values(&phase.claims, &data.claims)?);
        }
        // Formation admits reads only in tables and only of phases <= the
        // reading phase; challenges and claims name phases from 1.
        let scalar = |input: StagedInput| -> A::Value {
            match input {
                StagedInput::Public(index) => publics[index as usize].clone(),
                StagedInput::Challenge { phase, index } => {
                    challenges[phase as usize - 1][index as usize].clone()
                }
                StagedInput::Claim { phase, index } => {
                    claims[phase as usize - 1][index as usize].clone()
                }
                StagedInput::Read { .. } => unreachable!("formation refuses scalar reads"),
            }
        };
        let mut result = StagedEvaluation {
            satisfied: true,
            work,
            residuals: vec![],
            global: vec![],
        };
        for (p, phase) in self.phases.iter().enumerate() {
            for (t, table) in phase.tables.iter().enumerate() {
                if !admitted.present[t] || table.assertions.is_empty() {
                    continue;
                }
                let base = &bundle.tables[t];
                let height = admitted.heights[t];
                let base_groups = bundle.present_groups(t, config, instance, witness);
                // Rows split into segments over which the active assertions
                // are fixed; each row evaluates their outputs once.
                let ranges: Vec<_> = table
                    .assertions
                    .iter()
                    .map(|a| scope_rows(a.scope, height))
                    .collect();
                let mut cuts = BTreeSet::from([0, height]);
                for &(lo, hi) in &ranges {
                    if lo < hi {
                        cuts.insert(lo);
                        cuts.insert(hi);
                    }
                }
                let cuts: Vec<_> = cuts.into_iter().collect();
                let mut residuals: Vec<Vec<StagedResidual>> = vec![vec![]; ranges.len()];
                for segment in cuts.windows(2) {
                    let (from, to) = (segment[0], segment[1]);
                    let active: Vec<usize> = (0..ranges.len())
                        .filter(|&i| {
                            ranges[i].0 < ranges[i].1 && ranges[i].0 <= from && to <= ranges[i].1
                        })
                        .collect();
                    if active.is_empty() {
                        continue;
                    }
                    let positions: Vec<usize> = active
                        .iter()
                        .map(|&i| table.assertions[i].output)
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect();
                    let selected = table.arena.select(&positions)?;
                    let slot =
                        |output: usize| positions.binary_search(&output).expect("selected output");
                    for r in from..to {
                        let mut fetch = |input: usize| -> Result<A::Value> {
                            let StagedInput::Read {
                                phase: j,
                                group,
                                offset,
                                column,
                            } = table.inputs[input]
                            else {
                                return Ok(scalar(table.inputs[input]));
                            };
                            let read = read_row(base.read_model, height, r, offset);
                            let group = group as usize;
                            if j == 0 {
                                let g = &base.groups[group];
                                return element(
                                    algebra,
                                    g.field,
                                    g.width,
                                    base_groups[group],
                                    read,
                                    column,
                                );
                            }
                            let (_, field, width) =
                                &self.phases[j as usize - 1].tables[t].groups[group];
                            let columns = &assignment.phases[j as usize - 1].tables[t]
                                .as_ref()
                                .expect("present")[group];
                            element(algebra, *field, *width, columns, read, column)
                        };
                        let values = interpret(&selected, algebra, &mut fetch)?;
                        for &i in &active {
                            let output = table.assertions[i].output;
                            let value = algebra.coordinates(
                                output_field(&table.arena, output),
                                &values[slot(output)],
                            );
                            result.satisfied &= is_zero(&value);
                            residuals[i].push(StagedResidual {
                                phase: p as u32 + 1,
                                table: t,
                                assertion: i,
                                row: r,
                                value,
                            });
                        }
                    }
                }
                result.residuals.extend(residuals.into_iter().flatten());
            }
        }
        if !global_outputs.is_empty() {
            let values = interpret(global, algebra, &mut |input| {
                Ok(scalar(global_inputs[input]))
            })?;
            for &output in global_outputs {
                let value = algebra.coordinates(output_field(global, output), &values[output]);
                result.satisfied &= is_zero(&value);
                result.global.push(value);
            }
        }
        Ok(result)
    }
}

#[cfg(test)]
#[path = "relation_tests.rs"]
mod tests;
