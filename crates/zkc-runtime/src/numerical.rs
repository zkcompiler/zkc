//! Independent admission of physical pointwise storage plans. No provider
//! arithmetic, producer allocator, or logical-source correspondence lives here.
use crate::ring::{self, Expression, Node};
use crate::vm::Identity;
use serde_json::Value;

pub const BYTE_LIMIT: usize = 16_384;
pub const EXPRESSION_BYTES: usize = 4_096;
pub const LANE_LIMIT: usize = 256;
pub const INPUT_LIMIT: usize = 1_023;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Error(pub &'static str);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

/// Immutable after reading. The consumer must use these actual locations and
/// lane bound; admission is not a permission to substitute a different plan.
#[derive(Clone, Debug)]
pub struct Plan {
    expression: Expression,
    lanes: usize,
    slots: usize,
    locations: Vec<usize>,
}

fn dependencies(node: &Node) -> impl Iterator<Item = usize> {
    let pair = match *node {
        Node::Add(a, b) | Node::Mul(a, b) => [Some(a), Some(b)],
        Node::Neg(a) => [Some(a), None],
        _ => [None, None],
    };
    pair.into_iter().flatten()
}

impl Plan {
    pub fn parse(body: &str, field: Identity, mask: &[u8]) -> Result<Self> {
        if body.len() > BYTE_LIMIT {
            return Err(Error("numerical-plan-bytes"));
        }
        if mask.len() > INPUT_LIMIT || !mask.iter().all(|b| matches!(b, b'0' | b'1')) {
            return Err(Error("numerical-mask"));
        }
        // The shared lexical reader bounds nesting before serde allocation and
        // admits only arrays, strings and natural numbers. Canonical equality
        // below also excludes alternate whitespace and escaped spellings.
        let json = ring::parse_json(body).map_err(|_| Error("numerical-plan"))?;
        let row = json.as_array().ok_or(Error("numerical-plan"))?;
        if row.len() != 5 || row[0].as_str() != Some("zkc.numerical-plan/0") {
            return Err(Error("numerical-plan"));
        }
        let natural = |value: &Value| {
            value
                .as_u64()
                .and_then(|n| usize::try_from(n).ok())
                .ok_or(Error("numerical-plan-shape"))
        };
        let lanes = natural(&row[2])?;
        let slots = natural(&row[3])?;
        let locations = row[4].as_array().ok_or(Error("numerical-plan-shape"))?;
        if !(1..=LANE_LIMIT).contains(&lanes) || !(1..=ring::NODE_LIMIT).contains(&slots) {
            return Err(Error("numerical-plan-shape"));
        }
        if row[1].to_string().len() > EXPRESSION_BYTES {
            return Err(Error("numerical-plan-bytes"));
        }
        let expression = Expression::decode(&row[1]).map_err(|_| Error("numerical-expression"))?;
        if field.field_characteristic().is_none()
            || expression.inputs().len() != mask.len()
            || expression.outputs().len() != 1
        {
            return Err(Error("numerical-body-signature"));
        }
        if expression.inputs().iter().any(|f| *f != field)
            || expression.facts().iter().any(|f| f.field != field)
            || expression
                .nodes()
                .iter()
                .any(|n| matches!(n, Node::Embed(..)))
        {
            return Err(Error("numerical-body-field"));
        }
        let nodes = expression.nodes();
        if slots > nodes.len() || locations.len() != nodes.len() {
            return Err(Error("numerical-plan-shape"));
        }
        let locations: Vec<_> = locations.iter().map(natural).collect::<Result<_>>()?;
        let mut used = vec![false; slots];
        let mut varying = vec![false; nodes.len()];
        for (id, node) in nodes.iter().enumerate() {
            let Some(used) = used.get_mut(locations[id]) else {
                return Err(Error("numerical-plan-shape"));
            };
            *used = true;
            varying[id] = matches!(node, Node::Input(i) if mask[*i] == b'1')
                || dependencies(node).any(|i| varying[i]);
        }
        if used.contains(&false) {
            return Err(Error("numerical-plan-shape"));
        }
        let root = expression.outputs()[0];
        let mut persistent = vec![false; nodes.len()];
        persistent[root] = !varying[root];
        for (id, node) in nodes.iter().enumerate() {
            if varying[id] {
                for dependency in dependencies(node) {
                    persistent[dependency] |= !varying[dependency];
                }
            }
        }
        // Read exact symbolic owners before each write. Persistent invariants
        // survive every chunk; all varying values are redefined each chunk.
        // This validates alternatives rather than replaying producer liveness.
        let mut contents = vec![None; slots];
        for phase in [false, true] {
            for (id, node) in nodes.iter().enumerate() {
                if varying[id] != phase {
                    continue;
                }
                if dependencies(node).any(|i| contents[locations[i]] != Some(i))
                    || contents[locations[id]].is_some_and(|i| persistent[i])
                {
                    return Err(Error("numerical-plan-schedule"));
                }
                contents[locations[id]] = Some(id);
            }
        }
        if contents[locations[root]] != Some(root) {
            return Err(Error("numerical-plan-schedule"));
        }
        if serde_json::json!([
            "zkc.numerical-plan/0",
            expression.encode(),
            lanes,
            slots,
            locations
        ])
        .to_string()
            != body
        {
            return Err(Error("numerical-plan-canonical"));
        }
        Ok(Self {
            expression,
            lanes,
            slots,
            locations,
        })
    }

    pub fn expression(&self) -> &Expression {
        &self.expression
    }
    pub fn lanes(&self) -> usize {
        self.lanes
    }
    pub fn slots(&self) -> usize {
        self.slots
    }
    pub fn locations(&self) -> &[usize] {
        &self.locations
    }
    pub fn into_parts(self) -> (Expression, usize, usize, Vec<usize>) {
        (self.expression, self.lanes, self.slots, self.locations)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn fixture() -> Value {
        json!([
            "zkc.numerical-plan/0",
            [
                "zkc.ring/0",
                ["koala-bear", "koala-bear"],
                [
                    ["input", 0],
                    ["input", 1],
                    ["mul", 1, 1],
                    ["add", 0, 2],
                    ["mul", 3, 3]
                ],
                [4]
            ],
            8,
            2,
            [1, 0, 0, 1, 1]
        ])
    }
    fn read(value: &Value, mask: &[u8]) -> Result<Plan> {
        Plan::parse(&value.to_string(), Identity::KoalaBear, mask)
    }
    #[test]
    fn reuse_reads_before_write_and_preserves_invariants() {
        let p = read(&fixture(), b"10").unwrap();
        assert_eq!((p.lanes(), p.slots()), (8, 2));
        assert_eq!(p.locations(), [1, 0, 0, 1, 1]);
        let mut value = fixture();
        value[3] = json!(5);
        value[4] = json!([0, 1, 2, 3, 4]);
        for mask in [b"00", b"01", b"10", b"11"] {
            read(&value, mask).unwrap();
        }
    }
    #[test]
    fn stale_slot_map_cannot_clobber_a_live_or_persistent_value() {
        for locations in [[0, 0, 0, 1, 1], [1, 0, 0, 0, 1], [1, 0, 0, 1, 0]] {
            let mut value = fixture();
            value[4] = json!(locations);
            assert_eq!(
                read(&value, b"10").err(),
                Some(Error("numerical-plan-schedule"))
            );
        }
        assert_eq!(
            read(&fixture(), b"01").err(),
            Some(Error("numerical-plan-schedule"))
        );
    }
    #[test]
    fn exact_shape_capacity_and_nominal_domain() {
        for (index, replacement) in [
            (2, json!(0)),
            (2, json!(257)),
            (3, json!(0)),
            (3, json!(6)),
            (3, json!(3)),
            (4, json!([1, 0, 0, 1])),
            (4, json!([1, 0, 0, 1, 2])),
        ] {
            let mut value = fixture();
            value[index] = replacement;
            assert_eq!(
                read(&value, b"10").err(),
                Some(Error("numerical-plan-shape"))
            );
        }
        assert_eq!(read(&fixture(), b"1x").err(), Some(Error("numerical-mask")));
        assert_eq!(
            read(&fixture(), b"1").err(),
            Some(Error("numerical-body-signature"))
        );
        assert_eq!(
            Plan::parse(&fixture().to_string(), Identity::BabyBear, b"10").err(),
            Some(Error("numerical-body-field"))
        );
    }
    #[test]
    fn canonical_current_carrier_only() {
        let value = fixture();
        assert_eq!(read(&value[1], b"10").err(), Some(Error("numerical-plan")));
        let body = value.to_string();
        assert_eq!(
            Plan::parse(&format!(" {body}"), Identity::KoalaBear, b"10").err(),
            Some(Error("numerical-plan-canonical"))
        );
        assert_eq!(
            Plan::parse(&" ".repeat(BYTE_LIMIT + 1), Identity::KoalaBear, b"10").err(),
            Some(Error("numerical-plan-bytes"))
        );
        for malformed in [
            "[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]",
            "{}",
            "[null]",
            "[-1]",
            "[00]",
            "[1.0]",
        ] {
            assert_eq!(
                Plan::parse(malformed, Identity::KoalaBear, b"10").err(),
                Some(Error("numerical-plan"))
            );
        }
    }
}
