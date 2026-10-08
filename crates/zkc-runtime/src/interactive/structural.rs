//! Finite, locally installed structural declarations. Carrier text supplies
//! arguments, never constructor metadata, permissions, or executable authority.
use super::{AdmissionError, ErrorCode, Identity, LogicalType, Type};
use std::sync::Arc;

type Result<T> = std::result::Result<T, AdmissionError>;

pub const TYPE_DEPTH_LIMIT: usize = 8;
pub const TYPE_NODE_LIMIT: usize = 200_000;
pub const STRUCTURAL_SPELLING_LIMIT: usize = 4096;
pub const NATURAL_ARGUMENT_LIMIT: u64 = 1_048_576;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArgumentKind {
    FieldDomain,
    Type,
    Nat,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeArgument {
    Domain(Identity),
    Type(LogicalType),
    Nat(u64),
}
impl TypeArgument {
    fn spelling(&self) -> String {
        match self {
            Self::Domain(d) => d.name().into(),
            Self::Type(t) => t.spelling(),
            Self::Nat(n) => n.to_string(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Constructor {
    name: &'static str,
    kind: Type,
    parameters: &'static [ArgumentKind],
    copy: bool,
    drop: bool,
}
static CONSTRUCTORS: &[Constructor] = &[
    Constructor {
        name: "sequence",
        kind: Type::Sequence,
        parameters: &[ArgumentKind::Type],
        copy: true,
        drop: true,
    },
    Constructor {
        name: "field_array",
        kind: Type::FieldArray,
        parameters: &[ArgumentKind::FieldDomain, ArgumentKind::Nat],
        copy: true,
        drop: true,
    },
    Constructor {
        name: "fixed_vector",
        kind: Type::FixedVector,
        parameters: &[ArgumentKind::Type, ArgumentKind::Nat],
        copy: true,
        drop: true,
    },
];

fn invalid(detail: &str) -> AdmissionError {
    AdmissionError::new(ErrorCode::Type, detail)
}

/// Immutable kinded arguments, admitted against a local declaration. No public
/// field permits a caller to replace the declaration or its permissions.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StructuralType {
    constructor: &'static Constructor,
    arguments: Box<[TypeArgument]>,
}
impl StructuralType {
    pub fn head(&self) -> &'static str {
        self.constructor.name
    }
    pub fn arguments(&self) -> &[TypeArgument] {
        &self.arguments
    }
    pub fn parameter_kinds(&self) -> &[ArgumentKind] {
        self.constructor.parameters
    }
    pub(super) fn kind(&self) -> Type {
        self.constructor.kind
    }
    pub fn spelling(&self) -> String {
        format!(
            "{}<{}>",
            self.head(),
            self.arguments
                .iter()
                .map(TypeArgument::spelling)
                .collect::<Vec<_>>()
                .join(",")
        )
    }
    pub fn is_duplicable(&self) -> bool {
        self.constructor.copy
            && self.arguments.iter().all(|arg| match arg {
                TypeArgument::Type(t) => t.is_duplicable(),
                _ => true,
            })
    }
    pub fn is_discardable(&self) -> bool {
        self.constructor.drop
            && self.arguments.iter().all(|arg| match arg {
                TypeArgument::Type(t) => t.is_discardable(),
                _ => true,
            })
    }
    pub(super) fn retained_bytes(&self) -> usize {
        self.arguments.iter().fold(512usize, |bytes, arg| {
            bytes.saturating_add(256).saturating_add(match arg {
                TypeArgument::Type(t) => t.descriptor_bytes(),
                _ => 0,
            })
        })
    }
}

struct ParsedType {
    ty: LogicalType,
    nodes: usize,
    // Inline graph subtrees have only passed the containing spelling's
    // expansion bound. Text lookups require this spelling's own bound too.
    spelling_checked: bool,
}

pub(super) struct ParseBudget {
    remaining: usize,
    bytes: usize,
    cache: std::collections::BTreeMap<(usize, String), ParsedType>,
}
impl ParseBudget {
    pub(super) fn new() -> Self {
        Self {
            remaining: TYPE_NODE_LIMIT,
            bytes: super::Limits::TYPE_BYTES,
            cache: Default::default(),
        }
    }
    pub(super) fn cached(
        &mut self,
        spelling: &str,
        depth: usize,
        require_spelling_check: bool,
    ) -> Result<Option<LogicalType>> {
        if let Some(entry) = self.cache.get(&(depth, spelling.into())) {
            if require_spelling_check && !entry.spelling_checked {
                return Ok(None);
            }
            let (ty, nodes) = (entry.ty.clone(), entry.nodes);
            self.charge(nodes)?;
            return Ok(Some(ty));
        }
        Ok(None)
    }
    pub(super) fn remember(
        &mut self,
        spelling: &str,
        depth: usize,
        ty: LogicalType,
        nodes: usize,
        spelling_checked: bool,
    ) {
        self.cache.insert(
            (depth, spelling.into()),
            ParsedType {
                ty,
                nodes,
                spelling_checked,
            },
        );
    }
    pub(super) fn allocate(&mut self, bytes: usize) -> Result<()> {
        self.bytes = self
            .bytes
            .checked_sub(bytes)
            .ok_or_else(|| AdmissionError::new(ErrorCode::Limit, "type descriptor byte ceiling"))?;
        Ok(())
    }
    pub(super) fn remaining(&self) -> usize {
        self.remaining
    }
    pub(super) fn charge(&mut self, nodes: usize) -> Result<()> {
        self.remaining = self
            .remaining
            .checked_sub(nodes)
            .ok_or_else(|| invalid("logical-type-limit"))?;
        Ok(())
    }
    pub(super) fn node(&mut self, depth: usize) -> Result<()> {
        if depth > TYPE_DEPTH_LIMIT || self.remaining == 0 {
            return Err(invalid("logical-type-limit"));
        }
        self.remaining -= 1;
        Ok(())
    }
}

pub(super) fn natural(s: &str) -> Result<u64> {
    crate::logical::natural_index(s)
        .ok()
        .filter(|n| *n <= NATURAL_ARGUMENT_LIMIT)
        .ok_or_else(|| invalid("structural-natural"))
}

pub(super) fn arguments(
    values: &[&str],
    kinds: &[ArgumentKind],
    depth: usize,
    budget: &mut ParseBudget,
) -> Result<Vec<TypeArgument>> {
    if values.len() != kinds.len() {
        return Err(invalid("structural-arity"));
    }
    values
        .iter()
        .zip(kinds)
        .map(|(value, kind)| {
            Ok(match kind {
                ArgumentKind::Type => {
                    TypeArgument::Type(LogicalType::parse_nested(value, depth, budget)?)
                }
                ArgumentKind::Nat => {
                    budget.node(depth)?;
                    TypeArgument::Nat(natural(value)?)
                }
                ArgumentKind::FieldDomain => {
                    budget.node(depth)?;
                    let identity = Identity::parse(value)?;
                    LogicalType::new(Type::Field, identity)?;
                    TypeArgument::Domain(identity)
                }
            })
        })
        .collect()
}

pub(super) fn parse(
    spelling: &str,
    depth: usize,
    budget: &mut ParseBudget,
) -> Result<Arc<StructuralType>> {
    if depth >= TYPE_DEPTH_LIMIT || spelling.len() > STRUCTURAL_SPELLING_LIMIT {
        return Err(invalid("logical-type-limit"));
    }
    if spelling
        .bytes()
        .any(|b| b.is_ascii_whitespace() || b == b'@')
    {
        return Err(invalid("structural-spelling"));
    }
    let (head, body) = spelling
        .split_once('<')
        .ok_or_else(|| invalid("structural-spelling"))?;
    let constructor = CONSTRUCTORS
        .iter()
        .find(|c| c.name == head)
        .ok_or_else(|| invalid("uninstalled structural constructor"))?;
    let body = body
        .strip_suffix('>')
        .ok_or_else(|| invalid("structural-spelling"))?;
    let mut parts = Vec::new();
    let mut start = 0;
    let mut nesting = 0usize;
    for (i, b) in body.bytes().enumerate() {
        match b {
            b'<' => {
                nesting += 1;
                if depth + nesting >= TYPE_DEPTH_LIMIT {
                    return Err(invalid("logical-type-limit"));
                }
            }
            b'>' => {
                nesting = nesting
                    .checked_sub(1)
                    .ok_or_else(|| invalid("structural-spelling"))?
            }
            b',' if nesting == 0 => {
                parts.push(&body[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    if nesting != 0 {
        return Err(invalid("structural-spelling"));
    }
    parts.push(&body[start..]);
    budget.allocate(512 + 256 * parts.len())?;
    let arguments = arguments(&parts, constructor.parameters, depth + 1, budget)?;
    if constructor.kind == Type::Sequence
        && !matches!(arguments.as_slice(), [TypeArgument::Type(t)]
            if t.is_duplicable() && t.is_discardable())
    {
        return Err(invalid("sequence-element-permission"));
    }
    Ok(Arc::new(StructuralType {
        constructor,
        arguments: arguments.into_boxed_slice(),
    }))
}

impl LogicalType {
    pub fn sequence(element: Self) -> Result<Self> {
        Self::application("sequence", &[TypeArgument::Type(element)])
    }
    pub fn sequence_element(&self) -> Option<&Self> {
        if self.kind() != Type::Sequence {
            return None;
        }
        match self.structural()?.arguments() {
            [TypeArgument::Type(element)] => Some(element),
            _ => None,
        }
    }
    /// Construct through the same bounded canonical admission as carrier input.
    pub fn application(head: &str, arguments: &[TypeArgument]) -> Result<Self> {
        let constructor = CONSTRUCTORS
            .iter()
            .find(|c| c.name == head)
            .ok_or_else(|| invalid("uninstalled structural constructor"))?;
        if arguments.len() != constructor.parameters.len() {
            return Err(invalid("structural-arity"));
        }
        for (argument, kind) in arguments.iter().zip(constructor.parameters) {
            match (argument, kind) {
                (TypeArgument::Type(_), ArgumentKind::Type) => {}
                (TypeArgument::Nat(n), ArgumentKind::Nat) if *n <= NATURAL_ARGUMENT_LIMIT => {}
                (TypeArgument::Domain(d), ArgumentKind::FieldDomain) => {
                    LogicalType::new(Type::Field, *d)?;
                }
                _ => return Err(invalid("structural-kind")),
            }
        }
        let spelling = format!(
            "{head}<{}>",
            arguments
                .iter()
                .map(TypeArgument::spelling)
                .collect::<Vec<_>>()
                .join(",")
        );
        let parsed = Self::parse(&spelling)?;
        if parsed.structural().map(StructuralType::arguments) != Some(arguments) {
            return Err(invalid("structural-kind"));
        }
        Ok(parsed)
    }
    pub fn field_array(field: Identity, length: u64) -> Result<Self> {
        Self::application(
            "field_array",
            &[TypeArgument::Domain(field), TypeArgument::Nat(length)],
        )
    }
    pub fn field_array_parts(&self) -> Option<(Identity, u64)> {
        if self.kind() != Type::FieldArray {
            return None;
        }
        match self.structural()?.arguments() {
            [TypeArgument::Domain(field), TypeArgument::Nat(n)] => Some((*field, *n)),
            _ => None,
        }
    }
    pub fn fixed_vector(element: Self, length: u64) -> Result<Self> {
        Self::application(
            "fixed_vector",
            &[TypeArgument::Type(element), TypeArgument::Nat(length)],
        )
    }
    pub fn fixed_vector_parts(&self) -> Option<(&LogicalType, u64)> {
        if self.kind() != Type::FixedVector {
            return None;
        }
        match self.structural()?.arguments() {
            [TypeArgument::Type(element), TypeArgument::Nat(n)] => Some((element, *n)),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn native_protocol_ports_exclude_affine_variants_but_allow_resources() {
        let variant = zkc_test_support::variants::logical(
            "Local",
            json!([["guard", ["resource_unit:Guard"]]]),
        );
        for spelling in [
            variant.clone(),
            format!("fixed_vector<{variant},2>"),
            format!("fixed_vector<fixed_vector<{variant},2>,0>"),
        ] {
            assert!(
                !LogicalType::parse(&spelling).unwrap().is_program_port(),
                "{spelling}"
            );
        }
        for spelling in [
            "bool",
            "rng:bls12-381.fr",
            "resource_unit:Guard",
            "fixed_vector<rng:bls12-381.fr,0>",
            "fixed_vector<fixed_vector<resource_unit:Guard,1>,2>",
        ] {
            assert!(
                LogicalType::parse(spelling).unwrap().is_program_port(),
                "{spelling}"
            );
        }
    }

    #[test]
    fn budget_is_shared_across_variant_payloads_and_type_arguments() {
        let inner = zkc_test_support::variants::logical("Inner", json!([["value", ["bool"]]]));
        let outer = zkc_test_support::variants::logical(
            "Outer",
            json!([["value", [format!("fixed_vector<{inner},0>")]]]),
        );
        // Outer variant, application, inner variant, Bool, Nat: five nodes.
        let mut budget = ParseBudget {
            remaining: 5,
            ..ParseBudget::new()
        };
        assert!(LogicalType::parse_nested(&outer, 0, &mut budget).is_ok());
        assert_eq!(budget.remaining, 0);
        let mut budget = ParseBudget {
            remaining: 4,
            ..ParseBudget::new()
        };
        let error = LogicalType::parse_nested(&outer, 0, &mut budget).unwrap_err();
        assert_eq!(error.code, ErrorCode::Type);
        assert_eq!(error.detail, "logical-type-limit");
    }
    #[test]
    fn repeated_structural_leaves_share_descriptors_and_keep_expanded_node_counts() {
        let inner = zkc_test_support::variants::logical("Inner", json!([["yes", ["bool"]]]));
        let sequence = format!("sequence<{inner}>");
        let nested = format!("sequence<{sequence}>");
        let outer = zkc_test_support::variants::logical(
            "Outer",
            json!([["values", [&sequence, &sequence, &nested, &nested]]]),
        );
        // Outer + 2*(sequence, Inner, bool) + 2*(sequence, sequence, Inner, bool).
        for nodes in [14, 15] {
            let mut budget = ParseBudget {
                remaining: nodes,
                ..ParseBudget::new()
            };
            let parsed = LogicalType::parse_nested(&outer, 0, &mut budget);
            if nodes == 14 {
                let error = parsed.unwrap_err();
                assert_eq!(error.code, ErrorCode::Type);
                assert_eq!(error.detail, "logical-type-limit");
                continue;
            }
            assert_eq!(budget.remaining, 0);
            let ty = parsed.unwrap();
            let payload = ty.variant_descriptor().unwrap().alternatives()[0].payload();
            assert!(std::ptr::eq(
                payload[0].structural().unwrap(),
                payload[1].structural().unwrap()
            ));
            let a = payload[0]
                .sequence_element()
                .unwrap()
                .variant_descriptor()
                .unwrap();
            let b = payload[1]
                .sequence_element()
                .unwrap()
                .variant_descriptor()
                .unwrap();
            assert!(Arc::ptr_eq(a, b));
            let c = payload[2]
                .sequence_element()
                .unwrap()
                .sequence_element()
                .unwrap()
                .variant_descriptor()
                .unwrap();
            let d = payload[3]
                .sequence_element()
                .unwrap()
                .sequence_element()
                .unwrap()
                .variant_descriptor()
                .unwrap();
            assert!(Arc::ptr_eq(c, d));
            assert!(
                !Arc::ptr_eq(a, c),
                "different depths have independent admission entries"
            );
        }
    }

    #[test]
    fn descriptor_allocation_charge_has_an_exact_boundary() {
        let variant = zkc_test_support::variants::logical("One", json!([["value", ["bool"]]]));
        for (spelling, charge) in [
            ("sequence<bool>".to_owned(), 512 + 256),
            (variant.clone(), 512 + 4 * variant.len() + 256 + 256),
        ] {
            for bytes in [charge - 1, charge] {
                let mut budget = ParseBudget {
                    bytes,
                    ..ParseBudget::new()
                };
                let result = LogicalType::parse_nested(&spelling, 0, &mut budget);
                if bytes == charge {
                    assert!(result.is_ok());
                    assert_eq!(budget.bytes, 0);
                } else {
                    let error = result.unwrap_err();
                    assert_eq!(error.code, ErrorCode::Limit);
                    assert_eq!(error.detail, "type descriptor byte ceiling");
                }
            }
        }
    }

    #[test]
    fn cached_variant_permissions_match_recursive_payload_checks() {
        use super::super::PhysicalType;
        fn message(t: &LogicalType) -> bool {
            if let Some(v) = t.variant_descriptor() {
                t.is_duplicable()
                    && v.alternatives()
                        .iter()
                        .flat_map(|a| a.payload())
                        .all(message)
            } else if let Some(t) = t.sequence_element() {
                message(t)
            } else {
                t.is_native_message_data()
            }
        }
        fn port(t: &LogicalType) -> bool {
            if let Some(v) = t.variant_descriptor() {
                t.is_duplicable() && v.alternatives().iter().flat_map(|a| a.payload()).all(port)
            } else if let Some(s) = t.structural() {
                s.arguments().iter().all(|a| match a {
                    TypeArgument::Type(t) => port(t),
                    _ => true,
                })
            } else {
                true
            }
        }
        fn represented(t: &LogicalType) -> bool {
            if let Some(v) = t.variant_descriptor() {
                v.alternatives()
                    .iter()
                    .flat_map(|a| a.payload())
                    .all(represented)
            } else if let Some(t) = t.sequence_element() {
                represented(t)
            } else {
                PhysicalType::default_for(t.clone()).is_ok()
            }
        }
        let child =
            zkc_test_support::variants::logical("Child", json!([["some", ["bool"]], ["none", []]]));
        for leaf in [
            "bool".into(),
            "rng:bls12-381.fr".into(),
            "resource_unit:Guard".into(),
            format!("sequence<{child}>"),
            format!("fixed_vector<{child},2>"),
            "fixed_vector<field:koala-bear,8>".into(),
        ] {
            let spelling = zkc_test_support::variants::logical(
                "Root",
                json!([["value", [leaf]], ["empty", []]]),
            );
            let t = LogicalType::parse(&spelling).unwrap();
            assert_eq!(t.is_native_message_data(), message(&t));
            assert_eq!(t.is_program_port(), port(&t));
            assert_eq!(
                PhysicalType::default_for(t.clone()).is_ok(),
                represented(&t)
            );
        }
    }
    #[test]
    fn inline_variant_cache_cannot_bypass_a_leaf_spellings_own_expansion_limit() {
        use zkc_test_support::variants::encode_tree;
        let mut nominal = json!("aaaaaaaaaa");
        let mut witness = None;
        for _ in 0..14 {
            nominal = json!([&nominal, &nominal]);
            let inner = json!([&nominal, [["a", ["bool"]]]]);
            let spelling = encode_tree(inner.clone());
            if LogicalType::parse(&spelling).is_ok() {
                continue;
            }
            let inline = json!(["Mid", [["n", [&inner]]]]);
            let root = json!(["padding".repeat(512), [["m", [&inline]]]]);
            // It must be valid inline under the containing graph's own bound.
            if LogicalType::parse(&encode_tree(root)).is_ok() {
                witness = Some((spelling, inline));
                break;
            }
        }
        let (inner, inline) = witness.expect("bounded expansion counterexample");
        let outer = LogicalType::parse(&encode_tree(json!([
            "padding".repeat(512),
            [["m", [&inline]]]
        ])))
        .unwrap();
        let nested = outer.variant_descriptor().unwrap().alternatives()[0].payload()[0]
            .variant_descriptor()
            .unwrap()
            .alternatives()[0]
            .payload()[0]
            .variant_descriptor()
            .unwrap();
        assert_eq!(
            nested.nominal_identity().unwrap_err().detail,
            "variant:graph-limit"
        );
        assert_eq!(
            outer
                .variant_descriptor()
                .unwrap()
                .nominal_identity()
                .unwrap(),
            json!("padding".repeat(512))
        );

        let leaf = format!("sequence<{inner}>");
        let error = LogicalType::parse(&leaf).unwrap_err();
        assert_eq!(error.detail, "variant:graph-limit");
        for arms in [
            json!([["m", [&inline]], ["s", [&leaf]]]),
            json!([["s", [&leaf]], ["m", [&inline]]]),
        ] {
            let root = encode_tree(json!(["padding".repeat(512), arms]));
            let error = LogicalType::parse(&root).unwrap_err();
            assert_eq!(error.code, ErrorCode::Type);
            assert_eq!(error.detail, "variant:graph-limit");
        }
    }

    #[test]
    fn a_valid_inline_variant_and_standalone_leaf_share_after_spelling_validation() {
        use zkc_test_support::variants::encode_tree;
        let inner = json!(["Inner", [["a", ["bool"]]]]);
        let inline = json!(["Mid", [["n", [&inner]]]]);
        let leaf = format!("sequence<{}>", encode_tree(inner));
        for reversed in [false, true] {
            let mut arms = vec![json!(["m", [&inline]]), json!(["s", [&leaf]])];
            if reversed {
                arms.reverse();
            }
            let root = LogicalType::parse(&encode_tree(json!(["Root", arms]))).unwrap();
            let arms = root.variant_descriptor().unwrap().alternatives();
            let a = arms[usize::from(reversed)].payload()[0]
                .variant_descriptor()
                .unwrap()
                .alternatives()[0]
                .payload()[0]
                .variant_descriptor()
                .unwrap();
            let b = arms[usize::from(!reversed)].payload()[0]
                .sequence_element()
                .unwrap()
                .variant_descriptor()
                .unwrap();
            assert!(Arc::ptr_eq(a, b));
        }
    }
}
