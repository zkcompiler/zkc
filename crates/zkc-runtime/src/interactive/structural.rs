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
static CONSTRUCTORS: &[Constructor] = &[Constructor {
    name: "fixed_vector",
    kind: Type::FixedVector,
    parameters: &[ArgumentKind::Type, ArgumentKind::Nat],
    copy: true,
    drop: true,
}];

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

pub(super) struct ParseBudget {
    remaining: usize,
}
impl ParseBudget {
    pub(super) fn new() -> Self {
        Self {
            remaining: TYPE_NODE_LIMIT,
        }
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
    let arguments = arguments(&parts, constructor.parameters, depth + 1, budget)?;
    Ok(Arc::new(StructuralType {
        constructor,
        arguments: arguments.into_boxed_slice(),
    }))
}

impl LogicalType {
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
    fn budget_is_shared_across_variant_payloads_and_type_arguments() {
        let inner = zkc_test_support::variants::logical("Inner", json!([["value", ["bool"]]]));
        let outer = zkc_test_support::variants::logical(
            "Outer",
            json!([["value", [format!("fixed_vector<{inner},0>")]]]),
        );
        // Outer variant, application, inner variant, Bool, Nat: five nodes.
        let mut budget = ParseBudget { remaining: 5 };
        assert!(LogicalType::parse_nested(&outer, 0, &mut budget).is_ok());
        assert_eq!(budget.remaining, 0);
        let mut budget = ParseBudget { remaining: 4 };
        let error = LogicalType::parse_nested(&outer, 0, &mut budget).unwrap_err();
        assert_eq!(error.code, ErrorCode::Type);
        assert_eq!(error.detail, "logical-type-limit");
    }
}
