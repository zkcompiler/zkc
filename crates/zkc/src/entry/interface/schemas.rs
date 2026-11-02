use super::syntax::Leaf;
use super::{InterfaceError as E, Result, hash, identifier, raw::*, require, text};
use std::collections::{BTreeMap, BTreeSet};
mod logical;
pub(super) use logical::{native_width, row_bound};

pub(in crate::entry) struct Schemas<'a> {
    remaining: usize,
    retained: usize,
    retained_limit: usize,
    leaves: BTreeMap<&'a str, Leaf>,
    schemas: BTreeMap<&'a str, &'a Schema>,
}
impl<'a> Schemas<'a> {
    #[cfg(test)]
    pub(in crate::entry) fn new() -> Self {
        Self::with_limits(super::InterfaceLimits::DEFAULT)
    }
    /// Validation work and the retained summary charge use the Host's
    /// selected interface admission allowances.
    pub(in crate::entry) fn with_limits(limits: super::InterfaceLimits) -> Self {
        Self {
            remaining: limits.work,
            retained: 0,
            retained_limit: limits.descriptor_bytes,
            leaves: BTreeMap::new(),
            schemas: BTreeMap::new(),
        }
    }
    pub(super) fn charge(&mut self, count: usize) -> Result<()> {
        self.remaining = self.remaining.checked_sub(count).ok_or(E::Limit)?;
        Ok(())
    }
    pub(super) fn setup_properties(&self, spelling: &str) -> Result<(&'static str, bool)> {
        self.leaves
            .get(spelling)
            .map(|leaf| (leaf.head, leaf.needs_setup))
            .ok_or(E::Schema)
    }
    pub(in crate::entry) fn finish(self) -> BTreeMap<String, Leaf> {
        self.leaves
            .into_iter()
            .map(|(s, l)| (s.to_owned(), l))
            .collect()
    }
    fn leaf(&mut self, spelling: &'a str) -> Result<&Leaf> {
        self.charge(spelling.len() + 1)?;
        text(spelling, 256 * 1024)?;
        if !self.leaves.contains_key(spelling) {
            let leaf = Leaf::parse(spelling, &mut self.remaining)?;
            self.retained = self
                .retained
                .checked_add(
                    spelling.len()
                        + 256
                        + leaf
                            .alternatives
                            .iter()
                            .map(|(label, payload)| {
                                label.len() + payload.iter().map(|s| s.len() + 32).sum::<usize>()
                            })
                            .sum::<usize>(),
                )
                .ok_or(E::Limit)?;
            require(self.retained <= self.retained_limit, E::Limit)?;
            self.leaves.insert(spelling, leaf);
        }
        Ok(&self.leaves[spelling])
    }
    pub(in crate::entry) fn check(&mut self, schema: &'a Schema, depth: usize) -> Result<()> {
        use Permission::*;
        require(depth <= 32, E::Limit)?;
        self.charge(1 + schema.display_type.len() + schema.identity.len())?;
        text(&schema.display_type, 256 * 1024)?;
        require(hash(&schema.identity), E::Schema)?;
        require(
            !schema.sealed
                || matches!(
                    schema.kind,
                    Kind::Record | Kind::LogicalRecord | Kind::Variant | Kind::Associated
                ),
            E::Schema,
        )?;
        if let Some(generated) = &schema.generated {
            self.charge(1 + generated.len())?;
            require(
                hash(generated)
                    && matches!(schema.kind, Kind::Record | Kind::Variant | Kind::Associated),
                E::Schema,
            )?;
        }
        require(
            schema.leaves.len() <= 1024 && schema.custody <= 1024,
            E::Limit,
        )?;
        require(
            (schema.kind == Kind::Array) == schema.element.is_some(),
            E::Schema,
        )?;
        require(
            schema.kind == Kind::LogicalRecord || schema.roles.is_empty(),
            E::Schema,
        )?;
        require(schema.roles.len() <= 16, E::Limit)?;
        let mut role_names = BTreeSet::new();
        for role in &schema.roles {
            self.charge(1 + role.len())?;
            require(identifier(role) && role_names.insert(role), E::Schema)?;
        }
        if let Some(element) = &schema.element {
            self.check(element, depth + 1)?;
            require(
                schema
                    .permissions
                    .iter()
                    .all(|p| element.permissions.contains(p)),
                E::Schema,
            )?;
        }
        require(
            schema.permissions.windows(2).all(|p| p[0] < p[1]),
            E::Schema,
        )?;
        require(
            !schema.permissions.contains(&Copy) || schema.permissions.contains(&Drop),
            E::Schema,
        )?;
        require(
            schema.kind != Kind::Associated || !schema.constructible,
            E::Schema,
        )?;
        require(
            schema.fields.is_empty() || schema.alternatives.is_empty(),
            E::Schema,
        )?;
        for (index, spelling) in schema.leaves.iter().enumerate() {
            let leaf = self.leaf(spelling)?;
            if index < schema.custody as usize {
                continue;
            }
            require(
                !schema.constructible
                    || matches!(
                        schema.kind,
                        Kind::Record | Kind::Tuple | Kind::Array | Kind::Variant
                    )
                    || leaf.constructible,
                E::Schema,
            )?;
            for permission in &schema.permissions {
                require(
                    match permission {
                        Copy => leaf.copy,
                        Drop => leaf.drop,
                    },
                    E::Schema,
                )?;
            }
        }
        let start = schema.custody as usize;
        if schema.custody != 0 {
            require(
                !schema.permissions.contains(&Copy)
                    && if schema.kind == Kind::LogicalRecord {
                        start == schema.roles.len() && schema.leaves.is_empty()
                    } else {
                        start == 1
                            && matches!(
                                schema.kind,
                                Kind::Record | Kind::Variant | Kind::Associated
                            )
                            && !schema.constructible
                            && schema.leaves.first().is_some_and(|l| {
                                l == &format!("resource_unit:zkl_resource_{}", schema.identity)
                            })
                    },
                E::Schema,
            )?;
        }
        if !schema.alternatives.is_empty() {
            require(
                schema.kind == Kind::Variant && schema.leaves.len() == start + 1,
                E::Schema,
            )?;
            let leaf = &self.leaves[schema.leaves[start].as_str()];
            require(
                leaf.source_identity.as_deref() == Some(schema.identity.as_str()),
                E::Schema,
            )?;
            let alternatives = leaf.alternatives.clone();
            require(schema.alternatives.len() == alternatives.len(), E::Schema)?;
            let mut names = BTreeSet::new();
            for (index, (actual, expected)) in
                schema.alternatives.iter().zip(&alternatives).enumerate()
            {
                require(
                    identifier(&actual.name)
                        && names.insert(&actual.name)
                        && expected.0 == crate::source_names::native_alternative_name(index as u32),
                    E::Schema,
                )?;
                let payload = &expected.1;
                self.fields(&actual.fields, payload, 0, depth, &schema.permissions)?;
            }
        } else if schema.is_logical() && !schema.kind.is_handle() {
            self.logical_fields(schema, depth)?;
        } else if !schema.fields.is_empty() {
            self.fields(
                &schema.fields,
                &schema.leaves,
                start,
                depth,
                &schema.permissions,
            )?;
        } else {
            require(schema.leaves.len() <= start.max(1), E::Schema)?;
            if start == 0
                && let Some(leaf) = schema.leaves.first()
            {
                require(
                    !matches!(self.leaves[leaf.as_str()].head, "variant" | "resource_unit"),
                    E::Schema,
                )?;
            }
        }
        self.logical_schema(schema, depth)?;
        self.shape(schema)?;
        if let Some(previous) = self.schemas.insert(&schema.identity, schema) {
            self.charge(1 + schema.leaves.len() + schema.fields.len() + schema.alternatives.len())?;
            // Children were checked and interned first, so their exact identities
            // suffice here. Avoid recursively comparing repeated type subtrees.
            require(same_schema(previous, schema), E::Schema)?;
        }
        Ok(())
    }
    fn fields(
        &mut self,
        fields: &'a [Field],
        leaves: &[String],
        start: usize,
        depth: usize,
        permissions: &[Permission],
    ) -> Result<()> {
        let mut next = start;
        let mut names = BTreeSet::new();
        let mut positional = None;
        for (index, field) in fields.iter().enumerate() {
            self.charge(1 + field.name.len())?;
            text(&field.name, 128)?;
            let numbered = field.name.bytes().all(|b| b.is_ascii_digit());
            let expected_numbered = *positional.get_or_insert(numbered);
            require(
                numbered == expected_numbered
                    && (if numbered {
                        field.name == index.to_string()
                    } else {
                        identifier(&field.name)
                    })
                    && names.insert(&field.name)
                    && field.offset as usize == next,
                E::Schema,
            )?;
            let end = next
                .checked_add(field.schema.leaves.len())
                .ok_or(E::Limit)?;
            require(
                leaves.get(next..end) == Some(field.schema.leaves.as_slice()),
                E::Schema,
            )?;
            self.check(&field.schema, depth + 1)?;
            require(
                !field.schema.is_logical()
                    && field.placement.is_none()
                    && field.maximum_rows.get().is_none()
                    && permissions
                        .iter()
                        .all(|p| field.schema.permissions.contains(p)),
                E::Schema,
            )?;
            next = end;
        }
        require(next == leaves.len(), E::Schema)
    }
    pub(super) fn participants(&mut self, schema: &Schema) -> Result<()> {
        self.charge(1 + schema.leaves.len())?;
        require(
            schema.permissions.contains(&Permission::Copy)
                && schema
                    .leaves
                    .iter()
                    .all(|leaf| self.leaves[leaf.as_str()].participants),
            E::Schema,
        )?;
        if let Some(element) = &schema.element {
            self.participants(element)?;
        }
        for field in schema
            .fields
            .iter()
            .chain(schema.alternatives.iter().flat_map(|a| &a.fields))
        {
            self.participants(&field.schema)?;
        }
        Ok(())
    }
    fn shape(&self, s: &Schema) -> Result<()> {
        let start = s.custody as usize;
        require(
            s.kind == Kind::Variant || s.alternatives.is_empty(),
            E::Schema,
        )?;
        let valid = match s.kind {
            Kind::Oracle | Kind::OracleSequence => {
                s.custody == 0
                    && !s.constructible
                    && s.leaves.is_empty()
                    && s.permissions == [Permission::Copy, Permission::Drop]
                    && s.fields.is_empty()
            }
            Kind::LogicalRecord => !s.constructible && s.leaves.is_empty(),
            Kind::Variant => !s.alternatives.is_empty(),
            Kind::Associated => s.fields.len() == 1 && s.fields[0].name == "value",
            Kind::Record | Kind::Tuple | Kind::Array => {
                if s.is_logical() && (s.constructible || s.custody != 0 || !s.leaves.is_empty()) {
                    return Err(E::Schema);
                }
                if !s.is_logical() && s.fields.is_empty() && s.leaves.len() != start {
                    return Err(E::Schema);
                }
                s.fields.iter().enumerate().all(|(i, f)| {
                    (if s.kind == Kind::Record {
                        identifier(&f.name)
                    } else {
                        f.name == i.to_string() && f.public
                    }) && (s.kind != Kind::Array
                        || s.element
                            .as_ref()
                            .is_some_and(|e| f.schema.identity == e.identity))
                })
            }
            Kind::Unit => s.fields.is_empty() && s.leaves.is_empty(),
            _ => {
                s.fields.is_empty() && s.leaves.len() == 1 && {
                    let kind = self.leaves[s.leaves[0].as_str()].head;
                    match s.kind {
                        Kind::Boolean => kind == "bool",
                        Kind::Index => kind == "index",
                        Kind::Field => kind == "field",
                        Kind::Group => kind == "group",
                        Kind::Builtin => matches!(
                            kind,
                            "vector"
                                | "matrix"
                                | "groups"
                                | "indices"
                                | "bytes"
                                | "shake128_state"
                                | "polynomial"
                                | "table"
                                | "point"
                                | "round"
                                | "sequence"
                                | "field_array"
                                | "commitment"
                                | "commitments"
                                | "proof"
                                | "prover_key"
                                | "verifier_key"
                                | "opening_state"
                                | "opening_states"
                        ),
                        _ => false,
                    }
                }
            }
        };
        require(valid, E::Schema)
    }
}
fn same_fields(a: &[Field], b: &[Field]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|(a, b)| {
            a.name == b.name
                && a.offset == b.offset
                && a.public == b.public
                && a.placement == b.placement
                && a.schema.identity == b.schema.identity
                && a.maximum_rows == b.maximum_rows
        })
}
fn same_schema(a: &Schema, b: &Schema) -> bool {
    a.kind == b.kind
        && a.identity == b.identity
        && a.generated == b.generated
        && a.display_type == b.display_type
        && a.custody == b.custody
        && a.sealed == b.sealed
        && a.roles == b.roles
        && a.element.as_ref().map(|e| &e.identity) == b.element.as_ref().map(|e| &e.identity)
        && a.constructible == b.constructible
        && a.permissions == b.permissions
        && a.leaves == b.leaves
        && a.oracle == b.oracle
        && a.maximum == b.maximum
        && a.data_schema.get().map(|s| &s.identity) == b.data_schema.get().map(|s| &s.identity)
        && same_fields(&a.fields, &b.fields)
        && a.alternatives.len() == b.alternatives.len()
        && a.alternatives
            .iter()
            .zip(&b.alternatives)
            .all(|(a, b)| a.name == b.name && same_fields(&a.fields, &b.fields))
}
/// Source constructor authority is independent of native decoding.
pub(in crate::entry) fn check_import(schema: &Schema) -> std::result::Result<(), String> {
    if schema.is_logical() || schema.custody != 0 || schema.sealed || !schema.constructible {
        return Err("entry-input-constructor".into());
    }
    if let Some(element) = &schema.element {
        check_import(element)?;
    }
    for field in schema
        .fields
        .iter()
        .chain(schema.alternatives.iter().flat_map(|a| &a.fields))
    {
        if !field.public {
            return Err("entry-input-constructor".into());
        }
        check_import(&field.schema)?;
    }
    Ok(())
}
pub(in crate::entry) fn check_export(schema: &Schema) -> std::result::Result<(), String> {
    if schema.is_logical() || schema.custody != 0 || !schema.permissions.contains(&Permission::Copy)
    {
        return Err("entry-output-custody".into());
    }
    Ok(())
}
