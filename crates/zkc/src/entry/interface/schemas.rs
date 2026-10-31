use super::syntax::Leaf;
use super::{InterfaceError as E, Result, hash, identifier, raw::*, require, text};
use std::collections::{BTreeMap, BTreeSet};
mod logical;
pub(super) use logical::{native_width, row_bound};

pub(in crate::entry) struct Schemas<'a> {
    remaining: usize,
    retained: usize,
    leaves: BTreeMap<&'a str, Leaf>,
    schemas: BTreeMap<&'a str, &'a Schema>,
}
impl<'a> Schemas<'a> {
    pub(in crate::entry) fn new() -> Self {
        Self {
            remaining: 1_000_000,
            retained: 0,
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
            require(self.retained <= 16 * 1024 * 1024, E::Limit)?;
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
        require(schema.leaves.len() <= 1024, E::Limit)?;
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
            if schema.custody && index == 0 {
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
        let start = usize::from(schema.custody);
        if schema.custody {
            require(
                matches!(schema.kind, Kind::Record | Kind::Variant | Kind::Associated)
                    && !schema.permissions.contains(&Copy)
                    && !schema.constructible
                    && schema.leaves.first().is_some_and(|l| {
                        l == &format!("resource_unit:zkl_resource_{}", schema.identity)
                    }),
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
        } else if schema.kind == Kind::LogicalRecord {
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
                !field.schema.kind.is_logical()
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
    pub(super) fn participants(&self, schema: &Schema) -> Result<()> {
        require(
            schema.permissions.contains(&Permission::Copy)
                && schema
                    .leaves
                    .iter()
                    .all(|leaf| self.leaves[leaf.as_str()].participants),
            E::Schema,
        )
    }
    fn shape(&self, s: &Schema) -> Result<()> {
        let start = usize::from(s.custody);
        require(
            s.kind == Kind::Variant || s.alternatives.is_empty(),
            E::Schema,
        )?;
        let valid = match s.kind {
            Kind::Oracle | Kind::OracleSequence | Kind::LogicalRecord => {
                !s.custody
                    && !s.constructible
                    && s.leaves.is_empty()
                    && s.permissions == [Permission::Copy, Permission::Drop]
                    && (if s.kind == Kind::LogicalRecord {
                        !s.fields.is_empty()
                    } else {
                        s.fields.is_empty()
                    })
            }
            Kind::Variant => !s.alternatives.is_empty(),
            Kind::Associated => s.fields.len() == 1 && s.fields[0].name == "value",
            Kind::Record | Kind::Tuple | Kind::Array => {
                if s.fields.is_empty() && s.leaves.len() != start {
                    return Err(E::Schema);
                }
                s.fields.iter().enumerate().all(|(i, f)| {
                    (if s.kind == Kind::Record {
                        identifier(&f.name)
                    } else {
                        f.name == i.to_string()
                    }) && (s.kind != Kind::Array
                        || f.schema.identity == s.fields[0].schema.identity)
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
                && a.schema.identity == b.schema.identity
                && a.maximum_rows == b.maximum_rows
        })
}
fn same_schema(a: &Schema, b: &Schema) -> bool {
    a.kind == b.kind
        && a.identity == b.identity
        && a.display_type == b.display_type
        && a.custody == b.custody
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
    if schema.kind.is_logical() || schema.custody || !schema.constructible {
        return Err("entry-input-constructor".into());
    }
    for field in schema
        .fields
        .iter()
        .chain(schema.alternatives.iter().flat_map(|a| &a.fields))
    {
        check_import(&field.schema)?;
    }
    Ok(())
}
pub(in crate::entry) fn check_export(schema: &Schema) -> std::result::Result<(), String> {
    if schema.kind.is_logical() || schema.custody || !schema.permissions.contains(&Permission::Copy)
    {
        return Err("entry-output-custody".into());
    }
    Ok(())
}
