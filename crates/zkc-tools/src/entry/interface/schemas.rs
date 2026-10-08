use super::{InterfaceError as E, Result, hash, identifier, raw::*, require, text};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use zkc_runtime::interactive::{Identity, LogicalType, Type};

struct Leaf {
    ty: LogicalType,
    shared: bool,
    needs_setup: bool,
    source_identity: Option<String>,
}
pub(super) struct Schemas<'a> {
    remaining: usize,
    retained: usize,
    leaves: BTreeMap<&'a str, Leaf>,
    schemas: BTreeMap<&'a str, &'a Schema>,
}
impl<'a> Schemas<'a> {
    pub(super) fn new() -> Self {
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
    pub(super) fn setup_properties(&self, spelling: &str) -> Result<(Type, bool)> {
        self.leaves
            .get(spelling)
            .map(|leaf| (leaf.ty.kind(), leaf.needs_setup))
            .ok_or(E::Schema)
    }
    pub(super) fn finish(self) -> BTreeMap<String, LogicalType> {
        self.leaves
            .into_iter()
            .map(|(s, l)| (s.to_owned(), l.ty))
            .collect()
    }
    fn leaf(&mut self, spelling: &'a str) -> Result<&Leaf> {
        self.charge(spelling.len() + 1)?;
        text(spelling, 256 * 1024)?;
        if !self.leaves.contains_key(spelling) {
            let ty = LogicalType::parse(spelling).map_err(|_| E::Schema)?;
            require(ty.spelling() == spelling, E::Schema)?;
            self.retained = self
                .retained
                .checked_add(ty.descriptor_bytes())
                .ok_or(E::Limit)?;
            require(self.retained <= 16 * 1024 * 1024, E::Limit)?;
            let shared = shared(&ty, &mut self.remaining)?;
            let needs_setup = needs_setup(&ty, &mut self.remaining)?;
            let source_identity = ty.variant_descriptor().and_then(|d| {
                let nominal = d.nominal_identity().ok()?;
                let values = nominal.as_array()?;
                if values.len() != 2 || values[0].as_str()? != "zkc.language" {
                    return None;
                }
                let key = values[1].as_str()?;
                (!key.is_empty()).then(|| format!("{:x}", Sha256::digest(key.as_bytes())))
            });
            self.leaves.insert(
                spelling,
                Leaf {
                    ty,
                    shared,
                    needs_setup,
                    source_identity,
                },
            );
        }
        Ok(&self.leaves[spelling])
    }
    pub(super) fn check(&mut self, schema: &'a Schema, depth: usize) -> Result<()> {
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
            schema.fields.is_empty() || schema.alternatives.is_empty(),
            E::Schema,
        )?;
        for (index, spelling) in schema.leaves.iter().enumerate() {
            let leaf = self.leaf(spelling)?;
            if schema.custody && index == 0 {
                continue;
            }
            for permission in &schema.permissions {
                require(
                    match permission {
                        Copy => leaf.ty.is_duplicable(),
                        Drop => leaf.ty.is_discardable(),
                        Wire => leaf.ty.is_native_message_data(),
                        Share => {
                            !schema.fields.is_empty()
                                || !schema.alternatives.is_empty()
                                || leaf.shared
                        }
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
                    && !schema.permissions.contains(&Wire)
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
            let descriptor = leaf.ty.variant_descriptor().ok_or(E::Schema)?.clone();
            require(
                schema.alternatives.len() == descriptor.alternatives().len(),
                E::Schema,
            )?;
            for (actual, expected) in schema.alternatives.iter().zip(descriptor.alternatives()) {
                require(
                    identifier(&actual.name) && actual.name == expected.label(),
                    E::Schema,
                )?;
                let payload: Vec<_> = expected
                    .payload()
                    .iter()
                    .map(LogicalType::spelling)
                    .collect();
                self.fields(&actual.fields, &payload, 0, depth, &schema.permissions)?;
            }
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
                    !matches!(
                        self.leaves[leaf.as_str()].ty.kind(),
                        Type::Variant | Type::ResourceUnit
                    ),
                    E::Schema,
                )?;
            }
        }
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
                permissions
                    .iter()
                    .all(|p| field.schema.permissions.contains(p)),
                E::Schema,
            )?;
            next = end;
        }
        require(next == leaves.len(), E::Schema)
    }
    fn shape(&self, s: &Schema) -> Result<()> {
        let start = usize::from(s.custody);
        require(
            s.kind == Kind::Variant || s.alternatives.is_empty(),
            E::Schema,
        )?;
        let valid = match s.kind {
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
                    let kind = self.leaves[s.leaves[0].as_str()].ty.kind();
                    match s.kind {
                        Kind::Boolean => kind == Type::Bool,
                        Kind::Index => kind == Type::Index,
                        Kind::Field => kind == Type::Field,
                        Kind::Group => kind == Type::Group,
                        Kind::Builtin => matches!(
                            kind,
                            Type::Vector
                                | Type::Matrix
                                | Type::Groups
                                | Type::Indices
                                | Type::Polynomial
                                | Type::Table
                                | Type::Point
                                | Type::Round
                                | Type::Sequence
                                | Type::FieldArray
                                | Type::Commitment
                                | Type::Commitments
                                | Type::Proof
                                | Type::ProverKey
                                | Type::VerifierKey
                                | Type::OpeningState
                                | Type::OpeningStates
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
            a.name == b.name && a.offset == b.offset && a.schema.identity == b.schema.identity
        })
}
fn same_schema(a: &Schema, b: &Schema) -> bool {
    a.kind == b.kind
        && a.identity == b.identity
        && a.display_type == b.display_type
        && a.custody == b.custody
        && a.permissions == b.permissions
        && a.leaves == b.leaves
        && same_fields(&a.fields, &b.fields)
        && a.alternatives.len() == b.alternatives.len()
        && a.alternatives
            .iter()
            .zip(&b.alternatives)
            .all(|(a, b)| a.name == b.name && same_fields(&a.fields, &b.fields))
}
// Source Share is placement permission, separate from Copy and native wire
// encoding. A copyable setup key, for example, is still participant-local.
fn shared(ty: &LogicalType, remaining: &mut usize) -> Result<bool> {
    *remaining = remaining.checked_sub(1).ok_or(E::Limit)?;
    if let Some(element) = ty.sequence_element() {
        return Ok(ty.is_duplicable() && shared(element, remaining)?);
    }
    if let Some(descriptor) = ty.variant_descriptor() {
        let mut result = ty.is_duplicable();
        for ty in descriptor.alternatives().iter().flat_map(|a| a.payload()) {
            result &= shared(ty, remaining)?;
        }
        return Ok(result);
    }
    Ok(matches!(
        ty.kind(),
        Type::Bool
            | Type::Field
            | Type::Group
            | Type::FieldArray
            | Type::Index
            | Type::Indices
            | Type::Vector
            | Type::Matrix
            | Type::Groups
            | Type::Polynomial
            | Type::Table
            | Type::Point
            | Type::Round
            | Type::Commitment
            | Type::Commitments
            | Type::Proof
    ))
}

fn needs_setup(ty: &LogicalType, remaining: &mut usize) -> Result<bool> {
    *remaining = remaining.checked_sub(1).ok_or(E::Limit)?;
    if matches!(ty.kind(), Type::ProverKey | Type::VerifierKey)
        || ty.identity() == Identity::MultilinearKzgBls12381
    {
        return Ok(true);
    }
    if let Some(element) = ty.sequence_element() {
        return needs_setup(element, remaining);
    }
    if let Some(variant) = ty.variant_descriptor() {
        for arm in variant.alternatives() {
            for field in arm.payload() {
                if needs_setup(field, remaining)? {
                    return Ok(true);
                }
            }
        }
    }
    Ok(false)
}
