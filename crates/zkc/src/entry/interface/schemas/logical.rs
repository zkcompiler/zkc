//! Independent logical metadata checks, grounded in Contracts/OracleKinds.cpp
//! and LanguageInterfaceReader.cpp. No native graph or handle is admitted here.
use super::*;

impl<'a> Schemas<'a> {
    pub(super) fn logical_schema(&mut self, schema: &'a Schema, depth: usize) -> Result<()> {
        if schema.kind == Kind::LogicalRecord && schema.roles.is_empty() {
            // Current-schema migration alternative for the brace source profile.
            // Remove with its Layout seam when the source profile is retired.
            require(
                schema.custody == 0 && schema.permissions == [Permission::Copy, Permission::Drop],
                E::Schema,
            )?;
            let mut direct_handle = false;
            for field in &schema.fields {
                self.charge(1)?;
                require(field.placement.is_none(), E::Schema)?;
                if field.schema.kind.is_handle() {
                    direct_handle = true;
                } else {
                    self.shared(&field.schema)?;
                }
            }
            require(direct_handle, E::Schema)?;
        }
        let handle = schema.kind.is_handle();
        require(
            schema.oracle.get().is_some() == handle
                && schema.data_schema.get().is_some() == handle
                && schema.maximum.get().is_some() == (schema.kind == Kind::OracleSequence),
            E::Schema,
        )?;
        if let Some(oracle) = schema.oracle.get() {
            self.charge(1 + oracle.kind.len() + oracle.arguments.len())?;
            require(
                oracle.kind == "table" && matches!(oracle.arguments.len(), 1 | 2),
                E::Schema,
            )?;
            let OracleArgument::Type(row) = &oracle.arguments[0] else {
                return Err(E::Schema);
            };
            let facts = self.leaf(row)?;
            require(
                facts.copy && facts.drop && facts.total && facts.participants,
                E::Schema,
            )?;
            require(
                oracle.arguments.len() == 1
                    || matches!(oracle.arguments[1], OracleArgument::Nat(_)),
                E::Schema,
            )?;
            // Table::Data is specialized for scalar field/group/index rows;
            // every other canonical row is an ordinary sequence of that row.
            let data = match facts.head {
                "field" => format!("vector:{}", row.strip_prefix("field:").ok_or(E::Schema)?),
                "group" => format!("groups:{}", row.strip_prefix("group:").ok_or(E::Schema)?),
                "index" => "indices".to_owned(),
                _ => format!("sequence<{row}>"),
            };
            let expected = if schema.kind == Kind::OracleSequence {
                format!("sequence<{data}>")
            } else {
                data
            };
            let associated = schema.data_schema.get().ok_or(E::Schema)?;
            self.check(associated, depth + 1)?;
            require(
                associated.kind == Kind::Builtin && associated.leaves == [expected],
                E::Schema,
            )?;
            self.shared(associated)?;
        }
        Ok(())
    }
    pub(super) fn logical_fields(&mut self, schema: &'a Schema, depth: usize) -> Result<()> {
        let mut offset = schema.custody as usize;
        let mut names = BTreeSet::new();
        require(schema.leaves.is_empty(), E::Schema)?;
        for (index, field) in schema.fields.iter().enumerate() {
            self.charge(1 + field.name.len())?;
            require(
                (if schema.kind == Kind::LogicalRecord {
                    identifier(&field.name)
                } else {
                    field.name == index.to_string()
                }) && names.insert(&field.name)
                    && field.offset as usize == offset,
                E::Schema,
            )?;
            self.check(&field.schema, depth + 1)?;
            require(
                schema
                    .permissions
                    .iter()
                    .all(|p| field.schema.permissions.contains(p)),
                E::Schema,
            )?;
            if schema.kind == Kind::LogicalRecord && !schema.roles.is_empty() {
                let formula = field.placement.as_ref().ok_or(E::Schema)?;
                super::super::placement::check(&field.schema, formula, schema.roles.len(), self)?;
            } else {
                require(field.placement.is_none(), E::Schema)?;
            }
            if field.schema.kind.is_handle() {
                row_bound(&field.schema, field.maximum_rows.get().copied())?;
            } else {
                require(field.maximum_rows.get().is_none(), E::Schema)?;
            }
            offset = offset
                .checked_add(body_width(&field.schema))
                .ok_or(E::Limit)?;
            require(offset <= 1024, E::Limit)?;
        }
        Ok(())
    }
    pub(super) fn shared(&mut self, schema: &Schema) -> Result<()> {
        self.charge(1 + schema.leaves.len())?;
        require(
            !schema.is_logical()
                && schema.custody == 0
                && schema.permissions == [Permission::Copy, Permission::Drop]
                && schema
                    .leaves
                    .iter()
                    .all(|l| self.leaves[l.as_str()].total && self.leaves[l.as_str()].participants),
            E::Schema,
        )?;
        if let Some(element) = &schema.element {
            self.shared(element)?;
        }
        for field in schema
            .fields
            .iter()
            .chain(schema.alternatives.iter().flat_map(|a| &a.fields))
        {
            self.shared(&field.schema)?;
        }
        Ok(())
    }
}

/// Unsized row bounds and sequence capacities are independent, full u64 values.
pub(in crate::entry::interface) fn row_bound(
    schema: &Schema,
    maximum: Option<Unsigned>,
) -> Result<()> {
    let oracle = schema.oracle.get().ok_or(E::Schema)?;
    require(
        (oracle.arguments.len() == 1) == maximum.is_some(),
        E::Schema,
    )
}

/// Protocol slots differ from logical-record body offsets: every handle, even a
/// zero-capacity sequence, occupies its data/anchor pair.
pub(in crate::entry::interface) fn native_width(schema: &Schema) -> usize {
    if schema.kind.is_handle() {
        2
    } else if schema.is_logical() {
        schema.custody as usize
            + schema
                .fields
                .iter()
                .map(|f| native_width(&f.schema))
                .sum::<usize>()
    } else {
        schema.leaves.len()
    }
}
pub(in crate::entry::interface) fn body_width(schema: &Schema) -> usize {
    if schema.kind.is_handle() {
        1
    } else if schema.is_logical() {
        schema.custody as usize
            + schema
                .fields
                .iter()
                .map(|f| body_width(&f.schema))
                .sum::<usize>()
    } else {
        schema.leaves.len()
    }
}
