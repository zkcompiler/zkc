//! Independent logical metadata checks, grounded in Contracts/OracleKinds.cpp
//! and LanguageInterfaceReader.cpp. No native graph or handle is admitted here.
use super::*;

impl<'a> Schemas<'a> {
    pub(super) fn logical_schema(&mut self, schema: &'a Schema, depth: usize) -> Result<()> {
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
        let mut offset = 0;
        let mut names = BTreeSet::new();
        let mut handle = false;
        require(schema.leaves.is_empty(), E::Schema)?;
        for field in &schema.fields {
            self.charge(1 + field.name.len())?;
            require(
                identifier(&field.name)
                    && names.insert(&field.name)
                    && field.offset as usize == offset,
                E::Schema,
            )?;
            self.check(&field.schema, depth + 1)?;
            require(
                field.schema.kind != Kind::LogicalRecord
                    && !field.schema.custody
                    && field.schema.permissions == [Permission::Copy, Permission::Drop],
                E::Schema,
            )?;
            if field.schema.kind.is_handle() {
                row_bound(&field.schema, field.maximum_rows.get().copied())?;
                offset += 1;
                handle = true;
            } else {
                require(field.maximum_rows.get().is_none(), E::Schema)?;
                self.shared(&field.schema)?;
                offset += field.schema.leaves.len();
            }
            require(offset <= 1024, E::Limit)?;
        }
        require(handle, E::Schema)
    }
    pub(super) fn shared(&mut self, schema: &Schema) -> Result<()> {
        self.charge(1 + schema.leaves.len())?;
        require(
            !schema.kind.is_logical()
                && !schema.custody
                && schema.permissions == [Permission::Copy, Permission::Drop]
                && schema
                    .leaves
                    .iter()
                    .all(|l| self.leaves[l.as_str()].total && self.leaves[l.as_str()].participants),
            E::Schema,
        )?;
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
    if schema.kind == Kind::LogicalRecord {
        schema.fields.iter().map(|f| native_width(&f.schema)).sum()
    } else if schema.kind.is_handle() {
        2
    } else {
        schema.leaves.len()
    }
}
