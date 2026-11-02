//! Logical application values. Layout and constructor authority come from the
//! authenticated source interface, never from a caller-supplied type spelling.
use super::interface::raw::{Field, Kind, Schema};
use crate::execution::InputValue;
use std::{collections::BTreeMap, sync::Arc};
use zkc_cpu::Value as NativeValue;
use zkc_runtime::vm::Value as _;

type Result<T> = std::result::Result<T, String>;

#[derive(Debug)]
pub enum Value {
    Leaf(InputValue),
    /// An admitted whole value whose representation is inaccessible to callers.
    Opaque(OpaqueValue),
    Unit,
    Tuple(Vec<Value>),
    Array(Vec<Value>),
    Record(BTreeMap<String, Value>),
    Variant {
        alternative: String,
        fields: BTreeMap<String, Value>,
    },
    Associated(Box<Value>),
}
/// Immutable ordinary data retained from an admitted output. Schema metadata is
/// public; storage and construction of this owner are private to the SDK.
#[derive(Clone)]
pub struct OpaqueValue {
    schema: Arc<Schema>,
    value: Arc<Value>,
}
impl std::fmt::Debug for OpaqueValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OpaqueValue")
            .field("type", &self.schema.display_type)
            .field("identity", &self.schema.identity)
            .finish_non_exhaustive()
    }
}
impl OpaqueValue {
    pub fn schema(&self) -> &Schema {
        &self.schema
    }
    /// Compare the generated binding's ordinary schema description. This grants
    /// no construction authority; transport independently checks complete equality.
    pub fn matches_binding(&self, expected: &[u8; 32]) -> bool {
        &schema_fingerprint(&self.schema) == expected
    }
    /// Return an admitted native leaf. This applies only to public native kinds;
    /// it never opens an associated representation or a source record.
    pub fn leaf(&self) -> Result<Value> {
        if !self.schema.sealed
            && matches!(
                self.schema.kind,
                Kind::Boolean | Kind::Index | Kind::Field | Kind::Group | Kind::Builtin
            )
            && let Value::Leaf(_) = self.value.as_ref()
        {
            return Ok(duplicate(&self.value));
        }
        Err("entry-value-projection".into())
    }
    /// Select one public product child. Every subsequent selection is checked
    /// on the returned child, so an inaccessible ancestor cannot be skipped.
    pub fn field(&self, name: &str) -> Result<Value> {
        if self.schema.sealed || self.schema.kind == Kind::Associated {
            return Err("entry-value-projection".into());
        }
        let field = self
            .schema
            .fields
            .iter()
            .find(|f| f.name == name && f.public)
            .ok_or("entry-value-projection")?;
        let value = match self.value.as_ref() {
            Value::Record(values) => values.get(name),
            Value::Tuple(values) | Value::Array(values) => self
                .schema
                .fields
                .iter()
                .position(|f| f.name == name)
                .and_then(|i| values.get(i)),
            _ => None,
        }
        .ok_or("entry-value-projection")?;
        Ok(protect(&field.schema, duplicate(value)))
    }
    /// Inspect the active alternative of an unsealed variant only.
    pub fn alternative(&self) -> Result<&str> {
        if self.schema.sealed {
            return Err("entry-value-projection".into());
        }
        match self.value.as_ref() {
            Value::Variant { alternative, .. } => Ok(alternative),
            _ => Err("entry-value-projection".into()),
        }
    }
    pub fn variant_field(&self, alternative: &str, name: &str) -> Result<Value> {
        if self.alternative()? != alternative {
            return Err("entry-value-alternative".into());
        }
        let arm = self
            .schema
            .alternatives
            .iter()
            .find(|a| a.name == alternative)
            .ok_or("entry-value-projection")?;
        let field = arm
            .fields
            .iter()
            .find(|f| f.name == name && f.public)
            .ok_or("entry-value-projection")?;
        let Value::Variant { fields, .. } = self.value.as_ref() else {
            return Err("entry-value-projection".into());
        };
        Ok(protect(
            &field.schema,
            duplicate(fields.get(name).ok_or("entry-value-projection")?),
        ))
    }
    pub(in crate::entry) fn open(&self, schema: &Schema) -> Result<Value> {
        super::interface::schemas::check_export(schema)?;
        if self.schema.as_ref() != schema {
            return Err("entry-value-schema".into());
        }
        Ok(duplicate(&self.value))
    }
    pub(in crate::entry) fn readable(&self) -> Result<&Value> {
        check_readable_schema(&self.schema)?;
        Ok(&self.value)
    }
    pub(in crate::entry) fn retained_bytes(&self) -> usize {
        // Schemas are bounded by interface admission; charge each retained use.
        self.schema
            .describe()
            .to_string()
            .len()
            .saturating_add(description_bytes(&self.value))
    }
}
pub(in crate::entry) fn schema_fingerprint(schema: &Schema) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    // Compact UTF-8 JSON with recursively sorted object keys. Array order is
    // semantic; downstream serde_json map-storage features must not affect bytes.
    let mut description = schema.describe();
    description.sort_all_objects();
    Sha256::digest(description.to_string().as_bytes()).into()
}
pub(in crate::entry) fn needs_opaque(schema: &Schema) -> bool {
    schema.sealed
        || !schema.constructible
        || (matches!(
            schema.kind,
            Kind::Boolean | Kind::Index | Kind::Field | Kind::Group | Kind::Builtin
        ) && schema.leaves.iter().any(|s| {
            !zkc_runtime::vm::LogicalType::parse(s).is_ok_and(|t| t.is_native_message_data())
        }))
        || schema.kind == Kind::Associated
        || schema
            .element
            .as_ref()
            .is_some_and(|e| super::interface::schemas::check_import(e).is_err())
        || schema
            .fields
            .iter()
            .chain(schema.alternatives.iter().flat_map(|a| &a.fields))
            .any(|f| !f.public)
}
pub(in crate::entry) fn protect(schema: &Schema, value: Value) -> Value {
    if matches!(value, Value::Opaque(_)) || !needs_opaque(schema) {
        value
    } else {
        Value::Opaque(OpaqueValue {
            schema: Arc::new(schema.clone()),
            value: Arc::new(value),
        })
    }
}
impl Value {
    pub fn leaf(&self) -> Result<Value> {
        match self {
            Self::Opaque(value) => value.leaf(),
            Self::Leaf(_) => Ok(duplicate(self)),
            _ => Err("entry-value-projection".into()),
        }
    }
    /// Select a public product child from a transparent description or retained
    /// owner. Opaque storage checks the admitted ancestor before returning a child.
    pub fn field(&self, name: &str) -> Result<Value> {
        match self {
            Self::Opaque(value) => value.field(name),
            Self::Record(values) => values
                .get(name)
                .map(duplicate)
                .ok_or_else(|| "entry-value-projection".into()),
            Self::Tuple(values) | Self::Array(values) => name
                .parse::<usize>()
                .ok()
                .filter(|i| i.to_string() == name)
                .and_then(|i| values.get(i))
                .map(duplicate)
                .ok_or_else(|| "entry-value-projection".into()),
            _ => Err("entry-value-projection".into()),
        }
    }
    pub fn alternative(&self) -> Result<&str> {
        match self {
            Self::Opaque(value) => value.alternative(),
            Self::Variant { alternative, .. } => Ok(alternative),
            _ => Err("entry-value-projection".into()),
        }
    }
    pub fn variant_field(&self, alternative: &str, name: &str) -> Result<Value> {
        match self {
            Self::Opaque(value) => value.variant_field(alternative, name),
            Self::Variant {
                alternative: active,
                fields,
            } if active == alternative => fields
                .get(name)
                .map(duplicate)
                .ok_or_else(|| "entry-value-projection".into()),
            Self::Variant { .. } => Err("entry-value-alternative".into()),
            _ => Err("entry-value-projection".into()),
        }
    }
}
impl From<NativeValue> for Value {
    fn from(value: NativeValue) -> Self {
        Self::Leaf(value.into())
    }
}
impl From<InputValue> for Value {
    fn from(value: InputValue) -> Self {
        Self::Leaf(value)
    }
}

pub(super) fn flatten(schema: &Schema, value: Value, out: &mut Vec<InputValue>) -> Result<()> {
    flatten_checked(schema, value, out, false)
}
fn flatten_checked(
    schema: &Schema,
    value: Value,
    out: &mut Vec<InputValue>,
    retained: bool,
) -> Result<()> {
    if let Value::Opaque(value) = value {
        return flatten_checked(schema, value.open(schema)?, out, true);
    }
    if !retained {
        if schema.is_logical()
            || schema.custody != 0
            || schema.sealed
            || !schema.constructible
            || schema
                .fields
                .iter()
                .chain(schema.alternatives.iter().flat_map(|a| &a.fields))
                .any(|f| !f.public)
        {
            return Err("entry-input-constructor".into());
        }
        // Empty containers retain their element's construction authority even
        // though no runtime child can carry an authenticated retained origin.
        if schema.fields.is_empty()
            && let Some(element) = &schema.element
        {
            super::interface::schemas::check_import(element)?;
        }
    }
    match (schema.kind, value) {
        (Kind::Unit, Value::Unit) => Ok(()),
        (Kind::Tuple, Value::Tuple(values)) | (Kind::Array, Value::Array(values)) => {
            if schema.fields.len() != values.len() {
                return Err("entry-input-shape".into());
            }
            for (field, value) in schema.fields.iter().zip(values) {
                flatten_checked(&field.schema, value, out, retained)?;
            }
            Ok(())
        }
        (Kind::Associated, Value::Associated(value)) if retained => {
            flatten_checked(&schema.fields[0].schema, *value, out, true)
        }
        (Kind::Record, Value::Record(values)) => {
            flatten_fields(&schema.fields, values, out, retained)
        }
        (
            Kind::Variant,
            Value::Variant {
                alternative,
                fields,
            },
        ) => {
            let (index, arm) = schema
                .alternatives
                .iter()
                .enumerate()
                .find(|(_, arm)| arm.name == alternative)
                .ok_or("entry-input-alternative")?;
            let mut payload = Vec::new();
            flatten_fields(&arm.fields, fields, &mut payload, retained)?;
            out.push(InputValue::Variant {
                alternative: index,
                payload,
            });
            Ok(())
        }
        (
            Kind::Boolean | Kind::Index | Kind::Field | Kind::Group | Kind::Builtin,
            Value::Leaf(value),
        ) => {
            if !retained
                && !schema.leaves.iter().all(|s| {
                    zkc_runtime::vm::LogicalType::parse(s).is_ok_and(|t| t.is_native_message_data())
                })
            {
                return Err("entry-input-codec".into());
            }
            if !matches!(
                value,
                InputValue::Native(_)
                    | InputValue::Wire(_)
                    | InputValue::WireSource { .. }
                    | InputValue::Prepared(_)
            ) {
                return Err("entry-input-kind".into());
            }
            out.push(value);
            Ok(())
        }
        _ => Err("entry-input-shape".into()),
    }
}
fn flatten_fields(
    fields: &[Field],
    mut values: BTreeMap<String, Value>,
    out: &mut Vec<InputValue>,
    retained: bool,
) -> Result<()> {
    if fields.len() != values.len() {
        return Err("entry-input-fields".into());
    }
    for field in fields {
        let value = values.remove(&field.name).ok_or("entry-input-fields")?;
        flatten_checked(&field.schema, value, out, retained)?;
    }
    Ok(())
}

/// Bytes one reconstructed schema node allocates in a named description.
const NODE_BYTES: usize = 128;
/// The description bytes a conversion reads from these named values.
pub(super) fn request_bytes<'a>(values: impl IntoIterator<Item = &'a Value>) -> usize {
    values
        .into_iter()
        .map(description_bytes)
        .fold(0usize, usize::saturating_add)
}
/// Charge converting named values to native operands: the values' description
/// bytes are read once as logical work, and the converted operand list is a
/// fresh allocation.
pub(super) fn charge_conversion(
    ledger: &zkc_runtime::vm::ExecutionLedger,
    read: usize,
    operands: usize,
) -> Result<()> {
    ledger
        .charge(
            zkc_runtime::vm::WorkBudget {
                instructions: 0,
                iterations: 0,
                logical_bytes: read as u64,
            },
            operands.saturating_mul(std::mem::size_of::<InputValue>()),
        )
        .map_err(|_| "entry-request-limit".into())
}
/// Charge reconstructing named results: every returned native value is read
/// once as logical work, and each schema node of the description is a fresh
/// allocation.
pub(super) fn charge_reconstruction<'a>(
    ledger: &zkc_runtime::vm::ExecutionLedger,
    schemas: impl IntoIterator<Item = &'a Schema>,
    leaves: impl IntoIterator<Item = &'a NativeValue>,
) -> Result<()> {
    fn nodes(schema: &Schema) -> usize {
        1 + schema
            .fields
            .iter()
            .chain(schema.alternatives.iter().flat_map(|a| &a.fields))
            .map(|f| nodes(&f.schema))
            .sum::<usize>()
    }
    let read = leaves
        .into_iter()
        .map(|leaf| leaf.retained_bytes())
        .fold(0usize, usize::saturating_add);
    let fresh = schemas
        .into_iter()
        .map(nodes)
        .fold(0usize, usize::saturating_add)
        .saturating_mul(NODE_BYTES);
    ledger
        .charge(
            zkc_runtime::vm::WorkBudget {
                instructions: 0,
                iterations: 0,
                logical_bytes: read as u64,
            },
            fresh,
        )
        .map_err(|_| "entry-output-limit".into())
}

/// The bound native ABI has already checked output types and slices. Only
/// complete successful returns are reconstructed through this function.
pub(super) fn collect(
    schema: &Schema,
    leaves: &mut impl Iterator<Item = NativeValue>,
) -> Result<Value> {
    super::interface::schemas::check_export(schema)?;
    Ok(protect(
        schema,
        match schema.kind {
            Kind::Unit => Value::Unit,
            Kind::Tuple => Value::Tuple(collect_sequence(&schema.fields, leaves)?),
            Kind::Array => Value::Array(collect_sequence(&schema.fields, leaves)?),
            Kind::Record => Value::Record(collect_fields(&schema.fields, leaves)?),
            Kind::Associated => {
                Value::Associated(Box::new(collect(&schema.fields[0].schema, leaves)?))
            }
            Kind::Variant => {
                let NativeValue::Variant(value) = leaves.next().ok_or("entry-output-shape")? else {
                    return Err("entry-output-shape".into());
                };
                let arm = schema
                    .alternatives
                    .get(value.alternative())
                    .ok_or("entry-output-alternative")?;
                let mut payload = value.payload().iter().cloned();
                let fields = collect_fields(&arm.fields, &mut payload)?;
                if payload.next().is_some() {
                    return Err("entry-output-shape".into());
                }
                Value::Variant {
                    alternative: arm.name.clone(),
                    fields,
                }
            }
            _ => Value::from(leaves.next().ok_or("entry-output-shape")?),
        },
    ))
}
fn collect_sequence(
    fields: &[Field],
    leaves: &mut impl Iterator<Item = NativeValue>,
) -> Result<Vec<Value>> {
    fields
        .iter()
        .map(|field| collect(&field.schema, leaves))
        .collect()
}
fn collect_fields(
    fields: &[Field],
    leaves: &mut impl Iterator<Item = NativeValue>,
) -> Result<BTreeMap<String, Value>> {
    fields
        .iter()
        .map(|field| Ok((field.name.clone(), collect(&field.schema, leaves)?)))
        .collect()
}

// Standard conversions keep generated bindings thin. They construct descriptions;
// the admitted Host still checks source permissions and concrete native types.
impl From<bool> for Value {
    fn from(value: bool) -> Self {
        NativeValue::Bool(value).into()
    }
}
impl TryFrom<Value> for bool {
    type Error = String;
    fn try_from(value: Value) -> Result<Self> {
        if let Value::Leaf(InputValue::Native(value)) = value
            && let NativeValue::Bool(value) = *value
        {
            return Ok(value);
        }
        Err("entry-binding-value".into())
    }
}
impl From<u64> for Value {
    fn from(value: u64) -> Self {
        NativeValue::Index(value).into()
    }
}
impl TryFrom<Value> for u64 {
    type Error = String;
    fn try_from(value: Value) -> Result<Self> {
        if let Value::Leaf(InputValue::Native(value)) = value
            && let NativeValue::Index(value) = *value
        {
            return Ok(value);
        }
        Err("entry-binding-value".into())
    }
}
impl From<()> for Value {
    fn from(_: ()) -> Self {
        Self::Unit
    }
}
impl TryFrom<Value> for () {
    type Error = String;
    fn try_from(value: Value) -> Result<Self> {
        match value {
            Value::Unit => Ok(()),
            _ => Err("entry-binding-value".into()),
        }
    }
}
impl<T: Into<Value>, const N: usize> From<[T; N]> for Value {
    fn from(values: [T; N]) -> Self {
        Self::Array(values.into_iter().map(Into::into).collect())
    }
}
impl<T: TryFrom<Value>, const N: usize> TryFrom<Value> for [T; N]
where
    T::Error: std::fmt::Display,
{
    type Error = String;
    fn try_from(value: Value) -> Result<Self> {
        let Value::Array(values) = value else {
            return Err("entry-binding-value".into());
        };
        if values.len() != N {
            return Err("entry-binding-value".into());
        }
        values
            .into_iter()
            .map(|v| T::try_from(v).map_err(|error| error.to_string()))
            .collect::<Result<Vec<T>>>()?
            .try_into()
            .map_err(|_| "entry-binding-value".into())
    }
}

pub(in crate::entry) fn duplicate(value: &crate::entry::Value) -> crate::entry::Value {
    use crate::entry::Value;
    match value {
        Value::Leaf(v) => Value::Leaf(duplicate_input(v)),
        Value::Unit => Value::Unit,
        Value::Opaque(v) => Value::Opaque(v.clone()),
        Value::Tuple(v) => Value::Tuple(v.iter().map(duplicate).collect()),
        Value::Array(v) => Value::Array(v.iter().map(duplicate).collect()),
        Value::Record(v) => {
            Value::Record(v.iter().map(|(n, v)| (n.clone(), duplicate(v))).collect())
        }
        Value::Variant {
            alternative,
            fields,
        } => Value::Variant {
            alternative: alternative.clone(),
            fields: fields
                .iter()
                .map(|(n, v)| (n.clone(), duplicate(v)))
                .collect(),
        },
        Value::Associated(v) => Value::Associated(Box::new(duplicate(v))),
    }
}
fn duplicate_input(value: &InputValue) -> InputValue {
    match value {
        InputValue::Native(v) => InputValue::Native(v.clone()),
        InputValue::Wire(v) => InputValue::Wire(v.clone()),
        InputValue::Prepared(v) => InputValue::Prepared(v.clone()),
        InputValue::WireSource { file, sha256 } => InputValue::WireSource {
            file: file.clone(),
            sha256: *sha256,
        },
        InputValue::Resource { budget } => InputValue::Resource { budget: *budget },
        InputValue::VerifierKey => InputValue::VerifierKey,
        InputValue::ProverKey(v) => InputValue::ProverKey(v.clone()),
        InputValue::ProverKeyFile { path, fingerprint } => InputValue::ProverKeyFile {
            path: path.clone(),
            fingerprint: *fingerprint,
        },
        InputValue::ProverKeyInput { file, fingerprint } => InputValue::ProverKeyInput {
            file: file.clone(),
            fingerprint: *fingerprint,
        },
        InputValue::Variant {
            alternative,
            payload,
        } => InputValue::Variant {
            alternative: *alternative,
            payload: payload.iter().map(duplicate_input).collect(),
        },
    }
}

/// Conservative ownership of descriptions retained by application contexts.
/// File descriptors retain no file contents until bounded native loading.
pub(in crate::entry) fn description_bytes(value: &crate::entry::Value) -> usize {
    use crate::entry::Value;
    let children = match value {
        Value::Unit => 0,
        Value::Opaque(v) => v.retained_bytes(),
        Value::Leaf(input) => match input {
            InputValue::Native(v) => v.retained_bytes(),
            InputValue::Wire(v) => v.len(),
            InputValue::Prepared(v) => v
                .value()
                .retained_bytes()
                .saturating_add(v.canonical_bytes().len()),
            InputValue::ProverKey(v) => v.value().retained_bytes(),
            InputValue::ProverKeyFile { path, .. } => path.len(),
            InputValue::Variant { payload, .. } => payload.len() * 512,
            _ => 0,
        },
        Value::Tuple(v) | Value::Array(v) => v.iter().map(description_bytes).sum(),
        Value::Record(v) => v.iter().map(|(n, v)| n.len() + description_bytes(v)).sum(),
        Value::Variant {
            alternative,
            fields,
        } => {
            alternative.len()
                + fields
                    .iter()
                    .map(|(n, v)| n.len() + description_bytes(v))
                    .sum::<usize>()
        }
        Value::Associated(v) => description_bytes(v),
    };
    children.saturating_add(512)
}

// Only admitted child outputs reach this internal reconstruction path. Preserve
// exact schemas when opening opaque owners, including inside transparent products.
pub(in crate::entry) fn open_output(schema: &Schema, value: Value) -> Result<Value> {
    let value = if let Value::Opaque(v) = value {
        v.open(schema)?
    } else {
        value
    };
    Ok(match value {
        Value::Record(mut values) => {
            for field in &schema.fields {
                let value = values
                    .remove(&field.name)
                    .ok_or("entry-host-output-shape")?;
                values.insert(field.name.clone(), open_output(&field.schema, value)?);
            }
            Value::Record(values)
        }
        Value::Tuple(values) => Value::Tuple(open_sequence(schema, values)?),
        Value::Array(values) => Value::Array(open_sequence(schema, values)?),
        Value::Associated(v) => {
            Value::Associated(Box::new(open_output(&schema.fields[0].schema, *v)?))
        }
        Value::Variant {
            alternative,
            mut fields,
        } => {
            let arm = schema
                .alternatives
                .iter()
                .find(|a| a.name == alternative)
                .ok_or("entry-host-output-shape")?;
            for field in &arm.fields {
                let value = fields
                    .remove(&field.name)
                    .ok_or("entry-host-output-shape")?;
                fields.insert(field.name.clone(), open_output(&field.schema, value)?);
            }
            Value::Variant {
                alternative,
                fields,
            }
        }
        value => value,
    })
}
fn open_sequence(schema: &Schema, values: Vec<Value>) -> Result<Vec<Value>> {
    if schema.fields.len() != values.len() {
        return Err("entry-host-output-shape".into());
    }
    schema
        .fields
        .iter()
        .zip(values)
        .map(|(f, v)| open_output(&f.schema, v))
        .collect()
}
/// Readable output is projection. Native leaf codecs cannot authorize opening
/// an inaccessible source aggregate.
pub(in crate::entry) fn check_readable_schema(schema: &Schema) -> Result<()> {
    if schema.sealed
        || schema.kind == Kind::Associated
        || schema
            .fields
            .iter()
            .chain(schema.alternatives.iter().flat_map(|a| &a.fields))
            .any(|f| !f.public)
    {
        return Err("entry-output-opaque".into());
    }
    if let Some(element) = &schema.element {
        check_readable_schema(element)?;
    }
    for f in schema
        .fields
        .iter()
        .chain(schema.alternatives.iter().flat_map(|a| &a.fields))
    {
        check_readable_schema(&f.schema)?;
    }
    Ok(())
}
pub(in crate::entry) fn check_readable(value: &Value) -> Result<()> {
    check_readable_at(value, 0)
}
fn check_readable_at(value: &Value, depth: usize) -> Result<()> {
    if depth > crate::io::document::MAX_DEPTH {
        return Err("entry-output-encoding".into());
    }
    match value {
        Value::Opaque(value) => check_readable_schema(value.schema())?,
        Value::Record(v) | Value::Variant { fields: v, .. } => {
            for value in v.values() {
                check_readable_at(value, depth + 1)?;
            }
        }
        Value::Tuple(v) | Value::Array(v) => {
            for value in v {
                check_readable_at(value, depth + 1)?;
            }
        }
        Value::Associated(v) => check_readable_at(v, depth + 1)?,
        _ => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests;
