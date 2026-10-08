//! Logical application values. Layout and constructor authority come from the
//! authenticated source interface, never from a caller-supplied type spelling.
use super::interface::raw::{Field, Kind, Permission, Schema};
use crate::protocol::run::InputValue;
use std::collections::BTreeMap;
use zkc_backends::Value as NativeValue;

type Result<T> = std::result::Result<T, String>;

#[derive(Debug)]
pub enum Value {
    Leaf(InputValue),
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

/// Constructor permission is checked once at Entry admission. The validated
/// schema inherits that permission through all product fields and alternatives.
pub(super) fn check_import(schema: &Schema) -> Result<()> {
    if schema.custody || !schema.permissions.contains(&Permission::Wire) {
        return Err("entry-input-constructor".into());
    }
    Ok(())
}
pub(super) fn flatten(schema: &Schema, value: Value, out: &mut Vec<InputValue>) -> Result<()> {
    match (schema.kind, value) {
        (Kind::Unit, Value::Unit) => Ok(()),
        (Kind::Tuple, Value::Tuple(values)) | (Kind::Array, Value::Array(values)) => {
            if schema.fields.len() != values.len() {
                return Err("entry-input-shape".into());
            }
            for (field, value) in schema.fields.iter().zip(values) {
                flatten(&field.schema, value, out)?;
            }
            Ok(())
        }
        (Kind::Record, Value::Record(values)) => flatten_fields(&schema.fields, values, out),
        (Kind::Associated, Value::Associated(value)) => {
            flatten(&schema.fields[0].schema, *value, out)
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
            flatten_fields(&arm.fields, fields, &mut payload)?;
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
            if !matches!(value, InputValue::Native(_) | InputValue::Wire(_)) {
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
) -> Result<()> {
    if fields.len() != values.len() {
        return Err("entry-input-fields".into());
    }
    for field in fields {
        let value = values.remove(&field.name).ok_or("entry-input-fields")?;
        flatten(&field.schema, value, out)?;
    }
    Ok(())
}

pub(super) fn check_export(schema: &Schema) -> Result<()> {
    if schema.custody || !schema.permissions.contains(&Permission::Copy) {
        return Err("entry-output-custody".into());
    }
    Ok(())
}
/// The bound native ABI has already checked output types and slices. Only
/// complete successful returns are reconstructed through this function.
pub(super) fn collect(
    schema: &Schema,
    leaves: &mut impl Iterator<Item = NativeValue>,
) -> Result<Value> {
    Ok(match schema.kind {
        Kind::Unit => Value::Unit,
        Kind::Tuple => Value::Tuple(collect_sequence(&schema.fields, leaves)?),
        Kind::Array => Value::Array(collect_sequence(&schema.fields, leaves)?),
        Kind::Record => Value::Record(collect_fields(&schema.fields, leaves)?),
        Kind::Associated => Value::Associated(Box::new(collect(&schema.fields[0].schema, leaves)?)),
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
    })
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
