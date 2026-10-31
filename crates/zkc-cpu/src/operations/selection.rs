//! Selection of already computed immutable scalar values.
use crate::{Policy, Result, Value, refused};
use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, LogicalType, OperationBinding, OperationSignature,
    PhysicalType, Type, Value as _,
};

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    if !binding.physical_arguments.is_empty() {
        return None;
    }
    let (kind, domain) = match (binding.contract.as_str(), binding.arguments.as_slice()) {
        ("bool.select", []) => (Type::Bool, Identity::None),
        ("index.select", []) => (Type::Index, Identity::None),
        ("field.select", [domain]) => (Type::Field, Identity::parse(domain).ok()?),
        ("curve.select", [domain]) => (Type::Group, Identity::parse(domain).ok()?),
        _ => return None,
    };
    // The native type owner advertises its own layout and provider. This does
    // not derive executable support from the logical declaration catalogue.
    let (provider, scalar) = if domain == Identity::None {
        (
            "native",
            PhysicalType::default_for(LogicalType::new(kind, domain).ok()?).ok()?,
        )
    } else {
        let owner = crate::domains::INSTALLED.iter().find(|owner| {
            if kind == Type::Field {
                owner.field == domain
            } else {
                owner.group == Some(domain)
            }
        })?;
        (owner.provider, owner.physical(kind)?)
    };
    if binding.implementation != format!("{provider}/{}", binding.contract) {
        return None;
    }
    let condition =
        PhysicalType::default_for(LogicalType::new(Type::Bool, Identity::None).ok()?).ok()?;
    Some(OperationSignature {
        inputs: vec![condition, scalar.clone(), scalar.clone()],
        outputs: vec![scalar],
        attributes: AttributeRule::None,
    })
}

pub(crate) fn apply(args: &[Value], policy: &Policy, available: usize) -> Result<Vec<Value>> {
    let [Value::Bool(condition), yes, no] = args else {
        return Err(refused("selection-operands"));
    };
    // Common invocation admission already checked both exact physical ports.
    // Retain this private handler's scalar boundary before copying any value.
    if yes.physical_type() != no.physical_type()
        || !matches!(
            yes.physical_type().kind(),
            Type::Bool | Type::Index | Type::Field | Type::Group
        )
    {
        return Err(refused("selection-operands"));
    }
    let selected = if *condition { yes } else { no };
    policy.output(selected.retained_bytes(), available)?;
    Ok(vec![selected.clone()])
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("native/bool.select", "bool.select"),
    ("native/index.select", "index.select"),
    ("arkworks/field.select", "field.select"),
    ("dalek/field.select", "field.select"),
    ("plonky3/field.select", "field.select"),
    ("arkworks/curve.select", "curve.select"),
    ("dalek/curve.select", "curve.select"),
];
