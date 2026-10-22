//! Checked logical u64 indices. These are independent of field characteristic
//! and host pointer size; arithmetic never wraps and division by zero refuses.
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, LogicalType, OperationBinding, OperationSignature,
    PhysicalType, Type,
};

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use AttributeRule::{None as NoAttributes, Unsigned64};
    use Type::{Bool, Index, Indices};
    if !binding.arguments.is_empty()
        || binding.implementation != format!("native/{}", binding.contract)
    {
        return None;
    }
    // Native advertisements are independent of the runtime admission catalogue.
    let (inputs, outputs, attributes): (&[Type], &[Type], _) = match binding.contract.as_str() {
        "index.constant" => (&[], &[Index], Unsigned64),
        "index.add" | "index.sub" | "index.mul" | "index.div" | "index.mod" => {
            (&[Index, Index], &[Index], NoAttributes)
        }
        "index.equal" | "index.less" => (&[Index, Index], &[Bool], NoAttributes),
        "indices.empty" => (&[], &[Indices], NoAttributes),
        "indices.append" => (&[Indices, Index], &[Indices], NoAttributes),
        "indices.at" => (&[Indices, Index], &[Index], NoAttributes),
        "indices.length" => (&[Indices], &[Index], NoAttributes),
        _ => return None,
    };
    let physical =
        |kind| PhysicalType::default_for(LogicalType::new(kind, Identity::None).ok()?).ok();
    Some(OperationSignature {
        inputs: inputs
            .iter()
            .copied()
            .map(physical)
            .collect::<Option<_>>()?,
        outputs: outputs
            .iter()
            .copied()
            .map(physical)
            .collect::<Option<_>>()?,
        attributes,
    })
}

/// Decode the single canonical decimal shared by attribute validation and the
/// ordinary constant handler. The caller retains its own refusal identifier.
pub(crate) fn decode_unsigned64(attributes: &[String]) -> Option<u64> {
    let [literal] = attributes else {
        return None;
    };
    literal
        .parse::<u64>()
        .ok()
        .filter(|value| value.to_string() == *literal)
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    attributes: &[String],
    policy: &Policy,
    available: usize,
) -> Result<Vec<Value>> {
    if !name.starts_with("index.") && !name.starts_with("indices.") {
        return Err(refused("kernel-operands"));
    }
    use Value::{Bool, Index, Indices};
    let output = match (name, args) {
        ("index.constant", []) => {
            Index(decode_unsigned64(attributes).ok_or_else(|| refused("index-constant"))?)
        }
        ("index.add", [Index(a), Index(b)]) => {
            Index(a.checked_add(*b).ok_or_else(|| refused("index-overflow"))?)
        }
        ("index.sub", [Index(a), Index(b)]) => Index(
            a.checked_sub(*b)
                .ok_or_else(|| refused("index-underflow"))?,
        ),
        ("index.mul", [Index(a), Index(b)]) => {
            Index(a.checked_mul(*b).ok_or_else(|| refused("index-overflow"))?)
        }
        ("index.div", [Index(a), Index(b)]) => Index(
            a.checked_div(*b)
                .ok_or_else(|| refused("index-zero-divisor"))?,
        ),
        ("index.mod", [Index(a), Index(b)]) => Index(
            a.checked_rem(*b)
                .ok_or_else(|| refused("index-zero-divisor"))?,
        ),
        ("index.equal", [Index(a), Index(b)]) => Bool(a == b),
        ("index.less", [Index(a), Index(b)]) => Bool(a < b),
        ("indices.empty", []) => {
            policy.output(size(0, 8)?, available)?;
            Indices(Vec::new().into())
        }
        ("indices.append", [Indices(ns), Index(n)]) => {
            let len = ns
                .len()
                .checked_add(1)
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.vector_width(len, 8)?;
            policy.output(size(len, 8)?, available)?;
            let mut result = crate::operations::arithmetic::reserve(len)?;
            result.extend_from_slice(ns);
            result.push(*n);
            Indices(result.into())
        }
        ("indices.at", [Indices(ns), Index(n)]) => {
            let n = usize::try_from(*n).map_err(|_| refused("index-bounds"))?;
            Index(*ns.get(n).ok_or_else(|| refused("index-bounds"))?)
        }
        ("indices.length", [Indices(ns)]) => {
            Index(u64::try_from(ns.len()).map_err(|_| exhausted("size-overflow"))?)
        }
        _ => return Err(refused("index-operands")),
    };
    Ok(vec![output])
}

pub(crate) const CONSTANT_IMPLEMENTATIONS: &[(&str, &str)] =
    &[("native/index.constant", "index.constant")];

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("native/index.add", "index.add"),
    ("native/index.sub", "index.sub"),
    ("native/index.mul", "index.mul"),
    ("native/index.div", "index.div"),
    ("native/index.mod", "index.mod"),
    ("native/index.equal", "index.equal"),
    ("native/index.less", "index.less"),
    ("native/indices.empty", "indices.empty"),
    ("native/indices.append", "indices.append"),
    ("native/indices.at", "indices.at"),
    ("native/indices.length", "indices.length"),
];

#[cfg(test)]
mod tests {
    use super::*;
    fn run(name: &str, args: &[Value]) -> Result<Vec<Value>> {
        apply(name, args, &[], &Policy::default(), usize::MAX)
    }
    #[test]
    fn ordinary_constants_keep_canonical_syntax_and_operand_error_precedence() {
        for (literal, expected) in [("0", 0), ("12", 12), ("18446744073709551615", u64::MAX)] {
            assert!(matches!(
                apply("index.constant", &[], &[literal.into()], &Policy::default(), usize::MAX)
                    .unwrap()[0],
                Value::Index(actual) if actual == expected
            ));
        }
        for attributes in [
            vec![],
            vec!["".into()],
            vec!["00".into()],
            vec!["+1".into()],
            vec!["-1".into()],
            vec![" 1".into()],
            vec!["1\n".into()],
            vec!["1_0".into()],
            vec!["18446744073709551616".into()],
            vec!["1".into(), "2".into()],
        ] {
            assert_eq!(
                apply(
                    "index.constant",
                    &[],
                    &attributes,
                    &Policy::default(),
                    usize::MAX
                )
                .unwrap_err(),
                refused("index-constant")
            );
            assert_eq!(
                apply(
                    "index.constant",
                    &[Value::Index(1)],
                    &attributes,
                    &Policy::default(),
                    usize::MAX
                )
                .unwrap_err(),
                refused("index-operands")
            );
        }
    }
    #[test]
    fn arithmetic_is_checked_not_modular() {
        use Value::Index;
        assert!(matches!(
            run("index.add", &[Index(u64::MAX - 1), Index(1)]).unwrap()[0],
            Index(u64::MAX)
        ));
        for (name, a, b, code) in [
            ("index.add", u64::MAX, 1, "index-overflow"),
            ("index.mul", u64::MAX, 2, "index-overflow"),
            ("index.sub", 0, 1, "index-underflow"),
            ("index.div", 7, 0, "index-zero-divisor"),
            ("index.mod", 7, 0, "index-zero-divisor"),
        ] {
            assert!(format!("{:?}", run(name, &[Index(a), Index(b)]).unwrap_err()).contains(code));
        }
        assert!(matches!(
            run("index.mod", &[Index(u64::MAX), Index(8)]).unwrap()[0],
            Index(7)
        ));
    }
    #[test]
    fn sequence_duplicates_bounds_and_wire() {
        let p = Policy::default();
        let ty =
            PhysicalType::default_for(LogicalType::new(Type::Indices, Identity::None).unwrap())
                .unwrap();
        let ns = Value::Indices(vec![u64::MAX, 9, 9].into());
        let backend = |policy| {
            crate::NativeBackend::new(
                policy,
                crate::EntryPolicy::new(crate::Domain::new("P", "wire", "main", None), None),
                Default::default(),
            )
            .unwrap()
        };
        let wire = backend(p).encode_native_value(&ns).unwrap();
        let decoded = backend(p).decode_native_value(&ty, &wire).unwrap();
        assert!(matches!(decoded, Value::Indices(xs) if xs.as_ref()==[u64::MAX,9,9]));
        assert!(run("indices.at", &[ns.clone(), Value::Index(3)]).is_err());
        for n in 0..wire.len() {
            assert!(backend(p).decode_native_value(&ty, &wire[..n]).is_err());
        }
        let mut extra = wire.clone();
        extra.push(0);
        assert!(backend(p).decode_native_value(&ty, &extra).is_err());
        let small = Policy {
            max_table_elements: 2,
            ..p
        };
        assert!(backend(small).decode_native_value(&ty, &wire).is_err());
        assert!(apply("indices.append", &[ns, Value::Index(1)], &[], &p, 256).is_err());
    }
}
