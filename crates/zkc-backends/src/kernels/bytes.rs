//! Immutable byte strings with bounded allocation and exact slice bounds.
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, LogicalType, OperationBinding, OperationSignature,
    PhysicalType, Type,
};

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use Type::{Bool, Bytes, Index};
    if !binding.arguments.is_empty()
        || binding.implementation != format!("native/{}", binding.contract)
    {
        return None;
    }
    if binding.contract == "bytes.join" {
        let bytes = LogicalType::new(Bytes, Identity::None).ok()?;
        return Some(OperationSignature {
            inputs: vec![
                PhysicalType::default_for(LogicalType::sequence(bytes.clone()).ok()?).ok()?,
            ],
            outputs: vec![PhysicalType::default_for(bytes).ok()?],
            attributes: AttributeRule::None,
        });
    }
    let (inputs, outputs): (&[Type], &[Type]) = match binding.contract.as_str() {
        "bytes.empty" => (&[], &[Bytes]),
        "bytes.repeat" => (&[Index, Index], &[Bytes]),
        "bytes.append" => (&[Bytes, Index], &[Bytes]),
        "bytes.concat" => (&[Bytes, Bytes], &[Bytes]),
        "bytes.slice" => (&[Bytes, Index, Index], &[Bytes]),
        "bytes.at" => (&[Bytes, Index], &[Index]),
        "bytes.length" => (&[Bytes], &[Index]),
        "bytes.equal" => (&[Bytes, Bytes], &[Bool]),
        _ => return None,
    };
    let port = |kind| PhysicalType::default_for(LogicalType::new(kind, Identity::None).ok()?).ok();
    Some(OperationSignature {
        inputs: inputs.iter().copied().map(port).collect::<Option<_>>()?,
        outputs: outputs.iter().copied().map(port).collect::<Option<_>>()?,
        attributes: AttributeRule::None,
    })
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    attributes: &[String],
    policy: &Policy,
    available: usize,
) -> Result<Vec<Value>> {
    use Value::{Bool, Bytes, Index};
    if !attributes.is_empty() {
        return Err(refused("bytes-attributes"));
    }
    for arg in args {
        if let Bytes(data) = arg {
            policy.bytes(data.len())?;
        }
    }
    let copy = |left: &[u8], right: &[u8]| -> Result<Value> {
        let len = left
            .len()
            .checked_add(right.len())
            .ok_or_else(|| exhausted("size-overflow"))?;
        policy.bytes(len)?;
        // Vec-to-Arc conversion temporarily retains both allocations.
        policy.output(size(len, 2)?, available)?;
        let mut out = crate::kernels::arithmetic::reserve(len)?;
        out.extend_from_slice(left);
        out.extend_from_slice(right);
        Ok(Bytes(out.into()))
    };
    let scalar = |value| {
        policy.output(512, available)?;
        Ok(value)
    };
    let output = match (name, args) {
        ("bytes.empty", []) => copy(&[], &[])?,
        ("bytes.repeat", [Index(byte), Index(count)]) => {
            let byte = u8::try_from(*byte).map_err(|_| refused("bytes-element"))?;
            let count = usize::try_from(*count).map_err(|_| exhausted("size-overflow"))?;
            policy.bytes(count)?;
            policy.output(size(count, 2)?, available)?;
            let mut out = crate::kernels::arithmetic::reserve(count)?;
            out.resize(count, byte);
            Bytes(out.into())
        }
        ("bytes.join", [Value::Sequence(parts)]) => {
            let bytes =
                LogicalType::new(Type::Bytes, Identity::None).expect("installed bytes type");
            if parts.physical_type().logical().sequence_element() != Some(&bytes) {
                return Err(refused("bytes-operands"));
            }
            // Check every fragment and the total before allocating or copying.
            let length = parts.iter().try_fold(0usize, |total, part| {
                let Bytes(part) = part else {
                    return Err(refused("bytes-operands"));
                };
                policy.bytes(part.len())?;
                total
                    .checked_add(part.len())
                    .ok_or_else(|| exhausted("size-overflow"))
            })?;
            policy.bytes(length)?;
            policy.output(size(length, 2)?, available)?;
            let mut out = crate::kernels::arithmetic::reserve(length)?;
            for part in parts.iter() {
                let Bytes(part) = part else {
                    unreachable!("checked fragment")
                };
                out.extend_from_slice(part);
            }
            Bytes(out.into())
        }
        ("bytes.append", [Bytes(a), Index(b)]) => {
            let byte = u8::try_from(*b).map_err(|_| refused("bytes-element"))?;
            copy(a, &[byte])?
        }
        ("bytes.concat", [Bytes(a), Bytes(b)]) => copy(a, b)?,
        ("bytes.slice", [Bytes(a), Index(start), Index(len)]) => {
            let start = usize::try_from(*start).map_err(|_| refused("bytes-bounds"))?;
            let len = usize::try_from(*len).map_err(|_| refused("bytes-bounds"))?;
            let end = start
                .checked_add(len)
                .ok_or_else(|| refused("bytes-bounds"))?;
            copy(
                a.get(start..end).ok_or_else(|| refused("bytes-bounds"))?,
                &[],
            )?
        }
        ("bytes.at", [Bytes(a), Index(index)]) => {
            let index = usize::try_from(*index).map_err(|_| refused("bytes-bounds"))?;
            scalar(Index(u64::from(
                *a.get(index).ok_or_else(|| refused("bytes-bounds"))?,
            )))?
        }
        ("bytes.length", [Bytes(a)]) => scalar(Index(a.len() as u64))?,
        ("bytes.equal", [Bytes(a), Bytes(b)]) => scalar(Bool(a == b))?,
        _ => return Err(refused("bytes-operands")),
    };
    Ok(vec![output])
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("native/bytes.empty", "bytes.empty"),
    ("native/bytes.repeat", "bytes.repeat"),
    ("native/bytes.join", "bytes.join"),
    ("native/bytes.append", "bytes.append"),
    ("native/bytes.concat", "bytes.concat"),
    ("native/bytes.slice", "bytes.slice"),
    ("native/bytes.at", "bytes.at"),
    ("native/bytes.length", "bytes.length"),
    ("native/bytes.equal", "bytes.equal"),
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Domain, EntryPolicy, NativeBackend};
    use zkc_runtime::vm::Value as RuntimeValue;

    fn bytes(value: &[u8]) -> Value {
        Value::Bytes(value.to_vec().into())
    }
    fn run(name: &str, args: &[Value]) -> Result<Vec<Value>> {
        apply(name, args, &[], &Policy::default(), usize::MAX)
    }

    #[test]
    fn bulk_bytes_preserve_order_and_preflight_limits() {
        for (byte, count) in [(0, 0), (255, 1), (128, 1024)] {
            let out = run("bytes.repeat", &[Value::Index(byte), Value::Index(count)]).unwrap();
            assert!(
                matches!(&out[0], Value::Bytes(v) if v.as_ref() == vec![byte as u8; count as usize])
            );
        }
        // Even zero copies must not legitimize an invalid byte.
        assert_eq!(
            run("bytes.repeat", &[Value::Index(256), Value::Index(0)])
                .unwrap_err()
                .code,
            "refused:bytes-element"
        );
        assert!(run("bytes.repeat", &[Value::Index(0), Value::Index(u64::MAX)]).is_err());
        let ty = LogicalType::new(Type::Bytes, Identity::None).unwrap();
        for parts in [
            vec![],
            vec![bytes(&[]), bytes(&[1, 255]), bytes(&[]), bytes(&[0])],
        ] {
            let expected: Vec<_> = parts
                .iter()
                .flat_map(|v| match v {
                    Value::Bytes(b) => b.to_vec(),
                    _ => unreachable!(),
                })
                .collect();
            let parts = Value::Sequence(
                crate::Sequence::new(ty.clone(), parts, &Policy::default()).unwrap(),
            );
            let out = run("bytes.join", std::slice::from_ref(&parts)).unwrap();
            assert!(matches!(&out[0], Value::Bytes(v) if v.as_ref() == expected));
            let limit = size(expected.len(), 2).unwrap();
            assert!(
                apply(
                    "bytes.join",
                    std::slice::from_ref(&parts),
                    &[],
                    &Policy::default(),
                    limit
                )
                .is_ok()
            );
            assert_eq!(
                apply("bytes.join", &[parts], &[], &Policy::default(), limit - 1)
                    .unwrap_err()
                    .code,
                "exhausted:output-bytes"
            );
        }
        let parts = Value::Sequence(
            crate::Sequence::new(ty, vec![bytes(&[1, 2]), bytes(&[3, 4])], &Policy::default())
                .unwrap(),
        );
        let policy = Policy {
            max_wire_bytes: 3,
            ..Default::default()
        };
        assert_eq!(
            apply("bytes.join", &[parts], &[], &policy, usize::MAX)
                .unwrap_err()
                .code,
            "exhausted:wire-bytes"
        );
        assert_eq!(
            apply(
                "bytes.repeat",
                &[Value::Index(0), Value::Index(4)],
                &[],
                &policy,
                usize::MAX
            )
            .unwrap_err()
            .code,
            "exhausted:wire-bytes"
        );
        let wrong = Value::Sequence(
            crate::Sequence::new(
                LogicalType::parse("index").unwrap(),
                vec![],
                &Policy::default(),
            )
            .unwrap(),
        );
        assert_eq!(
            run("bytes.join", &[wrong]).unwrap_err().code,
            "refused:bytes-operands"
        );
    }

    #[test]
    fn concatenation_slices_and_boundaries() {
        let output = run("bytes.concat", &[bytes(&[0, 128]), bytes(&[255])]).unwrap();
        let Value::Bytes(data) = &output[0] else {
            panic!("byte output")
        };
        assert_eq!(data.as_ref(), [0, 128, 255]);
        for (start, len, expected) in [(0, 3, &[0, 128, 255][..]), (1, 1, &[128]), (3, 0, &[])] {
            let out = run(
                "bytes.slice",
                &[output[0].clone(), Value::Index(start), Value::Index(len)],
            )
            .unwrap();
            assert!(matches!(&out[0], Value::Bytes(b) if b.as_ref() == expected));
        }
        for (start, len) in [(4, 0), (3, 1), (u64::MAX, 1), (1, u64::MAX)] {
            assert_eq!(
                run(
                    "bytes.slice",
                    &[output[0].clone(), Value::Index(start), Value::Index(len)]
                )
                .unwrap_err()
                .code,
                "refused:bytes-bounds"
            );
        }
        assert_eq!(
            run("bytes.append", &[bytes(&[]), Value::Index(256)])
                .unwrap_err()
                .code,
            "refused:bytes-element"
        );
        assert!(run("bytes.at", &[bytes(&[]), Value::Index(0)]).is_err());
        assert!(
            apply(
                "bytes.concat",
                &[bytes(&[1]), bytes(&[2])],
                &[],
                &Policy::default(),
                257
            )
            .is_err()
        );
        assert!(apply("bytes.length", &[bytes(&[])], &[], &Policy::default(), 511).is_err());
    }

    #[test]
    fn byte_wire_is_typed_bounded_and_exact() {
        let policy = Policy::default();
        let backend = NativeBackend::new(
            policy,
            EntryPolicy::new(Domain::new("P", "bytes", "main", None), None),
            Default::default(),
        )
        .unwrap();
        let value = bytes(&[0, 127, 128, 255]);
        let ty = value.physical_type();
        let wire = backend.encode_native_value(&value).unwrap();
        assert!(
            matches!(backend.decode_native_value(&ty, &wire).unwrap(), Value::Bytes(v) if v.as_ref() == [0, 127, 128, 255])
        );
        let indices = PhysicalType::default_for(LogicalType::parse("indices").unwrap()).unwrap();
        assert!(backend.decode_native_value(&indices, &wire).is_err());
        for end in 0..wire.len() {
            assert!(backend.decode_native_value(&ty, &wire[..end]).is_err());
        }
        let mut extra = wire.clone();
        extra.push(0);
        assert!(backend.decode_native_value(&ty, &extra).is_err());
        let mut large = wire.clone();
        large[6..10].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(backend.decode_native_value(&ty, &large).is_err());
        let small = Policy {
            max_wire_bytes: 3,
            ..policy
        };
        assert!(
            apply(
                "bytes.concat",
                &[bytes(&[1, 2]), bytes(&[3, 4])],
                &[],
                &small,
                usize::MAX
            )
            .is_err()
        );
    }
}
