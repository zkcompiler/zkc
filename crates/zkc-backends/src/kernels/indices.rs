//! Checked logical u64 indices. These are independent of field characteristic
//! and host pointer size; arithmetic never wraps and division by zero refuses.
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, KernelSignature, LogicalType, OperationBinding,
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
    let physical = |kind| {
        PhysicalType::default_for(LogicalType::new(kind, Identity::None).expect("index contract"))
    };
    Some(KernelSignature {
        inputs: inputs.iter().copied().map(physical).collect(),
        outputs: outputs.iter().copied().map(physical).collect(),
        attributes,
    })
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    attributes: &[String],
    policy: &Policy,
    available: usize,
) -> Option<Result<Vec<Value>>> {
    if !name.starts_with("index.") && !name.starts_with("indices.") {
        return None;
    }
    Some((|| {
        use Value::{Bool, Index, Indices};
        let output = match (name, args) {
            ("index.constant", []) => Index(
                attributes
                    .first()
                    .and_then(|n| n.parse::<u64>().ok().filter(|v| v.to_string() == *n))
                    .filter(|_| attributes.len() == 1)
                    .ok_or_else(|| refused("index-constant"))?,
            ),
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
                let mut result = crate::kernels::arithmetic::reserve(len)?;
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
    })())
}

pub(crate) fn encode(v: &Value, policy: &Policy) -> Option<Result<Vec<u8>>> {
    let (tag, count) = match v {
        Value::Index(_) => (31, None),
        Value::Indices(ns) => (32, Some(ns.len())),
        _ => return None,
    };
    Some((|| {
        if let Some(n) = count {
            policy.vector_width(n, 8)?;
        }
        let bytes = count
            .unwrap_or(1)
            .checked_mul(8)
            .and_then(|n| n.checked_add(if count.is_some() { 10 } else { 6 }))
            .ok_or_else(|| exhausted("wire-bytes"))?;
        policy.wire(bytes)?;
        let mut output = crate::kernels::arithmetic::reserve(bytes)?;
        output.extend_from_slice(b"ZKCV\x01");
        output.push(tag);
        match v {
            Value::Index(n) => output.extend(n.to_le_bytes()),
            Value::Indices(ns) => {
                output.extend(
                    u32::try_from(ns.len())
                        .map_err(|_| exhausted("element-limit"))?
                        .to_le_bytes(),
                );
                for n in ns.iter() {
                    output.extend(n.to_le_bytes());
                }
            }
            _ => unreachable!(),
        }
        Ok(output)
    })())
}

pub(crate) fn decode(ty: PhysicalType, bytes: &[u8], policy: &Policy) -> Option<Result<Value>> {
    let tag = match ty.kind() {
        Type::Index => 31,
        Type::Indices => 32,
        _ => return None,
    };
    Some((|| {
        policy.wire(bytes.len())?;
        if bytes.get(..5) != Some(b"ZKCV\x01") || bytes.get(5) != Some(&tag) {
            return Err(refused("wire-header"));
        }
        let read = |b: &[u8]| -> Result<u64> {
            Ok(u64::from_le_bytes(
                b.try_into().map_err(|_| refused("wire-length"))?,
            ))
        };
        if tag == 31 {
            return Ok(Value::Index(read(&bytes[6..])?));
        }
        let count = bytes.get(6..10).ok_or_else(|| refused("wire-length"))?;
        let n = usize::try_from(u32::from_le_bytes(
            count.try_into().map_err(|_| refused("wire-length"))?,
        ))
        .map_err(|_| exhausted("size-overflow"))?;
        if n.checked_mul(8).and_then(|n| n.checked_add(10)) != Some(bytes.len()) {
            return Err(refused("wire-length"));
        }
        policy.vector_width(n, 8)?;
        let mut ns = crate::kernels::arithmetic::reserve(n)?;
        for b in bytes[10..].as_chunks::<8>().0 {
            ns.push(read(b)?);
        }
        Ok(Value::Indices(ns.into()))
    })())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn run(name: &str, args: &[Value]) -> Result<Vec<Value>> {
        apply(name, args, &[], &Policy::default(), usize::MAX).unwrap()
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
            PhysicalType::default_for(LogicalType::new(Type::Indices, Identity::None).unwrap());
        let ns = Value::Indices(vec![u64::MAX, 9, 9].into());
        let wire = encode(&ns, &p).unwrap().unwrap();
        let decoded = decode(ty.clone(), &wire, &p).unwrap().unwrap();
        assert!(matches!(decoded, Value::Indices(xs) if xs.as_ref()==[u64::MAX,9,9]));
        assert!(run("indices.at", &[ns.clone(), Value::Index(3)]).is_err());
        for n in 0..wire.len() {
            assert!(decode(ty.clone(), &wire[..n], &p).unwrap().is_err());
        }
        let mut extra = wire.clone();
        extra.push(0);
        assert!(decode(ty.clone(), &extra, &p).unwrap().is_err());
        let small = Policy {
            max_table_elements: 2,
            ..p
        };
        assert!(decode(ty.clone(), &wire, &small).unwrap().is_err());
        assert!(
            apply("indices.append", &[ns, Value::Index(1)], &[], &p, 256)
                .unwrap()
                .is_err()
        );
    }
}
