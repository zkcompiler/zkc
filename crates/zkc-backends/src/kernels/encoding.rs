//! Exact mathematical encodings, separate from native transport and observation.
use crate::{GroupPoint, Policy, Result, Scalar, Value, ark, refused, value::size};
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, KernelSignature, LogicalType, OperationBinding,
    PhysicalType, Type,
};

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use Type::{Bool, Bytes, Field, Group};
    if binding.implementation != format!("arkworks/{}", binding.contract) {
        return None;
    }
    let (inputs, outputs, identity): (&[Type], &[Type], Identity) = match binding.contract.as_str()
    {
        "encoding.field_be" => (&[Field], &[Bytes], Identity::Bls12381Fr),
        "encoding.field_from_be" => (&[Bytes], &[Bool, Field], Identity::Bls12381Fr),
        "encoding.field_reduce_be" => (&[Bytes], &[Field], Identity::Bls12381Fr),
        "encoding.group_compressed" => (&[Group], &[Bytes], Identity::Bls12381G1),
        "encoding.group_from_compressed" => (&[Bytes], &[Bool, Group], Identity::Bls12381G1),
        _ => return None,
    };
    if binding.arguments != [identity.name()] {
        return None;
    }
    let port = |kind| {
        let domain = if matches!(kind, Field | Group) {
            identity
        } else {
            Identity::None
        };
        PhysicalType::default_for(LogicalType::new(kind, domain).ok()?).ok()
    };
    Some(KernelSignature {
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
    budget: &mut crate::external_kernels::Budget,
) -> Result<Vec<Value>> {
    if !attributes.is_empty() {
        return Err(refused("encoding-attributes"));
    }
    for value in args {
        if let Value::Bytes(bytes) = value {
            policy.bytes(bytes.len())?;
        }
    }
    match (name, args) {
        ("encoding.field_be", [Value::Field(value)]) => {
            policy.bytes(32)?;
            policy.output(size(32, 1)?, available)?;
            let mut bytes = zkc_arkworks::encode_scalar(value).map_err(ark)?;
            bytes.reverse();
            Ok(vec![Value::Bytes(bytes.to_vec().into())])
        }
        ("encoding.field_from_be", [Value::Bytes(bytes)]) => {
            policy.output(1024, available)?;
            let value = if let Ok(mut bytes) = <[u8; 32]>::try_from(bytes.as_ref()) {
                bytes.reverse();
                zkc_arkworks::decode_scalar(&bytes).ok()
            } else {
                None
            };
            Ok(vec![
                Value::Bool(value.is_some()),
                Value::Field(value.unwrap_or_default()),
            ])
        }
        ("encoding.field_reduce_be", [Value::Bytes(bytes)]) => {
            policy.output(512, available)?;
            budget.charge_units((bytes.len() as u64).saturating_mul(2))?;
            // Horner reduction reads the input directly: no input-sized copy.
            let radix = Scalar::from(256u64);
            let value = bytes.iter().fold(Scalar::from(0u64), |value, byte| {
                value * radix + Scalar::from(u64::from(*byte))
            });
            Ok(vec![Value::Field(value)])
        }
        ("encoding.group_compressed", [Value::Curve(point)]) => {
            policy.bytes(48)?;
            policy.output(size(48, 1)?, available)?;
            Ok(vec![Value::Bytes(
                point.to_bytes().map_err(ark)?.to_vec().into(),
            )])
        }
        ("encoding.group_from_compressed", [Value::Bytes(bytes)]) => {
            policy.output(1024, available)?;
            // Exact width, subgroup validation and canonical re-encoding are
            // owned by the checked group adapter; no transcript state is touched.
            let point = GroupPoint::from_bytes(bytes).ok();
            Ok(vec![
                Value::Bool(point.is_some()),
                Value::Curve(point.unwrap_or_else(GroupPoint::identity)),
            ])
        }
        _ => Err(refused("encoding-operands")),
    }
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("arkworks/encoding.field_be", "encoding.field_be"),
    ("arkworks/encoding.field_from_be", "encoding.field_from_be"),
    (
        "arkworks/encoding.field_reduce_be",
        "encoding.field_reduce_be",
    ),
    (
        "arkworks/encoding.group_compressed",
        "encoding.group_compressed",
    ),
    (
        "arkworks/encoding.group_from_compressed",
        "encoding.group_from_compressed",
    ),
];

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{BigInteger, PrimeField};
    fn bytes(b: &[u8]) -> Value {
        Value::Bytes(b.to_vec().into())
    }
    fn run(name: &str, args: &[Value]) -> Vec<Value> {
        apply(
            name,
            args,
            &[],
            &Policy::default(),
            usize::MAX,
            &mut Default::default(),
        )
        .unwrap()
    }
    #[test]
    fn field_encoding_is_exact_and_reduction_is_separate() {
        for value in [Scalar::from(0u64), Scalar::from(1u64), -Scalar::from(1u64)] {
            let encoded = run("encoding.field_be", &[Value::Field(value)]);
            let Value::Bytes(b) = &encoded[0] else {
                panic!("bytes")
            };
            assert_eq!(b.as_ref(), value.into_bigint().to_bytes_be());
            assert!(matches!(run("encoding.field_from_be", &encoded).as_slice(),
                [Value::Bool(true), Value::Field(v)] if *v == value));
        }
        let modulus = Scalar::MODULUS.to_bytes_be();
        for invalid in [
            vec![],
            vec![0; 31],
            vec![0; 33],
            modulus.clone(),
            vec![255; 32],
        ] {
            assert!(
                matches!(run("encoding.field_from_be", &[bytes(&invalid)]).as_slice(),
                [Value::Bool(false), Value::Field(v)] if *v == Scalar::from(0u64))
            );
        }
        assert!(
            matches!(run("encoding.field_reduce_be", &[bytes(&modulus)]).as_slice(),
            [Value::Field(v)] if *v == Scalar::from(0u64))
        );
        let wide = [0x5a; 64];
        assert!(
            matches!(run("encoding.field_reduce_be", &[bytes(&wide)]).as_slice(),
            [Value::Field(v)] if *v == zkc_arkworks::scalar_from_wide_be(&wide))
        );
    }
    #[test]
    fn reduction_debits_bounded_work_before_computation() {
        let input = bytes(&[0xa5; 4096]);
        let mut budget = crate::external_kernels::Budget {
            limit: 8191,
            spent: 0,
        };
        let denied = apply(
            "encoding.field_reduce_be",
            std::slice::from_ref(&input),
            &[],
            &Policy::default(),
            512,
            &mut budget,
        );
        assert_eq!(denied.unwrap_err().code, "exhausted:external-work-limit");
        assert_eq!(budget.spent, 0);
        budget.limit = 8192;
        let value = apply(
            "encoding.field_reduce_be",
            &[input],
            &[],
            &Policy::default(),
            512,
            &mut budget,
        )
        .unwrap();
        assert!(
            matches!(value.as_slice(), [Value::Field(v)] if *v == Scalar::from_be_bytes_mod_order(&[0xa5;4096]))
        );
        assert_eq!(budget.spent, 8192);
    }
    #[test]
    fn group_decoder_rejects_malformed_encodings_without_failing_the_kernel() {
        for value in [
            GroupPoint::generator(),
            GroupPoint::identity(),
            GroupPoint::generator().neg(),
        ] {
            let encoded = run("encoding.group_compressed", &[Value::Curve(value)]);
            assert!(
                matches!(run("encoding.group_from_compressed", &encoded).as_slice(),
                [Value::Bool(true), Value::Curve(p)] if *p == value)
            );
        }
        let mut bad_infinity = GroupPoint::identity().to_bytes().unwrap();
        bad_infinity[47] = 1;
        let mut bad_flags = GroupPoint::identity().to_bytes().unwrap();
        bad_flags[0] |= 0x20;
        // x=0 has y=2 on the curve, but is not in the prime-order subgroup.
        let mut torsion = vec![0; 48];
        torsion[0] = 0x80;
        // x=1 gives x^3+4=5, a nonsquare in this base field.
        let mut off_curve = torsion.clone();
        off_curve[47] = 1;
        let modulus = "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";
        let mut noncanonical: Vec<u8> = (0..modulus.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&modulus[i..i + 2], 16).unwrap())
            .collect();
        noncanonical[0] |= 0x80;
        for invalid in [
            torsion,
            off_curve,
            noncanonical,
            vec![],
            vec![0; 47],
            vec![0; 49],
            vec![255; 48],
            bad_infinity.to_vec(),
            bad_flags.to_vec(),
        ] {
            assert!(
                matches!(run("encoding.group_from_compressed", &[bytes(&invalid)]).as_slice(),
                [Value::Bool(false), Value::Curve(p)] if *p == GroupPoint::identity())
            );
        }
        assert!(
            apply(
                "encoding.group_from_compressed",
                &[bytes(&[0; 48])],
                &[],
                &Policy::default(),
                1023,
                &mut Default::default()
            )
            .is_err()
        );
    }
}
