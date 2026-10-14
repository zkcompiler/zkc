//! Exact mathematical encodings, separate from native transport and observation.
use crate::{GroupPoint, Policy, Result, Scalar, Value, ark, refused, value::size};
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, KernelSignature, LogicalType, OperationBinding,
    PhysicalType, Type,
};

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use Type::{Bool, Bytes, Field, Group, Groups, Vector};
    let [domain] = binding.arguments.as_slice() else {
        return None;
    };
    let identity = Identity::parse(domain).ok()?;
    let provider = identity.provider()?;
    if binding.implementation != format!("{provider}/{}", binding.contract) {
        return None;
    }
    let (inputs, outputs): (&[Type], &[Type]) = match (binding.contract.as_str(), identity) {
        ("encoding.field_be", Identity::Bls12381Fr)
        | ("encoding.field_le", Identity::Ristretto255Scalar) => (&[Field], &[Bytes]),
        ("encoding.fields_be", Identity::Bls12381Fr)
        | ("encoding.fields_le", Identity::Ristretto255Scalar) => (&[Vector], &[Bytes]),
        ("encoding.groups_compressed", Identity::Bls12381G1 | Identity::Edwards25519Prime) => {
            (&[Groups], &[Bytes])
        }
        ("encoding.field_from_be", Identity::Bls12381Fr)
        | ("encoding.field_from_le", Identity::Ristretto255Scalar) => (&[Bytes], &[Bool, Field]),
        ("encoding.field_reduce_be", Identity::Bls12381Fr)
        | ("encoding.field_reduce_le", Identity::Ristretto255Scalar) => (&[Bytes], &[Field]),
        ("encoding.group_compressed", Identity::Bls12381G1 | Identity::Edwards25519Prime) => {
            (&[Group], &[Bytes])
        }
        ("encoding.group_from_compressed", Identity::Bls12381G1 | Identity::Edwards25519Prime)
        | ("encoding.group_decode_cofactor", Identity::Edwards25519Prime) => {
            (&[Bytes], &[Bool, Group])
        }
        ("encoding.cryptonote_map", Identity::Edwards25519Prime) => (&[Bytes], &[Group]),
        _ => return None,
    };
    let port = |kind| {
        let domain = if matches!(kind, Field | Group | Vector | Groups) {
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

fn field_be(value: &Scalar) -> Result<[u8; 32]> {
    let mut bytes = zkc_arkworks::encode_scalar(value).map_err(ark)?;
    bytes.reverse();
    Ok(bytes)
}

// Ordered, fixed-width scalar encodings with no framing or transcript effects.
// Preflight the whole output before allocation; a failed element publishes no
// partial byte string. Vec-to-Arc conversion can temporarily retain both copies.
fn encode_collection<T, const WIDTH: usize>(
    values: &[T],
    policy: &Policy,
    available: usize,
    preflight: impl FnOnce() -> Result<()>,
    encode: impl Fn(&T) -> Result<[u8; WIDTH]>,
) -> Result<Vec<Value>> {
    let length = values
        .len()
        .checked_mul(WIDTH)
        .ok_or_else(|| crate::exhausted("size-overflow"))?;
    policy.bytes(length)?;
    policy.output(size(length, 2)?, available)?;
    preflight()?;
    let mut bytes = crate::kernels::arithmetic::reserve(length)?;
    for value in values {
        bytes.extend_from_slice(&encode(value)?);
    }
    Ok(vec![Value::Bytes(bytes.into())])
}

pub(crate) fn apply(
    name: &str,
    identity: Identity,
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
        ("encoding.fields_be", [Value::Vector(values)]) => {
            policy.vector(values.len())?;
            encode_collection(values, policy, available, || Ok(()), field_be)
        }
        ("encoding.fields_le", [Value::RistrettoVector(values)]) => {
            policy.vector(values.len())?;
            encode_collection(
                values,
                policy,
                available,
                || Ok(()),
                |value| Ok(value.to_bytes()),
            )
        }
        ("encoding.groups_compressed", [Value::Groups(values)]) => {
            policy.groups(values.len())?;
            encode_collection(
                values,
                policy,
                available,
                || Ok(()),
                |value| value.to_bytes().map_err(ark),
            )
        }
        ("encoding.groups_compressed", [Value::EdwardsGroups(values)]) => {
            policy.dalek_groups(values.len())?;
            encode_collection(
                values,
                policy,
                available,
                || budget.charge_units((values.len() as u64).saturating_mul(256)),
                |value| Ok(value.to_bytes()),
            )
        }
        ("encoding.field_be", [Value::Field(value)]) => {
            policy.bytes(32)?;
            policy.output(size(32, 1)?, available)?;
            let bytes = field_be(value)?;
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
        ("encoding.field_le", [Value::RistrettoField(value)]) => {
            policy.bytes(32)?;
            policy.output(size(32, 1)?, available)?;
            Ok(vec![Value::Bytes(value.to_bytes().to_vec().into())])
        }
        ("encoding.field_from_le", [Value::Bytes(bytes)]) => {
            policy.output(1024, available)?;
            let value = <[u8; 32]>::try_from(bytes.as_ref()).ok().and_then(|b| {
                Option::<crate::RistrettoScalar>::from(
                    crate::RistrettoScalar::from_canonical_bytes(b),
                )
            });
            Ok(vec![
                Value::Bool(value.is_some()),
                Value::RistrettoField(value.unwrap_or_default()),
            ])
        }
        ("encoding.field_reduce_le", [Value::Bytes(bytes)]) => {
            policy.output(512, available)?;
            budget.charge_units((bytes.len() as u64).saturating_mul(2))?;
            let radix = crate::RistrettoScalar::from(256u64);
            let value = bytes
                .iter()
                .rev()
                .fold(crate::RistrettoScalar::ZERO, |a, b| {
                    a * radix + crate::RistrettoScalar::from(u64::from(*b))
                });
            Ok(vec![Value::RistrettoField(value)])
        }
        ("encoding.group_compressed", [Value::EdwardsGroup(point)]) => {
            policy.bytes(32)?;
            policy.output(size(32, 1)?, available)?;
            budget.charge_units(256)?;
            Ok(vec![Value::Bytes(point.to_bytes().to_vec().into())])
        }
        (
            "encoding.group_from_compressed" | "encoding.group_decode_cofactor",
            [Value::Bytes(bytes)],
        ) if identity == Identity::Edwards25519Prime => {
            policy.output(1024, available)?;
            budget.charge_units(if name == "encoding.group_decode_cofactor" {
                2048
            } else {
                4096
            })?;
            let point = if name == "encoding.group_decode_cofactor" {
                crate::EdwardsPrime::decode_cofactor(bytes)
            } else {
                crate::EdwardsPrime::from_bytes(bytes)
            };
            Ok(vec![
                Value::Bool(point.is_some()),
                Value::EdwardsGroup(point.unwrap_or_else(crate::EdwardsPrime::identity)),
            ])
        }
        ("encoding.cryptonote_map", [Value::Bytes(bytes)]) => {
            policy.output(512, available)?;
            let input: [u8; 32] = bytes
                .as_ref()
                .try_into()
                .map_err(|_| refused("encoding-width"))?;
            budget.charge_units(2048)?;
            Ok(vec![Value::EdwardsGroup(crate::edwards::map(input)?)])
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
    ("arkworks/encoding.fields_be", "encoding.fields_be"),
    ("dalek/encoding.fields_le", "encoding.fields_le"),
    (
        "arkworks/encoding.groups_compressed",
        "encoding.groups_compressed",
    ),
    (
        "dalek/encoding.groups_compressed",
        "encoding.groups_compressed",
    ),
    ("dalek/encoding.field_le", "encoding.field_le"),
    ("dalek/encoding.field_from_le", "encoding.field_from_le"),
    ("dalek/encoding.field_reduce_le", "encoding.field_reduce_le"),
    (
        "dalek/encoding.group_compressed",
        "encoding.group_compressed",
    ),
    (
        "dalek/encoding.group_from_compressed",
        "encoding.group_from_compressed",
    ),
    (
        "dalek/encoding.group_decode_cofactor",
        "encoding.group_decode_cofactor",
    ),
    ("dalek/encoding.cryptonote_map", "encoding.cryptonote_map"),
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
            Identity::Bls12381Fr,
            args,
            &[],
            &Policy::default(),
            usize::MAX,
            &mut Default::default(),
        )
        .unwrap()
    }
    fn dalek(name: &str, args: &[Value]) -> Vec<Value> {
        let identity = if name.starts_with("encoding.field_") {
            Identity::Ristretto255Scalar
        } else {
            Identity::Edwards25519Prime
        };
        apply(
            name,
            identity,
            args,
            &[],
            &Policy::default(),
            usize::MAX,
            &mut Default::default(),
        )
        .unwrap()
    }
    #[test]
    fn collection_encodings_match_scalar_codecs_in_order() {
        let cases = [
            (
                "encoding.fields_be",
                "encoding.field_be",
                Identity::Bls12381Fr,
                Value::Vector(
                    vec![
                        Scalar::from(0u64),
                        Scalar::from(0x1234u64),
                        -Scalar::from(1u64),
                    ]
                    .into(),
                ),
                vec![
                    Value::Field(Scalar::from(0u64)),
                    Value::Field(Scalar::from(0x1234u64)),
                    Value::Field(-Scalar::from(1u64)),
                ],
            ),
            (
                "encoding.fields_le",
                "encoding.field_le",
                Identity::Ristretto255Scalar,
                Value::RistrettoVector(
                    vec![crate::RistrettoScalar::ZERO, crate::RistrettoScalar::ONE].into(),
                ),
                vec![
                    Value::RistrettoField(crate::RistrettoScalar::ZERO),
                    Value::RistrettoField(crate::RistrettoScalar::ONE),
                ],
            ),
            (
                "encoding.groups_compressed",
                "encoding.group_compressed",
                Identity::Bls12381G1,
                Value::Groups(vec![GroupPoint::identity(), GroupPoint::generator()].into()),
                vec![
                    Value::Curve(GroupPoint::identity()),
                    Value::Curve(GroupPoint::generator()),
                ],
            ),
            (
                "encoding.groups_compressed",
                "encoding.group_compressed",
                Identity::Edwards25519Prime,
                Value::EdwardsGroups(
                    vec![
                        crate::EdwardsPrime::identity(),
                        crate::EdwardsPrime::generator(),
                    ]
                    .into(),
                ),
                vec![
                    Value::EdwardsGroup(crate::EdwardsPrime::identity()),
                    Value::EdwardsGroup(crate::EdwardsPrime::generator()),
                ],
            ),
        ];
        for (bulk, scalar, identity, values, elements) in cases {
            let mut expected = vec![];
            for value in elements {
                let encoded = apply(
                    scalar,
                    identity,
                    &[value],
                    &[],
                    &Policy::default(),
                    usize::MAX,
                    &mut Default::default(),
                )
                .unwrap();
                let Value::Bytes(bytes) = &encoded[0] else {
                    panic!("bytes")
                };
                expected.extend_from_slice(bytes);
            }
            let limit = size(expected.len(), 2).unwrap();
            let encoded = apply(
                bulk,
                identity,
                std::slice::from_ref(&values),
                &[],
                &Policy::default(),
                limit,
                &mut Default::default(),
            )
            .unwrap();
            assert!(matches!(&encoded[0], Value::Bytes(b) if b.as_ref() == expected));
            assert_eq!(
                apply(
                    bulk,
                    identity,
                    std::slice::from_ref(&values),
                    &[],
                    &Policy::default(),
                    limit - 1,
                    &mut Default::default()
                )
                .unwrap_err()
                .code,
                "exhausted:output-bytes"
            );
            let policy = Policy {
                max_wire_bytes: expected.len() - 1,
                ..Default::default()
            };
            assert_eq!(
                apply(
                    bulk,
                    identity,
                    &[values],
                    &[],
                    &policy,
                    usize::MAX,
                    &mut Default::default()
                )
                .unwrap_err()
                .code,
                "exhausted:wire-bytes"
            );
        }
        for (op, value) in [
            ("encoding.fields_be", Value::Vector(vec![].into())),
            ("encoding.fields_le", Value::RistrettoVector(vec![].into())),
            ("encoding.groups_compressed", Value::Groups(vec![].into())),
            (
                "encoding.groups_compressed",
                Value::EdwardsGroups(vec![].into()),
            ),
        ] {
            let encoded = apply(
                op,
                Identity::None,
                &[value],
                &[],
                &Policy::default(),
                256,
                &mut Default::default(),
            )
            .unwrap();
            assert!(matches!(&encoded[0], Value::Bytes(b) if b.is_empty()));
        }
    }

    #[test]
    fn collection_output_preflight_precedes_external_work() {
        let values = [Value::EdwardsGroups(
            vec![crate::EdwardsPrime::generator(); 2].into(),
        )];
        let mut budget = crate::external_kernels::Budget {
            limit: 511,
            spent: 0,
        };
        let invoke = |available, budget: &mut crate::external_kernels::Budget| {
            apply(
                "encoding.groups_compressed",
                Identity::Edwards25519Prime,
                &values,
                &[],
                &Policy::default(),
                available,
                budget,
            )
        };
        assert_eq!(
            invoke(383, &mut budget).unwrap_err().code,
            "exhausted:output-bytes"
        );
        assert_eq!(budget.spent, 0);
        assert_eq!(
            invoke(384, &mut budget).unwrap_err().code,
            "exhausted:external-work-limit"
        );
        assert_eq!(budget.spent, 0);
        budget.limit = 512;
        assert!(invoke(384, &mut budget).is_ok());
        assert_eq!(budget.spent, 512);
    }

    #[test]
    fn little_endian_scalars_are_canonical_and_reduction_is_explicit() {
        use crate::RistrettoScalar as S;
        for value in [S::ZERO, S::ONE, -S::ONE, S::from(0x1234u64)] {
            let encoded = dalek("encoding.field_le", &[Value::RistrettoField(value)]);
            assert!(matches!(&encoded[0], Value::Bytes(b) if b.as_ref() == value.to_bytes()));
            assert!(
                matches!(dalek("encoding.field_from_le", &encoded).as_slice(),
                [Value::Bool(true), Value::RistrettoField(v)] if *v == value)
            );
        }
        let mut modulus = (-S::ONE).to_bytes();
        modulus[0] += 1;
        for invalid in [
            vec![],
            vec![0; 31],
            vec![0; 33],
            modulus.to_vec(),
            vec![255; 32],
        ] {
            assert!(
                matches!(dalek("encoding.field_from_le", &[bytes(&invalid)]).as_slice(),
                [Value::Bool(false), Value::RistrettoField(v)] if *v == S::ZERO)
            );
        }
        assert!(
            matches!(dalek("encoding.field_reduce_le", &[bytes(&modulus)]).as_slice(),
            [Value::RistrettoField(v)] if *v == S::ZERO)
        );
        for input in [[0x5a; 64], [255; 64], [0; 64]] {
            assert!(
                matches!(dalek("encoding.field_reduce_le", &[bytes(&input)]).as_slice(),
                [Value::RistrettoField(v)] if *v == S::from_bytes_mod_order_wide(&input))
            );
        }
        assert!(
            matches!(dalek("encoding.field_reduce_le", &[bytes(&[0x34,0x12])]).as_slice(),
            [Value::RistrettoField(v)] if *v == S::from(0x1234u64))
        );
    }
    #[test]
    fn edwards_encoding_distinguishes_raw_curve_and_subgroup_admission() {
        use crate::EdwardsPrime as G;
        use curve25519_dalek::constants::{ED25519_BASEPOINT_POINT, EIGHT_TORSION};
        for point in [G::identity(), G::generator(), -G::generator()] {
            let raw = dalek("encoding.group_compressed", &[Value::EdwardsGroup(point)]);
            assert!(
                matches!(dalek("encoding.group_from_compressed", &raw).as_slice(),
                [Value::Bool(true), Value::EdwardsGroup(v)] if *v == point)
            );
        }
        for torsion in EIGHT_TORSION.iter().skip(1) {
            let raw = bytes(&(ED25519_BASEPOINT_POINT + torsion).compress().to_bytes());
            assert!(
                matches!(dalek("encoding.group_from_compressed", std::slice::from_ref(&raw)).as_slice(),
                [Value::Bool(false), Value::EdwardsGroup(v)] if *v == G::identity())
            );
            assert!(
                matches!(dalek("encoding.group_decode_cofactor", &[raw]).as_slice(),
                [Value::Bool(true), Value::EdwardsGroup(v)] if *v == G::generator().scale(8u64.into()))
            );
        }
        for raw in [vec![], vec![0; 31], vec![0; 33], vec![255; 32]] {
            assert!(
                matches!(dalek("encoding.group_decode_cofactor", &[bytes(&raw)]).as_slice(),
                [Value::Bool(false), Value::EdwardsGroup(v)] if *v == G::identity())
            );
        }
    }
    #[test]
    fn map_and_little_endian_reduction_charge_before_work() {
        for (name, identity, input, work) in [
            (
                "encoding.cryptonote_map",
                Identity::Edwards25519Prime,
                vec![1; 32],
                2048,
            ),
            (
                "encoding.field_reduce_le",
                Identity::Ristretto255Scalar,
                vec![1; 64],
                128,
            ),
        ] {
            let mut budget = crate::external_kernels::Budget {
                limit: work - 1,
                spent: 0,
            };
            assert_eq!(
                apply(
                    name,
                    identity,
                    &[bytes(&input)],
                    &[],
                    &Policy::default(),
                    usize::MAX,
                    &mut budget
                )
                .unwrap_err()
                .code,
                "exhausted:external-work-limit"
            );
            assert_eq!(budget.spent, 0);
        }
        assert_eq!(
            apply(
                "encoding.cryptonote_map",
                Identity::Edwards25519Prime,
                &[bytes(&[0; 31])],
                &[],
                &Policy::default(),
                usize::MAX,
                &mut Default::default()
            )
            .unwrap_err()
            .code,
            "refused:encoding-width"
        );
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
            Identity::Bls12381Fr,
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
            Identity::Bls12381Fr,
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
                Identity::Bls12381G1,
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
