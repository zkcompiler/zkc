use curve25519_dalek::{
    constants::{ED25519_BASEPOINT_POINT, EIGHT_TORSION},
    scalar::Scalar,
};
use p3_baby_bear_043::BabyBear as F;
use p3_field_043::{BasedVectorSpace, PrimeCharacteristicRing, extension::BinomialExtensionField};
use zkc_backends::representations::*;
#[path = "fixtures/representations/generators.rs"]
mod generators;
use generators::MONERO_GENERATOR_VECTORS;
type EF = BinomialExtensionField<F, 4>;
fn hex(s: &str) -> [u8; 32] {
    assert_eq!(s.len(), 64);
    std::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
}
fn table(values: &[u32], axes: &[u32]) -> EvaluationTable<F> {
    EvaluationTable::new(
        EvaluationDomain::Boolean(OrderedAxes::new(axes.to_vec()).unwrap()),
        values.iter().copied().map(F::from_u32).collect(),
    )
    .unwrap()
}

#[test]
fn accepted_transcript_consistent_torsion_representative() {
    // Saved accepted proof's A, cross-checked against the unchanged pinned
    // Monero verifier; also pinned cleared output from scalarmult8.
    let bytes = hex("024bdd4b903aff4d46c1de799f94b76ba5cc93be45ed7869068c8989606474d6");
    let raw = RawEncodedEdwards::new(bytes);
    let decoded = raw.decode().unwrap();
    assert_eq!(
        decoded.check_subgroup(),
        Err(RepresentationError::NotPrimeSubgroup)
    );
    let image = decoded.clear_cofactor();
    assert_eq!(
        image.encoding().transcript_bytes(),
        &hex("477320fef87c51dbaa5e6a1c4635f4c7d2cb5e2dbfd5566729f333382a5b7791")
    );
    assert_eq!(decoded.raw().transcript_bytes(), &bytes);
    assert_ne!(image.encoding(), raw);
    assert_eq!(
        admit_scalar_module(EdwardsValue::Raw(&raw)),
        Err(RepresentationError::RawPointModule)
    );
    assert_eq!(
        admit_scalar_module(EdwardsValue::Decoded(&decoded)),
        Err(RepresentationError::RawPointModule)
    );
    assert_eq!(
        admit_scalar_module(EdwardsValue::Subgroup(&image)),
        Ok(&image)
    );
}

#[test]
fn raw_module_rewrite_counterexample_and_lawful_inverse_eight() {
    let a = -Scalar::ONE;
    let eight = Scalar::from(8u64);
    // Same order-four point as upstream's rct::zero() point encoding.
    let torsion = curve25519_dalek::edwards::CompressedEdwardsY([0; 32])
        .decompress()
        .unwrap();
    let raw_point = ED25519_BASEPOINT_POINT + torsion;
    assert_ne!(raw_point.mul_by_cofactor() * a, raw_point * (a * eight));
    let decoded = RawEncodedEdwards::new(raw_point.compress().to_bytes())
        .decode()
        .unwrap();
    let subgroup = decoded.clear_cofactor();
    assert_eq!(subgroup.scale(eight).scale(a), subgroup.scale(eight * a));
    for a in [
        Scalar::ZERO,
        Scalar::ONE,
        -Scalar::ONE,
        Scalar::from(347u64),
    ] {
        assert_eq!(
            subgroup.inverse_eight().scale(a),
            subgroup.scale(a * eight.invert())
        );
        assert_eq!(subgroup.inverse_eight().scale(eight), subgroup);
    }
    // Clearing all torsion representatives preserves arithmetic, not raw bytes.
    for torsion in EIGHT_TORSION {
        let p = RawEncodedEdwards::new((ED25519_BASEPOINT_POINT + torsion).compress().to_bytes());
        assert_eq!(p.decode().unwrap().clear_cofactor(), subgroup);
    }
}

#[test]
fn canonical_decoding_and_explicit_subgroup_check() {
    let base = RawEncodedEdwards::new(ED25519_BASEPOINT_POINT.compress().to_bytes());
    assert_eq!(
        admit_scalar_module(EdwardsValue::Raw(&base)),
        Err(RepresentationError::RawPointModule)
    );
    assert!(base.decode().unwrap().check_subgroup().is_ok());
    let mut identity = [0; 32];
    identity[0] = 1;
    assert!(
        RawEncodedEdwards::new(identity)
            .decode()
            .unwrap()
            .check_subgroup()
            .is_ok()
    );
    identity[31] = 128; // zero x with negative sign: upstream rejects
    assert_eq!(
        RawEncodedEdwards::new(identity).decode().unwrap_err(),
        RepresentationError::NonCanonicalPoint
    );
    let mut noncanonical = [255; 32];
    noncanonical[0] = 238;
    noncanonical[31] = 127; // p+1
    assert_eq!(
        RawEncodedEdwards::new(noncanonical).decode().unwrap_err(),
        RepresentationError::NonCanonicalPoint
    );
    assert_eq!(
        RawEncodedEdwards::new([2; 32]).decode().unwrap_err(),
        RepresentationError::InvalidPoint
    );
}

#[test]
fn pinned_generator_outputs_are_subgroup_values() {
    assert_eq!(MONERO_GENERATOR_VECTORS.len(), 7);
    for (vector, index) in MONERO_GENERATOR_VECTORS
        .iter()
        .zip([0, 1, 2, 3, 127, 128, 2047])
    {
        assert_eq!(vector.index, index);
        // Full hash-to-point recomputation is an upstream adapter check; this
        // test establishes the representation law required for using outputs.
        let p = RawEncodedEdwards::new(hex(vector.encoded_point_hex))
            .decode()
            .unwrap()
            .check_subgroup()
            .unwrap();
        assert_eq!(p.inverse_eight().scale(Scalar::from(8u64)), p);
        assert_eq!(hex(vector.hash_to_p3_input_hex).len(), 32);
    }
}

#[test]
fn upstream_axis_fixture_and_wrong_axis_refusal() {
    let t = table(&[1, 2, 4, 8], &[10, 20]);
    let r = F::from_u32(3);
    let s = F::from_u32(5);
    assert_eq!(t.evaluate(&[(10, r), (20, s)]).unwrap(), F::from_u32(64));
    assert_eq!(t.evaluate(&[(10, s), (20, r)]).unwrap(), F::from_u32(60));
    assert_eq!(
        t.fold(10, FoldConvention::HalfFirst, r),
        Err(RepresentationError::AxisMismatch)
    );
    assert_eq!(
        t.evaluate(&[(20, s), (10, r)]),
        Err(RepresentationError::AxisMismatch)
    );
    // A correctly labelled half-first evaluation can process the MSB first.
    let half = t
        .fold(20, FoldConvention::HalfFirst, s)
        .unwrap()
        .fold(10, FoldConvention::HalfFirst, r)
        .unwrap();
    assert_eq!(half.values(), &[F::from_u32(64)]);
    let reversed = OrderedAxes::new(vec![20, 10]).unwrap();
    let map = t
        .admit_boolean_mle()
        .unwrap()
        .permutation_to(&reversed)
        .unwrap();
    let transposed = t.permute_axes(&map).unwrap();
    assert_eq!(transposed.values(), &[1, 4, 2, 8].map(F::from_u32));
    assert_eq!(
        transposed.evaluate(&[(20, s), (10, r)]).unwrap(),
        F::from_u32(64)
    );
}

#[test]
fn permutations_preserve_evaluations_for_actual_domains() {
    for dims in 0..=7 {
        let axes: Vec<_> = (0..dims).collect();
        let values: Vec<_> = (0..1u32 << dims).map(|i| 13 * i * i + 7 * i + 1).collect();
        let t = table(&values, &axes);
        let point: Vec<_> = axes
            .iter()
            .map(|&axis| (axis, F::from_u32(axis + 2)))
            .collect();
        let expected = t.evaluate(&point).unwrap();
        for shift in 0..dims.max(1) as usize {
            let mut target = axes.clone();
            target.rotate_left(shift);
            let target = OrderedAxes::new(target).unwrap();
            let map = t
                .admit_boolean_mle()
                .unwrap()
                .permutation_to(&target)
                .unwrap();
            let mapped = t.permute_axes(&map).unwrap();
            let new_point: Vec<_> = target
                .axes()
                .iter()
                .map(|&axis| (axis, F::from_u32(axis + 2)))
                .collect();
            assert_eq!(mapped.evaluate(&new_point).unwrap(), expected);
            assert_eq!(
                mapped
                    .permute_axes(
                        &target
                            .permutation_to(t.admit_boolean_mle().unwrap())
                            .unwrap()
                    )
                    .unwrap(),
                t
            );
        }
    }
}

#[test]
fn extension_embedding_and_rotations() {
    let t = table(&[1, 2, 4, 8], &[0, 1]);
    let embedded = t.embed::<EF>();
    let r = F::from_u32(3);
    let s = F::from_u32(5);
    assert_eq!(
        embedded
            .evaluate(&[(0, EF::from(r)), (1, EF::from(s))])
            .unwrap(),
        EF::from(t.evaluate(&[(0, r), (1, s)]).unwrap())
    );
    assert_eq!(
        t.fold(0, FoldConvention::Adjacent, r)
            .unwrap()
            .embed::<EF>(),
        embedded
            .fold(0, FoldConvention::Adjacent, EF::from(r))
            .unwrap()
    );
    // Genuine non-base extension challenge, not just embedded base values.
    let z = EF::from_basis_coefficients_fn(|i| F::from_u32((i + 2) as u32));
    let eval = embedded.evaluate(&[(0, z), (1, EF::from(s))]).unwrap();
    let expected = (EF::ONE + z)
        + EF::from(s) * ((EF::from(F::from_u32(4)) + EF::from(F::from_u32(4)) * z) - (EF::ONE + z));
    assert_eq!(eval, expected);
    assert_eq!(
        t.rotate_rows(1).unwrap().values(),
        &[2, 4, 8, 1].map(F::from_u32)
    );
    for shift in [0, 1, 3, 4, usize::MAX] {
        let rotated = t.rotate_rows(shift).unwrap();
        assert_eq!(rotated.rotate_rows((4 - shift % 4) % 4).unwrap(), t);
        assert_eq!(rotated.embed::<EF>(), embedded.rotate_rows(shift).unwrap());
    }
    assert_ne!(
        t.rotate_rows(1)
            .unwrap()
            .evaluate(&[(0, r), (1, s)])
            .unwrap(),
        t.evaluate(&[(0, r), (1, s)]).unwrap()
    );
}

#[test]
fn unsupported_domains_and_malformed_maps_refuse() {
    use RepresentationError as E;
    assert_eq!(OrderedAxes::new(vec![0, 0]), Err(E::DuplicateAxis));
    assert_eq!(
        OrderedAxes::new((0..usize::BITS).collect()),
        Err(E::DimensionOverflow)
    );
    let axes = OrderedAxes::new(vec![0, 1]).unwrap();
    assert_eq!(
        EvaluationTable::<F>::new(EvaluationDomain::Boolean(axes.clone()), vec![F::ZERO]),
        Err(E::ShapeMismatch)
    );
    let univariate = EvaluationTable::new(
        EvaluationDomain::Univariate(vec![F::ZERO, F::ONE]),
        vec![F::ONE, F::ZERO],
    )
    .unwrap();
    assert_eq!(univariate.admit_boolean_mle(), Err(E::UnsupportedDomain));
    assert_eq!(
        univariate.fold(0, FoldConvention::Adjacent, F::ONE),
        Err(E::UnsupportedDomain)
    );
    assert_eq!(univariate.rotate_rows(1), Err(E::UnsupportedDomain));
    assert_eq!(
        EvaluationTable::<F>::new(EvaluationDomain::Univariate(vec![]), vec![]),
        Err(E::ShapeMismatch)
    );
    assert_eq!(
        EvaluationTable::new(
            EvaluationDomain::Univariate(vec![F::ONE, F::ONE]),
            vec![F::ZERO; 2]
        ),
        Err(E::DuplicateNode)
    );
    assert_eq!(
        axes.permutation_to(&OrderedAxes::new(vec![0, 2]).unwrap())
            .unwrap_err(),
        E::InvalidPermutation
    );
    assert_eq!(
        axes.permutation_to(&OrderedAxes::new(vec![0]).unwrap())
            .unwrap_err(),
        E::InvalidPermutation
    );
    let map = axes.permutation_to(&axes).unwrap();
    assert_eq!(map.source_index(4), Err(E::IndexOutOfBounds));
    assert_eq!(
        table(&[1, 2, 3, 4], &[1, 0]).permute_axes(&map),
        Err(E::AxisMismatch)
    );
    assert_eq!(univariate.permute_axes(&map), Err(E::UnsupportedDomain));
    assert_eq!(table(&[7], &[]).evaluate(&[]), Ok(F::from_u32(7)));
    for convention in [FoldConvention::Adjacent, FoldConvention::HalfFirst] {
        assert_eq!(
            table(&[7], &[]).fold(0, convention, F::ONE),
            Err(E::AxisMismatch)
        );
    }
    assert_eq!(table(&[1, 2], &[0]).evaluate(&[]), Err(E::ShapeMismatch));
    assert_eq!(E::RawPointModule.code(), "representation.raw-point-module");
    assert_eq!(
        E::UnsupportedDomain.to_string(),
        "representation.unsupported-domain"
    );
}
