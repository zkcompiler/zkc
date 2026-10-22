//! Small-scalar repeated-addition controls and pinned-provider canonical bytes.
//! Repeated addition is independent of the multiplication/batching loop; both
//! controls still share upstream field/group arithmetic and are not proofs.
macro_rules! scaling_tests {
    ($name:ident, $point:ty, $affine:ty, $scalar:ty) => {
        mod $name {
            use ark_ec::{AffineRepr, CurveGroup};
            use ark_ff::{One, PrimeField};
            use ark_serialize::CanonicalSerialize;
            use zkc_kernels::{Error, SCALING_CHUNK_CAP};
            type Point = $point;
            type Scalar = $scalar;

            fn repeated_add(point: Point, scalar: usize) -> Point {
                (0..scalar).fold(Point::identity(), |sum, _| sum.add(&point))
            }

            fn bases(len: usize) -> Vec<Point> {
                let generator = Point::generator();
                let choices = [
                    Point::identity(),
                    generator,
                    generator.neg(),
                    generator.add(&generator),
                    generator,
                ];
                (0..len)
                    .map(|index| choices[index % choices.len()])
                    .collect()
            }

            #[test]
            fn small_scalars_and_chunk_boundaries_match_repeated_addition() {
                for len in [0, 1, 2, 3, 17, 33, 255, 256, 257, 513] {
                    let points = bases(len);
                    let saved = points.clone();
                    let scalars: Vec<_> = (0..len).map(|i| Scalar::from((i % 5) as u64)).collect();
                    let expected: Vec<_> = points
                        .iter()
                        .enumerate()
                        .map(|(i, point)| repeated_add(*point, i % 5))
                        .collect();
                    for chunk in [0, 2, 17, SCALING_CHUNK_CAP] {
                        let mut output = vec![Point::generator(); len];
                        Point::scale_each_into(&scalars, &points, &mut output, chunk).unwrap();
                        assert_eq!(output, expected, "per-point len={len}, chunk={chunk}");
                        for scalar in [0, 1, 3] {
                            Point::scale_many_into(
                                &points,
                                Scalar::from(scalar as u64),
                                &mut output,
                                chunk,
                            )
                            .unwrap();
                            let expected: Vec<_> = points
                                .iter()
                                .map(|point| repeated_add(*point, scalar))
                                .collect();
                            assert_eq!(output, expected, "common len={len}, chunk={chunk}");
                        }
                    }
                    assert_eq!(points, saved);
                }
                let mut output = vec![Point::generator(); 257];
                Point::scale_many_into(
                    &vec![Point::identity(); 257],
                    -Scalar::one(),
                    &mut output,
                    SCALING_CHUNK_CAP,
                )
                .unwrap();
                assert_eq!(output, vec![Point::identity(); 257]);
            }

            fn scalar_samples() -> Vec<Scalar> {
                let mut samples = vec![
                    Scalar::from(0),
                    Scalar::one(),
                    -Scalar::one(),
                    -Scalar::from(2),
                    Scalar::from_be_bytes_mod_order(&[0xab; 64]),
                    Scalar::from_le_bytes_mod_order(&[0x53; 32]),
                ];
                for bit in [63, 64, 127, 128, 191, 192, 253] {
                    let mut bytes = [0; 32];
                    bytes[bit / 8] = 1 << (bit % 8);
                    let scalar = Scalar::from_le_bytes_mod_order(&bytes);
                    samples.extend([scalar - Scalar::one(), scalar, scalar + Scalar::one()]);
                }
                samples
            }

            #[test]
            fn full_width_scalars_match_upstream_canonical_bytes() {
                let samples = scalar_samples();
                // The raw reference uses the historical affine dispatch, not the
                // shared batch helper. G2 canonical bytes cover both Fq2 parts.
                let raw = [
                    <$affine>::identity(),
                    <$affine>::generator(),
                    -<$affine>::generator(),
                    (<$affine>::generator() + <$affine>::generator()).into_affine(),
                ];
                let points: Vec<_> = (0..257)
                    .map(|index| {
                        let mut bytes = Vec::new();
                        raw[index % raw.len()]
                            .serialize_compressed(&mut bytes)
                            .unwrap();
                        Point::from_bytes(&bytes).unwrap()
                    })
                    .collect();
                let scalars: Vec<_> = (0..points.len())
                    .map(|i| samples[i % samples.len()])
                    .collect();
                let expected: Vec<_> = scalars
                    .iter()
                    .enumerate()
                    .map(|(i, scalar)| {
                        let mut bytes = Vec::new();
                        raw[i % raw.len()]
                            .mul_bigint(scalar.into_bigint())
                            .into_affine()
                            .serialize_compressed(&mut bytes)
                            .unwrap();
                        bytes
                    })
                    .collect();
                for chunk in [0, 17, SCALING_CHUNK_CAP] {
                    let mut output = vec![Point::identity(); points.len()];
                    Point::scale_each_into(&scalars, &points, &mut output, chunk).unwrap();
                    for (actual, expected) in output.iter().zip(&expected) {
                        assert_eq!(actual.to_bytes().unwrap().as_slice(), expected);
                        assert_eq!(Point::from_bytes(expected).unwrap(), *actual);
                    }
                    let scalar = samples[4];
                    Point::scale_many_into(&points, scalar, &mut output, chunk).unwrap();
                    for (index, actual) in output.iter().enumerate() {
                        let mut bytes = Vec::new();
                        raw[index % raw.len()]
                            .mul_bigint(scalar.into_bigint())
                            .into_affine()
                            .serialize_compressed(&mut bytes)
                            .unwrap();
                        assert_eq!(actual.to_bytes().unwrap().as_slice(), bytes);
                    }
                }
                // The common-scalar helper also covers every full-width sample
                // on a short asymmetric input, independently of chunk count.
                for scalar in samples {
                    let short = &points[..5];
                    let mut output = vec![Point::identity(); short.len()];
                    Point::scale_many_into(short, scalar, &mut output, 2).unwrap();
                    for (index, actual) in output.iter().enumerate() {
                        let mut expected = Vec::new();
                        raw[index % raw.len()]
                            .mul_bigint(scalar.into_bigint())
                            .into_affine()
                            .serialize_compressed(&mut expected)
                            .unwrap();
                        assert_eq!(actual.to_bytes().unwrap().as_slice(), expected);
                    }
                }
            }

            #[test]
            fn lengths_are_checked_before_destination_writes() {
                let points = bases(3);
                let saved = [Point::generator(); 2];
                let mut output = saved;
                assert_eq!(
                    Point::scale_many_into(&points, Scalar::one(), &mut output, 2),
                    Err(Error::InvalidEncoding)
                );
                assert_eq!(output, saved);
                assert_eq!(
                    Point::scale_each_into(&[Scalar::one(); 3], &points, &mut output, 2),
                    Err(Error::InvalidEncoding)
                );
                assert_eq!(output, saved);
                let mut output = [Point::generator(); 3];
                let saved = output;
                assert_eq!(
                    Point::scale_each_into(&[Scalar::one(); 2], &points, &mut output, 2),
                    Err(Error::InvalidEncoding)
                );
                assert_eq!(output, saved);
                assert!(Point::scaling_workspace_bytes(SCALING_CHUNK_CAP + 1).is_none());
                assert!(Point::scaling_workspace_bytes(usize::MAX).is_none());
            }
        }
    };
}

scaling_tests!(
    bls_g1,
    zkc_kernels::GroupPoint,
    ark_bls12_381::G1Affine,
    ark_bls12_381::Fr
);
scaling_tests!(
    bls_g2,
    zkc_kernels::bls12_381::G2,
    ark_bls12_381::G2Affine,
    ark_bls12_381::Fr
);
scaling_tests!(
    bn_g1,
    zkc_kernels::bn254::G1,
    ark_bn254::G1Affine,
    ark_bn254::Fr
);
scaling_tests!(
    bn_g2,
    zkc_kernels::bn254::G2,
    ark_bn254::G2Affine,
    ark_bn254::Fr
);
