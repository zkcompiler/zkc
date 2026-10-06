//! Direct library equations, independent of compiler recipes and backend kernels.
use super::*;
#[allow(dead_code)]
#[path = "../support/domain_transcript.rs"]
mod transcript;
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::{Field, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use p3_field::TwoAdicField;
fn encode<T: CanonicalSerialize>(value: &T) -> Vec<u8> {
    let mut out = Vec::new();
    value.serialize_compressed(&mut out).unwrap();
    out
}
fn matrix_products(matrices: &Sequence, w: &[F]) -> Vec<Vec<F>> {
    matrices
        .elements()
        .iter()
        .map(|value| {
            let Value::Bn254Matrix(matrix) = value else {
                panic!("QAP matrix");
            };
            assert_eq!(matrix.columns(), w.len());
            let mut rows = vec![F::zero(); matrix.rows()];
            for &(row, col, coefficient) in matrix.entries() {
                rows[row as usize] += coefficient * w[col as usize];
            }
            rows
        })
        .collect()
}
/// Prove the negative control isolates ONE rather than a row or public mismatch.
pub fn check_one_control(values: &[Value]) {
    let [
        Value::Sequence(matrices),
        Value::Bn254Vector(public),
        Value::Bn254Vector(w),
        ..,
    ] = values
    else {
        panic!("QAP control inputs");
    };
    assert_eq!(w[0], F::from(2));
    assert_eq!(&w[1..1 + public.len()], &public[..]);
    let rows = matrix_products(matrices, w);
    assert_eq!(rows.len(), 3);
    assert_eq!(rows[0].len(), rows[1].len());
    assert_eq!(rows[0].len(), rows[2].len());
    assert!(
        rows[0]
            .iter()
            .zip(&rows[1])
            .zip(&rows[2])
            .all(|((a, b), c)| *a * b == *c)
    );
}
pub fn check(
    family: &str,
    n: usize,
    values: &[Value],
    envelope: &Json,
    input: &Json,
    proof: &[u8],
) -> usize {
    let frames = packets(proof);
    match family {
        "qap-composition" => {
            assert_eq!(frames.len(), 3);
            let [
                Value::Sequence(matrices),
                _,
                Value::Bn254Vector(w),
                Value::Bn254G1Vector(query),
                Value::Bn254G2(g2),
                Value::Bn254Field(shift),
                _,
            ] = values
            else {
                panic!("QAP inputs");
            };
            let products = matrix_products(matrices, w);
            assert!(products.iter().all(|rows| rows.len() == n));
            let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
            let coset = domain.get_coset(*shift).unwrap();
            let mut witness = b"ZKCV\x01\x29".to_vec();
            witness.extend_from_slice(&(w.len() as u32).to_le_bytes());
            for value in w.iter() {
                witness.extend(encode(value));
            }
            assert_eq!(frames[0].1, witness);
            let evaluate = |rows: &[F]| {
                if n > 16 {
                    return coset.fft(&domain.ifft(rows));
                }
                // Direct Lagrange interpolation avoids the backend's FFT path
                // on small composition cases. Domain roots and field arithmetic
                // remain explicit library premises.
                let roots: Vec<_> = domain.elements().collect();
                coset
                    .elements()
                    .map(|point| {
                        roots
                            .iter()
                            .enumerate()
                            .map(|(i, root)| {
                                let (numerator, denominator) = roots
                                    .iter()
                                    .enumerate()
                                    .filter(|(j, _)| *j != i)
                                    .fold((F::from(1), F::from(1)), |(num, den), (_, other)| {
                                        (num * (point - other), den * (*root - other))
                                    });
                                rows[i] * numerator * denominator.inverse().unwrap()
                            })
                            .sum::<F>()
                    })
                    .collect::<Vec<_>>()
            };
            let a = evaluate(&products[0]);
            let b = evaluate(&products[1]);
            let c = evaluate(&products[2]);
            let point = a
                .iter()
                .zip(b)
                .zip(c)
                .zip(query.iter())
                .fold(
                    ark_bn254::G1Projective::zero(),
                    |sum, (((a, b), c), base)| {
                        let raw = base.to_bytes().unwrap();
                        let base = ark_bn254::G1Affine::deserialize_compressed(&raw[..]).unwrap();
                        sum + base * (*a * b - c)
                    },
                )
                .into_affine();
            let raw = g2.to_bytes().unwrap();
            let g2 = ark_bn254::G2Affine::deserialize_compressed(&raw[..]).unwrap();
            assert_eq!(&frames[1].1[6..], encode(&point));
            assert_eq!(
                &frames[2].1[6..],
                encode(&ark_bn254::Bn254::pairing(point, g2))
            );
        }
        "target-accumulation" => {
            assert_eq!(frames.len(), 1);
            let point = (ark_bn254::G1Affine::generator() * F::from(13 * n as u64)).into_affine();
            assert_eq!(
                &frames[0].1[6..],
                encode(&ark_bn254::Bn254::pairing(
                    point,
                    ark_bn254::G2Affine::generator()
                ))
            );
        }
        "air-composition" => {
            assert_eq!(frames.len(), 5);
            let mut replay = transcript::Replay::new(
                envelope,
                input,
                proof,
                "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
            );
            replay.message("trace", "P", "V");
            replay.query("draw", 6, "random.koala-bear.ext8-binomial3/1", "V");
            let challenge = replay.extension();
            replay.observe(
                "challenge",
                "V",
                "P",
                &transcript::extension_wire(challenge),
            );
            assert_eq!(
                replay.message("challenge_echo", "P", "V"),
                transcript::extension_wire(challenge)
            );
            replay.message("root", "P", "V");
            let row = replay.message("row", "P", "V");
            assert_eq!(&row[..10], b"ZKCV\x01\x1b\x01\0\0\0");
            let actual =
                transcript::extension_value(&[b"ZKCV\x01\x1a".as_slice(), &row[10..]].concat());
            replay.message("path", "P", "V");
            let rejections = replay.finish();
            let root = E::two_adic_generator(n.trailing_zeros() as usize);
            let x = E::from_u64(7)
                * E::two_adic_generator((2 * n).trailing_zeros() as usize).exp_u64((n - 1) as u64);
            let at_zero =
                (0..n).map(|i| E::from_u64(3 + 2 * i as u64)).sum::<E>() / E::from_u64(n as u64);
            // Barycentric evaluation on all trace-domain roots, not the FFT path.
            let evaluate = |point: E| {
                let mut omega = E::ONE;
                let mut sum = E::ZERO;
                for i in 0..n {
                    sum += E::from_u64(3 + 2 * i as u64) * omega / (point - omega);
                    omega *= root;
                }
                (point.exp_u64(n as u64) - E::ONE) * sum / E::from_u64(n as u64)
            };
            let positive = (evaluate(x) - at_zero) / x;
            let negative = (evaluate(-x) - at_zero) / (-x);
            let expected = (positive + negative) / E::from_u64(2)
                + challenge * (positive - negative) / (E::from_u64(2) * x);
            assert_eq!(actual, expected);
            return rejections;
        }
        _ => panic!("unknown client"),
    }
    0
}

pub fn check_g2_ingress() {
    use ark_bn254::{Fq, Fq2, G2Affine};
    use ark_serialize::CanonicalSerialize;
    use zkc_runtime::interactive::Value as RuntimeValue;
    let wrong = (0u64..100)
        .find_map(|n| {
            G2Affine::get_point_from_x_unchecked(Fq2::new(Fq::from(n), Fq::from(1)), false)
                .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        })
        .unwrap();
    assert!(wrong.is_on_curve());
    let mut wire = b"ZKCV\x01\x30".to_vec();
    wrong.serialize_compressed(&mut wire).unwrap();
    let ty = Value::Bn254G2(Bn254G2::generator()).physical_type();
    assert_eq!(
        codec().decode_native_value(&ty, &wire).unwrap_err(),
        zkc_backends::NativeWireError::Invalid(zkc_runtime::interactive::DecodeReason::Group)
    );
}
