//! Rectangular coordinate permutations preserve every installed field carrier.
#[path = "domains/support.rs"]
mod support;
use p3_field::BasedVectorSpace;
use support::{backend, one};
use zkc_backends::{Bn254Scalar, KoalaBear, KoalaBearExt8, Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::interactive::{OperationBinding, Value as _};

#[test]
fn rectangular_transpose_preserves_coordinates_and_is_an_involution() {
    let numbers = [2u64, 3, 5, 7, 11, 13];
    let p = Policy::default();
    let vectors = [
        (
            "arkworks",
            Value::vector(&numbers.map(Scalar::from), &p).unwrap(),
        ),
        (
            "arkworks",
            Value::bn254_vector(&numbers.map(Bn254Scalar::from), &p).unwrap(),
        ),
        (
            "dalek",
            Value::ristretto_vector(&numbers.map(RistrettoScalar::from), &p).unwrap(),
        ),
        (
            "plonky3",
            Value::koala_bear_vector(&numbers.map(|x| KoalaBear::new(x as u32)), &p).unwrap(),
        ),
        (
            "plonky3",
            Value::koala_bear_ext8_vector(
                &numbers.map(|x| {
                    KoalaBearExt8::from_basis_coefficients_fn(|i| {
                        KoalaBear::new(x as u32 + 17 * i as u32)
                    })
                }),
                &p,
            )
            .unwrap(),
        ),
    ];
    for (provider, vector) in vectors {
        let nominal = vector.physical_type().logical().identity().name();
        let binding = OperationBinding {
            contract: "vector.transpose".into(),
            arguments: vec![nominal.into()],
            implementation: format!("{provider}/vector.transpose"),
        };
        let original = backend(p).encode_native_value(&vector).unwrap();
        let width = (original.len() - 10) / numbers.len();
        for (rows, columns) in [(1, 6), (2, 3), (3, 2), (6, 1)] {
            let out = one(
                backend(p),
                binding.clone(),
                &[],
                vec![vector.clone(), Value::Index(rows), Value::Index(columns)],
            )
            .0
            .unwrap()
            .remove(0);
            let mut expected = original[..10].to_vec();
            for column in 0..columns as usize {
                for row in 0..rows as usize {
                    let at = 10 + (row * columns as usize + column) * width;
                    expected.extend(&original[at..at + width]);
                }
            }
            assert_eq!(backend(p).encode_native_value(&out).unwrap(), expected);
            let restored = one(
                backend(p),
                binding.clone(),
                &[],
                vec![out, Value::Index(columns), Value::Index(rows)],
            )
            .0
            .unwrap()
            .remove(0);
            assert_eq!(backend(p).encode_native_value(&restored).unwrap(), original);
        }
        for (rows, columns) in [(0, 6), (2, 2), (3, 3), (u64::MAX, 2)] {
            let error = one(
                backend(p),
                binding.clone(),
                &[],
                vec![vector.clone(), Value::Index(rows), Value::Index(columns)],
            )
            .0
            .unwrap_err();
            assert!(error.contains("vector-shape"), "{error}");
        }
        let mut empty_binding = binding.clone();
        empty_binding.contract = "vector.empty".into();
        empty_binding.implementation = format!("{provider}/vector.empty");
        let empty = one(backend(p), empty_binding, &[], vec![])
            .0
            .unwrap()
            .remove(0);
        for (rows, columns) in [(0, 0), (0, u64::MAX), (u64::MAX, 0)] {
            let result = one(
                backend(p),
                binding.clone(),
                &[],
                vec![empty.clone(), Value::Index(rows), Value::Index(columns)],
            )
            .0
            .unwrap()
            .remove(0);
            assert_eq!(
                backend(p).encode_native_value(&result).unwrap(),
                backend(p).encode_native_value(&empty).unwrap()
            );
        }
    }
}
