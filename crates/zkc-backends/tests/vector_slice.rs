//! Dynamic vector slicing is a shared field-family operation, not host logic.
#[path = "domains/support.rs"]
mod support;
use support::{backend, one};
use zkc_backends::{Bn254Scalar, KoalaBear, Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::interactive::{OperationBinding, Value as _};

#[test]
fn slice_checks_dynamic_bounds_and_preserves_every_installed_scalar_carrier() {
    let numbers = [2u64, 3, 5, 7];
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
            Value::koala_bear_ext8_vector(&numbers.map(|x| KoalaBear::new(x as u32).into()), &p)
                .unwrap(),
        ),
    ];
    for (provider, vector) in vectors {
        let nominal = vector.physical_type().logical().identity().name();
        let binding = OperationBinding {
            contract: "vector.slice".into(),
            arguments: vec![nominal.into()],
            implementation: format!("{provider}/vector.slice"),
        };
        for (start, length) in [(0, 4), (1, 2), (4, 0), (0, 0)] {
            let out = one(
                backend(p),
                binding.clone(),
                &[],
                vec![vector.clone(), Value::Index(start), Value::Index(length)],
            )
            .0
            .unwrap();
            assert_eq!(out[0].physical_type(), vector.physical_type());
            // Compare canonical bytes independently using the sequence framing.
            let b = backend(p);
            let original = b.encode_value(&vector).unwrap();
            let width = (original.len() - 10) / 4;
            let mut expected = original[..6].to_vec();
            expected.extend((length as u32).to_le_bytes());
            expected.extend(
                &original[10 + start as usize * width..10 + (start + length) as usize * width],
            );
            assert_eq!(b.encode_value(&out[0]).unwrap(), expected);
        }
        for (start, length) in [(5, 0), (4, 1), (1, 4), (u64::MAX, 1), (1, u64::MAX)] {
            assert!(
                one(
                    backend(p),
                    binding.clone(),
                    &[],
                    vec![vector.clone(), Value::Index(start), Value::Index(length)]
                )
                .0
                .is_err()
            );
        }
    }
}
