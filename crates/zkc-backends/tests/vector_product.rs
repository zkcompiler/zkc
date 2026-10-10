//! Product values, independent admission and scalar output capacity.
#[path = "domains/support.rs"]
mod support;

use p3_field::BasedVectorSpace;
use serde_json::json;
use support::{Controlled, assert_value, backend, one, program};
use zkc_backends::{Bn254Scalar, KoalaBear, KoalaBearExt8, Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::interactive::{Backend, ErrorCode, OperationBinding, Value as _, admit_supplied};

fn cases(numbers: &[u64], expected: u64) -> [(Value, Value); 5] {
    let p = Policy::default();
    [
        (
            Value::vector(
                &numbers
                    .iter()
                    .copied()
                    .map(Scalar::from)
                    .collect::<Vec<_>>(),
                &p,
            )
            .unwrap(),
            Value::Field(Scalar::from(expected)),
        ),
        (
            Value::bn254_vector(
                &numbers
                    .iter()
                    .copied()
                    .map(Bn254Scalar::from)
                    .collect::<Vec<_>>(),
                &p,
            )
            .unwrap(),
            Value::Bn254Field(Bn254Scalar::from(expected)),
        ),
        (
            Value::ristretto_vector(
                &numbers
                    .iter()
                    .copied()
                    .map(RistrettoScalar::from)
                    .collect::<Vec<_>>(),
                &p,
            )
            .unwrap(),
            Value::RistrettoField(RistrettoScalar::from(expected)),
        ),
        (
            Value::koala_bear_vector(
                &numbers
                    .iter()
                    .map(|n| KoalaBear::new(*n as u32))
                    .collect::<Vec<_>>(),
                &p,
            )
            .unwrap(),
            Value::KoalaBearField(KoalaBear::new(expected as u32)),
        ),
        (
            Value::koala_bear_ext8_vector(
                &numbers
                    .iter()
                    .map(|n| KoalaBearExt8::from(KoalaBear::new(*n as u32)))
                    .collect::<Vec<_>>(),
                &p,
            )
            .unwrap(),
            Value::KoalaBearExt8Field(KoalaBearExt8::from(KoalaBear::new(expected as u32))),
        ),
    ]
}

fn binding(vector: &Value) -> OperationBinding {
    let identity = vector.physical_type().logical().identity();
    OperationBinding {
        contract: "vector.product".into(),
        arguments: vec![identity.name().into()],
        implementation: format!("{}/vector.product", identity.provider().unwrap()),
    }
}

#[test]
fn product_has_identity_one_and_multiplies_every_coefficient_in_each_field() {
    for (numbers, expected) in [
        (&[][..], 1),
        (&[7][..], 7),
        (&[2, 3, 5][..], 30),
        (&[2, 0, 5][..], 0),
        (&[3, 3, 3, 3][..], 81),
    ] {
        for (vector, expected) in cases(numbers, expected) {
            let operation = binding(&vector);
            let signature = operation.signature().unwrap();
            assert_eq!(signature.inputs, [vector.physical_type()]);
            assert_eq!(signature.outputs, [expected.physical_type()]);
            assert_eq!(
                backend(Policy::default()).binding_signature(&operation),
                Some(signature)
            );
            let result = one(backend(Policy::default()), operation, &[], vec![vector])
                .0
                .unwrap();
            assert_eq!(result.len(), 1);
            assert_value(&result[0], &expected);
        }
    }
}

#[test]
fn extension_product_reduces_non_base_coefficients() {
    // In this declared basis X^8 = 3. These expectations do not call a
    // production multiplication helper or reduce only the base coordinate.
    let x = KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new(u32::from(i == 1)));
    let x7 = KoalaBearExt8::from_basis_coefficients_fn(|i| KoalaBear::new(u32::from(i == 7)));
    for (coefficients, expected) in [
        (vec![x, x7], 3),
        (vec![x; 16], 9),
        (vec![x, KoalaBearExt8::from(KoalaBear::new(0)), x7], 0),
    ] {
        let vector = Value::koala_bear_ext8_vector(&coefficients, &Policy::default()).unwrap();
        let result = one(
            backend(Policy::default()),
            binding(&vector),
            &[],
            vec![vector],
        )
        .0
        .unwrap();
        assert_value(
            &result[0],
            &Value::KoalaBearExt8Field(KoalaBearExt8::from(KoalaBear::new(expected))),
        );
    }
}

#[test]
fn product_charges_scalar_output_even_for_empty_and_zero_inputs() {
    for (numbers, expected) in [(&[][..], 1), (&[2, 3][..], 6), (&[0, 3][..], 0)] {
        for (vector, expected) in cases(numbers, expected) {
            for limit in [0, 511, 512] {
                let mut controlled = Controlled::new(backend(Policy::default()));
                controlled.output_limit = Some(limit);
                let (result, observed) =
                    one(controlled, binding(&vector), &[], vec![vector.clone()]);
                if limit < 512 {
                    assert_eq!(result.unwrap_err(), "exhausted:output-bytes");
                    assert!(observed.outputs.is_empty());
                } else {
                    assert_value(&result.unwrap()[0], &expected);
                    assert_eq!(observed.outputs.len(), 1);
                }
            }
        }
    }
}

#[test]
fn product_refuses_wrong_value_kind_nominal_field_parameters_and_implementation() {
    let all = cases(&[2, 3], 6);
    for (i, (vector, scalar)) in all.iter().enumerate() {
        for wrong in [
            scalar.clone(),
            Value::Index(0),
            all[(i + 1) % all.len()].0.clone(),
        ] {
            let mut controlled = Controlled::new(backend(Policy::default()));
            controlled.substitute = Some(wrong);
            let (result, observed) = one(controlled, binding(vector), &[], vec![vector.clone()]);
            assert_eq!(result.unwrap_err(), "refused:kernel-operands");
            assert!(observed.outputs.is_empty());
        }
        let mut controlled = Controlled::new(backend(Policy::default()));
        controlled.implementation = Some(
            binding(vector)
                .implementation
                .replace("vector.product", "vector.sum"),
        );
        assert_eq!(
            one(controlled, binding(vector), &[], vec![vector.clone()])
                .0
                .unwrap_err(),
            "refused:kernel-operands"
        );

        let mut controlled = Controlled::new(backend(Policy::default()));
        controlled.attributes = Some(vec!["0".into()]);
        assert_eq!(
            one(controlled, binding(vector), &[], vec![vector.clone()])
                .0
                .unwrap_err(),
            "refused:kernel-attributes"
        );
    }
}

#[test]
fn native_reader_refuses_product_port_and_attribute_mutations() {
    for (vector, scalar) in cases(&[], 1) {
        let operation = binding(&vector);
        let signature = operation.signature().unwrap();
        for (inputs, args, outputs, attrs, code) in [
            (
                vec![scalar.physical_type()],
                vec!["a0"],
                signature.outputs.clone(),
                vec![],
                ErrorCode::Signature,
            ),
            (
                signature.inputs.clone(),
                vec![],
                signature.outputs.clone(),
                vec![],
                ErrorCode::Signature,
            ),
            (
                signature.inputs.clone(),
                vec!["a0", "a0"],
                signature.outputs.clone(),
                vec![],
                ErrorCode::Signature,
            ),
            (
                signature.inputs.clone(),
                vec!["a0"],
                signature.inputs.clone(),
                vec![],
                ErrorCode::Signature,
            ),
            (
                signature.inputs.clone(),
                vec!["a0"],
                signature.outputs.clone(),
                vec!["0"],
                ErrorCode::Attributes,
            ),
        ] {
            let bytes = program(
                std::slice::from_ref(&operation),
                &inputs,
                vec![json!(["op", "product", "b0", attrs, args, ["out"]])],
                &outputs,
                &["out".into()],
            );
            assert_eq!(
                admit_supplied(&bytes, &backend(Policy::default()))
                    .unwrap_err()
                    .code,
                code
            );
        }
    }
}

#[test]
fn product_inputs_retain_canonical_vector_decoding() {
    let b = backend(Policy::default());
    for (vector, _) in cases(&[2, 3], 6) {
        let signature = binding(&vector).signature().unwrap();
        let mut bytes = b.encode_native_value(&vector).unwrap();
        assert_value(
            &b.decode_native_value(&signature.inputs[0], &bytes).unwrap(),
            &vector,
        );
        // Native vectors have a six-byte type tag and a four-byte length.
        // All-ones coefficient encodings exceed every installed field modulus.
        bytes[10..].fill(255);
        assert_eq!(
            b.decode_native_value(&signature.inputs[0], &bytes)
                .unwrap_err()
                .to_string(),
            "native-wire-invalid:scalar"
        );
    }
}
