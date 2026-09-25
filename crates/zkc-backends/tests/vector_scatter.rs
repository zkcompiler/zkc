//! Sparse assembly uses ordinary field/vector contracts in all installed fields.
#[path = "domains/support.rs"]
mod support;

use serde_json::json;
use support::{Controlled, assert_value, backend, one, program};
use zkc_backends::{KoalaBear, Policy, Value};
use zkc_runtime::interactive::{Backend, ErrorCode, OperationBinding, admit_supplied};

fn binding(domain: usize, contract: &str) -> OperationBinding {
    let (field, provider) = [
        ("bls12-381.fr", "arkworks"),
        ("ristretto255.scalar", "dalek"),
        ("koala-bear", "plonky3"),
    ][domain];
    OperationBinding {
        contract: contract.into(),
        arguments: vec![field.into()],
        implementation: format!("{provider}/{contract}"),
    }
}
fn vector(domain: usize, values: &[u64]) -> Value {
    if domain < 2 {
        support::vector(domain == 1, values)
    } else {
        Value::koala_bear_vector(
            &values
                .iter()
                .map(|n| KoalaBear::new(*n as u32))
                .collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap()
    }
}
fn plan(domain: usize, contract: &str, attrs: &[&str]) -> Vec<u8> {
    let binding = binding(domain, contract);
    let signature = binding.signature().unwrap();
    let args = if contract == "vector.constant" {
        vec![]
    } else {
        vec!["a0"]
    };
    program(
        &[binding],
        &signature.inputs,
        vec![json!(["op", "site", "b0", attrs, args, ["out"]])],
        &signature.outputs,
        &["out".into()],
    )
}

#[test]
fn constants_scatter_collisions_and_empty_in_all_fields() {
    let modulus_minus_one = [
        "52435875175126190479447740508185965837690552500527637822603658699938581184512",
        "7237005577332262213973186563042994240857116359379907606001950938285454250988",
        "2130706432",
    ];
    for (d, minus_one) in modulus_minus_one.iter().enumerate() {
        let b = backend(Policy::default());
        for name in ["vector.constant", "vector.scatter_sum"] {
            let row = binding(d, name);
            assert_eq!(b.binding_signature(&row), Some(row.signature().unwrap()));
            let mut wrong = row.clone();
            wrong.implementation = format!("invented/{name}");
            assert!(wrong.signature().is_err());
            assert!(b.binding_signature(&wrong).is_none());
        }
        let call = |name, attrs: &[&str], args| {
            one(backend(Policy::default()), binding(d, name), attrs, args)
                .0
                .unwrap()
        };
        assert_value(&call("vector.constant", &[], vec![])[0], &vector(d, &[]));
        assert_value(
            &call("vector.constant", &["0", "7", "0"], vec![])[0],
            &vector(d, &[0, 7, 0]),
        );
        let wrapped = call("vector.constant", &[minus_one, "2"], vec![]).remove(0);
        assert_value(
            &call("vector.scatter_sum", &["1", "0", "0"], vec![wrapped])[0],
            &vector(d, &[1]),
        );
        for (attrs, values, expected) in [
            (vec!["0"], vec![], vec![]),
            (vec!["3"], vec![], vec![0, 0, 0]),
            (vec!["4", "2", "0", "2"], vec![5, 7, 9], vec![7, 0, 14, 0]),
        ] {
            assert_value(
                &call("vector.scatter_sum", &attrs, vec![vector(d, &values)])[0],
                &vector(d, &expected),
            );
        }
        // Independent integer dot-product formula for every output coordinate.
        for n in [1, 2, 3, 17, 64] {
            let indices = (0..137).map(|j| (j * 7 + j / 3) % n).collect::<Vec<_>>();
            let values = (0..137).map(|j| (j * j + 11) as u64).collect::<Vec<_>>();
            let expected = (0..n)
                .map(|row| {
                    values
                        .iter()
                        .enumerate()
                        .map(|(j, value)| value * u64::from(indices[j] == row))
                        .sum()
                })
                .collect::<Vec<_>>();
            let attrs = std::iter::once(n.to_string())
                .chain(indices.iter().map(ToString::to_string))
                .collect::<Vec<_>>();
            assert_value(
                &call(
                    "vector.scatter_sum",
                    &attrs.iter().map(String::as_str).collect::<Vec<_>>(),
                    vec![vector(d, &values)],
                )[0],
                &vector(d, &expected),
            );
        }
    }
}

#[test]
fn admission_rejects_noncanonical_attributes_without_modular_reduction() {
    let moduli = [
        "52435875175126190479447740508185965837690552500527637822603658699938581184513",
        "7237005577332262213973186563042994240857116359379907606001950938285454250989",
        "2130706433",
    ];
    for (d, modulus) in moduli.iter().enumerate() {
        for bad in ["", "01", "+1", "-1", "1.0", "١", modulus] {
            assert_eq!(
                admit_supplied(
                    &plan(d, "vector.constant", &["1", bad]),
                    &backend(Policy::default())
                )
                .unwrap_err()
                .code,
                ErrorCode::Attributes
            );
        }
        for attrs in [
            vec![],
            vec!["00"],
            vec!["1", "01"],
            vec!["18446744073709551616"],
            vec!["1", "-1"],
        ] {
            assert_eq!(
                admit_supplied(
                    &plan(d, "vector.scatter_sum", &attrs),
                    &backend(Policy::default())
                )
                .unwrap_err()
                .code,
                ErrorCode::Attributes
            );
        }
        let bytes = plan(d, "vector.scatter_sum", &["1", "0"]);
        let mut bad: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        bad[3][0][2][0][1] = json!(
            binding((d + 1) % 3, "vector.scatter_sum")
                .signature()
                .unwrap()
                .inputs[0]
                .spelling()
        );
        assert!(
            admit_supplied(
                &serde_json::to_vec(&bad).unwrap(),
                &backend(Policy::default())
            )
            .is_err()
        );
    }
}

#[test]
fn preflight_precedes_output_allocation_and_preserves_policy_errors() {
    for d in 0..3 {
        for (attrs, values, expected) in [
            (vec!["1"], vec![1], "refused:length-mismatch"),
            (vec!["1", "0", "0"], vec![1], "refused:length-mismatch"),
            (vec!["0", "0"], vec![1], "refused:vector-index"),
            (vec!["2", "0", "2"], vec![1, 2], "refused:vector-index"),
            // The final bad index takes precedence over an impossible output.
            (
                vec!["18446744073709551615", "18446744073709551615"],
                vec![1],
                if usize::BITS == 64 {
                    "refused:vector-index"
                } else {
                    "refused:kernel-attributes"
                },
            ),
        ] {
            let mut controlled = Controlled::new(backend(Policy::default()));
            controlled.output_limit = Some(0);
            let (result, state) = one(
                controlled,
                binding(d, "vector.scatter_sum"),
                &attrs,
                vec![vector(d, &values)],
            );
            assert_eq!(result.unwrap_err(), expected);
            assert!(state.outputs.is_empty());
        }
        for (name, attrs, args) in [
            ("vector.constant", vec!["1", "2", "3"], vec![]),
            ("vector.scatter_sum", vec!["3", "0"], vec![vector(d, &[1])]),
        ] {
            let p = Policy {
                max_table_elements: 2,
                ..Policy::default()
            };
            assert_eq!(
                one(backend(p), binding(d, name), &attrs, args)
                    .0
                    .unwrap_err(),
                "exhausted:element-limit"
            );
        }
        for (name, attrs, args) in [
            ("vector.constant", vec!["1"; 100], vec![]),
            (
                "vector.scatter_sum",
                vec!["100", "0"],
                vec![vector(d, &[1])],
            ),
        ] {
            let p = Policy {
                max_value_bytes: 320,
                ..Policy::default()
            };
            assert_eq!(
                one(backend(p), binding(d, name), &attrs, args)
                    .0
                    .unwrap_err(),
                "exhausted:output-bytes"
            );
        }
        for (name, attrs, args) in [
            ("vector.constant", vec![], vec![]),
            ("vector.constant", vec!["1"], vec![]),
            ("vector.scatter_sum", vec!["0"], vec![vector(d, &[])]),
            ("vector.scatter_sum", vec!["1", "0"], vec![vector(d, &[1])]),
        ] {
            let mut b = Controlled::new(backend(Policy::default()));
            b.output_limit = Some(0);
            assert_eq!(
                one(b, binding(d, name), &attrs, args).0.unwrap_err(),
                "exhausted:output-bytes"
            );
        }
        let mut wrong = Controlled::new(backend(Policy::default()));
        wrong.substitute = Some(vector((d + 1) % 3, &[1]));
        assert_eq!(
            one(
                wrong,
                binding(d, "vector.scatter_sum"),
                &["1", "0"],
                vec![vector(d, &[1])]
            )
            .0
            .unwrap_err(),
            "refused:kernel-operands"
        );
    }
}

#[test]
fn native_rechecks_attributes_even_after_admission() {
    let moduli = [
        "52435875175126190479447740508185965837690552500527637822603658699938581184513",
        "7237005577332262213973186563042994240857116359379907606001950938285454250989",
        "2130706433",
    ];
    for (d, modulus) in moduli.iter().enumerate() {
        // Admit canonical input, then mutate the actual backend invocation.
        for bad in ["01", *modulus] {
            let mut b = Controlled::new(backend(Policy::default()));
            b.attributes = Some(vec!["1".into(), bad.into()]);
            b.output_limit = Some(0);
            let result = one(b, binding(d, "vector.constant"), &["1", "2"], vec![]).0;
            assert_eq!(
                result.unwrap_err(),
                if d == 0 {
                    "refused:invalid-encoding"
                } else {
                    "refused:noncanonical-scalar"
                }
            );
        }
        for attrs in [vec![], vec!["1", "01"], vec!["18446744073709551616"]] {
            let mut b = Controlled::new(backend(Policy::default()));
            b.attributes = Some(attrs.iter().map(|s| (*s).into()).collect());
            let result = one(
                b,
                binding(d, "vector.scatter_sum"),
                &["1", "0"],
                vec![vector(d, &[1])],
            )
            .0;
            assert_eq!(result.unwrap_err(), "refused:kernel-attributes");
        }
    }
}
