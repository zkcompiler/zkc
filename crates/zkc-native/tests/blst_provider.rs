//! Installed provider refusals publish no values and preserve aliased inputs.
#[path = "domains/support.rs"]
mod support;
use support::{Controlled, assert_value, backend, one};
use zkc_native::{Bls12381G2, G1, Policy, Scalar, Value};
use zkc_runtime::vm::OperationBinding;

fn binding(contract: &str, domain: &str) -> OperationBinding {
    OperationBinding {
        contract: contract.into(),
        arguments: vec![domain.into()],
        implementation: format!("blst/{contract}"),
    }
}
fn inputs(contract: &str, g2: bool, n: usize) -> Vec<Value> {
    let s: Vec<_> = (0..n).map(|i| Scalar::from((i + 1) as u64)).collect();
    let p = if g2 {
        Value::Bls12381G2Vector(
            s.iter()
                .map(|&s| Bls12381G2::generator().scale(s))
                .collect::<Vec<_>>()
                .into(),
        )
    } else {
        Value::Groups(
            s.iter()
                .map(|&s| G1::generator().scale(s))
                .collect::<Vec<_>>()
                .into(),
        )
    };
    match contract {
        "pairing.check" => vec![
            p,
            Value::Bls12381G2Vector(
                s.iter()
                    .map(|&s| Bls12381G2::generator().scale(s))
                    .collect::<Vec<_>>()
                    .into(),
            ),
        ],
        "curve.vector_scale" => vec![p, Value::Field(Scalar::from(7))],
        _ => vec![Value::Vector(s.into()), p],
    }
}

#[test]
fn output_refusal_precedes_allocations_and_failure_publishes_nothing() {
    for g2 in [false, true] {
        for contract in [
            "curve.msm",
            "curve.scale_each",
            "curve.vector_scale",
            "pairing.check",
        ] {
            if g2 && contract == "pairing.check" {
                continue;
            }
            let domain = if contract == "pairing.check" {
                "bls12-381.fr"
            } else if g2 {
                "bls12-381.g2"
            } else {
                "bls12-381.g1"
            };
            let args = inputs(contract, g2, 3);
            let aliases = args.clone();
            let mut controlled = Controlled::new(backend(Policy::default()));
            controlled.output_limit = Some(0);
            let failure = zkc_kernels::allocation::failure::after(0);
            let (result, controlled) = one(controlled, binding(contract, domain), &[], args);
            drop(failure);
            assert_eq!(result.unwrap_err(), "exhausted:output-bytes");
            assert!(controlled.outputs.is_empty());
            for (alias, fresh) in aliases.iter().zip(inputs(contract, g2, 3)) {
                assert_value(alias, &fresh);
            }
            for successful in 0..5 {
                let failure = zkc_kernels::allocation::failure::after(successful);
                let (result, controlled) = one(
                    Controlled::new(backend(Policy::default())),
                    binding(contract, domain),
                    &[],
                    aliases.clone(),
                );
                drop(failure);
                if let Err(error) = result {
                    assert_eq!(error, "exhausted:allocation");
                    assert!(controlled.outputs.is_empty());
                }
                for (alias, fresh) in aliases.iter().zip(inputs(contract, g2, 3)) {
                    assert_value(alias, &fresh);
                }
            }
        }
    }
}

#[test]
fn empty_and_mismatched_vectors_follow_mathematical_contracts() {
    for g2 in [false, true] {
        let domain = if g2 { "bls12-381.g2" } else { "bls12-381.g1" };
        let expected = if g2 {
            Value::Bls12381G2(Bls12381G2::identity())
        } else {
            Value::Curve(G1::identity())
        };
        let result = one(
            backend(Policy::default()),
            binding("curve.msm", domain),
            &[],
            inputs("curve.msm", g2, 0),
        )
        .0
        .unwrap();
        assert_value(&result[0], &expected);
        for n in [0, 1, 4] {
            let mut args = inputs("curve.msm", g2, 3);
            args[0] = Value::Vector(vec![Scalar::from(1); n].into());
            let (result, controlled) = one(
                Controlled::new(backend(Policy {
                    max_numerical_work: 0,
                    ..Policy::default()
                })),
                binding("curve.msm", domain),
                &[],
                args,
            );
            assert_eq!(result.unwrap_err(), "refused:length-mismatch");
            assert!(controlled.outputs.is_empty());
        }
    }
    let result = one(
        backend(Policy::default()),
        binding("pairing.check", "bls12-381.fr"),
        &[],
        inputs("pairing.check", false, 0),
    )
    .0
    .unwrap();
    assert_value(&result[0], &Value::Bool(true));
}
