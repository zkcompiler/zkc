use super::support::*;
use serde_json::json;
use zkc_cpu::{Policy, Value};
use zkc_runtime::vm::{Backend, OperationBinding, Program, Value as RuntimeValue};

fn selected(name: &str, domain: Option<&str>) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: domain.into_iter().map(str::to_owned).collect(),
        implementation: format!(
            "{}/{name}",
            match domain {
                Some("ristretto255.scalar" | "ristretto255.group") => "dalek",
                Some(_) => "arkworks",
                None => "native",
            }
        ),
        physical_arguments: vec![],
    }
}

fn examples() -> Vec<(OperationBinding, Value, Value)> {
    let mut examples = vec![
        (
            selected("bool.select", None),
            Value::Bool(false),
            Value::Bool(true),
        ),
        (
            selected("index.select", None),
            Value::Index(0),
            Value::Index(u64::MAX),
        ),
    ];
    for d in [false, true] {
        examples.push((
            selected(
                "field.select",
                Some(if d {
                    "ristretto255.scalar"
                } else {
                    "bls12-381.fr"
                }),
            ),
            field(d, 7),
            field(d, 19),
        ));
        let group = |i| call(d, "curve.at", &[i], vec![groups(d, &[3, 5])]).remove(0);
        examples.push((
            selected(
                "curve.select",
                Some(if d {
                    "ristretto255.group"
                } else {
                    "bls12-381.g1"
                }),
            ),
            group("0"),
            group("1"),
        ));
    }
    examples
}

#[test]
fn scalar_selection_preserves_both_branches_and_exact_output_charges() {
    for (binding, yes, no) in examples() {
        let cpu = backend(Policy::default());
        assert_eq!(
            cpu.binding_signature(&binding),
            Some(binding.signature().unwrap())
        );
        for condition in [false, true] {
            let alias = one(
                backend(Policy::default()),
                binding.clone(),
                &[],
                vec![Value::Bool(condition), yes.clone(), yes.clone()],
            )
            .0
            .unwrap();
            assert_value(&alias[0], &yes);
            let expected = if condition { &yes } else { &no };
            let args = vec![Value::Bool(condition), yes.clone(), no.clone()];
            let mut exact = Controlled::new(backend(Policy::default()));
            exact.output_limit = Some(expected.retained_bytes());
            let result = one(exact, binding.clone(), &[], args.clone()).0.unwrap();
            assert_eq!(result.len(), 1);
            assert_value(&result[0], expected);
            let mut short = Controlled::new(backend(Policy::default()));
            short.output_limit = Some(expected.retained_bytes() - 1);
            assert_eq!(
                one(short, binding.clone(), &[], args).0.unwrap_err(),
                "exhausted:output-bytes"
            );
        }
    }
}

#[test]
fn scalar_selection_refuses_wrong_owners_nominals_parameters_and_ports() {
    for (binding, yes, no) in examples() {
        let cpu = backend(Policy::default());
        for mutation in ["implementation", "arguments", "physical"] {
            let mut bad = binding.clone();
            match mutation {
                "implementation" => bad.implementation = format!("uninstalled/{}", bad.contract),
                "arguments" => bad.arguments.push("bls12-381.fr".into()),
                _ => bad.physical_arguments.push("scalar".into()),
            }
            assert!(bad.signature().is_err());
            assert!(cpu.binding_signature(&bad).is_none());
        }
        if !binding.arguments.is_empty() {
            let mut bad = binding.clone();
            bad.arguments[0] = if binding.contract == "field.select" {
                "bls12-381.g1"
            } else {
                "bls12-381.fr"
            }
            .into();
            assert!(bad.signature().is_err());
            assert!(cpu.binding_signature(&bad).is_none());
        }
        let signature = binding.signature().unwrap();
        for (parameters, inputs) in [
            (json!(["0"]), signature.inputs.clone()),
            (
                json!([]),
                vec![
                    signature.inputs[1].clone(),
                    signature.inputs[0].clone(),
                    signature.inputs[2].clone(),
                ],
            ),
        ] {
            // The second malformed signature is indistinguishable only for Bool.
            if parameters == json!([]) && binding.contract == "bool.select" {
                continue;
            }
            let bytes = program(
                &[binding.clone()],
                &inputs,
                vec![json!([
                    "op",
                    "selection",
                    "b0",
                    parameters,
                    ["a0", "a1", "a2"],
                    ["result"]
                ])],
                &signature.outputs,
                &["result".into()],
            );
            assert!(Program::decode(&bytes, zkc_cpu::cpu_contracts()).is_err());
        }
        let mut substituted = Controlled::new(backend(Policy::default()));
        substituted.substitute = Some(Value::Index(0));
        assert!(
            one(substituted, binding, &[], vec![Value::Bool(true), yes, no])
                .0
                .is_err()
        );
    }
}

#[test]
fn scalar_selection_signatures_cover_every_installed_nominal_owner() {
    let cpu = backend(Policy::default());
    for owner in zkc_cpu::domains::INSTALLED {
        for (contract, identity) in std::iter::once(("field.select", owner.field))
            .chain(owner.group.map(|group| ("curve.select", group)))
        {
            let binding = OperationBinding {
                contract: contract.into(),
                arguments: vec![identity.name().into()],
                implementation: format!("{}/{contract}", owner.provider),
                physical_arguments: vec![],
            };
            let native = cpu
                .binding_signature(&binding)
                .expect("installed native scalar owner");
            assert_eq!(native, binding.signature().unwrap(), "{}", identity.name());
            for provider in ["native", "arkworks", "dalek", "plonky3"] {
                if provider == owner.provider {
                    continue;
                }
                let mut wrong = binding.clone();
                wrong.implementation = format!("{provider}/{contract}");
                assert!(wrong.signature().is_err());
                assert!(cpu.binding_signature(&wrong).is_none());
            }
        }
    }
}
