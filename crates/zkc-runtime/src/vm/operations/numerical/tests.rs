use super::*;
use crate::ring::Expression;
use crate::vm::Program;
use serde_json::{Value as Json, json};
use zkc_test_support::numerical_plan;

fn binding(field: &str, provider: &str, mode: &str, mask: &str) -> OperationBinding {
    OperationBinding {
        physical_arguments: vec![],
        contract: format!("numerical.{mode}"),
        arguments: vec![field.into(), mask.into()],
        implementation: format!("{provider}/numerical.{mode}"),
    }
}

#[test]
fn numerical_logical_ports_preserve_positional_zeroes_and_exact_fields() {
    for (field, provider) in [
        ("bn254.fr", "arkworks"),
        ("bls12-381.fr", "arkworks"),
        ("ristretto255.scalar", "dalek"),
        ("koala-bear", "plonky3"),
        ("koala-bear.ext4-binomial3", "plonky3"),
        ("koala-bear.ext8-binomial3", "plonky3"),
        ("gf2-64.pentanomial-4-3-1", "plonky3"),
        ("gf2-64.pentanomial-4-3-1.ext3-trinomial1", "plonky3"),
    ] {
        for mode in ["map", "sum", "product"] {
            for mask in ["", "0", "00101"] {
                let binding = binding(field, provider, mode, mask);
                let logical = binding.logical_signature().unwrap();
                assert_eq!(logical.inputs.len(), 1 + mask.len());
                assert_eq!(logical.inputs[0].spelling(), "index");
                for (input, bit) in logical.inputs[1..].iter().zip(mask.bytes()) {
                    assert_eq!(input.identity().name(), field);
                    assert_eq!(
                        input.kind(),
                        if bit == b'0' {
                            Type::Field
                        } else {
                            Type::Vector
                        }
                    );
                }
                assert_eq!(logical.outputs[0].identity().name(), field);
                assert_eq!(
                    logical.outputs[0].kind(),
                    if mode == "map" {
                        Type::Vector
                    } else {
                        Type::Field
                    }
                );
                assert_eq!(logical.attributes, AttributeRule::NumericalExpression);
                assert!(binding.signature().is_ok());
                for wrong in ["arkworks", "dalek", "plonky3", "missing"] {
                    assert_eq!(
                        OperationBinding {
                            physical_arguments: vec![],
                            implementation: format!("{wrong}/numerical.{mode}"),
                            ..binding.clone()
                        }
                        .signature()
                        .is_ok(),
                        wrong == provider
                    );
                }
            }
        }
    }
    let valid = binding("koala-bear", "plonky3", "map", "");
    assert_eq!(
        OperationBinding {
            physical_arguments: vec![],
            arguments: vec!["koala-bear".into(), "0".repeat(1023)],
            ..valid.clone()
        }
        .signature()
        .unwrap()
        .inputs
        .len(),
        1024
    );
    for arguments in [
        vec![],
        vec!["koala-bear".into()],
        vec!["koala-bear".into(), "".into(), "".into()],
        vec!["koala-bear".into(), "0".repeat(1024)],
        vec!["koala-bear".into(), "01x".into()],
        vec!["koala-bear".into(), "０".into()],
        vec!["bls12-381.g1".into(), "1".into()],
    ] {
        assert_eq!(
            OperationBinding {
                arguments,
                ..valid.clone()
            }
            .signature()
            .unwrap_err()
            .code,
            ErrorCode::Signature
        );
    }
}

fn program(binding: &OperationBinding, parameters: &[String], dormant: bool) -> Vec<u8> {
    let signature = binding.signature().unwrap();
    let mut ports: Vec<_> = signature
        .inputs
        .iter()
        .enumerate()
        .map(|(i, t)| json!([format!("a{i}"), t.spelling()]))
        .collect();
    let mut names: Vec<_> = (0..ports.len()).map(|i| format!("a{i}")).collect();
    let output = signature.outputs[0].spelling();
    let op = json!(["op", "evaluate", "expr", parameters, names, ["result"]]);
    let body = if dormant {
        ports.push(json!(["condition", "bool@native.bool/0"]));
        names.push("condition".into());
        json!([
            [
                "if",
                "choose",
                "condition",
                ["a0", "a1"],
                [op, ["yield", ["result"]]],
                [["yield", ["a1"]]],
                ["chosen"]
            ],
            ["return", ["chosen"]]
        ])
    } else {
        json!([op, ["return", ["result"]]])
    };
    serde_json::to_vec(&json!([
        "zkc.program/0",
        [[
            "expr",
            binding.contract,
            binding.arguments,
            binding.implementation,
            binding.physical_arguments
        ]],
        [[
            "function",
            "evaluate",
            ports,
            [output],
            body,
            ["evaluate", []]
        ]],
        [[
            "participant",
            "actor",
            "instance",
            "P",
            ports,
            [output],
            [
                ["local", "local", "evaluate", names, ["returned"]],
                ["return", ["returned"]]
            ],
            []
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]))
    .unwrap()
}

#[test]
fn admission_checks_the_actual_body_and_dormant_branches() {
    let binding = binding("koala-bear", "plonky3", "map", "1");
    let valid = numerical_plan(json!(["zkc.ring/0", ["koala-bear"], [["input", 0]], [0]]));
    for dormant in [false, true] {
        assert!(
            Program::decode(
                &program(&binding, std::slice::from_ref(&valid), dormant),
                &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
            )
            .is_ok()
        );
        for parameters in [
            vec![],
            vec![valid.clone(), valid.clone()],
            vec![format!(" {valid}")],
            vec![valid.replace("\"input\",0", "\"input\",1")],
            vec![valid.replace("koala-bear", "bls12-381.fr")],
            vec![numerical_plan(json!([
                "zkc.ring/0",
                [],
                [["constant", "koala-bear", "1"]],
                [0]
            ]))],
            vec![numerical_plan(json!([
                "zkc.ring/0",
                ["koala-bear"],
                [["input", 0]],
                [0, 0]
            ]))],
            vec![numerical_plan(json!([
                "zkc.ring/0",
                ["koala-bear"],
                [["input", 0]],
                []
            ]))],
            vec![numerical_plan(json!([
                "zkc.ring/0",
                ["koala-bear"],
                [["constant", "bls12-381.fr", "1"]],
                [0]
            ]))],
            vec!["not a Ring body".into()],
        ] {
            assert_eq!(
                Program::decode(
                    &program(&binding, &parameters, dormant),
                    &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
                )
                .unwrap_err()
                .code,
                ErrorCode::Attributes
            );
        }
    }
    let extension = binding_for_extension();
    let embedded = numerical_plan(json!([
        "zkc.ring/0",
        ["koala-bear"],
        [["input", 0], ["embed", "koala-bear.ext4-binomial3", 0]],
        [1]
    ]));
    assert_eq!(
        parameters(&extension, &[embedded]).unwrap_err().code,
        ErrorCode::Attributes
    );
}

fn binding_for_extension() -> OperationBinding {
    binding("koala-bear.ext4-binomial3", "plonky3", "map", "1")
}

fn body_with_bytes(bytes: usize) -> String {
    for count in 1..400 {
        let mut nodes: Vec<Json> = vec![json!(["constant", "bls12-381.fr", "1"])];
        nodes.extend((0..count).map(|i| json!(["neg", i])));
        let mut body = json!(["zkc.ring/0", [], nodes, [count]]);
        let length = body.to_string().len();
        if let Some(extra) = bytes.checked_sub(length).filter(|n| *n < 69) {
            body[2][0][2] = json!("1".repeat(1 + extra));
            return body.to_string();
        }
    }
    panic!("missing boundary fixture");
}

#[test]
fn canonical_body_byte_boundary_is_exact() {
    let binding = binding("bls12-381.fr", "arkworks", "map", "");
    let exact = body_with_bytes(4096);
    assert_eq!(exact.len(), 4096);
    assert!(
        Program::decode(
            &program(
                &binding,
                &[numerical_plan(serde_json::from_str(&exact).unwrap())],
                false
            ),
            &crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose())
        )
        .is_ok()
    );
    let over = body_with_bytes(4097);
    assert!(Expression::parse(&over).is_ok());
    assert_eq!(
        parameters(
            &binding,
            &[numerical_plan(serde_json::from_str(&over).unwrap())]
        )
        .unwrap_err()
        .code,
        ErrorCode::Limit
    );
}
