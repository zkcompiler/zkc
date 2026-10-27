use super::*;
use crate::{
    entry::{NamedValues, arguments::proof_inputs},
    execution::{Capacity, InputValue, PreparedData},
};
use std::sync::Arc;

fn public_types(interface: &Interface) -> Vec<zkc_runtime::vm::PhysicalType> {
    interface
        .public_ports()
        .flat_map(|p| p.schema.leaves.clone())
        .map(|spelling| {
            zkc_runtime::vm::PhysicalType::default_for(
                interface.logical_type(&spelling).unwrap().clone(),
            )
            .unwrap()
        })
        .collect()
}

fn statement_interface(statement: Value) -> Interface {
    let mut doc = document();
    let leaves = statement["leaves"].as_array().unwrap().len();
    doc["protocols"][0]["inputs"][0]["type"] = statement["type"].clone();
    doc["protocols"][0]["inputs"][0]["schema"] = statement.clone();
    doc["protocols"][0]["inputs"][0]["native"] = json!((0..leaves).collect::<Vec<_>>());
    doc["protocols"][0]["inputs"][1]["native"] = json!([leaves]);
    doc["relations"][0]["inputs"][0]["schema"] = statement;
    doc["relations"][0]["inputs"][0]["native"] = json!((0..leaves).collect::<Vec<_>>());
    doc["relations"][0]["inputs"][1]["native"] = json!([leaves]);
    read(&doc).unwrap()
}

fn variant_schema(name: &str, children: Vec<Value>) -> Value {
    let leaves: Vec<_> = children
        .iter()
        .flat_map(|child| child["leaves"].as_array().unwrap().iter().cloned())
        .collect();
    let payload: Vec<_> = leaves
        .iter()
        .map(|leaf| match leaf.as_str() {
            Some(spelling) if spelling.starts_with("variant:") => {
                zkc_test_support::variants::tree(spelling)
            }
            _ => leaf.clone(),
        })
        .collect();
    let spelling = zkc_test_support::variants::encode_tree(json!([
        [
            "zkc.language",
            crate::source_names::encode_nominal_identity(name)
        ],
        [["case00000000", payload]]
    ]));
    let mut offset = 0;
    let fields: Vec<_> = children
        .into_iter()
        .enumerate()
        .map(|(index, child)| {
            let field = json!({"name":index.to_string(),"offset":offset,"schema":child});
            offset += field["schema"]["leaves"].as_array().unwrap().len();
            field
        })
        .collect();
    let mut variant = schema("variant", name, json!([spelling]));
    variant["alternatives"] = json!([{"name":"Payload","fields":fields}]);
    variant
}

#[test]
fn public_wire_duplication_preserves_the_original_payload_allocation() {
    let bytes = schema("builtin", "bytes", json!(["bytes"]));
    let mut pair = schema("tuple", "(bytes,bytes)", json!(["bytes", "bytes"]));
    pair["fields"] = json!([
        {"name":"0","offset":0,"schema":bytes},
        {"name":"1","offset":1,"schema":bytes}
    ]);
    let interface = statement_interface(pair);
    let role = &interface.roles()[interface.proof().unwrap().verifier];
    for len in [1, 1024 * 1024] {
        let data = PreparedData::from_value(
            zkc_cpu::Value::Bytes(vec![0x93; len].into()),
            Capacity::default(),
        )
        .unwrap();
        let original = data.canonical_bytes().to_vec();
        let payload = original.as_ptr();
        let owner: Arc<Vec<u8>> = original.into();
        assert_eq!(owner.as_ptr(), payload);
        let public = vec![
            InputValue::Wire(owner.clone()),
            InputValue::Wire(owner.clone()),
        ];
        let inputs = proof_inputs(
            &interface,
            role,
            &public,
            &public_types(&interface),
            NamedValues::new(),
            Capacity::default(),
            &Default::default(),
        )
        .unwrap();
        assert_eq!(inputs.len(), 2);
        for input in &inputs {
            let InputValue::Wire(bytes) = input else {
                panic!("expected shared Wire")
            };
            assert!(Arc::ptr_eq(bytes, &owner));
            assert_eq!(bytes.as_ptr(), payload);
            assert_eq!(bytes.as_slice(), data.canonical_bytes());
        }
    }
}

#[test]
fn nested_public_wire_occurrences_keep_exact_byte_sum_limits_and_preflight_order() {
    let boolean = schema("boolean", "bool", json!(["bool"]));
    let inner = variant_schema("sample::Pair", vec![boolean.clone(), boolean.clone()]);
    let interface = statement_interface(variant_schema("sample::Envelope", vec![boolean, inner]));
    let role = &interface.roles()[interface.proof().unwrap().verifier];
    let owner: Arc<Vec<u8>> = b"ZKCV\x00\x05\x01".to_vec().into();
    let public = vec![InputValue::Variant {
        alternative: 0,
        payload: vec![
            InputValue::Wire(owner.clone()),
            InputValue::Variant {
                alternative: 0,
                payload: vec![
                    InputValue::Wire(owner.clone()),
                    InputValue::Wire(owner.clone()),
                ],
            },
        ],
    }];
    let bound = 3 * owner.len();
    for (live, total, succeeds) in [
        (bound, bound + 1, true),
        (bound + 1, bound, true),
        (bound - 1, bound, false),
        (bound, bound - 1, false),
    ] {
        let mut capacity = Capacity::default();
        capacity.values.live_bytes = live;
        capacity.values.total_bytes = total;
        let result = proof_inputs(
            &interface,
            role,
            &public,
            &public_types(&interface),
            NamedValues::new(),
            capacity,
            &Default::default(),
        );
        if succeeds {
            let inputs = result.unwrap();
            let InputValue::Variant { payload, .. } = &inputs[0] else {
                panic!("expected outer variant")
            };
            let InputValue::Variant { payload: inner, .. } = &payload[1] else {
                panic!("expected inner variant")
            };
            for input in [&payload[0], &inner[0], &inner[1]] {
                let InputValue::Wire(bytes) = input else {
                    panic!("expected shared Wire")
                };
                assert!(Arc::ptr_eq(bytes, &owner));
            }
        } else {
            assert_eq!(result.unwrap_err(), "entry-input-limit");
        }
    }
    let mut capacity = Capacity::default();
    capacity.values.live_bytes = 0;
    capacity.wire_bytes = owner.len() - 1;
    assert_eq!(
        proof_inputs(
            &interface,
            role,
            &public,
            &public_types(&interface),
            NamedValues::new(),
            capacity,
            &Default::default(),
        )
        .unwrap_err(),
        "native-capacity-wire"
    );
    let malformed = vec![InputValue::Variant {
        alternative: 1,
        payload: vec![],
    }];
    assert_eq!(
        proof_inputs(
            &interface,
            role,
            &malformed,
            &public_types(&interface),
            NamedValues::new(),
            capacity,
            &Default::default(),
        )
        .unwrap_err(),
        "native-input-alternative"
    );
    capacity.wire_bytes = owner.len();
    let malformed = vec![InputValue::Variant {
        alternative: 0,
        payload: vec![
            InputValue::Wire(owner),
            InputValue::Variant {
                alternative: 0,
                payload: vec![],
            },
        ],
    }];
    assert_eq!(
        proof_inputs(
            &interface,
            role,
            &malformed,
            &public_types(&interface),
            NamedValues::new(),
            capacity,
            &Default::default(),
        )
        .unwrap_err(),
        "native-input-payload"
    );
}
