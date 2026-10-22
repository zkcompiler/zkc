use super::*;
use crate::{Domain, EntryPolicy, NativeBackend, Scalar, Sequence};
use serde_json::json;
use std::sync::Arc;
use zkc_runtime::interpreter::Runner;
use zkc_runtime::vm::{Action, Backend, FrameExit, LogicalType, OperationBinding, Program};

// Reuse a real installed binding and Runner-minted active frame, replacing
// only result construction so Core::outputs can be tested independently.
struct Check {
    native: NativeBackend,
    values: Vec<Value>,
    fresh: usize,
    full: usize,
    checked: bool,
}
impl Backend for Check {
    type Value = Value;
    type Operation = crate::NativeOperation;
    type Call = ();
    type Checkpoint = ();
    fn prepare_binding(&self, b: &OperationBinding) -> Option<Self::Operation> {
        self.native.prepare_binding(b)
    }
    fn validate_value(&self, v: &Value) -> Result<()> {
        self.native.validate_value(v)
    }
    fn enter_frame(&mut self, f: &Frame, args: &[Value]) -> Result<()> {
        self.native.enter_frame(f, args)
    }
    fn leave_frame(&mut self, f: &Frame, exit: FrameExit, values: &[Value]) -> Result<()> {
        self.native.leave_frame(f, exit, values)
    }
    fn apply(
        &mut self,
        operation: &Self::Operation,
        i: &Invocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>> {
        if i.site != "output" {
            return self.native.apply(operation, i, args);
        }
        self.native.core.resources.active(i.frame).unwrap();
        let i = Invocation {
            retained: Retained::NONE,
            max_output_bytes: self.fresh,
            ..*i
        };
        let core = &mut self.native.core;
        let values = core.outputs(&i, args, self.values.clone()).unwrap();
        if self.fresh > 0 {
            let short = Invocation {
                max_output_bytes: self.fresh - 1,
                ..i
            };
            assert_eq!(
                core.outputs(&short, args, self.values.clone())
                    .unwrap_err()
                    .code,
                "exhausted:output-bytes"
            );
        }
        // Full tuple charging remains conservative even for shared outputs.
        core.policy.max_value_bytes = self.full;
        core.outputs(&i, args, self.values.clone()).unwrap();
        core.policy.max_value_bytes = self.full - 1;
        assert_eq!(
            core.outputs(&i, args, self.values.clone())
                .unwrap_err()
                .code,
            "exhausted:output-bytes"
        );
        core.policy = Policy::default();
        self.checked = true;
        Ok(values)
    }
}

fn check(
    binding: OperationBinding,
    args: Vec<Value>,
    values: Vec<Value>,
    fresh: usize,
    full: usize,
) {
    let sig = binding.signature().unwrap();
    let names: Vec<_> = (0..args.len()).map(|n| format!("a{n}")).collect();
    let ports: Vec<_> = names
        .iter()
        .zip(&sig.inputs)
        .map(|(name, ty)| json!([name, ty.spelling()]))
        .collect();
    let results: Vec<_> = (0..values.len()).map(|n| format!("r{n}")).collect();
    let row = json!([
        "b",
        binding.contract,
        binding.arguments,
        binding.implementation,
        binding.physical_arguments
    ]);
    let body = json!([["op", "output", "b", [], names, results], ["return", []]]);
    let function = json!(["function", "f", ports, [], body, ["f", []]]);
    let body = json!([["local", "work", "f", names, []], ["return", []]]);
    let participant = json!(["participant", "actor", "instance", "P", ports, [], body, []]);
    let mut carrier = json!([
        "zkc.program/0",
        [row],
        [function],
        [participant],
        [["entry", "main", [["P", "actor"]]]]
    ]);
    if binding.implementation == "arkworks-diagonal/vector.mul" {
        // Local views must have a reached consumer under the installed contract.
        carrier[1].as_array_mut().unwrap().push(json!([
            "dot",
            "vector.dot",
            ["bls12-381.fr"],
            "arkworks-diagonal/vector.dot",
            []
        ]));
        carrier[2][0][4].as_array_mut().unwrap().insert(
            1,
            json!(["op", "consume", "dot", [], ["a0", "r0"], ["sum"]]),
        );
    }
    let bytes = serde_json::to_vec(&carrier).unwrap();
    let native = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        Default::default(),
    )
    .unwrap();
    let backend = Check {
        native,
        values,
        fresh,
        full,
        checked: false,
    };
    let program = Program::decode(&bytes, crate::native_contracts()).unwrap();
    program.check_installation(&backend).unwrap();
    let mut runner = Runner::new(&program, "main", "P", "session", backend, args)
        .unwrap_or_else(|e| panic!("{}", e.error));
    let Action::Local(local) = runner.poll() else {
        panic!("expected local call")
    };
    runner.execute_local(&local.cut).unwrap();
    assert!(matches!(runner.poll(), Action::Returned(_)));
    let backend = runner.into_backend();
    assert!(backend.checked);
    assert_eq!(backend.native.active_frames(), 0);
}
fn binding(contract: &str, arguments: &[&str], provider: &str) -> OperationBinding {
    OperationBinding {
        contract: contract.into(),
        arguments: arguments.iter().map(|s| (*s).into()).collect(),
        implementation: format!("{provider}/{contract}"),
        physical_arguments: vec![],
    }
}
fn vector() -> Value {
    Value::Vector(vec![Scalar::from(7); 2].into())
}
fn sequence(value: Value) -> Value {
    Value::Sequence(
        Sequence::new(
            zkc_runtime::vm::PhysicalType::default_for(
                zkc_runtime::vm::LogicalType::sequence(value.physical_type().logical()).unwrap(),
            )
            .unwrap(),
            vec![value],
            &Policy::default(),
        )
        .unwrap(),
    )
}

#[test]
fn nested_operand_backing_is_free_but_inline_child_is_owned() {
    let child = vector();
    check(
        binding("sequence.at", &["vector:bls12-381.fr"], "native"),
        vec![sequence(child.clone()), Value::Index(0)],
        vec![child],
        0,
        320,
    );
    let scalar = Value::Field(Scalar::from(7));
    check(
        binding("sequence.at", &["field:bls12-381.fr"], "native"),
        vec![sequence(scalar.clone()), Value::Index(0)],
        vec![scalar],
        512,
        512,
    );
}

#[test]
fn new_array_and_view_charge_only_their_own_storage() {
    let Value::Vector(elements) = vector() else {
        unreachable!()
    };
    let array = Value::FieldArray(
        crate::FieldArray::new(
            zkc_runtime::vm::PhysicalType::default_for(
                LogicalType::field_array(zkc_runtime::vm::Identity::Bls12381Fr, 2).unwrap(),
            )
            .unwrap(),
            elements.clone(),
        )
        .unwrap(),
    );
    // The complete selected descriptor is owned; the scalar backing is shared.
    let owned = 1024 + array.physical_type().descriptor_bytes();
    check(
        binding(
            "field_array.from_vector",
            &["bls12-381.fr", "2"],
            "arkworks",
        ),
        vec![Value::Vector(elements.clone())],
        vec![array],
        owned,
        owned + 320,
    );
    let view = Value::FrDiagonal(Arc::new(
        crate::diagonal::Diagonal::new(elements.clone(), elements.clone()).unwrap(),
    ));
    // The view owns 256 bytes and retains the same parent twice.
    check(
        binding("vector.mul", &["bls12-381.fr"], "arkworks-diagonal"),
        vec![Value::Vector(elements.clone()), Value::Vector(elements)],
        vec![view],
        256,
        896,
    );
}

#[test]
fn tuple_charge_deduplicates_identity_in_either_output_order() {
    let operand = vector();
    let fresh = vector();
    // Two-element vectors each have a known 256 + 2*32 = 320 byte charge.
    for values in [
        vec![operand.clone(), fresh.clone()],
        vec![fresh.clone(), operand.clone()],
        vec![fresh.clone(), fresh.clone()],
    ] {
        check(
            binding("vector.split", &["bls12-381.fr"], "arkworks"),
            vec![operand.clone()],
            values,
            320,
            640,
        );
    }
    check(
        binding("vector.split", &["bls12-381.fr"], "arkworks"),
        vec![operand.clone()],
        vec![operand.clone(), operand],
        0,
        640,
    );
    check(
        binding("vector.split", &["bls12-381.fr"], "arkworks"),
        vec![vector()],
        vec![vector(), vector()],
        640,
        640,
    );
}

#[test]
fn inline_result_before_fresh_backing_keeps_its_owned_charge() {
    // This installed tuple puts 512 owned bytes before the first backing;
    // use its actual ordering rather than inventing a reversed signature.
    check(
        binding("encoding.fields_from_be", &["bls12-381.fr"], "arkworks"),
        vec![Value::Bytes(vec![0; 64].into())],
        vec![
            Value::Bool(true),
            Value::Vector(vec![Scalar::from(0); 2].into()),
        ],
        832,
        832,
    );
}
