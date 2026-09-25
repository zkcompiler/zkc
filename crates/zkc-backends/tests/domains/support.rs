#![allow(dead_code, unused_imports)]
#[path = "../common/fixture.rs"]
mod fixture;
pub use fixture::*;

use serde_json::{Value as Json, json};
use zkc_backends::{NativeBackend, Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::interactive::{
    Backend, OperationBinding, PhysicalType, Runner, StopKind, Value as RuntimeValue,
    admit_supplied,
};
/// The thirteen tests that arrive through this root name the built backend,
/// and all of them vary the policy.
pub fn backend(p: Policy) -> NativeBackend {
    fixture::backend().policy(p).build()
}
pub fn field(d: bool, n: u64) -> Value {
    if d {
        Value::RistrettoField(RistrettoScalar::from(n))
    } else {
        Value::Field(Scalar::from(n))
    }
}
pub fn vector(d: bool, n: &[u64]) -> Value {
    if d {
        Value::ristretto_vector(
            &n.iter()
                .copied()
                .map(RistrettoScalar::from)
                .collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap()
    } else {
        Value::vector(
            &n.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap()
    }
}
pub fn groups(d: bool, n: &[u64]) -> Value {
    if d {
        Value::ristretto_groups(
            &n.iter()
                .map(|n| {
                    curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT
                        * RistrettoScalar::from(*n)
                })
                .collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap()
    } else {
        Value::groups(
            &n.iter()
                .map(|n| zkc_backends::GroupPoint::generator().scale(Scalar::from(*n)))
                .collect::<Vec<_>>(),
            &Policy::default(),
        )
        .unwrap()
    }
}
pub fn binding(d: bool, name: &str) -> OperationBinding {
    let nominal = if name.starts_with("curve.") && name != "curve.response" {
        if d {
            "ristretto255.group"
        } else {
            "bls12-381.g1"
        }
    } else if name == "transcript.challenge" {
        if d {
            "merlin3.ristretto255.scalar64le/1"
        } else {
            "merlin3.bls12-381.fr64be/1"
        }
    } else {
        if d {
            "ristretto255.scalar"
        } else {
            "bls12-381.fr"
        }
    };
    let common = matches!(
        name,
        "bool.and" | "bool.not" | "bool.or" | "control.require"
    );
    OperationBinding {
        contract: name.into(),
        arguments: if common { vec![] } else { vec![nominal.into()] },
        implementation: format!("{}/{name}", if d && !common { "dalek" } else { "arkworks" }),
    }
}
pub fn program(
    bindings: &[OperationBinding],
    inputs: &[PhysicalType],
    operations: Vec<Json>,
    outputs: &[PhysicalType],
    returns: &[String],
) -> Vec<u8> {
    let ports = inputs
        .iter()
        .enumerate()
        .map(|(i, t)| json!([format!("a{i}"), t.spelling()]))
        .collect::<Vec<_>>();
    let input_names = (0..inputs.len())
        .map(|i| format!("a{i}"))
        .collect::<Vec<_>>();
    let result_types = outputs.iter().map(|t| t.spelling()).collect::<Vec<_>>();
    let result_names = (0..outputs.len())
        .map(|i| format!("result{i}"))
        .collect::<Vec<_>>();
    let rows = bindings
        .iter()
        .enumerate()
        .map(|(j, b)| json!([format!("b{j}"), b.contract, b.arguments, b.implementation]))
        .collect::<Vec<_>>();
    let mut body = operations;
    body.push(json!(["return", returns]));
    serde_json::to_vec(&json!([
        "zkc.participants/1",
        rows,
        "physical",
        [[
            "function",
            "testfn",
            ports,
            result_types,
            body,
            ["testfn", []]
        ]],
        [[
            "participant",
            "actor",
            "instance",
            "P",
            [],
            ports,
            result_types,
            [
                ["local", "local", "testfn", input_names, result_names],
                ["return", result_names]
            ]
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]))
    .unwrap()
}
pub fn run_program<B: Backend<Value = Value>>(
    b: B,
    bytes: &[u8],
    args: Vec<Value>,
) -> (Result<Vec<Value>, String>, B) {
    let admitted = admit_supplied(bytes, &b).unwrap();
    let runner = Runner::new(&admitted, "main", "P", "session", b, args)
        .unwrap_or_else(|e| panic!("{}", e.error));
    let (outcome, backend) = fixture::drive(runner);
    (
        outcome.map_err(|stop| match stop.kind {
            StopKind::Backend(e) => e.code,
            other => format!("{other:?}"),
        }),
        backend,
    )
}
pub fn one<B: Backend<Value = Value>>(
    b: B,
    binding: OperationBinding,
    attrs: &[&str],
    args: Vec<Value>,
) -> (Result<Vec<Value>, String>, B) {
    let sig = binding.signature().unwrap();
    let outputs = (0..sig.outputs.len())
        .map(|j| format!("o{j}"))
        .collect::<Vec<_>>();
    let names = (0..args.len()).map(|j| format!("a{j}")).collect::<Vec<_>>();
    let program = program(
        &[binding],
        &sig.inputs,
        vec![json!(["op", "site", "b0", attrs, names, outputs])],
        &sig.outputs,
        &outputs,
    );
    run_program(b, &program, args)
}
pub fn call(d: bool, name: &str, attrs: &[&str], args: Vec<Value>) -> Vec<Value> {
    one(backend(Policy::default()), binding(d, name), attrs, args)
        .0
        .unwrap()
}
pub fn assert_value(a: &Value, b: &Value) {
    let backend = backend(Policy::default());
    assert_eq!(a.physical_type(), b.physical_type());
    assert_eq!(
        backend.encode_value(a).unwrap(),
        backend.encode_value(b).unwrap()
    );
}
pub fn assert_error(d: bool, name: &str, attrs: &[&str], args: Vec<Value>, code: &str) {
    assert_eq!(
        one(backend(Policy::default()), binding(d, name), attrs, args)
            .0
            .unwrap_err(),
        code
    );
}

pub struct Controlled {
    pub inner: NativeBackend,
    pub output_limit: Option<usize>,
    pub substitute: Option<Value>,
    pub implementation: Option<String>,
    pub attributes: Option<Vec<String>>,
    pub outputs: Vec<Vec<Value>>,
}
impl Controlled {
    pub fn new(inner: NativeBackend) -> Self {
        Self {
            inner,
            output_limit: None,
            substitute: None,
            implementation: None,
            attributes: None,
            outputs: Vec::new(),
        }
    }
}
impl Backend for Controlled {
    type Value = Value;
    fn binding_signature(
        &self,
        b: &OperationBinding,
    ) -> Option<zkc_runtime::interactive::BoundSignature> {
        self.inner.binding_signature(b)
    }
    fn validate_value(&self, v: &Value) -> Result<(), zkc_runtime::interactive::BackendError> {
        self.inner.validate_value(v)
    }
    fn enter_frame(
        &mut self,
        f: &zkc_runtime::interactive::Frame,
        a: &[Value],
    ) -> Result<(), zkc_runtime::interactive::BackendError> {
        self.inner.enter_frame(f, a)
    }
    fn leave_frame(
        &mut self,
        f: &zkc_runtime::interactive::Frame,
        e: zkc_runtime::interactive::FrameExit,
        v: &[Value],
    ) -> Result<(), zkc_runtime::interactive::BackendError> {
        self.inner.leave_frame(f, e, v)
    }
    fn apply(
        &mut self,
        i: &zkc_runtime::interactive::Invocation<'_>,
        a: &[Value],
    ) -> Result<Vec<Value>, zkc_runtime::interactive::BackendError> {
        let mut args = a.to_vec();
        if let Some(v) = &self.substitute {
            args[0] = v.clone();
        }
        let result = self.inner.apply(
            &zkc_runtime::interactive::Invocation {
                attributes: self.attributes.as_deref().unwrap_or(i.attributes),
                max_output_bytes: self.output_limit.unwrap_or(i.max_output_bytes),
                kernel: self.implementation.as_deref().unwrap_or(i.kernel),
                ..*i
            },
            &args,
        );
        if let Ok(values) = &result {
            self.outputs.push(values.clone());
        }
        result
    }
}

/// The tagged, length-prefixed encoding these fixtures are written in.
///
/// Independent of the production codec on purpose, which is why it is here
/// rather than imported from `zkc_runtime::logical` -- and written once,
/// because independence is from that codec rather than from itself.
pub fn tree(v: &Json) -> Vec<u8> {
    match v {
        Json::String(s) => [
            vec![0],
            (s.len() as u64).to_le_bytes().to_vec(),
            s.as_bytes().to_vec(),
        ]
        .concat(),
        Json::Array(a) => [
            vec![1],
            (a.len() as u64).to_le_bytes().to_vec(),
            a.iter().flat_map(tree).collect(),
        ]
        .concat(),
        _ => panic!("a fixture is a string or an array of them"),
    }
}
