#![allow(dead_code, unused_imports)]
mod fixture;
pub use fixture::*;

use serde_json::{Value as Json, json};
use zkc_backends::*;
use zkc_runtime::interactive::{Backend, Runner, Stop, admit_supplied};

pub fn f(n: u64) -> Value {
    Value::Field(Scalar::from(n))
}
pub fn ark_backend(n: Option<usize>) -> NativeBackend {
    match n {
        Some(n) => backend().arity(n).build(),
        None => backend().build(),
    }
}
pub fn table(a: &[u64]) -> Value {
    Value::table(
        &a.iter().copied().map(Scalar::from).collect::<Vec<_>>(),
        &Policy::default(),
    )
    .unwrap()
}
pub fn point(a: &[u64]) -> Value {
    Value::point(
        a.iter().copied().map(Scalar::from).collect(),
        &Policy::default(),
    )
    .unwrap()
}
pub fn token(v: &Value) -> &Capability {
    match v {
        Value::Rng(t) | Value::Nonce(t) => t,
        _ => panic!("not token"),
    }
}
pub fn op(site: &str, kernel: &str, inputs: &[&str], outputs: &[&str]) -> Json {
    json!(["op", site, kernel, [], inputs, outputs])
}
pub fn program(
    ports: &[(&str, &str)],
    operations: Vec<Json>,
    results: &[&str],
    returns: &[&str],
) -> Vec<u8> {
    let mut body = operations;
    body.push(json!(["return", returns]));
    let args = ports.iter().map(|p| p.0).collect::<Vec<_>>();
    let names = (0..results.len())
        .map(|i| format!("out{i}"))
        .collect::<Vec<_>>();
    participants(json!([
        [["function", "kernel_test", ports, results, body]],
        [[
            "participant",
            "participant_test",
            "instance",
            "P",
            ports,
            results,
            [
                ["local", "local_site", "kernel_test", args, names],
                ["return", names]
            ],
            []
        ]],
        [["entry", "main", [["P", "participant_test"]]]]
    ]))
    .unwrap()
}
pub fn load<B: Backend<Value = Value>>(bytes: &[u8], backend: B, inputs: Vec<Value>) -> Runner<B> {
    let admitted = admit_supplied(bytes, &backend).unwrap();
    Runner::new(&admitted, "main", "P", "session", backend, inputs)
        .unwrap_or_else(|e| panic!("load failed: {}", e.error))
}
// The eleven tests that arrive through this root call the whole run `finish`.
pub use fixture::drive as finish;
pub fn run<B: Backend<Value = Value>>(
    bytes: &[u8],
    backend: B,
    inputs: Vec<Value>,
) -> (std::result::Result<Vec<Value>, Stop>, B) {
    finish(load(bytes, backend, inputs))
}
pub fn scalar(v: &Value) -> Scalar {
    match v {
        Value::Field(s) => *s,
        _ => panic!("not scalar"),
    }
}

pub fn transcript_attributes(
    kind: &str,
    source: &str,
    site: &str,
    sender: &str,
    receiver: &str,
) -> Vec<String> {
    let event = if kind == "message" {
        json!([kind, source, site, site, sender, receiver])
    } else {
        json!([
            "query",
            source,
            site,
            "input_0",
            "random.bls12-381.fr/1",
            "draw",
            receiver
        ])
    };
    vec![zkc_test_support::hex(
        &zkc_runtime::logical::encode_tree(&json!([
            "zkc.native-origin-template",
            "main",
            [],
            [],
            event
        ]))
        .unwrap(),
    )]
}

/// Small test-only declaration builder. Domains and implementations are fixed
/// BLS bindings; this does not accept a serialized closed-profile artifact.
pub fn participants(mut declarations: Json) -> Result<Vec<u8>, serde_json::Error> {
    use zkc_runtime::interactive::{LogicalType, OperationBinding, PhysicalType};
    fn physical(kind: &str) -> String {
        if kind.contains('@') {
            return kind.to_owned();
        }
        let nominal = match kind {
            "bool" | "index" | "indices" => kind.to_owned(),
            "group" | "groups" => format!("{kind}:bls12-381.g1"),
            "commitment" | "proof" | "prover_key" | "verifier_key" | "opening_state" => {
                format!("{kind}:multilinear.kzg.bls12-381/1")
            }
            "transcript" => "transcript:merlin3.bls12-381.fr64be/1".into(),
            _ => format!("{kind}:bls12-381.fr"),
        };
        PhysicalType::default_for(LogicalType::parse(&nominal).unwrap())
            .unwrap()
            .spelling()
    }
    fn ports(inputs: &mut Json, index: usize) {
        for p in inputs.as_array_mut().unwrap() {
            p[index] = json!(physical(p[index].as_str().unwrap()));
        }
    }
    fn results(outputs: &mut Json) {
        for t in outputs.as_array_mut().unwrap() {
            *t = json!(physical(t.as_str().unwrap()));
        }
    }
    fn body(body: &mut Json) {
        for i in body.as_array_mut().unwrap() {
            if i[0] == "receive" {
                i[5] = json!(physical(i[5].as_str().unwrap()));
            }
            if i[0] == "loop" {
                body_loop(i);
            }
        }
    }
    fn body_loop(i: &mut Json) {
        body(&mut i[5]);
    }
    let mut bindings = std::collections::BTreeMap::new();
    assert_eq!(declarations.as_array().unwrap().len(), 3);
    for f in declarations[0].as_array_mut().unwrap() {
        ports(&mut f[2], 1);
        results(&mut f[3]);
        let mut types = f[2]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| {
                (
                    p[0].as_str().unwrap().to_owned(),
                    PhysicalType::parse(p[1].as_str().unwrap()).unwrap(),
                )
            })
            .collect::<std::collections::BTreeMap<_, _>>();
        let transcript = f[4].as_array().unwrap().iter().any(|op| {
            op[0] == "op"
                && op[2]
                    .as_str()
                    .unwrap()
                    .contains("transcript.native.indexed.")
        });
        if transcript {
            f[4].as_array_mut().unwrap().insert(
                0,
                json!([
                    "op",
                    "coordinates",
                    "indices.empty",
                    [],
                    [],
                    ["coordinates"]
                ]),
            );
        }
        for op in f[4].as_array_mut().unwrap() {
            if op[0] != "op" {
                continue;
            }
            let name = op[2].as_str().unwrap();
            let implementation = if name.contains('/') {
                name.to_owned()
            } else if name.starts_with("indices.") {
                format!("native/{name}")
            } else {
                format!("arkworks/{name}")
            };
            let contract = implementation
                .strip_prefix("arkworks/")
                .or_else(|| implementation.strip_prefix("native/"))
                .unwrap_or(&implementation)
                .to_owned();
            let arguments = if contract.starts_with("pcs.") {
                json!(["multilinear.kzg.bls12-381/1"])
            } else if contract.starts_with("curve.") && contract != "curve.response" {
                json!(["bls12-381.g1"])
            } else if contract == "transcript.native.indexed.observe.data" {
                json!([
                    "merlin3.bls12-381.fr64be/1",
                    types[op[4][1].as_str().unwrap()].logical().spelling()
                ])
            } else if contract.starts_with("transcript.") {
                json!(["merlin3.bls12-381.fr64be/1"])
            } else if matches!(
                contract.as_str(),
                "control.require" | "bool.and" | "bool.not" | "bool.or" | "indices.empty"
            ) {
                json!([])
            } else {
                json!(["bls12-381.fr"])
            };
            let declaration = OperationBinding {
                contract: contract.clone(),
                arguments: arguments
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|v| v.as_str().unwrap().to_owned())
                    .collect(),
                implementation: implementation.clone(),
            };
            let signature = declaration.signature().unwrap();
            for (v, ty) in op[5].as_array().unwrap().iter().zip(signature.outputs) {
                types.insert(v.as_str().unwrap().to_owned(), ty);
            }
            let key = if contract == "transcript.native.indexed.observe.data" {
                format!(
                    "observe_{}",
                    zkc_test_support::hex(arguments[1].as_str().unwrap().as_bytes())
                )
            } else {
                contract.clone()
            };
            bindings.insert(
                key.clone(),
                json!([key, contract, arguments, implementation]),
            );
            op[2] = json!(key);
        }
        let name = f[1].clone();
        f.as_array_mut().unwrap().push(json!([name, []]));
    }
    for p in declarations[1].as_array_mut().unwrap() {
        ports(&mut p[4], 1);
        results(&mut p[5]);
        body(&mut p[6]);
    }
    serde_json::to_vec(&json!([
        "zkc.program",
        bindings.into_values().collect::<Vec<_>>(),
        declarations[0],
        declarations[1],
        declarations[2]
    ]))
}
