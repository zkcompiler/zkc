//! Test-only generic interactive driver with caller-supplied random tapes.
//! Native primitives, admission, role scheduling and envelope checks are reused.
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::{
    Domain, EntryPolicy, InputBindings, NativeBackend, Policy, PublicInputs, Scalar, Value,
};
use zkc_runtime::interactive::{Packet, Runner, admit_physical};
use zkc_tools::{
    artifact::hex,
    protocol::{JointOutcome, ParticipantChecker, Schedule, Transport, drive},
};

fn backend(role: &str, session: &str) -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new(role, session, "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap()
}

#[derive(Default)]
struct RecordingTransport(Vec<String>);
impl Transport<Value> for RecordingTransport {
    fn transfer(&mut self, _: &Packet<Value>, bytes: Vec<u8>) -> Result<Vec<u8>, String> {
        self.0.push(hex(&bytes));
        Ok(bytes)
    }
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    assert_eq!(args.len(), 5, "SOURCE CANDIDATE CHECKER TEST_INPUTS OUTPUT");
    let source = std::fs::read(&args[0]).unwrap();
    let candidate = std::fs::read(&args[1]).unwrap();
    let checker = ParticipantChecker::new(&args[2]).unwrap();
    let config: Json = serde_json::from_slice(&std::fs::read(&args[3]).unwrap()).unwrap();
    let host = &config["host"];
    let session = host[2].as_str().unwrap();
    let admitted = admit_physical(&source, &candidate, &backend("P", session), &checker).unwrap();
    let mut schedule = Schedule::new(&admitted, "main", session).unwrap();
    let source_ports = schedule.inputs().unwrap();
    let mut runners = BTreeMap::new();
    let mut handles = BTreeMap::new();
    for role in admitted.entry("main").unwrap() {
        let record = host[4]
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r[0] == role.role)
            .unwrap();
        let mut native = backend(&role.role, session);
        let mut bindings = InputBindings::new();
        let mut issued = Vec::new();
        for service in record[1].as_array().unwrap() {
            let label = service[1].as_str().unwrap();
            let tape = config["tapes"][&role.role][label]
                .as_array()
                .unwrap()
                .iter()
                .map(|n| Scalar::from(n.as_u64().unwrap()))
                .collect();
            let budget: u64 = service[2].as_str().unwrap().parse().unwrap();
            let resource = native
                .issue_test_tape(
                    Domain::new(
                        &role.role,
                        session,
                        "main",
                        if service[3] == "entry" {
                            Some(&role.instance)
                        } else {
                            None
                        },
                    ),
                    budget,
                    tape,
                )
                .unwrap();
            bindings.insert(label, resource.clone()).unwrap();
            issued.push((label.to_string(), resource));
        }
        let inputs: Vec<_> = source_ports[&role.role]
            .iter()
            .zip(&role.inputs)
            .map(|((original, _), (target, _))| {
                assert_eq!(
                    admitted
                        .source_map()
                        .unwrap()
                        .port(&role.instance, &role.role, original),
                    Some(target.as_str())
                );
                let value = record[2]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|p| p[0] == *original)
                    .unwrap();
                json!([target, value[1]])
            })
            .collect();
        let values = native
            .inputs_from_json(
                &role,
                &serde_json::to_vec(&json!(["zkc.inputs/1", inputs])).unwrap(),
                &bindings,
            )
            .unwrap();
        handles.insert(role.role.clone(), issued);
        let runner = Runner::new(&admitted, "main", &role.role, session, native, values)
            .unwrap_or_else(|e| panic!("{}", e.error));
        runners.insert(role.role.clone(), runner);
    }
    let mut wire = RecordingTransport::default();
    let report = drive(&mut schedule, &mut runners, &mut wire);
    let mut resources = Vec::new();
    for (role, runner) in &runners {
        assert_eq!(runner.backend().active_frames(), 0);
        for (label, value) in &handles[role] {
            let Value::Rng(token) = value else {
                unreachable!()
            };
            let state = runner.backend().observe(token).unwrap();
            resources.push(json!([
                role,
                label,
                state.generation,
                state.draw_count,
                state.budget
            ]));
        }
    }
    let outcome = match report.outcome {
        JointOutcome::Returned(values) => {
            let mut outputs = BTreeMap::new();
            for (role, vs) in values {
                let encoded: Vec<_> = vs.iter().map(|v| match v {
                    Value::Bool(b) => json!(["bool", b.to_string()]),
                    Value::Rng(token) => {
                        let label = handles[&role].iter().find(|(_, v)|
                            matches!(v, Value::Rng(t) if t.issued_id() == token.issued_id())).unwrap().0.clone();
                        json!(["rng:bls12-381.fr", [format!("{role}_{label}"), token.generation().to_string()]])
                    }
                    _ => panic!("unexpected output"),
                }).collect();
                outputs.insert(role, encoded);
            }
            json!(["returned", outputs])
        }
        JointOutcome::Stopped(stop) => json!(["stopped", stop.role, format!("{:?}", stop.kind)]),
        JointOutcome::Failed(error) => panic!("driver failed: {error}"),
    };
    let result = json!({"outcome":outcome, "messages":wire.0, "resources":resources,
        "cancelled_roles":report.cancelled.iter().map(|s| s.role.clone()).collect::<Vec<_>>()});
    std::fs::write(
        Path::new(&args[4]),
        serde_json::to_vec_pretty(&result).unwrap(),
    )
    .unwrap();
}
