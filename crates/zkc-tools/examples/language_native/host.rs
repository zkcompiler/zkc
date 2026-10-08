//! Fresh compiler packages exercise logical Host ingress and returned values.
use super::interface::alter;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path};
use zkc_backends::{Scalar, Value as Native};
use zkc_tools::{
    entry::{Package, RoleInputs, RunEntry, RunRequest, SetupAuthority, Value},
    protocol::run::{HostLimits, InputValue, Outcome},
};
fn package(directory: &Path, name: &str) -> Package {
    let bytes = std::fs::read(directory.join(name)).unwrap();
    Package::capture(&bytes, &Sha256::digest(&bytes).into(), Package::MAX_BYTES).unwrap()
}
fn fields<const N: usize>(values: [(&str, Value); N]) -> BTreeMap<String, Value> {
    values
        .into_iter()
        .map(|(name, value)| (name.to_owned(), value))
        .collect()
}
fn scalar(n: u64) -> Value {
    Native::Field(Scalar::from(n)).into()
}
fn data(arm: usize, wire: bool) -> Value {
    let leaf = if wire {
        let mut bytes = b"ZKCV\x01\x01".to_vec();
        let mut scalar = [0; 32];
        scalar[0] = 7;
        bytes.extend_from_slice(&scalar);
        InputValue::Wire(bytes).into()
    } else {
        scalar(7)
    };
    let choice = if arm == 0 {
        Value::Variant {
            alternative: "Empty".into(),
            fields: BTreeMap::new(),
        }
    } else {
        let inner = if arm == 1 {
            Value::Variant {
                alternative: "Empty".into(),
                fields: BTreeMap::new(),
            }
        } else {
            Value::Variant {
                alternative: "Pair".into(),
                fields: fields([("0", leaf), ("1", scalar(11))]),
            }
        };
        Value::Variant {
            alternative: "Data".into(),
            fields: fields([
                ("0", inner),
                (
                    "1",
                    Value::Tuple(vec![Native::Bool(false).into(), Value::Unit]),
                ),
                ("2", Value::Array(vec![scalar(13), scalar(17)])),
            ]),
        }
    };
    Value::Record(fields([
        ("choice", choice),
        ("marker", Native::Bool(true).into()),
    ]))
}
fn request(arm: usize, wire: bool) -> RunRequest {
    RunRequest {
        session: "named-values".into(),
        setups: BTreeMap::new(),
        roles: BTreeMap::from([
            (
                "P".into(),
                RoleInputs {
                    inputs: fields([("payload", data(arm, wire)), ("empty", Value::Unit)]),
                    services: BTreeMap::new(),
                },
            ),
            (
                "V".into(),
                RoleInputs {
                    inputs: BTreeMap::new(),
                    services: BTreeMap::new(),
                },
            ),
        ]),
    }
}
fn normalized(value: &Value) -> Json {
    match value {
        Value::Unit => json!(["unit"]),
        Value::Tuple(v) => json!(["tuple", v.iter().map(normalized).collect::<Vec<_>>()]),
        Value::Array(v) => json!(["array", v.iter().map(normalized).collect::<Vec<_>>()]),
        Value::Record(v) => json!([
            "record",
            v.iter()
                .map(|(n, v)| (n, normalized(v)))
                .collect::<BTreeMap<_, _>>()
        ]),
        Value::Variant {
            alternative,
            fields,
        } => json!([
            "variant",
            alternative,
            fields
                .iter()
                .map(|(n, v)| (n, normalized(v)))
                .collect::<BTreeMap<_, _>>()
        ]),
        Value::Leaf(InputValue::Native(v)) => match v.as_ref() {
            Native::Bool(v) => json!(["bool", v]),
            Native::Field(v) => json!(["field", v.to_string()]),
            _ => panic!("unexpected scalar output"),
        },
        _ => panic!("unexpected logical output"),
    }
}
fn refuses(host: &RunEntry, request: RunRequest, expected: &str) {
    match host.prepare(request) {
        Err(code) => assert_eq!(code.code(), expected),
        Ok(_) => panic!("expected {expected}"),
    }
}
pub(super) fn run(directory: &Path) {
    services(directory);
    shared_inputs(directory);
    let publication = package(directory, "typed-host_values.entry");
    let host = RunEntry::admit(
        publication.clone(),
        HostLimits::default(),
        SetupAuthority::default(),
    )
    .unwrap();
    for arm in 0..3 {
        for wire in [false, true] {
            let report = host.prepare(request(arm, wire)).unwrap().execute();
            assert_eq!(
                report.native.execution.as_ref().unwrap().outcome,
                Outcome::Completed
            );
            assert!(report.native.cleanup_errors.is_empty());
            assert!(report.output_error.is_none());
            let report = report
                .into_result()
                .unwrap_or_else(|_| panic!("completed run failed"));
            let outputs = report.outputs.unwrap();
            assert_eq!(
                normalized(&outputs["P"]["sent"]),
                normalized(&data(arm, false))
            );
            assert_eq!(
                normalized(&outputs["V"]["received"]),
                normalized(&data(arm, false))
            );
            assert!(matches!(outputs["V"]["empty"], Value::Unit));
        }
    }
    let mut bad = request(0, false);
    bad.roles.remove("V");
    refuses(&host, bad, "entry-input-roles");
    let mut bad = request(0, false);
    bad.roles.get_mut("P").unwrap().inputs.remove("empty");
    refuses(&host, bad, "entry-input-names");
    let mut bad = request(0, false);
    let p = bad.roles.get_mut("P").unwrap();
    let empty = p.inputs.remove("empty").unwrap();
    p.inputs.insert("unknown".into(), empty);
    refuses(&host, bad, "entry-input-names");
    let mut bad = request(0, false);
    bad.roles
        .get_mut("V")
        .unwrap()
        .services
        .insert("unknown".into(), 1);
    refuses(&host, bad, "entry-service-names");
    for (value, expected) in [
        (
            Value::Record(fields([("other", data(0, false))])),
            "entry-input-fields",
        ),
        (Value::Tuple(vec![]), "entry-input-shape"),
        (
            Value::Record(fields([
                (
                    "choice",
                    Value::Variant {
                        alternative: "Unknown".into(),
                        fields: BTreeMap::new(),
                    },
                ),
                ("marker", Native::Bool(true).into()),
            ])),
            "entry-input-alternative",
        ),
        (
            Value::Record(fields([
                (
                    "choice",
                    Value::Variant {
                        alternative: "Empty".into(),
                        fields: fields([("0", scalar(3))]),
                    },
                ),
                ("marker", Native::Bool(true).into()),
            ])),
            "entry-input-fields",
        ),
    ] {
        let mut bad = request(0, false);
        bad.roles
            .get_mut("P")
            .unwrap()
            .inputs
            .insert("payload".into(), value);
        refuses(&host, bad, expected);
    }
    // Source constructor authority remains required even for native values.
    let private = alter(&publication, |_, interface| {
        fn remove_wire(value: &mut Json) {
            match value {
                Json::Object(fields) => {
                    if fields.get("kind").and_then(Json::as_str) == Some("record") {
                        fields
                            .get_mut("permissions")
                            .unwrap()
                            .as_array_mut()
                            .unwrap()
                            .retain(|p| p != "Wire");
                    }
                    for value in fields.values_mut() {
                        remove_wire(value);
                    }
                }
                Json::Array(values) => {
                    for value in values {
                        remove_wire(value);
                    }
                }
                _ => {}
            }
        }
        remove_wire(interface);
    });
    match RunEntry::admit(private, HostLimits::default(), SetupAuthority::default()) {
        Err(code) => assert_eq!(code.code(), "entry-input-constructor"),
        Ok(_) => panic!("private constructor admitted"),
    }
    match RunEntry::admit(
        package(directory, "host-custody.entry"),
        HostLimits::default(),
        SetupAuthority::default(),
    ) {
        Err(code) => assert_eq!(code.code(), "entry-output-custody"),
        Ok(_) => panic!("affine output admitted"),
    }
    let mut limits = HostLimits::default();
    limits.capacity.work.instructions = 0;
    let stopped = RunEntry::admit(publication, limits, SetupAuthority::default()).unwrap();
    let stopped = stopped.prepare(request(0, false)).unwrap().execute();
    assert!(!stopped.is_success());
    assert!(stopped.outputs.is_none());
    assert!(matches!(
        stopped.native.execution.as_ref().unwrap().outcome,
        Outcome::ParticipantStopped { .. }
    ));
}

fn services(directory: &Path) {
    let host = RunEntry::admit(
        package(directory, "host-services.entry"),
        HostLimits::default(),
        SetupAuthority::default(),
    )
    .unwrap();
    for (go, budget, transitions, completed) in [
        (true, 2, 2, true),
        (false, 0, 0, false),
        (true, 1, 2, false),
    ] {
        let report = host
            .prepare(RunRequest {
                session: "named-services".into(),
                setups: BTreeMap::new(),
                roles: BTreeMap::from([
                    (
                        "P".into(),
                        RoleInputs {
                            inputs: BTreeMap::new(),
                            services: BTreeMap::new(),
                        },
                    ),
                    (
                        "V".into(),
                        RoleInputs {
                            inputs: fields([("go", Native::Bool(go).into())]),
                            services: BTreeMap::from([("coins".into(), budget)]),
                        },
                    ),
                ]),
            })
            .unwrap()
            .execute();
        assert!(report.native.cleanup_errors.is_empty());
        assert_eq!(
            report.native.resources[0]["state"]["transitions"],
            transitions
        );
        assert_eq!(report.is_success(), completed);
        assert_eq!(report.outputs.is_some(), completed);
        if let Some(outputs) = report.outputs {
            assert_eq!(
                normalized(&outputs["P"]["p"]),
                normalized(&outputs["V"]["v"])
            );
        }
    }
}
fn shared_inputs(directory: &Path) {
    let host = RunEntry::admit(
        package(directory, "transfer.entry"),
        HostLimits::default(),
        SetupAuthority::default(),
    )
    .unwrap();
    // Run inputs belong to each participant. Source sharing does not assume
    // equal values at distinct roles or replace the native local-only policy.
    let report = host
        .prepare(RunRequest {
            session: "named-shared".into(),
            setups: BTreeMap::new(),
            roles: BTreeMap::from([
                (
                    "P".into(),
                    RoleInputs {
                        inputs: fields([("x", scalar(2)), ("c", scalar(3))]),
                        services: BTreeMap::new(),
                    },
                ),
                (
                    "V".into(),
                    RoleInputs {
                        inputs: fields([("c", scalar(5))]),
                        services: BTreeMap::new(),
                    },
                ),
            ]),
        })
        .unwrap()
        .execute();
    let outputs = report.outputs.unwrap();
    assert!(outputs["P"].is_empty());
    assert_eq!(normalized(&outputs["V"]["delta"]), normalized(&scalar(2)));
}
