use serde_json::Value as Json;
use std::collections::BTreeMap;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Value};
use zkc_tools::proof::{AttemptPolicy, NativeDeployment};

// An empty test provider distinguishes refusal before issuance from reaching
// the issuance phase. The expected byte total is computed from public codec
// estimates and actual entry occurrences, independently of the host planner.
pub fn private_input_admission_boundary(
    deployment: &NativeDeployment,
    envelope: &Json,
    input: &Json,
    attempts: Option<&AttemptPolicy>,
) {
    use zkc_runtime::interactive::{LogicalType, PhysicalType};
    let codec = NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "test", "main", None), None),
        Default::default(),
    )
    .unwrap();
    assert_ne!(envelope[2][1][5], "", "control must select a transcript");
    let estimate = |logical: &Json, wire: &Json| {
        let ty = PhysicalType::default_for(LogicalType::parse(logical.as_str().unwrap()).unwrap())
            .unwrap();
        let wire = wire.as_str().unwrap();
        let bytes: Vec<_> = (0..wire.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&wire[i..i + 2], 16).unwrap())
            .collect();
        codec.native_input_retained_bytes(&ty, &bytes).unwrap()
    };
    let mut public = BTreeMap::new();
    for (port, value) in envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .zip(input[1].as_array().unwrap())
    {
        public.insert(port[1].as_str().unwrap(), estimate(&port[2], &value[2]));
    }
    let role = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r[0] == envelope[2][1][2])
        .unwrap();
    let mut pool: usize = public.values().sum();
    let mut entry = 0;
    for (port, value) in role[2]
        .as_array()
        .unwrap()
        .iter()
        .zip(input[2].as_array().unwrap())
    {
        let id = port[0].as_str().unwrap();
        let bytes = if matches!(value[1][0].as_str(), Some("nonce" | "rng")) {
            Value::capability_retained_bytes()
        } else {
            estimate(&port[1], &value[1][1])
        };
        if !public.contains_key(id) {
            pool += bytes;
        }
        entry += bytes;
    }
    if envelope[2][1][5] != "" {
        pool += Value::capability_retained_bytes();
        entry += Value::capability_retained_bytes();
    }
    let required = pool.max(entry);
    let bounded = |bytes| {
        let mut capacity = deployment.capacity();
        capacity.values.live_bytes = bytes;
        deployment.clone().with_capacity(capacity).unwrap()
    };
    let execute = |bytes| {
        let deployment = bounded(bytes);
        if let Some(policy) = attempts {
            let mut policy = policy.clone();
            policy.values.live_bytes = bytes;
            zkc_test_drivers::execute_test(
                &deployment,
                input,
                zkc_tools::proof::Invocation::Attempts(&policy),
                BTreeMap::new(),
            )
        } else {
            zkc_test_drivers::execute_test(
                &deployment,
                input,
                zkc_tools::proof::Invocation::one_shot(None),
                BTreeMap::new(),
            )
        }
    };
    assert_eq!(
        execute(required - 1).err().unwrap(),
        "artifact-input-bytes-limit"
    );
    let report = execute(required).unwrap();
    assert_eq!(
        report.outcome.unwrap_err(),
        "native-proof-test-entropy-port"
    );
    assert!(report.cleanup_errors.is_empty());
}
