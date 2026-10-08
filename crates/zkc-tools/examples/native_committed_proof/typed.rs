//! Ordering controls use malformed setup material and absent key files so later
//! import/I/O would produce a different failure from declaration/policy admission.
use super::*;
use zkc_tools::proof::{AttemptPolicy, InputValue, ProofInputs};

fn request(input: &Json) -> ProofInputs {
    let bytes = |v: &Json| zkc_test_support::unhex(v.as_str().unwrap());
    ProofInputs {
        public: input[1]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| InputValue::Wire(bytes(&row[2])))
            .collect(),
        inputs: input[2]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| match row[1][0].as_str().unwrap() {
                "wire" => InputValue::Wire(bytes(&row[1][1])),
                "verifier_key" => InputValue::VerifierKey,
                "prover_key_file" => InputValue::ProverKeyFile {
                    path: row[1][1][0].as_str().unwrap().into(),
                    fingerprint: bytes(&row[1][1][1]).try_into().unwrap(),
                },
                _ => panic!("unexpected test constructor"),
            })
            .collect(),
        context: bytes(&input[3]),
        services: vec![],
        transcript_budget: input[5].as_str().unwrap().parse().unwrap(),
    }
}
pub(super) fn preflight(deployment: &NativeDeployment, envelope: &Json, input: &Json) {
    let key = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .position(|p| p[2].as_str().unwrap().starts_with("verifier_key:"))
        .unwrap();
    let mut bad = request(input);
    bad.public[key] = InputValue::Wire(vec![]);
    bad.inputs[0] = Value::Bool(true).into();
    assert_eq!(
        deployment.execute_typed(&bad, None).err().unwrap(),
        "native-input-type"
    );
    bad = request(input);
    bad.public[key] = InputValue::Wire(vec![]);
    let mut capacity = deployment.capacity();
    capacity.wire_bytes = 0;
    let limited = deployment.clone().with_capacity(capacity).unwrap();
    assert_eq!(
        limited.execute_typed(&bad, None).err().unwrap(),
        "native-capacity-wire"
    );
}
pub(super) fn policy_before_file(
    deployment: &NativeDeployment,
    input: &Json,
    policy: &AttemptPolicy,
) {
    let mut input = input.clone();
    let row = input[2]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|row| row[1][0] == "prover_key_file")
        .unwrap();
    row[1][1][0] = json!("/nonexistent/zkc-proof-ordering-control");
    let mut policy = policy.clone();
    policy.completion = usize::MAX;
    assert_eq!(
        deployment.execute_attempts(&input, &policy).err().unwrap(),
        "native-attempt-completion"
    );
    assert_eq!(
        deployment
            .execute_attempts_typed(&request(&input), &policy)
            .err()
            .unwrap(),
        "native-attempt-completion"
    );
}

pub(super) fn material_request(input: &Json, keys: &Keys) -> ProofInputs {
    use zkc_tools::proof::{NativeCapacity, ProverMaterial};
    let capacity = NativeCapacity::default();
    let material = ProverMaterial::from_bytes(
        &keys
            .prover_key()
            .to_bytes(&Policy::default().ark_bounds())
            .unwrap(),
        keys.prover_key().material_fingerprint(),
        keys.verifier_key(),
        capacity,
    )
    .unwrap();
    let mut typed = request(input);
    for value in &mut typed.inputs {
        if matches!(value, InputValue::ProverKeyFile { .. }) {
            *value = InputValue::ProverKey(material.clone());
        }
    }
    typed
}
pub(super) fn material_parity(
    deployment: &NativeDeployment,
    input: &Json,
    keys: &Keys,
    validator: &Json,
    expected: &[u8],
) {
    let typed = material_request(input, keys);
    let other = Keys::setup_for_development(1, &Policy::default().ark_bounds()).unwrap();
    let wrong = material_request(input, &other);
    assert_eq!(
        deployment.execute_typed(&wrong, None).err().unwrap(),
        "native-proof-input-setup"
    );
    let mut bad_validator = request(validator);
    let key = typed
        .inputs
        .iter()
        .find_map(|value| match value {
            InputValue::ProverKey(material) => Some(material.clone()),
            _ => None,
        })
        .unwrap();
    let slot = bad_validator
        .inputs
        .iter_mut()
        .find(|value| matches!(value, InputValue::VerifierKey))
        .unwrap();
    *slot = InputValue::ProverKey(key);
    assert_eq!(
        deployment
            .execute_typed(&bad_validator, Some(expected))
            .err()
            .unwrap(),
        "native-proof-role-input-kind"
    );
    std::thread::scope(|scope| {
        let calls: Vec<_> = (0..2)
            .map(|_| scope.spawn(|| deployment.execute_typed(&typed, None).unwrap()))
            .collect();
        for call in calls {
            let report = call.join().unwrap();
            assert!(report.cleanup_errors.is_empty());
            assert_eq!(report.outcome.unwrap(), expected);
        }
    });
}
