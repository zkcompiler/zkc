use super::*;
use zkc_runtime::interactive::admit_supplied;
fn repin(envelope: &Json, candidate: &Json) -> Vec<u8> {
    let mut envelope = envelope.clone();
    let encoded = serde_json::to_string(candidate).unwrap();
    envelope[5] = json!(digest(encoded.as_bytes()));
    envelope[4] = json!(encoded);
    serde_json::to_vec(&envelope).unwrap()
}
fn refused(envelope: &Json, candidate: &Json, reason: &str) {
    admit_supplied(&serde_json::to_vec(candidate).unwrap(), &backend())
        .expect("mutation passes ordinary SSA/type/affine admission");
    let bytes = repin(envelope, candidate);
    assert_eq!(
        NativeDeployment::admit(&bytes, &digest(&bytes), Default::default()).unwrap_err(),
        reason
    );
}
fn replace(value: &mut Json, old: &str, new: &str) {
    match value {
        Json::String(s) if s == old => *s = new.into(),
        Json::Array(a) => {
            for v in a {
                replace(v, old, new)
            }
        }
        _ => {}
    }
}
pub fn nested(envelope: &Json, input: &Json, proof: &[u8]) {
    let original: Json = serde_json::from_str(envelope[4].as_str().unwrap()).unwrap();
    for duplicate in [false, true] {
        let mut candidate = original.clone();
        let call = &mut candidate[4][1][7][0][5][2][5][1];
        assert_eq!(call[0], "local");
        if duplicate {
            call[3][3] = call[3][2].clone();
        } else {
            call[3].as_array_mut().unwrap().swap(2, 3);
        }
        refused(envelope, &candidate, "native-proof-coordinate-operand");
    }
    let mut candidate = original.clone();
    candidate[4][1][7][0][2][2] = json!("9");
    refused(envelope, &candidate, "native-proof-loop-layout");
    let mut candidate = original.clone();
    let public = candidate[4][1][5][1][0].clone();
    candidate[4][1][7][0][5][2][5][1][3][1] = public;
    refused(envelope, &candidate, "native-proof-observation-payload");
    let mut candidate = original.clone();
    let helper = candidate[3]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|f| f[1] == "_transcript_1")
        .unwrap();
    helper[4][1][4][1] = helper[2][1][0].clone();
    refused(envelope, &candidate, "native-proof-helper-coordinates");
    let mut candidate = original.clone();
    let body = &mut candidate[4][1][7][0][5][2][5];
    let removed = body.as_array_mut().unwrap().remove(1);
    replace(
        body,
        removed[4][0].as_str().unwrap(),
        removed[3][0].as_str().unwrap(),
    );
    refused(envelope, &candidate, "native-proof-observation-order");
    // Generated helper symbols are implementation names, not origin bytes.
    let mut candidate = original.clone();
    let names: Vec<_> = candidate[3]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|f| {
            f[1].as_str()
                .filter(|s| s.starts_with("_transcript"))
                .map(str::to_owned)
        })
        .collect();
    for name in names {
        replace(&mut candidate, &name, &format!("renamed{name}"));
    }
    let bytes = repin(envelope, &candidate);
    let deployment = NativeDeployment::admit(&bytes, &digest(&bytes), Default::default()).unwrap();
    assert!(
        execute(&deployment, input, Some(proof), "nested")
            .outcome
            .is_ok()
    );
}
pub fn proof(deployment: &NativeDeployment, input: &Json, proof: &[u8], family: &str, n: u64) {
    if n > 0 || family != "nested" {
        // Counts come from the received value; they are not trusted from the
        // descriptor. Sumcheck checks arity; nested control enforces its bound.
        let mut changed = proof.to_vec();
        changed[54..62].copy_from_slice(&9u64.to_le_bytes());
        let failure = execute(deployment, input, Some(&changed), family)
            .outcome
            .unwrap_err();
        assert!(
            failure.contains(if family == "nested" {
                "loop-count-bound"
            } else {
                "Explicit"
            }),
            "{failure}"
        );
    }
    if family != "nested" && n > 0 {
        let mut changed = proof.to_vec();
        // First array element starts after header, index frame and array header.
        changed[76..108].fill(255);
        let failure = execute(deployment, input, Some(&changed), family)
            .outcome
            .unwrap_err();
        assert!(failure.to_ascii_lowercase().contains("scalar"), "{failure}");
        let mut changed = proof.to_vec();
        changed[76..108].fill(0);
        assert!(
            execute(deployment, input, Some(&changed), family)
                .outcome
                .is_err()
        );
    }
}

pub fn false_claim(deployment: &NativeDeployment, envelope: &Json, input: &Json, proof: &[u8]) {
    let mut changed = input.clone();
    let bytes = hex(&backend()
        .encode_native_value(&Value::Field(Scalar::from(0)))
        .unwrap());
    for row in changed[1].as_array_mut().unwrap() {
        if row[1] == "3" {
            row[2] = json!(bytes);
        }
    }
    for row in changed[2].as_array_mut().unwrap() {
        if row[0] == "3" {
            row[1][1] = json!(bytes);
        }
    }
    let mut rebound = proof.to_vec();
    rebound[8..40].copy_from_slice(&Sha256::digest(reference::root(envelope, &changed)));
    let report = execute(deployment, &changed, Some(&rebound), "sumcheck");
    assert!(
        report.outcome.is_err(),
        "even a zero-round proof must check the original public polynomial"
    );
}
