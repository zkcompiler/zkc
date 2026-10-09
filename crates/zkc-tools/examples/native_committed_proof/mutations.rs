//! Malformed messages and changed mathematical statements, with binding headers
//! recomputed where needed so terminal failures are not just envelope failures.
use super::*;
use zkc_runtime::interactive::Value as RuntimeValue;
fn error(deployment: &NativeDeployment, input: &Json, proof: Option<&[u8]>) -> String {
    match deployment.execute(input, proof) {
        Err(e) => e,
        Ok(report) => {
            let error = report.outcome.expect_err("mutation accepted");
            assert!(
                !error.contains("cleanup") && !error.contains("active-frames"),
                "{error}"
            );
            error
        }
    }
}
fn refuse(deployment: &NativeDeployment, input: &Json, proof: Option<&[u8]>, expected: &str) {
    let actual = error(deployment, input, proof);
    assert!(
        actual.to_lowercase().contains(&expected.to_lowercase()),
        "expected {expected}, got {actual}"
    );
}
fn rebind(envelope: &Json, input: &Json, proof: &[u8]) -> Vec<u8> {
    let mut changed = proof.to_vec();
    changed[8..40].copy_from_slice(&Sha256::digest(reference::root(envelope, input)));
    changed
}
fn public(input: &Json, port: usize, bytes: &[u8]) -> Json {
    let mut changed = input.clone();
    let name = port.to_string();
    let encoding = hex(bytes);
    changed[1]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|p| p[1] == name)
        .unwrap()[2] = json!(encoding);
    if let Some(row) = changed[2]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|p| p[0] == name && p[1][0] == "wire")
    {
        row[1][1] = json!(encoding);
    }
    changed
}
fn frames(proof: &[u8]) -> Vec<std::ops::Range<usize>> {
    let mut frames = Vec::new();
    let mut offset = 40;
    while offset < proof.len() {
        let n = u64::from_le_bytes(proof[offset..offset + 8].try_into().unwrap()) as usize;
        offset += 8;
        frames.push(offset..offset + n);
        offset += n;
    }
    frames
}
pub fn check(
    deployment: &NativeDeployment,
    envelope: &Json,
    inputs: (&Json, &Json),
    proof: &[u8],
    family: &str,
    keys: &Keys,
    path: &Path,
) {
    let (p, v) = inputs;
    let codec = backend(keys);
    let bounds = Policy::default().ark_bounds();
    let authored = family == "authored";
    // Local opening state has no external input constructor. A variant wrapping
    // a PCS value is admitted only with explicit authority for that input.
    let nested = zkc_test_support::variants::logical(
        "PrivateCommitment",
        json!([["value", ["commitment:multilinear.kzg.bls12-381/0"]]]),
    );
    for logical in ["opening_state:multilinear.kzg.bls12-381/0", &nested] {
        let ty = zkc_runtime::interactive::PhysicalType::default_for(
            zkc_runtime::interactive::LogicalType::parse(logical).unwrap(),
        )
        .unwrap();
        let mut changed = envelope.clone();
        let mut candidate: Json = serde_json::from_str(envelope[4].as_str().unwrap()).unwrap();
        let producer = candidate[3]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|p| p[3] == "P")
            .unwrap();
        let inputs = producer[4].as_array_mut().unwrap();
        inputs.insert(
            inputs.len() - usize::from(!authored),
            json!(["unloadable", ty.spelling()]),
        );
        changed[6]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|p| p[0] == "P")
            .unwrap()[2]
            .as_array_mut()
            .unwrap()
            .push(json!(["9", logical]));
        let bytes = serde_json::to_vec(&candidate).unwrap();
        let admitted = zkc_runtime::interactive::admit_supplied(&bytes, &codec);
        admitted.expect("unused private input must pass ordinary typed admission");
        changed[4] = json!(String::from_utf8(bytes.clone()).unwrap());
        changed[5] = json!(digest(&bytes));
        let bytes = serde_json::to_vec(&changed).unwrap();
        if logical == nested {
            assert_eq!(
                NativeDeployment::admit(
                    &bytes,
                    &Sha256::digest(&bytes).into(),
                    authority(keys, authored)
                )
                .unwrap_err(),
                "native-proof-key-authority"
            );
            let mut authorized = authority(keys, authored);
            authorized.inputs.insert(9, if authored { 2 } else { 6 });
            NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), authorized).unwrap();
        } else {
            assert_eq!(
                NativeDeployment::admit(
                    &bytes,
                    &Sha256::digest(&bytes).into(),
                    authority(keys, authored)
                )
                .unwrap_err(),
                "native-proof-role-input-type"
            );
        }
    }

    let vk_port = if authored { 2 } else { 6 };
    let root_port = if authored { 3 } else { 7 };
    let claim_port = if authored { 5 } else { 3 };
    let mut changed = v.clone();
    changed[3] = json!("01");
    refuse(deployment, &changed, Some(proof), "proof-header");
    if authored {
        // An authored PCS proof does not cryptographically bind unrelated app
        // context. A rewrapped header is accepted: retain this explicit limit.
        accepted(
            deployment,
            &changed,
            Some(&rebind(envelope, &changed, proof)),
        );
    }
    let changed = public(
        v,
        claim_port,
        &codec
            .encode_native_value(&Value::Field(Scalar::from(999)))
            .unwrap(),
    );
    refuse(
        deployment,
        &changed,
        Some(&rebind(envelope, &changed, proof)),
        if authored {
            "rejected"
        } else {
            "Explicit(\"reject\")"
        },
    );
    if authored {
        let changed = public(
            v,
            4,
            &codec
                .encode_native_value(&Value::Field(Scalar::from(9)))
                .unwrap(),
        );
        refuse(
            deployment,
            &changed,
            Some(&rebind(envelope, &changed, proof)),
            "Explicit(\"reject\")",
        );
    }
    let other =
        zkc_arkworks::Table::from_logical_vec(vec![Scalar::from(11), Scalar::from(17)], &bounds)
            .unwrap();
    let other = keys.prover_key().commit(&other).unwrap();
    let changed = public(
        v,
        root_port,
        &codec
            .encode_native_value(&Value::Commitment(Arc::new(other.commitment().clone())))
            .unwrap(),
    );
    refuse(
        deployment,
        &changed,
        Some(&rebind(envelope, &changed, proof)),
        "Explicit(\"reject\")",
    );
    let stale = Keys::setup_for_development(1, &bounds).unwrap();
    let changed = public(v, vk_port, &stale.verifier_key().to_bytes(&bounds).unwrap());
    refuse(
        deployment,
        &changed,
        Some(&rebind(envelope, &changed, proof)),
        "key-mismatch",
    );
    let mut extra = v.clone();
    extra[2]
        .as_array_mut()
        .unwrap()
        .push(json!(["100", ["wire", "00"]]));
    refuse(deployment, &extra, Some(proof), "role-inputs");
    let mut key = p.clone();
    let row = key[2]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|r| r[1][0] == "prover_key_file")
        .unwrap();
    row[1][1][1] = json!("00".repeat(32));
    refuse(deployment, &key, None, "key-mismatch");
    let mut key = p.clone();
    let row = key[2]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|r| r[1][0] == "prover_key_file")
        .unwrap();
    row[1][1][0] = json!(path.with_extension("missing").to_str().unwrap());
    refuse(deployment, &key, None, "artifact-io");
    let ranges = frames(proof);
    let opening = ranges.iter().find(|r| proof[r.start + 5] == 7).unwrap();
    for (relative, expected) in [
        (0, "header"),
        (6, "header"),
        (6 + 17, "header"),
        (87, "group"),
    ] {
        let mut corrupt = proof.to_vec();
        if relative == 87 {
            corrupt[opening.start + relative..opening.end].fill(0xff);
        } else {
            corrupt[opening.start + relative] ^= 1;
        }
        refuse(deployment, v, Some(&corrupt), expected);
    }
    // Validly encoded but false quotient at each opening must reach pcs.check.
    // Altering only a proof preserves the claimed scalar and terminal formula.
    for opening in ranges.iter().filter(|r| proof[r.start + 5] == 7) {
        use ark_serialize::CanonicalSerialize;
        let mut identity = Vec::new();
        ark_bls12_381::G2Affine::identity()
            .serialize_compressed(&mut identity)
            .unwrap();
        let mut changed = proof.to_vec();
        assert_eq!(opening.end - opening.start, 183); // one variable
        changed[opening.start + 87..opening.end].copy_from_slice(&identity);
        refuse(deployment, v, Some(&changed), "Explicit(\"reject\")");
    }
    let scalar = ranges
        .iter()
        .rev()
        .find(|r| proof[r.start + 5] == 1)
        .unwrap();
    let mut changed = proof.to_vec();
    changed[scalar.clone()].copy_from_slice(
        &codec
            .encode_native_value(&Value::Field(Scalar::from(999)))
            .unwrap(),
    );
    refuse(deployment, v, Some(&changed), "Explicit(\"reject\")");
    let mut malformed = proof.to_vec();
    malformed[scalar.start + 6..scalar.end].fill(0xff);
    refuse(deployment, v, Some(&malformed), "scalar");
    let mut long = proof.to_vec();
    long.push(0);
    refuse(deployment, v, Some(&long), "trailing");
    let short = &proof[..proof.len() - 1];
    refuse(deployment, v, Some(short), "proof-truncated");
    if !authored {
        let mut wrong_n = public(v, 0, &codec.encode_native_value(&Value::Index(0)).unwrap());
        // The original arity message is 1; check fails before any round.
        refuse(
            deployment,
            &wrong_n,
            Some(&rebind(envelope, &wrong_n, proof)),
            "Explicit(\"reject\")",
        );
        // Invalid VK with zero arity is refused during invocation admission.
        let mut vk = keys.verifier_key().to_bytes(&bounds).unwrap();
        vk[9..17].fill(0);
        wrong_n = public(v, vk_port, &vk);
        refuse(deployment, &wrong_n, Some(proof), "positive-arity-required");
    }
    // Original backing survives restriction and repeated opening through aliases.
    let table =
        zkc_arkworks::Table::from_logical_vec(vec![Scalar::from(1), Scalar::from(2)], &bounds)
            .unwrap();
    let state = keys.prover_key().commit(&table).unwrap();
    let alias = state.clone();
    let _scratch = table.restrict_first(Scalar::from(7)).unwrap();
    let (a, pa) = state.open(&[Scalar::from(7)]).unwrap();
    let (b, pb) = alias.open(&[Scalar::from(7)]).unwrap();
    assert_eq!(a, b);
    assert_eq!(pa.to_bytes(&bounds).unwrap(), pb.to_bytes(&bounds).unwrap());
    assert_eq!(
        state.original().logical_values().unwrap(),
        vec![Scalar::from(1), Scalar::from(2)]
    );
    assert!(!zkc_backends::has_native_wire(
        &Value::OpeningState(Arc::new(state)).physical_type()
    ));
}
