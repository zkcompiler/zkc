//! Source setup slots drive ordinary PCS kernels and both common native Hosts.
use super::interface::alter;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, path::Path, sync::Arc};
use zkc_arkworks::{Keys, Table};
use zkc_backends::{Policy, Scalar, Value as Native};
use zkc_tools::{
    artifact::native::{InputValue, NativeCapacity, ProverMaterial},
    entry::{
        AttemptOptions, BindingPolicy, NamedValues, Package, ProofEntry, ProofOptions,
        ProofRequest, RoleInputs, RunEntry, RunRequest, SetupAuthority, Value,
    },
    protocol::run::HostLimits,
};
fn package(directory: &Path, entry: &str) -> Package {
    let bytes = std::fs::read(directory.join(format!("pcs-setup-{entry}.entry"))).unwrap();
    Package::capture(&bytes, &Sha256::digest(&bytes).into(), Package::MAX_BYTES).unwrap()
}
fn point() -> Value {
    Native::Vector(vec![Scalar::from(7)].into()).into()
}
fn role(material: &[ProverMaterial], claim: Value, producing: bool) -> RoleInputs {
    let mut inputs = NamedValues::from([("point".into(), point()), ("claim".into(), claim)]);
    if producing {
        for (i, key) in material.iter().enumerate() {
            inputs.insert(format!("pk{i}"), InputValue::ProverKey(key.clone()).into());
            inputs.insert(
                format!("data{i}"),
                Native::Vector(vec![Scalar::from(3 + i as u64), Scalar::from(9)].into()).into(),
            );
        }
    }
    RoleInputs {
        inputs,
        services: BTreeMap::new(),
    }
}
fn accepted(values: &NamedValues) {
    assert!(matches!(
        &values["accepted"],
        Value::Leaf(InputValue::Native(value)) if matches!(value.as_ref(), Native::Bool(true))
    ));
}
pub(super) fn run(directory: &Path) {
    let bounds = Policy::default().ark_bounds();
    let keys: Vec<_> = (0..2)
        .map(|_| Keys::setup_for_development(1, &bounds).unwrap())
        .collect();
    let material: Vec<_> = keys
        .iter()
        .map(|key| {
            ProverMaterial::from_bytes(
                &key.prover_key().to_bytes(&bounds).unwrap(),
                key.prover_key().material_fingerprint(),
                key.verifier_key(),
                NativeCapacity::default(),
            )
            .unwrap()
        })
        .collect();
    let table = Table::from_logical_vec(vec![Scalar::from(3), Scalar::from(9)], &bounds).unwrap();
    let commitments: Vec<_> = keys
        .iter()
        .map(|key| key.prover_key().commit(&table).unwrap())
        .collect();
    let claim = |index: usize| {
        Value::Record(
            [
                (
                    "c".into(),
                    Native::Commitment(Arc::new(commitments[index].commitment().clone())).into(),
                ),
                ("tag".into(), Native::Bool(true).into()),
            ]
            .into(),
        )
    };
    let pins = || SetupAuthority {
        keys: ["first", "second"]
            .into_iter()
            .zip(&keys)
            .map(|(name, key)| (name.to_owned(), key.verifier_key().metadata().key_id()))
            .collect(),
    };
    let setups = || {
        ["first", "second"]
            .into_iter()
            .zip(&keys)
            .map(|(name, key)| {
                (
                    name.to_owned(),
                    key.verifier_key().to_bytes(&bounds).unwrap(),
                )
            })
            .collect()
    };
    let publication = package(directory, "Run");
    let host = RunEntry::admit(publication.clone(), HostLimits::default(), pins()).unwrap();
    let run_request = || RunRequest {
        session: "source_setups".into(),
        roles: [
            ("P".into(), role(&material, claim(0), true)),
            ("V".into(), role(&material, claim(0), false)),
        ]
        .into(),
        setups: setups(),
    };
    let report = host.prepare(run_request()).unwrap().execute();
    assert!(
        report.native.failure.is_none(),
        "{:?}",
        report.native.failure
    );
    assert!(report.native.cleanup_errors.is_empty());
    accepted(&report.outputs.unwrap()["V"]);
    assert_eq!(
        RunEntry::admit(
            publication.clone(),
            HostLimits::default(),
            SetupAuthority::default()
        )
        .err()
        .unwrap(),
        "entry-setup-authority"
    );
    let mut wrong = run_request();
    wrong.roles.get_mut("P").unwrap().inputs.insert(
        "pk0".into(),
        InputValue::ProverKey(material[1].clone()).into(),
    );
    assert_eq!(
        host.prepare(wrong).err().unwrap(),
        "native-proof-input-setup"
    );
    let mut extra = run_request();
    extra
        .roles
        .get_mut("V")
        .unwrap()
        .inputs
        .insert("vk0".into(), InputValue::VerifierKey.into());
    assert_eq!(host.prepare(extra).err().unwrap(), "entry-input-names");
    let mut missing = run_request();
    missing.setups.remove("second");
    assert_eq!(host.prepare(missing).err().unwrap(), "entry-setup-material");
    let mut supplied = run_request();
    supplied.setups.insert(
        "first".into(),
        keys[1].verifier_key().to_bytes(&bounds).unwrap(),
    );
    assert_eq!(host.prepare(supplied).err().unwrap(), "key-mismatch");
    let mut wrong_claim = run_request();
    for role in wrong_claim.roles.values_mut() {
        role.inputs.insert("claim".into(), claim(1));
    }
    assert_eq!(
        host.prepare(wrong_claim).err().unwrap(),
        "native-proof-input-setup"
    );
    let changed = alter(&publication, |_, interface| {
        interface["setups"][0]["name"] = "third".into();
    });
    assert_eq!(
        RunEntry::admit(changed, HostLimits::default(), pins())
            .err()
            .unwrap(),
        "entry-setup-authority"
    );
    let publication = package(directory, "Prove");
    let options = ProofOptions {
        binding: BindingPolicy::AllowHeaderOnly,
        ..Default::default()
    };
    let prover = ProofEntry::admit(publication.clone(), options, pins()).unwrap();
    let verifier = ProofEntry::admit(publication, options, pins()).unwrap();
    let request = |producing| ProofRequest {
        public: [("point".into(), point()), ("claim".into(), claim(0))].into(),
        inputs: role(&material, claim(0), producing),
        context: vec![1, 2, 3],
        transcript_budget: Some(0),
        setups: setups(),
    };
    // Reuse immutable material across independent complete invocations.
    let mut unloaded = request(true);
    unloaded.inputs.inputs.insert(
        "pk0".into(),
        InputValue::ProverKeyFile {
            path: "/nonexistent/zkc-attempt-key".into(),
            fingerprint: [0; 32],
        }
        .into(),
    );
    assert_eq!(
        prover
            .prove_attempts(
                unloaded,
                AttemptOptions {
                    count: 0,
                    ..Default::default()
                }
            )
            .err()
            .unwrap(),
        "native-attempt-limits"
    );
    for _ in 0..2 {
        let produced = prover.prove(request(true)).unwrap();
        assert!(produced.is_success(), "{:?}", produced.native.outcome);
        let proof = produced.native.outcome.unwrap();
        let checked = verifier.verify(request(false), &proof).unwrap();
        assert!(checked.is_success(), "{:?}", checked.native.outcome);
        accepted(checked.outputs.as_ref().unwrap());
        let mut changed = request(false);
        changed.public.insert(
            "point".into(),
            Native::Vector(vec![Scalar::from(8)].into()).into(),
        );
        // The role and separately supplied public value cannot disagree.
        assert_eq!(
            verifier.verify(changed, &proof).err().unwrap(),
            "native-proof-shared-public-input"
        );
        let mut corrupted = proof;
        let last = corrupted.len() - 1;
        corrupted[last] ^= 1;
        assert!(
            !verifier
                .verify(request(false), &corrupted)
                .is_ok_and(|r| r.is_success())
        );
    }
    for producing in [true, false] {
        let mut wrong = request(producing);
        wrong.public.insert("claim".into(), claim(1));
        wrong.inputs.inputs.insert("claim".into(), claim(1));
        let result = if producing {
            prover.prove(wrong)
        } else {
            verifier.verify(wrong, &[])
        };
        assert_eq!(result.err().unwrap(), "native-proof-input-setup");
    }
    let mut wrong = request(true);
    wrong.inputs.inputs.insert(
        "pk0".into(),
        InputValue::ProverKey(material[1].clone()).into(),
    );
    assert_eq!(
        prover.prove(wrong).err().unwrap(),
        "native-proof-input-setup"
    );
    let mut wrong_key = request(false);
    wrong_key.setups.insert(
        "first".into(),
        keys[1].verifier_key().to_bytes(&bounds).unwrap(),
    );
    assert_eq!(
        verifier.verify(wrong_key, &[]).err().unwrap(),
        "key-mismatch"
    );
    let mut extra = request(false);
    extra
        .public
        .insert("vk0".into(), InputValue::VerifierKey.into());
    assert_eq!(
        verifier.verify(extra, &[]).err().unwrap(),
        "entry-input-names"
    );
    let mut limited = options;
    limited.capacity.wire_bytes = 0;
    let limited = ProofEntry::admit(package(directory, "Prove"), limited, pins()).unwrap();
    assert_eq!(
        limited.prove(request(true)).err().unwrap(),
        "native-capacity-wire"
    );
}
