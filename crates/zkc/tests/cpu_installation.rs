//! SDK boundaries use the selected installation, including auxiliary codecs.
use serde_json::json;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use zkc::{
    entry::{self, outputs},
    execution::{Capacity, CpuExecution, CpuInstallation, InputValue, PreparedData, providers},
    run::{HostLimits, RoleInputs, RunHost, RunInputs, SetupAuthority},
};
use zkc_cpu::{Sequence, Value, Variant};
use zkc_runtime::{
    host::joint::Outcome,
    vm::{LogicalType, PhysicalType, Value as _},
};

fn plonky3() -> CpuInstallation {
    CpuInstallation::builder()
        .include(providers::Plonky3)
        .finish()
        .unwrap()
}
fn physical(name: &str) -> PhysicalType {
    PhysicalType::default_for(LogicalType::parse(name).unwrap()).unwrap()
}
fn echo(ty: &PhysicalType, installation: CpuInstallation) -> Result<RunHost, String> {
    let ty = ty.spelling();
    let program = json!([
        "zkc.program/0",
        [],
        [],
        [[
            "participant",
            "echo",
            "root",
            "P",
            [["x", ty]],
            [ty],
            [["return", ["x"]]],
            []
        ]],
        [["entry", "main", [["P", "echo"]]]]
    ]);
    let bytes = json!({"format":"zkc.run/0", "candidate":program.to_string(), "entry":"main", "roles":["P"],
        "steps":[{"role":0,"instruction":0,"anchor":null}]}).to_string().into_bytes();
    RunHost::admit_with_cpu(
        &bytes,
        &Sha256::digest(&bytes).into(),
        HostLimits::default().with_installation(installation),
        SetupAuthority::default(),
        CpuExecution::serial().unwrap(),
    )
}
#[test]
fn standard_and_plonky3_installations_keep_supported_typed_run_behavior() {
    for installation in [CpuInstallation::standard().unwrap(), plonky3()] {
        for value in [
            Value::Bool(true),
            Value::KoalaBearField(zkc_cpu::KoalaBear::new(7)),
        ] {
            let host = echo(&value.physical_type(), installation.clone()).unwrap();
            let report = host
                .prepare_typed(&RunInputs {
                    session: "session".into(),
                    roles: vec![RoleInputs {
                        role: "P".into(),
                        inputs: vec![value.into()],
                        services: vec![],
                    }],
                    setups: BTreeMap::new(),
                })
                .unwrap()
                .execute();
            assert!(matches!(
                report.execution.as_ref().unwrap().outcome,
                Outcome::Completed
            ));
            assert!(report.failure.is_none() && report.cleanup_errors.is_empty());
            for (_, backend) in &report.execution.as_ref().unwrap().backends {
                assert_eq!(
                    backend.installation().supports_setup(),
                    installation.supports_setup()
                );
            }
        }
    }
    for ty in [
        "field:bls12-381.fr",
        "field:bn254.fr",
        "field:ristretto255.scalar",
        "sequence<field:bls12-381.fr>",
    ] {
        let ty = physical(ty);
        assert!(echo(&ty, CpuInstallation::standard().unwrap()).is_ok());
        assert_eq!(
            echo(&ty, plonky3()).err().unwrap(),
            "run-Candidate(\"Representation: installation-type\")",
            "{}",
            ty.spelling()
        );
    }
}
fn omitted_values() -> Vec<Value> {
    let variant = zkc_test_support::variants::logical(
        "Mixed",
        json!([["empty", []], ["hidden", ["field:bls12-381.fr"]]]),
    );
    vec![
        Value::Field(zkc_cpu::Scalar::from(7)),
        Value::Bn254Field(zkc_cpu::Bn254Scalar::from(7)),
        Value::BlstField(zkc_kernels::blst::bls12_381::Scalar::from(7u64)),
        Value::HaloField(zkc_kernels::halo2curves::bn254::Scalar::from(7u64)),
        Value::RistrettoField(zkc_cpu::RistrettoScalar::from(7u64)),
        // An empty aggregate and inactive variant still retain their full type.
        Value::Sequence(
            Sequence::new(
                physical("sequence<field:bls12-381.fr>"),
                vec![],
                &Default::default(),
            )
            .unwrap(),
        ),
        Value::Variant(Variant::new(physical(&variant), 0, vec![]).unwrap()),
    ]
}
#[test]
fn auxiliary_preparation_cannot_reauthorize_omitted_or_inactive_providers() {
    let capacity = Capacity::default();
    for value in omitted_values() {
        let prepared = PreparedData::from_value(value.clone(), capacity).unwrap();
        assert!(
            PreparedData::from_value_with_installation(
                value,
                capacity,
                CpuExecution::serial().unwrap(),
                plonky3()
            )
            .is_err()
        );
        assert!(
            PreparedData::from_wire_with_installation(
                prepared.physical_type().clone(),
                prepared.canonical_bytes().to_vec(),
                capacity,
                CpuExecution::serial().unwrap(),
                plonky3()
            )
            .is_err()
        );
    }
}
#[test]
fn all_auxiliary_output_encoders_retain_the_selected_installation() {
    let capacity = Capacity::default();
    for value in omitted_values() {
        let value: entry::Value = value.into();
        assert!(outputs::function_output(&value, capacity, Default::default()).is_ok());
        assert_eq!(
            outputs::function_output_with_installation(
                &value,
                capacity,
                Default::default(),
                CpuExecution::serial().unwrap(),
                plonky3()
            )
            .unwrap_err(),
            "entry-output-encoding"
        );
        let values = BTreeMap::from([("value".into(), value)]);
        assert!(outputs::proof_outputs(&values, capacity, Default::default()).is_ok());
        assert_eq!(
            outputs::proof_outputs_with_installation(
                &values,
                capacity,
                Default::default(),
                CpuExecution::serial().unwrap(),
                plonky3()
            )
            .unwrap_err(),
            "entry-output-encoding"
        );
        let roles = BTreeMap::from([("P".into(), values)]);
        assert!(outputs::run_outputs(&roles, capacity, Default::default()).is_ok());
        assert_eq!(
            outputs::run_outputs_with_installation(
                &roles,
                capacity,
                Default::default(),
                CpuExecution::serial().unwrap(),
                plonky3()
            )
            .unwrap_err(),
            "entry-output-encoding"
        );
    }
}
#[test]
fn prepared_standard_data_is_revalidated_by_selected_typed_requests() {
    let host = echo(&physical("field:koala-bear"), plonky3()).unwrap();
    let value =
        PreparedData::from_value(Value::Field(zkc_cpu::Scalar::from(7)), Capacity::default())
            .unwrap();
    let request = RunInputs {
        session: "session".into(),
        roles: vec![RoleInputs {
            role: "P".into(),
            inputs: vec![InputValue::Prepared(value)],
            services: vec![],
        }],
        setups: BTreeMap::new(),
    };
    assert_eq!(
        host.prepare_typed(&request).err().unwrap(),
        "native-input-type"
    );
}

#[test]
fn selected_file_result_encoder_and_setup_import_do_not_restore_default_support() {
    let capacity = Capacity::default();
    #[cfg(feature = "files")]
    {
        let bindings =
            entry::files::Invocations::load_with_installation(None, capacity, true, plonky3())
                .unwrap();
        let (_, _, encoder) = bindings.into_parts();
        let value = Value::Field(zkc_cpu::Scalar::from(7)).into();
        assert_eq!(encoder.encode(&value).unwrap_err(), "entry-output-encoding");
    }
    let authority = entry::SetupAuthority {
        keys: BTreeMap::from([("key".into(), [0; 32])]),
    };
    let material = BTreeMap::from([("key".into(), vec![0])]);
    assert_eq!(
        outputs::output_setups_with_installation(&material, &authority, capacity, &plonky3())
            .unwrap_err(),
        "cpu-installation-setup"
    );
    // Existing material inventory and capacity errors retain their precedence.
    assert_eq!(
        outputs::output_setups_with_installation(
            &BTreeMap::new(),
            &authority,
            capacity,
            &plonky3()
        )
        .unwrap_err(),
        "entry-setup-material"
    );
}

#[test]
fn prepared_prover_material_rechecks_selected_setup_support() {
    use zkc::execution::ProverMaterial;
    let capacity = Capacity::default();
    let bounds = zkc_cpu::Policy::default().ark_bounds();
    let keys = zkc_kernels::arkworks::bls12_381::Keys::setup_with_rng(
        1,
        &mut ark_std::rand::thread_rng(),
        &bounds,
    )
    .unwrap();
    let bytes = keys.prover_key().to_bytes(&bounds).unwrap();
    let fingerprint = keys.prover_key().material_fingerprint();
    assert!(ProverMaterial::from_bytes(&bytes, fingerprint, keys.verifier_key(), capacity).is_ok());
    assert_eq!(
        ProverMaterial::from_bytes_with_installation(
            &bytes,
            fingerprint,
            keys.verifier_key(),
            capacity,
            &plonky3()
        )
        .unwrap_err(),
        "cpu-installation-setup"
    );
    let mut tight = capacity;
    tight.wire_bytes = bytes.len() - 1;
    assert_eq!(
        ProverMaterial::from_bytes_with_installation(
            &bytes,
            fingerprint,
            keys.verifier_key(),
            tight,
            &plonky3()
        )
        .unwrap_err(),
        "native-capacity-wire"
    );
}
