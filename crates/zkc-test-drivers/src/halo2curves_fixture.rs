//! Execute unmodified compiler-emitted BN254 provider programs.
use serde_json::{Value as Json, json};
use zkc_cpu::{
    CpuBackend, Domain, EntryPolicy, Policy, Value, cpu_contracts, cpu_contracts_with_policy,
};
use zkc_kernels::arkworks::bn254 as ark;
use zkc_runtime::{
    interpreter::Runner,
    vm::{Action, ExecutionPolicy, Program, Value as _},
};

pub(super) fn run(bytes: &[u8], mode: &str) {
    let bulk = mode.starts_with("bulk-");
    assert!(matches!(
        mode,
        "canonical"
            | "resident"
            | "mixed"
            | "g2-canonical"
            | "g2-resident"
            | "bulk-canonical"
            | "bulk-resident"
    ));
    if bulk {
        assert!(Program::decode(bytes, cpu_contracts()).is_err());
    }
    let contracts = cpu_contracts_with_policy(ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: bulk,
    });
    let program = Program::decode(bytes, &contracts).unwrap();
    let artifact: Json = serde_json::from_slice(bytes).unwrap();
    let participant = &artifact[3][0];
    let entry = artifact[4][0][1].as_str().unwrap();
    let role = participant[3].as_str().unwrap();
    let ports = participant[4].as_array().unwrap();
    let output = contracts
        .physical_type(participant[5][0].as_str().unwrap())
        .unwrap();
    let mut results = Vec::new();
    for scalar in [
        ark::Scalar::from(0),
        ark::Scalar::from(1),
        ark::Scalar::from(3),
        -ark::Scalar::from(6),
    ] {
        let native = CpuBackend::new(
            Policy::default(),
            EntryPolicy::new(Domain::new(role, "halo2curves-fixture", entry, None), None),
            Default::default(),
        )
        .unwrap()
        .with_contracts(contracts.clone())
        .unwrap();
        program.check_installation(&native).unwrap();
        let (ordinary, expected) = if bulk {
            let scalars = vec![scalar, ark::Scalar::from(0), ark::Scalar::from(2)];
            let a = ark::G1::generator();
            let b = ark::G2::generator();
            let coefficient = (scalar + ark::Scalar::from(6)) * ark::Scalar::from(2);
            (
                vec![
                    Value::Bn254Vector(scalars.into()),
                    Value::Bn254G1Vector(vec![a, a.neg(), a.scale(ark::Scalar::from(3))].into()),
                    Value::Bn254G2Vector(vec![b, b.neg(), b.scale(ark::Scalar::from(3))].into()),
                ],
                Value::Bool(
                    ark::pairing_check(&[a.scale(coefficient)], &[b.scale(coefficient)]).unwrap(),
                ),
            )
        } else {
            let doubled = scalar + scalar;
            let factor = doubled * doubled;
            if mode.starts_with("g2-") {
                let point = ark::G2::generator();
                (
                    vec![Value::Bn254G2(point.into()), Value::Bn254Field(scalar)],
                    Value::Bn254G2((point.scale(factor).neg()).into()),
                )
            } else {
                let point = ark::G1::generator();
                (
                    vec![Value::Bn254G1(point), Value::Bn254Field(scalar)],
                    Value::Bn254G1(point.scale(factor).neg()),
                )
            }
        };
        assert_eq!(ports.len(), ordinary.len());
        let inputs = ordinary
            .iter()
            .zip(ports)
            .map(|(value, port)| {
                let ty = contracts.physical_type(port[1].as_str().unwrap()).unwrap();
                native
                    .decode_native_value(&ty, &native.encode_native_value(value).unwrap())
                    .unwrap()
            })
            .collect();
        let expected = native.encode_native_value(&expected).unwrap();
        let mut runner = Runner::new(&program, entry, role, "halo2curves-fixture", native, inputs)
            .map_err(|failure| failure.error)
            .unwrap();
        let returned = loop {
            match runner.poll() {
                Action::Local(action) => runner.execute_local(&action.cut).unwrap(),
                Action::Returned(values) => break values,
                other => panic!("compiler BN254 execution: {other:?}"),
            }
        };
        assert_eq!(returned.len(), 1);
        assert_eq!(returned[0].physical_type(), output);
        let canonical = runner.backend().encode_native_value(&returned[0]).unwrap();
        assert_eq!(canonical, expected);
        results.push(zkc_test_support::hex(&canonical));
        let usage = runner.usage();
        assert!(matches!(runner.poll(), Action::Returned(_)));
        assert_eq!(runner.usage(), usage);
        assert_eq!(runner.backend().active_frames(), 0);
    }
    println!(
        "{}",
        json!({"mode": mode, "returned": results.len(), "canonical": results})
    );
}
