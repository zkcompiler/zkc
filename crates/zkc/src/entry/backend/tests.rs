use super::*;
use serde_json::json;
use sha2::{Digest, Sha256};
use zkc_runtime::{host::wire::WireError, vm::*};

#[derive(Clone, Debug)]
struct Number {
    value: u32,
    ty: PhysicalType,
}
impl zkc_runtime::vm::Value for Number {
    fn physical_type(&self) -> PhysicalType {
        self.ty.clone()
    }
    fn retained_bytes(&self) -> usize {
        64
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        Ok(())
    }
}
struct Add {
    signature: BoundSignature,
    id: ImplementationId,
}
impl InstalledOperation for Add {
    fn signature(&self) -> &BoundSignature {
        &self.signature
    }
    fn implementation_id(&self) -> Option<ImplementationId> {
        Some(self.id)
    }
    fn requirements(&self) -> ImplementationRequirements {
        ImplementationRequirements::default()
    }
}
struct Arithmetic {
    ty: PhysicalType,
    id: ImplementationId,
    frames: usize,
    applications: usize,
}
impl Backend for Arithmetic {
    type Value = Number;
    type Operation = Add;
    type Call = ();
    type Checkpoint = ();
    fn validate_value(&self, value: &Number) -> Result<(), BackendError> {
        if value.ty == self.ty && value.value < 2_130_706_433 {
            Ok(())
        } else {
            Err(BackendError::new("number"))
        }
    }
    fn prepare_binding(&self, b: &OperationBinding) -> Option<Add> {
        (b.contract == "field.add"
            && b.arguments == ["koala-bear"]
            && b.implementation == "test/field.add")
            .then(|| Add {
                signature: OperationSignature {
                    inputs: vec![self.ty.clone(), self.ty.clone()],
                    outputs: vec![self.ty.clone()],
                    attributes: AttributeRule::None,
                },
                id: self.id,
            })
    }
    fn enter_frame(&mut self, _: &Frame, args: &[Number]) -> Result<(), BackendError> {
        self.frames += 1;
        args.iter().try_for_each(|v| self.validate_value(v))
    }
    fn leave_frame(
        &mut self,
        _: &Frame,
        _: FrameExit,
        values: &[Number],
    ) -> Result<(), BackendError> {
        values.iter().try_for_each(|v| self.validate_value(v))
    }
    fn apply(
        &mut self,
        _: &Add,
        _: &Invocation<'_>,
        args: &[Number],
    ) -> Result<Vec<Number>, BackendError> {
        self.applications += 1;
        let [a, b] = args else {
            return Err(BackendError::new("operands"));
        };
        Ok(vec![Number {
            value: ((u64::from(a.value) + u64::from(b.value)) % 2_130_706_433) as u32,
            ty: self.ty.clone(),
        }])
    }
}
impl WireBackend for Arithmetic {
    fn supports_wire(&self, ty: &PhysicalType) -> bool {
        *ty == self.ty
    }
    fn fixed_wire_size(&self, ty: &PhysicalType) -> Option<usize> {
        self.supports_wire(ty).then_some(4)
    }
    fn encoding_bound(&self, value: &Number) -> Result<usize, WireError> {
        self.validate_value(value).map_err(WireError::Backend)?;
        Ok(4)
    }
    fn decoding_bound(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<usize, WireError> {
        if !self.supports_wire(ty) {
            return Err(WireError::Limit);
        }
        if bytes.len() != 4 {
            return Err(WireError::Invalid(DecodeReason::Length));
        }
        Ok(64)
    }
    fn encode_wire(&self, value: &Number) -> Result<Vec<u8>, WireError> {
        self.encoding_bound(value)?;
        Ok(value.value.to_le_bytes().to_vec())
    }
    fn decode_wire(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<Number, WireError> {
        self.decoding_bound(ty, bytes)?;
        let value = u32::from_le_bytes(
            bytes
                .try_into()
                .map_err(|_| WireError::Invalid(DecodeReason::Length))?,
        );
        if value >= 2_130_706_433 {
            return Err(WireError::Invalid(DecodeReason::Scalar));
        }
        Ok(Number {
            value,
            ty: ty.clone(),
        })
    }
}

fn installed() -> (Contracts, Arithmetic) {
    let mut builder = ContractsBuilder::empty();
    let ty = builder
        .add_representation(
            "test.koala/0",
            LogicalType::parse("field:koala-bear").unwrap(),
        )
        .unwrap();
    builder
        .add_wire_permission(ty.clone(), WireCodec::Native)
        .unwrap();
    let declaration = OperationBinding {
        contract: "field.add".into(),
        arguments: vec!["koala-bear".into()],
        implementation: "test/field.add".into(),
        physical_arguments: Vec::new(),
    };
    let signature = OperationSignature {
        inputs: vec![ty.clone(), ty.clone()],
        outputs: vec![ty.clone()],
        attributes: AttributeRule::None,
    };
    let id = builder
        .add_implementation(
            declaration,
            signature,
            ImplementationRequirements::default(),
        )
        .unwrap();
    (
        builder.finish(ExecutionPolicy {
            allow_unspecified_timing: true,
            allow_variable_time: false,
        }),
        Arithmetic {
            ty,
            id,
            frames: 0,
            applications: 0,
        },
    )
}
fn digest(value: &str) -> String {
    crate::io::bytes::hex(&Sha256::digest(value.as_bytes()))
}
fn package(ty: &PhysicalType, constructible: bool) -> Package {
    let field = json!({"kind":"field","identity":digest("F"),"type":"F","generated":null,"custody":0,"sealed":false,"roles":[],"element":null,"constructible":constructible,
        "permissions":["Copy","Drop"],"fields":[],"alternatives":[],"leaves":["field:koala-bear"]});
    let port = |name: &str, index: u32| json!({"name":name,"index":index,"native":[index],"placement":{"kind":"data","roles":[0]},"components":[{"path":[],"leaf":0,"role":0,"facet":"data","native":index}],"type":"F","schema":field});
    let interface = json!({"format":"zkc.language-interface/0","setups":[],"capture":digest("capture"),"original":digest("source"),"toolchain":"test",
        "entry":"example::Main","protocol":"example_Add","protocols":[{"symbol":"example_Add","roles":["P"],
        "inputs":[port("a",0),port("b",1)],"outputs":[port("sum",0)],"services":[],"common_input_requirements":[],"clauses":[]}],"relations":[],"job":{"kind":"run"}});
    let t = ty.spelling();
    let candidate = json!([
        "zkc.program/0",
        [["add", "field.add", ["koala-bear"], "test/field.add", []]],
        [[
            "function",
            "compute",
            [["a", t], ["b", t]],
            [t],
            [
                ["op", "sum", "add", [], ["a", "b"], ["c"]],
                ["return", ["c"]]
            ],
            ["f", []]
        ]],
        [[
            "participant",
            "p",
            "example_Add",
            "role00000000",
            [["a", t], ["b", t]],
            [t],
            [
                ["local", "sum", "compute", ["a", "b"], ["c"]],
                ["return", ["c"]]
            ],
            []
        ]],
        [["entry", "example_Add", [["role00000000", "p"]]]]
    ])
    .to_string();
    let artifact = json!({"format":"zkc.run/0","candidate":candidate,"entry":"example_Add","roles":["role00000000"],"steps":[
        {"role":0,"instruction":0,"anchor":0},{"role":0,"instruction":1,"anchor":null}]}).to_string();
    let bytes = json!({"format":"zkc.entry/0","original":"source","interface":interface.to_string(),"artifact":artifact,"assets":[],
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true,"oracle_realization": crate::entry::OracleSelection::default()}}).to_string();
    Package::capture(
        bytes.as_bytes(),
        &Sha256::digest(bytes.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap()
}
#[test]
fn independent_backend_executes_authenticated_source_application() {
    let (contracts, backend) = installed();
    let package = package(&backend.ty, true);
    let entry = BackendRun::admit(
        package,
        &contracts,
        &backend,
        joint::BundleLimits::default(),
    )
    .unwrap();
    let values = [20, 22]
        .map(|value| Number {
            value,
            ty: backend.ty.clone(),
        })
        .to_vec();
    let report = entry
        .execute(
            "sdk",
            vec![joint::RoleInput {
                role: "role00000000".into(),
                backend,
                values,
            }],
            joint::RunLimits::default(),
            &mut joint::NoHooks,
        )
        .unwrap();
    assert_eq!(report.outcome, joint::Outcome::Completed);
    assert_eq!(report.roles[0].outputs[0].value, 42);
}
#[test]
fn typed_backend_values_do_not_grant_source_constructor_authority() {
    let (contracts, backend) = installed();
    let package = package(&backend.ty, false);
    assert!(
        BackendRun::admit(
            package,
            &contracts,
            &backend,
            joint::BundleLimits::default()
        )
        .is_err()
    );
}
#[test]
fn another_contract_catalog_cannot_supply_an_installed_handle() {
    let (contracts, backend) = installed();
    let (_, other) = installed();
    let package = package(&backend.ty, true);
    assert!(
        BackendRun::admit(package, &contracts, &other, joint::BundleLimits::default()).is_err()
    );
}

fn change_package(package: &Package, change: impl FnOnce(&mut serde_json::Value)) -> Package {
    let mut frame: serde_json::Value = serde_json::from_slice(package.bytes()).unwrap();
    change(&mut frame);
    let bytes = frame.to_string();
    Package::capture(
        bytes.as_bytes(),
        &Sha256::digest(bytes.as_bytes()).into(),
        Package::MAX_BYTES,
    )
    .unwrap()
}

fn paired_run() -> (BackendRun, Arithmetic) {
    let (contracts, backend) = installed();
    let package = change_package(&package(&backend.ty, true), |frame| {
        let mut interface: serde_json::Value =
            serde_json::from_str(frame["interface"].as_str().unwrap()).unwrap();
        let protocol = &mut interface["protocols"][0];
        protocol["roles"] = json!(["P", "V"]);
        protocol["common_input_requirements"] = json!([{"components":[
            {"input":0,"role":"P","path":[]},{"input":0,"role":"V","path":[]}
        ],"observation":{"kind":"value"}}]);
        for kind in ["inputs", "outputs"] {
            for port in protocol[kind].as_array_mut().unwrap() {
                port["placement"]["roles"] = json!([0, 1]);
                let mut component = port["components"][0].clone();
                component["role"] = json!(1);
                port["components"].as_array_mut().unwrap().push(component);
            }
        }
        frame["interface"] = json!(interface.to_string());
        let mut artifact: serde_json::Value =
            serde_json::from_str(frame["artifact"].as_str().unwrap()).unwrap();
        let mut candidate: serde_json::Value =
            serde_json::from_str(artifact["candidate"].as_str().unwrap()).unwrap();
        let mut verifier = candidate[3][0].clone();
        verifier[1] = json!("v");
        verifier[3] = json!("role00000001");
        candidate[3].as_array_mut().unwrap().push(verifier);
        candidate[4][0][2]
            .as_array_mut()
            .unwrap()
            .push(json!(["role00000001", "v"]));
        artifact["candidate"] = json!(candidate.to_string());
        artifact["roles"] = json!(["role00000000", "role00000001"]);
        artifact["steps"] = json!([
            {"role":0,"instruction":0,"anchor":0}, {"role":1,"instruction":0,"anchor":1},
            {"role":0,"instruction":1,"anchor":null}, {"role":1,"instruction":1,"anchor":null}
        ]);
        frame["artifact"] = json!(artifact.to_string());
    });
    (
        BackendRun::admit(
            package,
            &contracts,
            &backend,
            joint::BundleLimits::default(),
        )
        .unwrap(),
        backend,
    )
}

fn trusted_context(run: &BackendRun, backend: &Arithmetic) -> (Vec<u8>, [u8; 32]) {
    // Hand-authored fixture authority only. These hashes identify the fixture;
    // computing them here does not authenticate an external application's source.
    let components = ["role00000000", "role00000001"]
        .map(|role| {
            let input = run
                .interface()
                .native_input_position(if role.ends_with('0') { "P" } else { "V" }, 0)
                .unwrap();
            InputComponent {
                role: role.into(),
                input,
                path: vec![],
            }
        })
        .to_vec();
    let required = vec![InputRequirement {
        components,
        ty: backend.ty.clone(),
        observation: Observation::Value,
    }];
    assert_eq!(run.common_input_requirements().unwrap(), required);
    let bytes = zkc_format::logical::encode_tree(&json!([
        "zkc.input-bindings/0",
        digest(std::str::from_utf8(run.bundle().admitted().bytes()).unwrap()),
        run.bundle().entry(),
        [[
            [["role00000000", "0", []], ["role00000001", "0", []]],
            backend.ty.spelling(),
            "value",
            ["active", "14000000"]
        ]]
    ]))
    .unwrap();
    let pin = Sha256::digest(&bytes).into();
    (bytes, pin)
}

#[test]
fn pinned_entry_checks_actual_components_before_creating_a_participant() {
    let (run, backend) = paired_run();
    let (bytes, pin) = trusted_context(&run, &backend);
    let bound = run.bind_common_inputs(&bytes, &pin).unwrap();
    let input = |role: &str, a, backend: Arithmetic| joint::RoleInput {
        role: role.into(),
        values: [a, 22]
            .map(|value| Number {
                value,
                ty: backend.ty.clone(),
            })
            .to_vec(),
        backend,
    };
    let error = match bound.start_role(
        "pinned",
        input("role00000001", 21, backend),
        ValueBudget::default(),
        WorkBudget::default(),
    ) {
        Ok(_) => panic!("disagreeing role input must refuse"),
        Err(error) => error,
    };
    assert!(matches!(error.error, RuntimeError::Backend(ref e) if e.code == "input-binding-Value"));
    assert_eq!(error.usage.instructions, 0);
    assert_eq!(error.usage.live_value_bytes, 0);
    assert_eq!(error.backend.frames, 0);
    assert_eq!(error.backend.applications, 0);
    let mut runner = bound
        .start_role(
            "pinned",
            input("role00000001", 20, error.backend),
            ValueBudget::default(),
            WorkBudget::default(),
        )
        .map_err(|e| e.error)
        .unwrap();
    let Action::Local(local) = runner.poll() else {
        panic!("local computation");
    };
    runner.execute_local(&local.cut).unwrap();
    let Action::Returned(values) = runner.poll() else {
        panic!("ordinary participant execution");
    };
    assert_eq!(values[0].value, 42);
    assert_eq!(runner.backend().applications, 1);
}

#[test]
fn pinned_entry_retains_inventory_pin_and_installation_boundaries() {
    for change in ["pin", "inventory", "role", "entry", "program"] {
        let (run, backend) = paired_run();
        let (mut bytes, _pin) = trusted_context(&run, &backend);
        let pin = match change {
            "pin" => [0; 32],
            "inventory" | "role" => {
                let mut tree = zkc_format::logical::decode_tree(&bytes).unwrap();
                if change == "inventory" {
                    tree[3] = json!([]);
                } else {
                    tree[3][0][0].as_array_mut().unwrap().swap(0, 1);
                }
                bytes = zkc_format::logical::encode_tree(&tree).unwrap();
                Sha256::digest(&bytes).into()
            }
            subject => {
                let mut tree = zkc_format::logical::decode_tree(&bytes).unwrap();
                tree[if subject == "entry" { 2 } else { 1 }] = json!("wrong");
                bytes = zkc_format::logical::encode_tree(&tree).unwrap();
                Sha256::digest(&bytes).into()
            }
        };
        let expected = match change {
            "pin" => BindingError::Identity,
            "inventory" | "role" => BindingError::Requirements,
            _ => BindingError::Subject,
        };
        assert!(
            matches!(run.bind_common_inputs(&bytes, &pin), Err(error) if error == expected),
            "{change}"
        );
    }
    let (run, backend) = paired_run();
    let (bytes, pin) = trusted_context(&run, &backend);
    let bound = run.bind_common_inputs(&bytes, &pin).unwrap();
    let (_, mut other) = installed();
    // Keep actual inputs valid while substituting only the independently issued
    // operation handle; common-value admission cannot authorize that handle.
    other.ty = backend.ty.clone();
    let values = [20, 22]
        .map(|value| Number {
            value,
            ty: other.ty.clone(),
        })
        .to_vec();
    let error = match bound.start_role(
        "other_installation",
        joint::RoleInput {
            role: "role00000000".into(),
            backend: other,
            values,
        },
        ValueBudget::default(),
        WorkBudget::default(),
    ) {
        Ok(_) => panic!("wrong installed operation authority must refuse"),
        Err(error) => error,
    };
    assert!(matches!(error.error, RuntimeError::Admission(_)));
    assert_eq!(error.backend.frames, 0);
}

#[test]
fn common_input_binding_does_not_supply_a_service_adapter_or_input_ports() {
    let (contracts, backend) = installed();
    let original = package(&backend.ty, true);
    let with_service = change_package(&original, |frame| {
        let mut interface: serde_json::Value =
            serde_json::from_str(frame["interface"].as_str().unwrap()).unwrap();
        interface["protocols"][0]["services"] = json!([
            {"name":"entropy", "contract":"random.bls12-381.fr/0", "owner":"P", "native":2}
        ]);
        frame["interface"] = json!(interface.to_string());
    });
    assert!(
        matches!(BackendRun::admit(with_service, &contracts, &backend, joint::BundleLimits::default()), Err(error) if error == "entry-backend-services")
    );

    let (run, backend) = paired_run();
    let (bytes, pin) = trusted_context(&run, &backend);
    let bound = run.bind_common_inputs(&bytes, &pin).unwrap();
    let error = match bound.start_role(
        "missing_input",
        joint::RoleInput {
            role: "role00000000".into(),
            backend,
            values: vec![],
        },
        ValueBudget::default(),
        WorkBudget::default(),
    ) {
        Ok(_) => panic!("binding must not invent missing inputs"),
        Err(error) => error,
    };
    assert!(matches!(error.error, RuntimeError::Backend(ref e) if e.code == "input-binding-Input"));
    assert_eq!(error.backend.frames, 0);
}

#[test]
fn execution_rechecks_the_actual_backend_catalog() {
    let (contracts, backend) = installed();
    let entry = BackendRun::admit(
        package(&backend.ty, true),
        &contracts,
        &backend,
        joint::BundleLimits::default(),
    )
    .unwrap();
    let (_, other) = installed();
    let values = [20, 22]
        .map(|value| Number {
            value,
            ty: other.ty.clone(),
        })
        .to_vec();
    assert!(
        entry
            .execute(
                "substitution",
                vec![joint::RoleInput {
                    role: "role00000000".into(),
                    backend: other,
                    values,
                }],
                joint::RunLimits::default(),
                &mut joint::NoHooks
            )
            .is_err()
    );
}

#[test]
fn authenticated_bytes_and_logical_participant_abi_are_independent_checks() {
    let (contracts, backend) = installed();
    let original = package(&backend.ty, true);
    let mut bytes = original.bytes().to_vec();
    bytes.push(b' ');
    assert!(matches!(
        Package::capture(&bytes, original.identity(), Package::MAX_BYTES),
        Err(super::super::PackageError::Identity)
    ));
    for change in ["role", "type", "entry"] {
        let changed = change_package(&original, |frame| {
            let mut artifact: serde_json::Value =
                serde_json::from_str(frame["artifact"].as_str().unwrap()).unwrap();
            let mut candidate: serde_json::Value =
                serde_json::from_str(artifact["candidate"].as_str().unwrap()).unwrap();
            match change {
                "role" => candidate[3][0][3] = json!("other"),
                "type" => candidate[3][0][4][0][1] = json!("index@native/index"),
                "entry" => artifact["entry"] = json!("other"),
                _ => unreachable!(),
            }
            artifact["candidate"] = json!(candidate.to_string());
            frame["artifact"] = json!(artifact.to_string());
        });
        assert!(
            BackendRun::admit(
                changed,
                &contracts,
                &backend,
                joint::BundleLimits::default()
            )
            .is_err(),
            "{change}"
        );
    }
}

#[test]
fn nested_source_constructor_authority_is_required() {
    let (contracts, backend) = installed();
    let original = package(&backend.ty, true);
    let changed = change_package(&original, |frame| {
        let mut interface: serde_json::Value =
            serde_json::from_str(frame["interface"].as_str().unwrap()).unwrap();
        let mut child = interface["protocols"][0]["inputs"][0]["schema"].clone();
        child["identity"] = json!(digest("opaque-child"));
        child["constructible"] = json!(false);
        let parent = json!({"kind":"record","identity":digest("outer"),"type":"Outer",
            "generated":null,"custody":0,"sealed":false,"roles":[],"element":null,"constructible":true,"permissions":["Copy","Drop"],
            "fields":[{"name":"value","offset":0,"public":true,"placement":null,"schema":child}],"alternatives":[],
            "leaves":["field:koala-bear"]});
        interface["protocols"][0]["inputs"][0]["type"] = json!("Outer");
        interface["protocols"][0]["inputs"][0]["schema"] = parent;
        interface["protocols"][0]["inputs"][0]["components"][0]["path"] = json!([0]);
        frame["interface"] = json!(interface.to_string());
    });
    // The source schema itself is valid; the portable application seam must
    // still refuse constructing its hidden nested field from backend values.
    assert!(BoundInterface::read(&changed).is_ok());
    assert!(matches!(BackendRun::admit(changed, &contracts, &backend,
        joint::BundleLimits::default()), Err(error) if error == "entry-input-constructor"));
}

#[test]
fn independent_codec_backend_reaches_the_same_common_driver_after_bounded_decoding() {
    let (contracts, backend) = installed();
    let entry = BackendRun::admit(
        package(&backend.ty, true),
        &contracts,
        &backend,
        joint::BundleLimits::default(),
    )
    .unwrap();
    let ty = backend.ty.clone();
    assert!(backend.supports_wire(&ty));
    let values = [20u32, 22]
        .map(|value| backend.decode_wire(&ty, &value.to_le_bytes()).unwrap())
        .to_vec();
    assert_eq!(
        backend.decode_wire(&ty, &[0]).err().unwrap(),
        WireError::Invalid(DecodeReason::Length)
    );
    assert_eq!(
        backend
            .decode_wire(&ty, &u32::MAX.to_le_bytes())
            .err()
            .unwrap(),
        WireError::Invalid(DecodeReason::Scalar)
    );
    let report = entry
        .execute(
            "encoded",
            vec![joint::RoleInput {
                role: "role00000000".into(),
                backend,
                values,
            }],
            joint::RunLimits::default(),
            &mut joint::NoHooks,
        )
        .unwrap();
    assert_eq!(report.outcome, joint::Outcome::Completed);
    assert_eq!(
        report.backends[0]
            .1
            .encode_wire(&report.roles[0].outputs[0])
            .unwrap(),
        42u32.to_le_bytes()
    );
}

#[test]
fn independent_backend_cannot_expose_an_opaque_source_output_as_raw_storage() {
    let (contracts, backend) = installed();
    let original = package(&backend.ty, true);
    let package = change_package(&original, |package| {
        let mut interface: serde_json::Value =
            serde_json::from_str(package["interface"].as_str().unwrap()).unwrap();
        let port = &mut interface["protocols"][0]["outputs"][0];
        let field = port["schema"].clone();
        let mut record = field.clone();
        record["kind"] = json!("record");
        record["identity"] = json!(digest("SecretOutput"));
        record["type"] = json!("SecretOutput");
        record["constructible"] = json!(false);
        record["fields"] =
            json!([{"name":"hidden","offset":0,"public":false,"placement":null,"schema":field}]);
        port["schema"] = record;
        port["type"] = json!("SecretOutput");
        port["components"][0]["path"] = json!([0]);
        package["interface"] = json!(interface.to_string());
    });
    assert_eq!(
        BackendRun::admit(package, &contracts, &backend, Default::default())
            .err()
            .unwrap(),
        "entry-backend-opaque"
    );
}

#[test]
fn pinned_entry_inspection_and_its_runner_share_one_participant_allowance() {
    let (run, backend) = paired_run();
    let (bytes, pin) = trusted_context(&run, &backend);
    let bound = run.bind_common_inputs(&bytes, &pin).unwrap();
    let input = |backend: Arithmetic| joint::RoleInput {
        role: "role00000001".into(),
        values: [20, 22]
            .map(|value| Number {
                value,
                ty: backend.ty.clone(),
            })
            .to_vec(),
        backend,
    };
    let logical = |logical_bytes| WorkBudget {
        logical_bytes,
        ..Default::default()
    };
    // Starts the participant and reports whether it returned the sum, with
    // the participant's own logical work.
    let execute = |backend, work| match bound.start_role(
        "pinned",
        input(backend),
        ValueBudget::default(),
        work,
    ) {
        Err(error) => Err(Box::new(error)),
        Ok(mut runner) => {
            let Action::Local(local) = runner.poll() else {
                panic!("local computation");
            };
            let returned = runner.execute_local(&local.cut).is_ok()
                && matches!(runner.poll(), Action::Returned(values) if values[0].value == 42);
            let usage = runner.usage().logical_bytes;
            Ok((returned, usage, runner.into_backend()))
        }
    };
    // Inspection reads the component root and the selected value, 64 bytes
    // each, and encodes its four-byte canonical frame.
    let inspection = 2 * 64 + 4;
    let error = *execute(backend, logical(inspection - 1)).err().unwrap();
    assert!(matches!(error.error, RuntimeError::Limit));
    assert_eq!(error.backend.frames, 0);
    let (returned, runner_work, backend) =
        execute(error.backend, WorkBudget::default()).ok().unwrap();
    assert!(returned && runner_work > 0);
    // The runner's own budget would admit its work, but inspection already
    // drew on the same participant allowance.
    let (returned, _, backend) = execute(backend, logical(runner_work + inspection - 1))
        .ok()
        .unwrap();
    assert!(!returned);
    let (returned, _, _) = execute(backend, logical(runner_work + inspection))
        .ok()
        .unwrap();
    assert!(returned);
}
