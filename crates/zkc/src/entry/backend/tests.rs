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
        Arithmetic { ty, id },
    )
}
fn digest(value: &str) -> String {
    crate::host::inputs::hex(&Sha256::digest(value.as_bytes()))
}
fn package(ty: &PhysicalType, constructible: bool) -> Package {
    let field = json!({"kind":"field","identity":digest("F"),"type":"F","custody":false,"constructible":constructible,
        "permissions":["Copy","Drop"],"fields":[],"alternatives":[],"leaves":["field:koala-bear"]});
    let port = |name: &str, index: u32| json!({"name":name,"index":index,"native":[index],"roles":["P"],"type":"F","schema":field});
    let interface = json!({"format":"zkc.language-interface/0","setups":[],"capture":digest("capture"),"original":digest("source"),"toolchain":"test",
        "entry":"example::Main","protocol":"example_Add","protocols":[{"symbol":"example_Add","roles":["P"],
        "inputs":[port("a",0),port("b",1)],"outputs":[port("sum",0)],"services":[],"clauses":[]}],"relations":[],"job":{"kind":"run"}});
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
        "options":{"simplify":true,"release_storage":false,"finite_bulk":true,"fuse_vector_reductions":false,"fuse_collect_fold":false,"calculation_batching":true}}).to_string();
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
            "custody":false,"constructible":true,"permissions":["Copy","Drop"],
            "fields":[{"name":"value","offset":0,"schema":child}],"alternatives":[],
            "leaves":["field:koala-bear"]});
        interface["protocols"][0]["inputs"][0]["type"] = json!("Outer");
        interface["protocols"][0]["inputs"][0]["schema"] = parent;
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
