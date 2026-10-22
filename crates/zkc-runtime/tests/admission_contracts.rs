//! Independent non-curve deployment: trusted contributions, resident arithmetic,
//! Runner control and the shared joint Host. No Native values, codecs or kernels.
use serde_json::{Value as Json, json};
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
use zkc_runtime::{
    host::{
        joint::*,
        wire::{WireBackend, WireError},
    },
    interpreter::{LocalRunner, Runner},
    vm::*,
};

const BOOL: &str = "bool@native.bool/0";
const REPRESENTATION: &str = "independent.offset-koala-bear/0";
const MODULUS: u64 = 2_130_706_433;
const OFFSET: u64 = 17;

#[derive(Debug, PartialEq, Eq)]
struct Residue {
    ty: PhysicalType,
    encoded: u64,
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Number {
    Field(Arc<Residue>),
    Bool(bool),
    Index(u64),
}
impl Number {
    fn field(ty: &PhysicalType, value: u64) -> Self {
        Self::Field(Arc::new(Residue {
            ty: ty.clone(),
            encoded: (value + OFFSET) % MODULUS,
        }))
    }
}
impl Value for Number {
    fn physical_type(&self) -> PhysicalType {
        match self {
            Self::Field(value) => value.ty.clone(),
            Self::Bool(_) => PhysicalType::parse(BOOL).unwrap(),
            Self::Index(_) => PhysicalType::parse("index@native.index/0").unwrap(),
        }
    }
    fn retained_bytes(&self) -> usize {
        match self {
            Self::Field(_) => std::mem::size_of::<Residue>(),
            _ => 8,
        }
    }
    fn retained_parts(&self, shared: &mut dyn FnMut(Backing) -> bool) -> usize {
        if let Self::Field(value) = self {
            shared(Backing::of(value, std::mem::size_of::<Residue>()));
            0
        } else {
            8
        }
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        if matches!(self, Self::Bool(_)) {
            Ok(())
        } else {
            Err(BackendError::new("no-field-codec"))
        }
    }
    fn control_bool(&self) -> Result<bool, BackendError> {
        if let Self::Bool(value) = self {
            Ok(*value)
        } else {
            Err(BackendError::new("bool"))
        }
    }
    fn from_control_bool(value: bool) -> Result<Self, BackendError> {
        Ok(Self::Bool(value))
    }
    fn control_index(&self) -> Result<u64, BackendError> {
        if let Self::Index(value) = self {
            Ok(*value)
        } else {
            Err(BackendError::new("index"))
        }
    }
    fn from_control_index(value: u64) -> Result<Self, BackendError> {
        Ok(Self::Index(value))
    }
}
fn declaration(operation: &str) -> OperationBinding {
    OperationBinding {
        contract: format!("field.{operation}"),
        arguments: vec!["koala-bear".into()],
        implementation: format!("independent/field.{operation}"),
        physical_arguments: vec![],
    }
}
fn requirements(timing: TimingRequirement) -> ImplementationRequirements {
    ImplementationRequirements {
        timing,
        timing_operands: if timing == TimingRequirement::VariableTime {
            &[0, 1]
        } else {
            &[]
        },
    }
}
fn signature(field: &PhysicalType, equal: bool) -> BoundSignature {
    BoundSignature {
        inputs: vec![field.clone(), field.clone()],
        outputs: vec![if equal {
            PhysicalType::parse(BOOL).unwrap()
        } else {
            field.clone()
        }],
        attributes: AttributeRule::None,
    }
}
struct Deployment {
    contracts: Contracts,
    field: PhysicalType,
    add: ImplementationId,
    equal: ImplementationId,
}
fn deployment(timing: TimingRequirement, policy: ExecutionPolicy) -> Deployment {
    deployment_with_requirements(requirements(timing), policy)
}
fn deployment_with_requirements(
    premises: ImplementationRequirements,
    policy: ExecutionPolicy,
) -> Deployment {
    let mut builder = ContractsBuilder::empty();
    let field = builder
        .add_representation(
            REPRESENTATION,
            LogicalType::new(Type::Field, Identity::KoalaBear).unwrap(),
        )
        .unwrap();
    let add = builder
        .add_implementation(declaration("add"), signature(&field, false), premises)
        .unwrap();
    let equal = builder
        .add_implementation(declaration("equal"), signature(&field, true), premises)
        .unwrap();
    Deployment {
        contracts: builder.finish(policy),
        field,
        add,
        equal,
    }
}
#[derive(Clone)]
struct Operation {
    signature: BoundSignature,
    id: ImplementationId,
    requirements: ImplementationRequirements,
    equal: bool,
}
impl InstalledOperation for Operation {
    fn signature(&self) -> &BoundSignature {
        &self.signature
    }
    fn implementation_id(&self) -> Option<ImplementationId> {
        Some(self.id)
    }
    fn requirements(&self) -> ImplementationRequirements {
        self.requirements
    }
    // Replay eligibility is deliberately independent of timing eligibility.
    fn deterministic(&self) -> bool {
        true
    }
}
struct Arithmetic {
    field: PhysicalType,
    add: ImplementationId,
    equal: ImplementationId,
    timing: TimingRequirement,
    timing_operands: Option<&'static [usize]>,
    wrong_ports: bool,
    missing: bool,
    entries: Arc<AtomicUsize>,
    frames: Vec<FrameId>,
    calls: usize,
}
impl Arithmetic {
    fn new(deployment: &Deployment) -> Self {
        Self {
            field: deployment.field.clone(),
            add: deployment.add,
            equal: deployment.equal,
            timing: TimingRequirement::OperandIndependent,
            timing_operands: None,
            wrong_ports: false,
            missing: false,
            entries: Arc::new(AtomicUsize::new(0)),
            frames: vec![],
            calls: 0,
        }
    }
}
impl Backend for Arithmetic {
    type Value = Number;
    type Operation = Operation;
    type Call = ();
    type Checkpoint = ();
    fn supports_boolean_literals(&self) -> bool {
        true
    }
    fn prepare_binding(&self, binding: &OperationBinding) -> Option<Operation> {
        if self.missing {
            return None;
        }
        let equal = if *binding == declaration("add") {
            false
        } else if *binding == declaration("equal") {
            true
        } else {
            return None;
        };
        // Author actual ports from this backend's typed carrier. Do not resolve
        // the expected signature or copy it from the Program being linked.
        let mut actual = signature(&self.field, equal);
        if self.wrong_ports {
            actual.outputs.clear();
        }
        Some(Operation {
            signature: actual,
            id: if equal { self.equal } else { self.add },
            requirements: {
                let mut premises = requirements(self.timing);
                if let Some(operands) = self.timing_operands {
                    premises.timing_operands = operands;
                }
                premises
            },
            equal,
        })
    }
    fn validate_value(&self, value: &Number) -> Result<(), BackendError> {
        if let Number::Field(value) = value
            && (value.ty != self.field || value.encoded >= MODULUS)
        {
            return Err(BackendError::new("residue"));
        }
        Ok(())
    }
    fn enter_frame(&mut self, frame: &Frame, _: &[Number]) -> Result<(), BackendError> {
        self.entries.fetch_add(1, Ordering::Relaxed);
        assert_eq!(frame.parent(), self.frames.last().copied());
        self.frames.push(frame.id());
        Ok(())
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        _: FrameExit,
        _: &[Number],
    ) -> Result<(), BackendError> {
        assert_eq!(self.frames.pop(), Some(frame.id()));
        Ok(())
    }
    fn apply(
        &mut self,
        operation: &Operation,
        invocation: &Invocation<'_>,
        args: &[Number],
    ) -> Result<Vec<Number>, BackendError> {
        if invocation.max_output_bytes < std::mem::size_of::<Residue>() {
            return Err(BackendError::new("capacity"));
        }
        let [Number::Field(a), Number::Field(b)] = args else {
            return Err(BackendError::new("ports"));
        };
        self.calls += 1;
        Ok(vec![if operation.equal {
            Number::Bool(a.encoded == b.encoded)
        } else {
            Number::Field(Arc::new(Residue {
                ty: self.field.clone(),
                encoded: (a.encoded + b.encoded + MODULUS - OFFSET) % MODULUS,
            }))
        }])
    }
}
impl WireBackend for Arithmetic {
    fn supports_wire(&self, ty: &PhysicalType) -> bool {
        ty.spelling() == BOOL
    }
    fn fixed_wire_size(&self, ty: &PhysicalType) -> Option<usize> {
        self.supports_wire(ty).then_some(1)
    }
    fn encoding_bound(&self, _: &Number) -> Result<usize, WireError> {
        Ok(1)
    }
    fn decoding_bound(&self, _: &PhysicalType, bytes: &[u8]) -> Result<usize, WireError> {
        if matches!(bytes, [0] | [1]) {
            Ok(8)
        } else {
            Err(WireError::Invalid(DecodeReason::Boolean))
        }
    }
    fn encode_wire(&self, value: &Number) -> Result<Vec<u8>, WireError> {
        if let Number::Bool(value) = value {
            Ok(vec![u8::from(*value)])
        } else {
            Err(WireError::Backend(BackendError::new("wire-type")))
        }
    }
    fn decode_wire(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<Number, WireError> {
        if !self.supports_wire(ty) {
            return Err(WireError::Backend(BackendError::new("wire-type")));
        }
        self.decoding_bound(ty, bytes)?;
        Ok(Number::Bool(bytes[0] == 1))
    }
}
fn carrier(field: &PhysicalType) -> Json {
    let field = field.spelling();
    json!([
        "zkc.program/0",
        [
            [
                "add",
                "field.add",
                ["koala-bear"],
                "independent/field.add",
                []
            ],
            [
                "equal",
                "field.equal",
                ["koala-bear"],
                "independent/field.equal",
                []
            ]
        ],
        [[
            "function",
            "calculate",
            [
                ["x", field],
                ["y", field],
                ["z", field],
                ["expected", field]
            ],
            [BOOL],
            [
                ["op", "first", "add", [], ["x", "y"], ["sum"]],
                ["op", "second", "add", [], ["sum", "z"], ["total"]],
                ["op", "compare", "equal", [], ["total", "expected"], ["ok"]],
                ["return", ["ok"]]
            ],
            ["calculate", []]
        ]],
        [
            [
                "participant",
                "p",
                "root",
                "P",
                [
                    ["x", field],
                    ["y", field],
                    ["z", field],
                    ["expected", field]
                ],
                [],
                [
                    [
                        "local",
                        "compute",
                        "calculate",
                        ["x", "y", "z", "expected"],
                        ["ok"]
                    ],
                    ["send", "publish", "answer", "V", "ok"],
                    ["return", []]
                ],
                []
            ],
            [
                "participant",
                "v",
                "root",
                "V",
                [],
                [BOOL],
                [
                    ["receive", "publish", "answer", "P", "ok", BOOL],
                    ["return", ["ok"]]
                ],
                []
            ]
        ],
        [["entry", "main", [["P", "p"], ["V", "v"]]]]
    ])
}
fn bytes(value: &Json) -> Vec<u8> {
    serde_json::to_vec(value).unwrap()
}
fn arguments(field: &PhysicalType) -> Vec<Number> {
    // Wrap the field modulus as well as exercising an adjacent resident call.
    [MODULUS - 1, 6, 7, 12]
        .into_iter()
        .map(|n| Number::field(field, n))
        .collect()
}
fn pinned_bundle(deployment: &Deployment) -> Vec<u8> {
    bytes(
        &json!({"format":"zkc.run/0", "candidate":carrier(&deployment.field).to_string(), "entry":"main", "roles":["P","V"],
        "steps":[{"role":0,"instruction":0,"anchor":0}, {"role":0,"instruction":1,"anchor":1},
                 {"role":1,"instruction":0,"anchor":1}, {"role":0,"instruction":2,"anchor":null},
                 {"role":1,"instruction":1,"anchor":null}]}),
    )
}
#[test]
fn independent_representation_executes_mathematics_through_runner_and_joint_host() {
    let d = deployment(
        TimingRequirement::OperandIndependent,
        ExecutionPolicy::operand_independent(),
    );
    assert!(PhysicalType::parse(&d.field.spelling()).is_err());
    assert!(!d.field.is_serializable());
    let program = Program::decode(&bytes(&carrier(&d.field)), &d.contracts).unwrap();
    let mut local = LocalRunner::new(
        &program,
        "calculate",
        "local",
        Arithmetic::new(&d),
        arguments(&d.field),
    )
    .unwrap_or_else(|_| panic!("local load"));
    assert!(matches!(local.execute(), Action::Returned(values) if values == &[Number::Bool(true)]));

    let mut runner = Runner::new_for_role_with_ledger(
        &program,
        "main",
        "P",
        "runner",
        Arithmetic::new(&d),
        arguments(&d.field),
        ValueBudget::default(),
        WorkBudget::default(),
        None,
    )
    .unwrap_or_else(|_| panic!("runner load"));
    let Action::Local(action) = runner.poll() else {
        panic!("local cut")
    };
    runner.execute_local(&action.cut).unwrap();
    assert_eq!(runner.backend().calls, 3);
    if let Some(counts) = runner.execution_counts().json() {
        assert_eq!(counts["operations"]["field.add"], 2);
        assert_eq!(counts["operations"]["field.equal"], 1);
        assert_eq!(counts["events"]["local_op"], 3);
        assert_eq!(counts["events"]["backend_enter_calls"], 2);
    }
    assert!(matches!(runner.poll(), Action::Send(_)));
    runner.cancel();
    assert!(runner.backend().frames.is_empty());

    let bundle = Bundle::admit(
        &pinned_bundle(&d),
        &Arithmetic::new(&d),
        &d.contracts,
        BundleLimits::default(),
    )
    .unwrap();
    let report = run(
        &bundle,
        "joint",
        vec![
            RoleInput {
                role: "P".into(),
                backend: Arithmetic::new(&d),
                values: arguments(&d.field),
            },
            RoleInput {
                role: "V".into(),
                backend: Arithmetic::new(&d),
                values: vec![],
            },
        ],
        RunLimits::default(),
        &mut NoHooks,
    )
    .unwrap();
    assert_eq!(report.outcome, Outcome::Completed);
    assert_eq!(report.roles[1].outputs, [Number::Bool(true)]);
    assert_eq!(
        (
            report.wire.sends,
            report.wire.receives,
            report.wire.sent_bytes
        ),
        (1, 1, 1)
    );
    assert_eq!(report.backends[0].1.calls, 3);
    assert!(
        report
            .backends
            .iter()
            .all(|(_, backend)| backend.frames.is_empty())
    );
}

#[test]
fn actual_ports_scoped_identity_missing_handlers_and_timing_refuse_before_frames() {
    let d = deployment(
        TimingRequirement::OperandIndependent,
        ExecutionPolicy::operand_independent(),
    );
    let other = deployment(
        TimingRequirement::OperandIndependent,
        ExecutionPolicy::operand_independent(),
    );
    assert_ne!(d.field, other.field);
    assert_ne!(d.add, other.add);
    let program = Program::decode(&bytes(&carrier(&d.field)), &d.contracts).unwrap();
    for mutation in 0..5 {
        let mut actual = Arithmetic::new(&d);
        match mutation {
            0 => actual.wrong_ports = true,
            1 => actual.add = other.add, // Same numeric slot, different catalog.
            2 => actual.missing = true,
            3 => actual.timing = TimingRequirement::VariableTime,
            4 => actual.field = other.field.clone(),
            _ => unreachable!(),
        }
        let entries = actual.entries.clone();
        assert_eq!(
            program.check_installation(&actual).unwrap_err().code,
            ErrorCode::Backend
        );
        assert_eq!(
            program
                .check_role_installation("main", "P", &actual)
                .unwrap_err()
                .code,
            ErrorCode::Backend
        );
        assert_eq!(
            program
                .check_local_installation("calculate", &actual)
                .unwrap_err()
                .code,
            ErrorCode::Backend
        );
        let error = match Runner::new_for_role_with_ledger(
            &program,
            "main",
            "P",
            "load",
            actual,
            arguments(&d.field),
            ValueBudget::default(),
            WorkBudget::default(),
            None,
        ) {
            Ok(_) => panic!("forged installation loaded"),
            Err(error) => error,
        };
        assert_eq!(entries.load(Ordering::Relaxed), 0);
        assert!(error.backend.frames.is_empty());
    }
    let permissive = deployment(
        TimingRequirement::OperandIndependent,
        ExecutionPolicy::general_purpose(),
    );
    let permissive_program =
        Program::decode(&bytes(&carrier(&permissive.field)), &permissive.contracts).unwrap();
    let mut changed_premise = Arithmetic::new(&permissive);
    changed_premise.timing = TimingRequirement::VariableTime;
    assert_eq!(
        permissive_program
            .check_installation(&changed_premise)
            .unwrap_err()
            .code,
        ErrorCode::Backend
    );
    // Cloning the immutable context retains all scoped identities.
    let clone = d.contracts.clone();
    assert_eq!(clone.physical_type(&d.field.spelling()).unwrap(), d.field);
    assert_eq!(
        clone
            .resolve(declaration("add"))
            .unwrap()
            .implementation_id(),
        Some(d.add)
    );
}

#[test]
fn artifact_identity_and_metadata_never_supply_installation_or_permissions() {
    let d = deployment(
        TimingRequirement::OperandIndependent,
        ExecutionPolicy::operand_independent(),
    );
    let empty = ContractsBuilder::empty().finish(ExecutionPolicy::general_purpose());
    assert_eq!(
        Program::decode(&bytes(&carrier(&d.field)), &empty)
            .unwrap_err()
            .code,
        ErrorCode::Signature
    );
    assert_eq!(
        empty
            .physical_type("field:koala-bear@plonky3.koala-bear/0")
            .unwrap_err()
            .code,
        ErrorCode::Representation
    );
    for (part, replacement) in [
        (1, json!("field.unknown")),
        (2, json!(["bls12-381.fr"])),
        (3, json!("forged/field.add")),
    ] {
        let mut artifact = carrier(&d.field);
        artifact[1][0][part] = replacement;
        assert_eq!(
            Program::decode(&bytes(&artifact), &d.contracts)
                .unwrap_err()
                .code,
            ErrorCode::Signature
        );
    }
    for spelling in [
        "field:koala-bear@forged.layout/0",
        "field:bls12-381.fr@independent.offset-koala-bear/0",
    ] {
        assert_eq!(
            d.contracts.physical_type(spelling).unwrap_err().code,
            ErrorCode::Representation
        );
    }
    let mut artifact = carrier(&d.field);
    artifact[3][0][6][1] = json!(["send", "publish", "answer", "V", "x"]);
    assert_eq!(
        Program::decode(&bytes(&artifact), &d.contracts)
            .unwrap_err()
            .code,
        ErrorCode::Type
    );

    for timing in [
        TimingRequirement::VariableTime,
        TimingRequirement::Unspecified,
    ] {
        let denied = deployment(timing, ExecutionPolicy::operand_independent());
        assert_eq!(
            denied
                .contracts
                .resolve(declaration("add"))
                .unwrap_err()
                .code,
            ErrorCode::Backend
        );
        assert_eq!(
            Program::decode(&bytes(&carrier(&denied.field)), &denied.contracts)
                .unwrap_err()
                .code,
            ErrorCode::Backend
        );
        let allowed = deployment(timing, ExecutionPolicy::general_purpose());
        let program =
            Program::decode(&bytes(&carrier(&allowed.field)), &allowed.contracts).unwrap();
        let mut actual = Arithmetic::new(&allowed);
        actual.timing = timing;
        program.check_installation(&actual).unwrap();
    }
}

#[test]
fn malformed_duplicate_and_cross_catalog_contributions_refuse() {
    let field = LogicalType::new(Type::Field, Identity::KoalaBear).unwrap();
    let mut builder = ContractsBuilder::empty();
    let ty = builder
        .add_representation(REPRESENTATION, field.clone())
        .unwrap();
    assert_eq!(
        builder
            .add_representation(REPRESENTATION, field.clone())
            .unwrap_err()
            .code,
        ErrorCode::Representation
    );
    for name in ["plonky3.koala-bear/0", "", "bad layout/0"] {
        assert_eq!(
            builder
                .add_representation(name, field.clone())
                .unwrap_err()
                .code,
            ErrorCode::Representation
        );
    }
    for spelling in [
        "bool",
        "index",
        "resource_unit:Slot.A",
        "rng:bls12-381.fr",
        "fixed_vector<field:koala-bear,1>",
    ] {
        let logical = LogicalType::parse(spelling).unwrap();
        assert_eq!(
            builder
                .add_representation("forbidden/0", logical)
                .unwrap_err()
                .code,
            ErrorCode::Representation
        );
    }
    let good = signature(&ty, false);
    let mut wrong = good.clone();
    wrong.outputs.clear();
    assert_eq!(
        builder
            .add_implementation(
                declaration("add"),
                wrong,
                requirements(TimingRequirement::OperandIndependent)
            )
            .unwrap_err()
            .code,
        ErrorCode::Signature
    );
    builder
        .add_implementation(
            declaration("add"),
            good.clone(),
            requirements(TimingRequirement::OperandIndependent),
        )
        .unwrap();
    assert_eq!(
        builder
            .add_implementation(
                declaration("add"),
                good,
                requirements(TimingRequirement::OperandIndependent)
            )
            .unwrap_err()
            .code,
        ErrorCode::Signature
    );
    let foreign = deployment(
        TimingRequirement::OperandIndependent,
        ExecutionPolicy::operand_independent(),
    );
    assert_eq!(
        builder
            .add_implementation(
                declaration("equal"),
                signature(&foreign.field, true),
                requirements(TimingRequirement::OperandIndependent)
            )
            .unwrap_err()
            .code,
        ErrorCode::Representation
    );
    assert_eq!(
        PhysicalType::new(ty.logical(), ty.representation())
            .unwrap_err()
            .code,
        ErrorCode::Representation
    );
}

#[test]
fn independent_values_remain_small_and_clone_shared_payload_without_allocation() {
    assert!(std::mem::size_of::<Number>() <= 24);
    assert!(std::mem::size_of::<ImplementationId>() <= 16);
    let d = deployment(
        TimingRequirement::OperandIndependent,
        ExecutionPolicy::operand_independent(),
    );
    let value = Number::field(&d.field, 1);
    let clone = value.clone();
    let (Number::Field(a), Number::Field(b)) = (&value, &clone) else {
        unreachable!()
    };
    assert!(Arc::ptr_eq(a, b));
    assert_eq!(Arc::strong_count(a), 2);
}

#[test]
fn shared_names_support_distinct_logical_layouts_and_exact_specializations() {
    let mut builder = ContractsBuilder::empty();
    let field_logical = LogicalType::new(Type::Field, Identity::KoalaBear).unwrap();
    let vector_logical = LogicalType::new(Type::Vector, Identity::KoalaBear).unwrap();
    let field = builder
        .add_representation("independent/shared", field_logical)
        .unwrap();
    let vector = builder
        .add_representation("independent/shared", vector_logical)
        .unwrap();
    assert_eq!(field.representation(), vector.representation());
    assert_ne!(field, vector);
    let bls_logical = LogicalType::new(Type::Field, Identity::Bls12381Fr).unwrap();
    let bls = builder
        .add_representation("independent/bls", bls_logical)
        .unwrap();
    let first = builder
        .add_implementation(
            declaration("add"),
            signature(&field, false),
            requirements(TimingRequirement::OperandIndependent),
        )
        .unwrap();
    let mut second_declaration = declaration("add");
    second_declaration.arguments = vec!["bls12-381.fr".into()];
    let second = builder
        .add_implementation(
            second_declaration.clone(),
            signature(&bls, false),
            requirements(TimingRequirement::OperandIndependent),
        )
        .unwrap();
    assert_ne!(first, second);
    let mut conflicting_owner = declaration("equal");
    conflicting_owner.implementation = declaration("add").implementation;
    assert_eq!(
        builder
            .add_implementation(
                conflicting_owner,
                signature(&field, true),
                requirements(TimingRequirement::OperandIndependent)
            )
            .unwrap_err()
            .code,
        ErrorCode::Signature
    );
    let context = builder.finish(ExecutionPolicy::operand_independent());
    assert_eq!(context.physical_type(&field.spelling()).unwrap(), field);
    assert_eq!(context.physical_type(&vector.spelling()).unwrap(), vector);
    assert_eq!(
        context
            .resolve(second_declaration)
            .unwrap()
            .implementation_id(),
        Some(second)
    );
}

#[test]
fn policy_changes_preserve_ids_and_do_not_mutate_admitted_programs() {
    let d = deployment(
        TimingRequirement::VariableTime,
        ExecutionPolicy::general_purpose(),
    );
    let program = Program::decode(&bytes(&carrier(&d.field)), &d.contracts).unwrap();
    let strict = d
        .contracts
        .with_policy(ExecutionPolicy::operand_independent());
    assert_eq!(strict.physical_type(&d.field.spelling()).unwrap(), d.field);
    assert_eq!(
        strict.resolve(declaration("add")).unwrap_err().code,
        ErrorCode::Backend
    );
    assert_eq!(
        Program::decode(program.bytes(), &strict).unwrap_err().code,
        ErrorCode::Backend
    );
    let mut backend = Arithmetic::new(&d);
    backend.timing = TimingRequirement::VariableTime;
    program.check_installation(&backend).unwrap();
    assert_eq!(
        program.contracts().policy(),
        ExecutionPolicy::general_purpose()
    );
    assert_eq!(
        d.contracts
            .resolve(declaration("add"))
            .unwrap()
            .implementation_id(),
        Some(d.add)
    );
}

#[test]
fn ordered_direct_conversion_requires_exact_trusted_law_and_ports() {
    let mut builder = ContractsBuilder::standard();
    let logical = LogicalType::new(Type::Field, Identity::KoalaBear).unwrap();
    let source = PhysicalType::default_for(logical.clone()).unwrap();
    let target = builder
        .add_representation(REPRESENTATION, logical.clone())
        .unwrap();
    let binding = OperationBinding {
        contract: "representation.convert".into(),
        arguments: vec![logical.spelling()],
        physical_arguments: vec![source.spelling(), target.spelling()],
        implementation: "independent/representation.convert".into(),
    };
    let ports = BoundSignature {
        inputs: vec![source.clone()],
        outputs: vec![target.clone()],
        attributes: AttributeRule::None,
    };
    let mut swapped = ports.clone();
    swapped.inputs = vec![target.clone()];
    swapped.outputs = vec![source];
    assert_eq!(
        builder
            .add_implementation(
                binding.clone(),
                swapped,
                requirements(TimingRequirement::OperandIndependent)
            )
            .unwrap_err()
            .code,
        ErrorCode::Signature
    );
    let id = builder
        .add_implementation(
            binding.clone(),
            ports.clone(),
            requirements(TimingRequirement::OperandIndependent),
        )
        .unwrap();
    let contracts = builder.finish(ExecutionPolicy::operand_independent());
    let admitted = contracts.resolve(binding.clone()).unwrap();
    assert_eq!(admitted.signature(), &ports);
    assert_eq!(admitted.implementation_id(), Some(id));
    assert!(!admitted.observes_history());
    let mut reverse = binding.clone();
    reverse.physical_arguments.swap(0, 1);
    assert_eq!(
        contracts.resolve(reverse).unwrap_err().code,
        ErrorCode::Signature
    );
    let standard = Contracts::standard(ExecutionPolicy::general_purpose());
    assert_eq!(
        standard.resolve(binding).unwrap_err().code,
        ErrorCode::Representation
    );
}

#[test]
fn weakened_expected_timing_and_operand_drift_refuse_before_frames() {
    // Mutate only the expected contribution. Actual backend metadata remains
    // independently authored, with exactly the same scoped IDs and ports.
    for expected in [
        ImplementationRequirements::default(),
        ImplementationRequirements {
            timing: TimingRequirement::OperandIndependent,
            timing_operands: &[],
        },
        ImplementationRequirements {
            timing: TimingRequirement::VariableTime,
            timing_operands: &[0],
        },
        ImplementationRequirements {
            timing: TimingRequirement::VariableTime,
            timing_operands: &[1],
        },
    ] {
        let d = deployment_with_requirements(expected, ExecutionPolicy::general_purpose());
        let program = Program::decode(&bytes(&carrier(&d.field)), &d.contracts).unwrap();
        let mut actual = Arithmetic::new(&d);
        actual.timing = TimingRequirement::VariableTime;
        let entries = actual.entries.clone();
        let installed = actual.prepare_binding(&declaration("add")).unwrap();
        assert_eq!(installed.implementation_id(), Some(d.add));
        assert_eq!(installed.signature(), &signature(&d.field, false));
        assert_eq!(
            installed.requirements(),
            requirements(TimingRequirement::VariableTime)
        );
        assert_eq!(
            program.check_installation(&actual).unwrap_err().code,
            ErrorCode::Backend
        );
        let error = match Runner::new(
            &program,
            "main",
            "P",
            "session",
            actual,
            arguments(&d.field),
        ) {
            Ok(_) => panic!("weakened expected timing loaded"),
            Err(error) => error,
        };
        assert_eq!(entries.load(Ordering::Relaxed), 0);
        assert!(error.backend.frames.is_empty());
    }
}

#[test]
fn exact_timing_grants_preserve_catalog_scope_and_immutable_program_policy() {
    let policy = ExecutionPolicy {
        allow_unspecified_timing: true,
        allow_variable_time: false,
    };
    let d = deployment(TimingRequirement::VariableTime, policy);
    let premise = requirements(TimingRequirement::VariableTime);
    let granted = d
        .contracts
        .with_timing_grant(declaration("add"), premise)
        .unwrap();
    assert_eq!(
        granted
            .resolve(declaration("add"))
            .unwrap()
            .implementation_id(),
        Some(d.add)
    );
    assert!(granted.resolve(declaration("equal")).is_err());
    assert!(d.contracts.resolve(declaration("add")).is_err());
    assert!(
        granted
            .with_timing_grant(declaration("add"), ImplementationRequirements::default())
            .is_err()
    );
    assert!(
        granted
            .with_timing_grant(
                declaration("add"),
                ImplementationRequirements {
                    timing: TimingRequirement::VariableTime,
                    timing_operands: &[0],
                }
            )
            .is_err()
    );
    let other = deployment(TimingRequirement::VariableTime, policy);
    assert!(!granted.permits_implementation(&declaration("add"), Some(other.add), premise));
    assert!(!granted.permits_implementation(
        &declaration("add"),
        Some(d.add),
        ImplementationRequirements {
            timing: TimingRequirement::VariableTime,
            timing_operands: &[1],
        }
    ));
    let complete = granted
        .with_timing_grant(declaration("equal"), premise)
        .unwrap();
    let program = Program::decode(&bytes(&carrier(&d.field)), &complete).unwrap();
    let mut actual = Arithmetic::new(&d);
    actual.timing = TimingRequirement::VariableTime;
    program.check_installation(&actual).unwrap();
    assert!(Program::decode(program.bytes(), &d.contracts).is_err());
    assert!(
        program
            .contracts()
            .permits_implementation(&declaration("add"), Some(d.add), premise)
    );
    // Explicit blanket grants still exist and do not pretend to prove timing.
    d.contracts
        .with_policy(ExecutionPolicy::general_purpose())
        .resolve(declaration("equal"))
        .unwrap();
}

#[test]
fn timing_operand_premises_are_bounded_ordered_and_explicit() {
    for (timing, operands) in [
        (TimingRequirement::VariableTime, &[][..]),
        (TimingRequirement::VariableTime, &[2][..]),
        (TimingRequirement::VariableTime, &[0, 0][..]),
        (TimingRequirement::VariableTime, &[1, 0][..]),
        (TimingRequirement::Unspecified, &[0][..]),
        (TimingRequirement::OperandIndependent, &[0][..]),
    ] {
        let mut builder = ContractsBuilder::empty();
        let ty = builder
            .add_representation(
                REPRESENTATION,
                LogicalType::new(Type::Field, Identity::KoalaBear).unwrap(),
            )
            .unwrap();
        let error = builder
            .add_implementation(
                declaration("add"),
                signature(&ty, false),
                ImplementationRequirements {
                    timing,
                    timing_operands: operands,
                },
            )
            .unwrap_err();
        assert_eq!(error.code, ErrorCode::Signature);
        assert_eq!(error.detail, "implementation-timing-operands");
    }
}

#[test]
fn wire_permission_requires_exact_leaves_and_admitted_aggregate_storage() {
    let logical = LogicalType::new(Type::Field, Identity::KoalaBear).unwrap();
    let mut builder = ContractsBuilder::empty();
    let field = builder
        .add_representation(REPRESENTATION, logical.clone())
        .unwrap();
    let vector = builder
        .add_representation(
            REPRESENTATION,
            LogicalType::new(Type::Vector, Identity::KoalaBear).unwrap(),
        )
        .unwrap();
    let other = deployment(
        TimingRequirement::OperandIndependent,
        ExecutionPolicy::general_purpose(),
    );
    assert_eq!(
        builder
            .add_wire_permission(other.field, WireCodec::Native)
            .unwrap_err()
            .code,
        ErrorCode::Representation
    );
    let denied = deployment(
        TimingRequirement::OperandIndependent,
        ExecutionPolicy::general_purpose(),
    );
    assert!(
        !denied
            .contracts
            .permits_wire(&denied.field, WireCodec::Native)
    );
    builder
        .add_wire_permission(field.clone(), WireCodec::Native)
        .unwrap();
    let selected_container = builder
        .aggregate_type(
            LogicalType::parse("sequence<field:koala-bear>").unwrap(),
            Representation::Sequence,
            vec![field.clone()],
        )
        .unwrap();
    builder
        .add_wire_permission(selected_container.clone(), WireCodec::Native)
        .unwrap();
    assert_eq!(
        builder
            .add_wire_permission(field.clone(), WireCodec::Native)
            .unwrap_err()
            .detail,
        "duplicate-wire-permission"
    );
    let contracts = builder.finish(ExecutionPolicy::general_purpose());
    assert!(contracts.permits_wire(&field, WireCodec::Native));
    assert!(contracts.permits_wire(&selected_container, WireCodec::Native));
    assert!(!contracts.permits_wire(&vector, WireCodec::Native));
    assert!(!contracts.permits_wire(&denied.field, WireCodec::Native));
    let default = PhysicalType::default_for(logical).unwrap();
    assert!(!contracts.permits_wire(&default, WireCodec::Native));
    let container =
        PhysicalType::default_for(LogicalType::parse("sequence<field:koala-bear>").unwrap())
            .unwrap();
    assert!(!contracts.permits_wire(&container, WireCodec::Native));
    let mut standard = ContractsBuilder::standard();
    let resource =
        PhysicalType::default_for(LogicalType::parse("resource_unit:Slot.A").unwrap()).unwrap();
    assert_eq!(
        standard
            .add_wire_permission(resource, WireCodec::Native)
            .unwrap_err()
            .detail,
        "wire-permission-type"
    );
}

#[test]
fn proof_entry_requires_exact_permission_for_selected_verifier_ports() {
    for (aggregate, grant) in [(false, false), (false, true), (true, false), (true, true)] {
        let mut builder = ContractsBuilder::empty();
        let ty = builder
            .add_representation(
                REPRESENTATION,
                LogicalType::new(Type::Field, Identity::KoalaBear).unwrap(),
            )
            .unwrap();
        if aggregate && grant {
            builder
                .add_wire_permission(ty.clone(), WireCodec::Native)
                .unwrap();
        }
        let ty = if aggregate {
            builder
                .aggregate_type(
                    LogicalType::parse("sequence<field:koala-bear>").unwrap(),
                    Representation::Sequence,
                    vec![ty],
                )
                .unwrap()
        } else {
            ty
        };
        if grant {
            builder
                .add_wire_permission(ty.clone(), WireCodec::Native)
                .unwrap();
        }
        let contracts = builder.finish(ExecutionPolicy::general_purpose());
        assert_eq!(contracts.permits_wire(&ty, WireCodec::Native), grant);
        // The selected verifier input is local data and never sent. Generic
        // admission accepts it, while proof-entry admission requires authority.
        let candidate = json!([
            "zkc.program/0",
            [],
            [],
            [
                [
                    "participant",
                    "p",
                    "root",
                    "P",
                    [["ok", BOOL]],
                    [],
                    [["send", "message", "message", "V", "ok"], ["return", []]],
                    []
                ],
                [
                    "participant",
                    "v",
                    "root",
                    "V",
                    [["selected", ty.spelling()]],
                    [BOOL],
                    [
                        ["receive", "message", "message", "P", "ok", BOOL],
                        ["return", ["ok"]]
                    ],
                    []
                ]
            ],
            [["entry", "main", [["P", "p"], ["V", "v"]]]]
        ]);
        let program = Program::decode(&bytes(&candidate), &contracts).unwrap();
        let result = NativeProofEntry::new(
            program,
            "main",
            "P",
            "V",
            0,
            ProofConstruction {
                suite: None,
                events: &[],
                plan: None,
                source_inputs: &Default::default(),
            },
        );
        if grant {
            assert!(result.is_ok(), "{result:?}");
        } else {
            assert_eq!(
                result.unwrap_err(),
                NativeProofError("native-proof-state-ports")
            );
        }
    }
}

#[test]
fn trusted_context_discovery_and_logical_constraints_are_independent_of_execution_permission() {
    let deploy = deployment(
        TimingRequirement::VariableTime,
        ExecutionPolicy::operand_independent(),
    );
    assert_eq!(
        deploy.contracts.installed_implementations(),
        vec![
            ("independent/field.add".into(), "field.add"),
            ("independent/field.equal".into(), "field.equal")
        ]
    );
    let add = declaration("add");
    let logical = deploy.contracts.logical_signature(&add).unwrap();
    assert_eq!(logical.inputs, vec![deploy.field.logical(); 2]);
    assert!(deploy.contracts.resolve(add.clone()).is_err());
    let mut wrong = add.clone();
    wrong.arguments = vec!["bls12-381.fr".into()];
    assert!(deploy.contracts.logical_signature(&wrong).is_err());
    wrong = add;
    wrong.physical_arguments = vec![deploy.field.spelling()];
    assert!(deploy.contracts.logical_signature(&wrong).is_err());
    assert!(
        ContractsBuilder::empty()
            .finish(ExecutionPolicy::general_purpose())
            .logical_signature(&declaration("add"))
            .is_err()
    );
}

#[test]
fn logical_aggregate_constraints_do_not_require_default_child_layouts() {
    let contracts = ContractsBuilder::standard().finish(ExecutionPolicy::operand_independent());
    let mut declaration = OperationBinding {
        contract: "sequence.empty".into(),
        arguments: vec!["fixed_vector<field:bls12-381.fr,2>".into()],
        implementation: String::new(),
        physical_arguments: vec![],
    };
    let logical = contracts.logical_signature(&declaration).unwrap();
    declaration.implementation = "native/sequence.empty".into();
    assert_eq!(contracts.logical_signature(&declaration).unwrap(), logical);
    assert!(contracts.resolve(declaration.clone()).is_err());
    declaration.implementation = "native/sequence.length".into();
    assert!(contracts.logical_signature(&declaration).is_err());
}

#[test]
fn physical_adapter_erasure_does_not_admit_a_logical_source_operation() {
    let contracts = Contracts::standard(ExecutionPolicy::general_purpose());
    for implementation in ["", "native/representation.convert"] {
        let binding = OperationBinding {
            contract: "representation.convert".into(),
            arguments: vec!["field:bls12-381.fr".into()],
            implementation: implementation.into(),
            physical_arguments: vec![],
        };
        assert!(contracts.logical_signature(&binding).is_err());
        assert!(binding.logical_signature().is_err());
    }
}
