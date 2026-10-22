//! Independent noncurve aggregate layouts, without Native values or providers.
use serde_json::{Value as Json, json};
use std::sync::Arc;
use zkc_runtime::{
    host::{
        joint::*,
        wire::{WireBackend, WireError},
    },
    interpreter::{LocalRunner, Runner},
    vm::*,
};
const BOOL: &str = "bool@native.bool/0";
const INDEX: &str = "index@native.index/0";
const SCALAR: &str = "control/koala-scalar";
const VECTOR: &str = "control/koala-vector";
const FIXED: &str = "control/koala-fixed";
#[derive(Clone, Debug, PartialEq, Eq)]
struct Scalar {
    ty: PhysicalType,
    value: u64,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Sequence {
    ty: PhysicalType,
    values: Vec<Datum>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Variant {
    ty: PhysicalType,
    alternative: usize,
    values: Vec<Datum>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Fixed {
    ty: PhysicalType,
    values: Vec<u64>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Datum {
    Bool(bool),
    Index(u64),
    Scalar(Arc<Scalar>),
    Sequence(Arc<Sequence>),
    Variant(Arc<Variant>),
    Fixed(Arc<Fixed>),
    Resource { ty: PhysicalType, generation: u64 },
}
impl Datum {
    fn sequence(ty: PhysicalType, values: Vec<Self>) -> Result<Self, BackendError> {
        let element = ty
            .sequence_element()
            .ok_or_else(|| BackendError::new("sequence-type"))?;
        if values.iter().any(|v| v.physical_type() != *element) {
            return Err(BackendError::new("sequence-element"));
        }
        Ok(Self::Sequence(Arc::new(Sequence { ty, values })))
    }
    fn owned_bytes(&self) -> usize {
        match self {
            Self::Bool(_) | Self::Index(_) => 8,
            Self::Resource { .. } => 64,
            _ => 0,
        }
    }
    fn aggregate_bytes<T>(ty: &PhysicalType, values: &[Self]) -> usize {
        std::mem::size_of::<T>()
            + ty.descriptor_bytes()
            + std::mem::size_of_val(values)
            + values.iter().map(Self::owned_bytes).sum::<usize>()
    }
}
impl Value for Datum {
    fn physical_type(&self) -> PhysicalType {
        match self {
            Self::Bool(_) => PhysicalType::parse(BOOL).unwrap(),
            Self::Index(_) => PhysicalType::parse(INDEX).unwrap(),
            Self::Scalar(v) => v.ty.clone(),
            Self::Sequence(v) => v.ty.clone(),
            Self::Variant(v) => v.ty.clone(),
            Self::Fixed(v) => v.ty.clone(),
            Self::Resource { ty, .. } => ty.clone(),
        }
    }
    fn pack_variant(
        ty: PhysicalType,
        alternative: usize,
        values: Vec<Self>,
    ) -> Result<Self, BackendError> {
        let expected = ty
            .variant_payload(alternative)
            .ok_or_else(|| BackendError::new("variant-alternative"))?;
        if expected.len() != values.len()
            || expected
                .iter()
                .zip(&values)
                .any(|(t, v)| *t != v.physical_type())
        {
            return Err(BackendError::new("variant-payload"));
        }
        Ok(Self::Variant(Arc::new(Variant {
            ty,
            alternative,
            values,
        })))
    }
    fn unpack_variant(&self) -> Result<(PhysicalType, usize, Vec<Self>), BackendError> {
        if let Self::Variant(v) = self {
            Ok((v.ty.clone(), v.alternative, v.values.clone()))
        } else {
            Err(BackendError::new("variant-type"))
        }
    }
    fn control_bool(&self) -> Result<bool, BackendError> {
        if let Self::Bool(v) = self {
            Ok(*v)
        } else {
            Err(BackendError::new("bool"))
        }
    }
    fn control_index(&self) -> Result<u64, BackendError> {
        if let Self::Index(v) = self {
            Ok(*v)
        } else {
            Err(BackendError::new("index"))
        }
    }
    fn from_control_bool(v: bool) -> Result<Self, BackendError> {
        Ok(Self::Bool(v))
    }
    fn from_control_index(v: u64) -> Result<Self, BackendError> {
        Ok(Self::Index(v))
    }
    fn preparation_parameter(&self) -> Option<Vec<u8>> {
        match self {
            Self::Bool(v) => Some(vec![u8::from(*v)]),
            Self::Index(v) => Some(v.to_le_bytes().to_vec()),
            _ => None,
        }
    }
    fn preparation_output(&self) -> bool {
        if self.physical_type().is_affine() {
            return false;
        }
        match self {
            Self::Resource { .. } => false,
            Self::Sequence(v) => v.values.iter().all(Value::preparation_output),
            Self::Variant(v) => {
                v.ty.children().unwrap().iter().all(|t| t.is_duplicable())
                    && v.values.iter().all(Value::preparation_output)
            }
            _ => true,
        }
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        if matches!(self, Self::Bool(_) | Self::Index(_)) {
            Ok(())
        } else {
            Err(BackendError::new("local-only-value"))
        }
    }
    fn retained_bytes(&self) -> usize {
        match self {
            Self::Scalar(v) => std::mem::size_of::<Scalar>() + v.ty.descriptor_bytes(),
            Self::Sequence(v) => {
                Self::aggregate_bytes::<Sequence>(&v.ty, &v.values)
                    + v.values
                        .iter()
                        .map(|c| c.retained_bytes() - c.owned_bytes())
                        .sum::<usize>()
            }
            Self::Variant(v) => {
                Self::aggregate_bytes::<Variant>(&v.ty, &v.values)
                    + v.values
                        .iter()
                        .map(|c| c.retained_bytes() - c.owned_bytes())
                        .sum::<usize>()
            }
            Self::Fixed(v) => {
                std::mem::size_of::<Fixed>() + v.ty.descriptor_bytes() + v.values.capacity() * 8
            }
            _ => self.owned_bytes(),
        }
    }
    fn retained_parts(&self, shared: &mut dyn FnMut(Backing) -> bool) -> usize {
        match self {
            Self::Scalar(v) => {
                shared(Backing::of(v, self.retained_bytes()));
            }
            Self::Fixed(v) => {
                shared(Backing::of(v, self.retained_bytes()));
            }
            Self::Sequence(v) => {
                if shared(Backing::of(
                    v,
                    Self::aggregate_bytes::<Sequence>(&v.ty, &v.values),
                )) {
                    for c in &v.values {
                        c.retained_parts(shared);
                    }
                }
            }
            Self::Variant(v) => {
                if shared(Backing::of(
                    v,
                    Self::aggregate_bytes::<Variant>(&v.ty, &v.values),
                )) {
                    for c in &v.values {
                        c.retained_parts(shared);
                    }
                }
            }
            _ => return self.owned_bytes(),
        }
        0
    }
}
#[derive(Clone)]
struct Operation {
    signature: BoundSignature,
    id: Option<ImplementationId>,
}
impl InstalledOperation for Operation {
    fn signature(&self) -> &BoundSignature {
        &self.signature
    }
    fn implementation_id(&self) -> Option<ImplementationId> {
        self.id
    }
    fn requirements(&self) -> ImplementationRequirements {
        ImplementationRequirements::default()
    }
    fn deterministic(&self) -> bool {
        true
    }
}
#[derive(Clone)]
struct Control {
    scalar: PhysicalType,
    fixed: PhysicalType,
    constant_id: ImplementationId,
    frames: Vec<FrameId>,
    calls: u64,
    generation: u64,
}
impl Backend for Control {
    type Value = Datum;
    type Operation = Operation;
    type Call = ();
    type Checkpoint = u64;
    fn computation_checkpoint(&self) -> Option<u64> {
        Some(self.calls)
    }
    fn replay_computation(&mut self, before: u64, after: u64) -> bool {
        self.calls += after - before;
        true
    }
    fn supports_boolean_literals(&self) -> bool {
        true
    }
    fn prepare_binding(&self, b: &OperationBinding) -> Option<Operation> {
        // Actual signatures are derived only from this adapter's own supported layouts.
        let (inputs, outputs, attributes, id) = if b.contract == "field.constant"
            && b.implementation == "control/field.constant"
            && b.arguments == ["koala-bear"]
            && b.physical_arguments.is_empty()
        {
            (
                vec![],
                vec![self.scalar.clone()],
                AttributeRule::KoalaBearDecimal,
                Some(self.constant_id),
            )
        } else if b.implementation == format!("native/{}", b.contract)
            && b.arguments == ["field:koala-bear"]
        {
            let sequence = match b.physical_arguments.as_slice() {
                [] => PhysicalType::parse("sequence<field:koala-bear>@logical.sequence/0").ok()?,
                [name] => {
                    let expected = PhysicalType::aggregate(
                        LogicalType::sequence(self.scalar.logical()).ok()?,
                        Representation::Sequence,
                        vec![self.scalar.clone()],
                    )
                    .ok()?;
                    if *name == expected.spelling() {
                        expected
                    } else {
                        return None;
                    }
                }
                _ => return None,
            };
            let element = sequence.sequence_element()?.clone();
            let index = PhysicalType::parse(INDEX).ok()?;
            let (inputs, outputs) = match b.contract.as_str() {
                "sequence.empty" => (vec![], vec![sequence]),
                "sequence.append" => (vec![sequence.clone(), element], vec![sequence]),
                "sequence.length" => (vec![sequence], vec![index]),
                "sequence.at" => (vec![sequence, index], vec![element]),
                _ => return None,
            };
            (inputs, outputs, AttributeRule::None, None)
        } else {
            return None;
        };
        Some(Operation {
            signature: BoundSignature {
                inputs,
                outputs,
                attributes,
            },
            id,
        })
    }
    fn validate_value(&self, v: &Datum) -> Result<(), BackendError> {
        match v {
            Datum::Scalar(v) if v.ty == self.scalar && v.value < 2_130_706_433 => Ok(()),
            Datum::Bool(_) | Datum::Index(_) => Ok(()),
            Datum::Resource { generation, .. } if *generation == self.generation => Ok(()),
            Datum::Resource { .. } => Err(BackendError::new("stale-resource")),
            Datum::Sequence(s) => {
                let element =
                    s.ty.sequence_element()
                        .ok_or_else(|| BackendError::new("sequence-type"))?;
                for v in &s.values {
                    if v.physical_type() != *element {
                        return Err(BackendError::new("sequence-element"));
                    }
                    self.validate_value(v)?;
                }
                Ok(())
            }
            Datum::Variant(s) => {
                let expected =
                    s.ty.variant_payload(s.alternative)
                        .ok_or_else(|| BackendError::new("variant-alternative"))?;
                if expected.len() != s.values.len() {
                    return Err(BackendError::new("variant-payload"));
                }
                for (t, v) in expected.iter().zip(&s.values) {
                    if v.physical_type() != *t {
                        return Err(BackendError::new("variant-payload"));
                    }
                    self.validate_value(v)?;
                }
                Ok(())
            }
            Datum::Fixed(v) if v.ty == self.fixed && v.values.len() == 2 => Ok(()),
            _ => Err(BackendError::new("unsupported-value")),
        }
    }
    fn enter_frame(&mut self, f: &Frame, args: &[Datum]) -> Result<(), BackendError> {
        for v in args {
            self.validate_value(v)?;
        }
        self.frames.push(f.id());
        Ok(())
    }
    fn leave_frame(&mut self, f: &Frame, _: FrameExit, args: &[Datum]) -> Result<(), BackendError> {
        assert_eq!(self.frames.pop(), Some(f.id()));
        for v in args {
            self.validate_value(v)?;
        }
        Ok(())
    }
    fn apply(
        &mut self,
        _: &Operation,
        invocation: &Invocation<'_>,
        args: &[Datum],
    ) -> Result<Vec<Datum>, BackendError> {
        self.calls += 1;
        let result = match (invocation.binding.declaration().contract.as_str(), args) {
            ("field.constant", []) => Datum::Scalar(Arc::new(Scalar {
                ty: self.scalar.clone(),
                value: invocation.attributes[0].parse().unwrap(),
            })),
            ("sequence.empty", []) => {
                Datum::sequence(invocation.binding.signature().outputs[0].clone(), vec![])?
            }
            ("sequence.append", [Datum::Sequence(sequence), value]) => {
                let mut values = sequence.values.clone();
                values.push(value.clone());
                Datum::sequence(sequence.ty.clone(), values)?
            }
            ("sequence.length", [Datum::Sequence(sequence)]) => {
                Datum::Index(sequence.values.len() as u64)
            }
            ("sequence.at", [Datum::Sequence(sequence), Datum::Index(i)]) => sequence
                .values
                .get(*i as usize)
                .cloned()
                .ok_or_else(|| BackendError::new("sequence-index"))?,
            _ => return Err(BackendError::new("unsupported-operation")),
        };
        Ok(vec![result])
    }
}
impl WireBackend for Control {
    fn supports_wire(&self, _: &PhysicalType) -> bool {
        false
    }
    fn encode_wire(&self, _: &Datum) -> Result<Vec<u8>, WireError> {
        Err(WireError::Limit)
    }
    fn decode_wire(&self, _: &PhysicalType, _: &[u8]) -> Result<Datum, WireError> {
        Err(WireError::Limit)
    }
}
struct Deployment {
    contracts: Contracts,
    backend: Control,
    sequence: PhysicalType,
    variant: PhysicalType,
}
fn deployment() -> Deployment {
    let mut builder = ContractsBuilder::standard();
    let scalar = builder
        .add_representation(SCALAR, LogicalType::parse("field:koala-bear").unwrap())
        .unwrap();
    let _vector = builder
        .add_representation(VECTOR, LogicalType::parse("vector:koala-bear").unwrap())
        .unwrap();
    let fixed_repr = builder
        .add_aggregate_representation(
            FIXED,
            Type::FixedVector,
            AggregateChildRule::Repeated {
                element: scalar.clone(),
                maximum_length: 1_048_576,
            },
        )
        .unwrap();
    let fixed = builder
        .aggregate_type(
            LogicalType::fixed_vector(scalar.logical(), 2).unwrap(),
            fixed_repr,
            vec![scalar.clone()],
        )
        .unwrap();
    let constant = OperationBinding {
        contract: "field.constant".into(),
        arguments: vec!["koala-bear".into()],
        implementation: "control/field.constant".into(),
        physical_arguments: vec![],
    };
    let constant_id = builder
        .add_implementation(
            constant,
            BoundSignature {
                inputs: vec![],
                outputs: vec![scalar.clone()],
                attributes: AttributeRule::KoalaBearDecimal,
            },
            ImplementationRequirements::default(),
        )
        .unwrap();
    let sequence = builder
        .aggregate_type(
            LogicalType::sequence(scalar.logical()).unwrap(),
            Representation::Sequence,
            vec![scalar.clone()],
        )
        .unwrap();
    let logical = LogicalType::parse(&zkc_test_support::variants::logical(
        "Control",
        json!([
            ["values", [sequence.logical().spelling()]],
            ["fixed", [fixed.logical().spelling()]]
        ]),
    ))
    .unwrap();
    let variant = builder
        .aggregate_type(
            logical,
            Representation::Variant,
            vec![sequence.clone(), fixed.clone()],
        )
        .unwrap();
    Deployment {
        contracts: builder.finish(ExecutionPolicy::general_purpose()),
        backend: Control {
            scalar,
            fixed,
            constant_id,
            frames: vec![],
            calls: 0,
            generation: 1,
        },
        sequence,
        variant,
    }
}
fn binding(
    contract: &str,
    implementation: &str,
    logical: &[&str],
    physical: Vec<String>,
) -> OperationBinding {
    OperationBinding {
        contract: contract.into(),
        arguments: logical.iter().map(|s| (*s).into()).collect(),
        implementation: implementation.into(),
        physical_arguments: physical,
    }
}
fn carrier(d: &Deployment) -> Json {
    let sequence = d.sequence.spelling();
    let variant = d.variant.spelling();
    json!([
        "zkc.program/0",
        [
            [
                "constant",
                "field.constant",
                ["koala-bear"],
                "control/field.constant",
                []
            ],
            [
                "empty",
                "sequence.empty",
                ["field:koala-bear"],
                "native/sequence.empty",
                [sequence]
            ],
            [
                "append",
                "sequence.append",
                ["field:koala-bear"],
                "native/sequence.append",
                [sequence]
            ],
            [
                "length",
                "sequence.length",
                ["field:koala-bear"],
                "native/sequence.length",
                [sequence]
            ]
        ],
        [[
            "function",
            "build",
            [["lower", INDEX], ["n", INDEX], ["c", BOOL]],
            [variant],
            [
                ["op", "empty", "empty", [], [], ["initial"]],
                ["op", "constant", "constant", ["7"], [], ["scalar"]],
                [
                    "for",
                    "repeat",
                    "i",
                    "lower",
                    "n",
                    [["state", "initial"]],
                    ["scalar"],
                    [
                        [
                            "op",
                            "repeat_append",
                            "append",
                            [],
                            ["state", "scalar"],
                            ["next"]
                        ],
                        ["yield", ["next"]]
                    ],
                    ["zero"]
                ],
                [
                    "if",
                    "branch",
                    "c",
                    ["zero", "scalar"],
                    [
                        ["op", "append", "append", [], ["zero", "scalar"], ["one"]],
                        ["yield", ["one"]]
                    ],
                    [["yield", ["zero"]]],
                    ["chosen"]
                ],
                ["variant", "pack", variant, "values", ["chosen"], "packed"],
                [
                    "match",
                    "inspect",
                    "packed",
                    [],
                    [
                        [
                            "values",
                            ["payload"],
                            [
                                ["op", "length", "length", [], ["payload"], ["size"]],
                                ["yield", ["payload"]]
                            ]
                        ],
                        ["fixed", ["payload"], [["stop", "inactive", "reject"]]]
                    ],
                    ["unpacked"]
                ],
                [
                    "variant",
                    "repack",
                    variant,
                    "values",
                    ["unpacked"],
                    "result"
                ],
                ["return", ["result"]]
            ],
            ["build", []]
        ]],
        [[
            "participant",
            "p",
            "root",
            "P",
            [["lower", INDEX], ["n", INDEX], ["c", BOOL]],
            [variant],
            [
                ["local", "build", "build", ["lower", "n", "c"], ["result"]],
                ["return", ["result"]]
            ],
            []
        ]],
        [["entry", "main", [["P", "p"]]]]
    ])
}
fn program(d: &Deployment) -> Program {
    Program::decode(&serde_json::to_vec(&carrier(d)).unwrap(), &d.contracts).unwrap()
}
fn runner(d: &Deployment, p: &Program, n: u64, condition: bool) -> Runner<Control> {
    Runner::new(
        p,
        "main",
        "P",
        "session",
        d.backend.clone(),
        vec![Datum::Index(0), Datum::Index(n), Datum::Bool(condition)],
    )
    .ok()
    .unwrap()
}
#[test]
fn selected_children_run_through_generic_control_and_shared_host() {
    let d = deployment();
    let p = program(&d);
    for n in [0, 1, 4] {
        for condition in [false, true] {
            let mut r = runner(&d, &p, n, condition);
            let Action::Local(action) = r.poll() else {
                panic!("local")
            };
            r.execute_local(&action.cut).unwrap();
            assert!(matches!(r.poll(), Action::Returned(_)));
            let values = r.returned_values().unwrap();
            assert_eq!(values[0].physical_type(), d.variant);
            let (_, _, payload) = values[0].unpack_variant().unwrap();
            let Datum::Sequence(sequence) = &payload[0] else {
                panic!("sequence")
            };
            assert_eq!(sequence.ty, d.sequence);
            assert_eq!(sequence.values.len(), n as usize + usize::from(condition));
        }
    }
    let bytes=serde_json::to_vec(&json!({"format":"zkc.run/0","candidate":String::from_utf8(p.bytes().to_vec()).unwrap(),"entry":"main","roles":["P"],"steps":[{"role":0,"instruction":0,"anchor":0},{"role":0,"instruction":1,"anchor":null}]})).unwrap();
    let bundle = Bundle::admit(&bytes, &d.backend, &d.contracts, BundleLimits::default()).unwrap();
    let report = run(
        &bundle,
        "session",
        vec![RoleInput {
            role: "P".into(),
            backend: d.backend.clone(),
            values: vec![Datum::Index(0), Datum::Index(3), Datum::Bool(true)],
        }],
        RunLimits::default(),
        &mut NoHooks,
    )
    .unwrap();
    assert_eq!(report.outcome, Outcome::Completed);
    assert_eq!(report.roles[0].outputs[0].physical_type(), d.variant);
}

#[test]
fn complete_layout_identity_canonical_elision_and_foreign_children() {
    let d = deployment();
    let foreign = deployment();
    assert!(std::mem::size_of::<LogicalType>() <= 40);
    assert!(std::mem::size_of::<PhysicalType>() <= 96);
    assert!(std::mem::size_of::<Datum>() <= 512);
    for ty in [&d.sequence, &d.variant, &d.backend.fixed] {
        assert_eq!(d.contracts.physical_type(&ty.spelling()).unwrap(), *ty);
        d.contracts.validate_type(ty).unwrap();
        assert!(foreign.contracts.validate_type(ty).is_err());
        assert!(PhysicalType::parse(&ty.spelling()).is_err());
    }
    let logical = d.variant.logical();
    let changed = d
        .contracts
        .aggregate_type(
            logical.clone(),
            Representation::Variant,
            vec![
                d.sequence.clone(),
                PhysicalType::default_for(d.backend.fixed.logical()).unwrap(),
            ],
        )
        .unwrap();
    assert_ne!(
        changed, d.variant,
        "inactive layouts participate in equality"
    );
    assert_eq!(changed.variant_payload(0), d.variant.variant_payload(0));
    assert!(
        d.contracts
            .aggregate_type(
                logical,
                Representation::Variant,
                vec![d.sequence.clone(), foreign.backend.fixed.clone()]
            )
            .is_err()
    );
    assert!(
        d.contracts
            .aggregate_type(
                d.sequence.logical(),
                Representation::Sequence,
                vec![PhysicalType::parse(INDEX).unwrap()]
            )
            .is_err()
    );
    assert!(
        d.contracts
            .aggregate_type(d.sequence.logical(), Representation::Sequence, vec![])
            .is_err()
    );
    assert!(
        d.contracts
            .aggregate_type(
                d.sequence.logical(),
                Representation::Sequence,
                vec![foreign.backend.scalar.clone()]
            )
            .is_err()
    );
    assert!(
        d.contracts
            .aggregate_type(
                d.backend.fixed.logical(),
                Representation::FixedVector,
                vec![d.backend.scalar.clone()]
            )
            .is_err()
    );
    for spelling in [
        "sequence<field:koala-bear>@logical.sequence/0[plonky3.koala-bear/0]",
        "sequence<field:koala-bear>@logical.sequence/0[]",
        "sequence<field:koala-bear>@logical.sequence/0[control/koala-scalar,control/koala-scalar]",
        "sequence<field:koala-bear>@logical.sequence/0[control/koala-scalar]extra",
        "sequence<field:koala-bear>@logical.sequence/0[ control/koala-scalar]",
        "field:koala-bear@control/koala-scalar[]",
    ] {
        assert!(d.contracts.physical_type(spelling).is_err(), "{spelling}");
    }
    let default = PhysicalType::parse("sequence<field:koala-bear>@logical.sequence/0").unwrap();
    assert_eq!(default.children().unwrap().len(), 1);
    assert_eq!(
        default.sequence_element().unwrap().representation(),
        Representation::KoalaBear
    );
    assert!(d.variant.descriptor_bytes() > d.variant.logical().descriptor_bytes());
    let mut spelling = String::from("bool@");
    spelling.push_str(&"a".repeat(1024 * 1024));
    assert!(d.contracts.physical_type(&spelling).is_err());
}

#[test]
fn specialization_is_separate_from_logical_arguments_and_defaults_are_one_choice() {
    let d = deployment();
    let selected = binding(
        "sequence.append",
        "native/sequence.append",
        &["field:koala-bear"],
        vec![d.sequence.spelling()],
    );
    let mut default = selected.clone();
    default.physical_arguments.clear();
    assert_eq!(
        selected.logical_signature().unwrap(),
        default.logical_signature().unwrap()
    );
    let a = d.contracts.resolve(selected.clone()).unwrap();
    let b = d.contracts.resolve(default).unwrap();
    assert_eq!(a.physical_arguments(), std::slice::from_ref(&d.sequence));
    assert_eq!(
        b.physical_arguments(),
        [PhysicalType::default_for(d.sequence.logical()).unwrap()]
    );
    assert_ne!(a.signature(), b.signature());
    assert_eq!(
        a.signature().inputs,
        [d.sequence.clone(), d.backend.scalar.clone()]
    );
    let mut malformed = selected.clone();
    malformed.physical_arguments = vec![d.backend.scalar.spelling()];
    assert!(malformed.logical_signature().is_ok());
    assert!(d.contracts.resolve(malformed).is_err());
    let mut extra = selected.clone();
    extra.physical_arguments.push(d.sequence.spelling());
    assert!(d.contracts.resolve(extra).is_err());
    let mut flat = binding(
        "field.add",
        "plonky3/field.add",
        &["koala-bear"],
        vec![d.backend.scalar.spelling()],
    );
    assert!(flat.logical_signature().is_ok());
    assert!(d.contracts.resolve(flat.clone()).is_err());
    flat.physical_arguments.clear();
    assert!(d.contracts.resolve(flat).is_ok());
    let direct = binding(
        "representation.convert",
        "control/representation.convert",
        &[&d.sequence.logical().spelling()],
        vec![
            PhysicalType::default_for(d.sequence.logical())
                .unwrap()
                .spelling(),
            d.sequence.spelling(),
        ],
    );
    assert!(
        d.contracts.resolve(direct).is_err(),
        "no lifted aggregate conversion law"
    );
    let mut bad = carrier(&d);
    bad[1][0].as_array_mut().unwrap().pop();
    assert_eq!(
        Program::decode(&serde_json::to_vec(&bad).unwrap(), &d.contracts)
            .unwrap_err()
            .code,
        ErrorCode::Record
    );
    let mut wrong = carrier(&d);
    wrong[1][2][4] = json!([]);
    assert!(
        Program::decode(&serde_json::to_vec(&wrong).unwrap(), &d.contracts).is_err(),
        "default append cannot consume selected sequence"
    );
}

#[test]
fn trusted_family_registration_is_bounded_scoped_and_uses_existing_inventory() {
    let mut b = ContractsBuilder::standard();
    let logical = LogicalType::parse("field:koala-bear").unwrap();
    let scalar = b.add_representation(SCALAR, logical).unwrap();
    let vector = b
        .add_representation(VECTOR, LogicalType::parse("vector:koala-bear").unwrap())
        .unwrap();
    let representation = b
        .add_aggregate_representation(
            FIXED,
            Type::FixedVector,
            AggregateChildRule::Repeated {
                element: scalar.clone(),
                maximum_length: 2,
            },
        )
        .unwrap();
    let fixed = b
        .aggregate_type(
            LogicalType::fixed_vector(scalar.logical(), 2).unwrap(),
            representation,
            vec![scalar.clone()],
        )
        .unwrap();
    assert!(
        b.aggregate_type(
            LogicalType::fixed_vector(scalar.logical(), 3).unwrap(),
            representation,
            vec![scalar.clone()]
        )
        .is_err()
    );
    let family = AggregateImplementationFamily::FixedVector {
        representation,
        scalar: scalar.clone(),
        vector,
    };
    let id = b
        .add_implementation_family(
            "fixed_vector.dot",
            "control/fixed_vector.dot",
            family.clone(),
            ImplementationRequirements::default(),
        )
        .unwrap();
    assert!(
        b.add_implementation_family(
            "fixed_vector.dot",
            "control/fixed_vector.dot",
            family.clone(),
            ImplementationRequirements::default()
        )
        .is_err()
    );
    assert!(
        b.add_implementation_family(
            "sequence.at",
            "control/wrong",
            family,
            ImplementationRequirements::default()
        )
        .is_err()
    );
    let contracts = b.finish(ExecutionPolicy::general_purpose());
    let declaration = binding(
        "fixed_vector.dot",
        "control/fixed_vector.dot",
        &["koala-bear", "2"],
        vec![fixed.spelling()],
    );
    let resolved = contracts.resolve(declaration.clone()).unwrap();
    assert_eq!(resolved.implementation_id(), Some(id));
    assert_eq!(resolved.signature().inputs, [fixed.clone(), fixed]);
    assert_eq!(resolved.signature().outputs, [scalar]);
    let mut default = declaration.clone();
    default.physical_arguments.clear();
    assert!(
        contracts.resolve(default).is_err(),
        "empty params select default storage, never contributed fallback"
    );
    let mut derived = declaration;
    derived.arguments[1] = "3".into();
    assert!(contracts.resolve(derived).is_err());
}

#[test]
fn aggregate_preparation_is_immutable_and_independent_of_wire_with_capacity_replay() {
    let d = deployment();
    let p = program(&d);
    let cache = PreparedComputations::new(&p, PreparationLimits::default());
    let mut baseline = None;
    for warm in [false, true] {
        let mut r = runner(&d, &p, 3, true);
        r.prepare_computations(cache.clone(), &[0, 1, 2]).unwrap();
        let Action::Local(action) = r.poll() else {
            panic!("local")
        };
        r.execute_local(&action.cut).unwrap();
        assert!(matches!(r.poll(), Action::Returned(_)));
        assert!(
            r.returned_values().unwrap()[0]
                .validate_serializable()
                .is_err()
        );
        assert_eq!(cache.stats().entries, 1);
        assert_eq!(cache.stats().hits, u64::from(warm));
        let current = (
            r.usage(),
            r.backend().calls,
            r.returned_values().unwrap().to_vec(),
        );
        if let Some(previous) = &baseline {
            assert_eq!(&current, previous)
        } else {
            baseline = Some(current)
        }
    }
    let mut limited = Runner::new_with_budgets(
        &p,
        "main",
        "P",
        "session",
        d.backend.clone(),
        vec![Datum::Index(0), Datum::Index(3), Datum::Bool(true)],
        ValueBudget::default(),
        WorkBudget {
            instructions: 2,
            ..WorkBudget::default()
        },
    )
    .ok()
    .unwrap();
    limited
        .prepare_computations(cache.clone(), &[0, 1, 2])
        .unwrap();
    let Action::Local(action) = limited.poll() else {
        panic!("local")
    };
    limited.execute_local(&action.cut).unwrap();
    assert!(matches!(limited.poll(),Action::Stopped(s) if s.kind==StopKind::Limit));
    assert_eq!(cache.stats().hits, 1);
}

fn local_echo(contracts: &Contracts, ty: &PhysicalType) -> Program {
    Program::decode(
        &serde_json::to_vec(&json!([
            "zkc.program/0",
            [],
            [[
                "function",
                "echo",
                [["x", ty.spelling()]],
                [ty.spelling()],
                [["return", ["x"]]],
                ["echo", []]
            ]],
            [],
            []
        ]))
        .unwrap(),
        contracts,
    )
    .unwrap()
}
#[test]
fn malformed_and_stale_nested_values_refuse_without_resource_reissuance() {
    let d = deployment();
    let p = local_echo(&d.contracts, &d.variant);
    let malformed = Datum::Variant(Arc::new(Variant {
        ty: d.variant.clone(),
        alternative: 0,
        values: vec![Datum::Bool(true)],
    }));
    assert!(LocalRunner::new(&p, "echo", "session", d.backend.clone(), vec![malformed]).is_err());
    let active_fixed = Datum::Fixed(Arc::new(Fixed {
        ty: d.backend.fixed.clone(),
        values: vec![1, 2],
    }));
    let packed = Datum::pack_variant(d.variant.clone(), 1, vec![active_fixed]).unwrap();
    let mut local = LocalRunner::new(
        &p,
        "echo",
        "session",
        d.backend.clone(),
        vec![packed.clone()],
    )
    .ok()
    .unwrap();
    assert!(matches!(local.execute(), Action::Returned(_)));
    let logical = LogicalType::parse(&zkc_test_support::variants::logical(
        "Resource",
        json!([["active", ["resource_unit:Aggregate"]], ["empty", []]]),
    ))
    .unwrap();
    let resource =
        PhysicalType::default_for(LogicalType::parse("resource_unit:Aggregate").unwrap()).unwrap();
    let ty = d
        .contracts
        .aggregate_type(logical, Representation::Variant, vec![resource.clone()])
        .unwrap();
    let p = local_echo(&d.contracts, &ty);
    let value = Datum::pack_variant(
        ty.clone(),
        0,
        vec![Datum::Resource {
            ty: resource.clone(),
            generation: 1,
        }],
    )
    .unwrap();
    assert!(!value.preparation_output());
    let mut local = LocalRunner::new(
        &p,
        "echo",
        "session",
        d.backend.clone(),
        vec![value.clone()],
    )
    .ok()
    .unwrap();
    assert!(matches!(local.execute(), Action::Returned(_)));
    assert_eq!(local.returned_values().unwrap(), [value]);
    let stale = Datum::pack_variant(
        ty,
        0,
        vec![Datum::Resource {
            ty: resource,
            generation: 0,
        }],
    )
    .unwrap();
    let rejected = LocalRunner::new(&p, "echo", "session", d.backend.clone(), vec![stale])
        .err()
        .unwrap();
    assert!(matches!(rejected.error,RuntimeError::Backend(e) if e.code=="stale-resource"));
    assert_eq!(d.backend.generation, 1);
}

#[test]
fn wire_checks_all_children_and_preserves_local_only_fixed_vectors() {
    let d = deployment();
    let mut b = ContractsBuilder::standard();
    let scalar = b
        .add_representation(SCALAR, LogicalType::parse("field:koala-bear").unwrap())
        .unwrap();
    let sequence = b
        .aggregate_type(
            d.sequence.logical(),
            Representation::Sequence,
            vec![scalar.clone()],
        )
        .unwrap();
    let denied = b.finish(ExecutionPolicy::general_purpose());
    assert!(!denied.permits_wire(&sequence, WireCodec::Native));
    let mut b = ContractsBuilder::standard();
    let scalar = b
        .add_representation(SCALAR, LogicalType::parse("field:koala-bear").unwrap())
        .unwrap();
    b.add_wire_permission(scalar.clone(), WireCodec::Native)
        .unwrap();
    let sequence = b
        .aggregate_type(d.sequence.logical(), Representation::Sequence, vec![scalar])
        .unwrap();
    let logical = LogicalType::parse(&zkc_test_support::variants::logical(
        "Wire",
        json!([
            ["values", [sequence.logical().spelling()]],
            ["fixed", ["fixed_vector<field:koala-bear,2>"]]
        ]),
    ))
    .unwrap();
    let variant = b
        .aggregate_type(
            logical,
            Representation::Variant,
            vec![
                sequence.clone(),
                PhysicalType::parse("fixed_vector<field:koala-bear,2>@plonky3.fixed-vector/0")
                    .unwrap(),
            ],
        )
        .unwrap();
    let contracts = b.finish(ExecutionPolicy::general_purpose());
    contracts.validate_type(&variant).unwrap();
    assert!(contracts.validate_type(&d.variant).is_err());
    assert!(contracts.permits_wire(&sequence, WireCodec::Native));
    assert!(
        !contracts.permits_wire(&variant, WireCodec::Native),
        "inactive fixed vectors have no Native frame"
    );
    assert!(
        !contracts.permits_wire(&d.sequence, WireCodec::Native),
        "foreign scoped leaf permission"
    );
}

#[test]
fn empty_catalog_wire_requires_parent_authority_and_every_child() {
    for parent in [false, true] {
        for leaf in [false, true] {
            let mut b = ContractsBuilder::empty();
            let scalar = b
                .add_representation(SCALAR, LogicalType::parse("field:koala-bear").unwrap())
                .unwrap();
            let sequence = b
                .aggregate_type(
                    LogicalType::parse("sequence<field:koala-bear>").unwrap(),
                    Representation::Sequence,
                    vec![scalar.clone()],
                )
                .unwrap();
            let variant = b
                .aggregate_type(
                    LogicalType::parse(&zkc_test_support::variants::logical(
                        "EmptyWire",
                        json!([
                            ["flag", ["bool"]],
                            ["inactive", [sequence.logical().spelling()]]
                        ]),
                    ))
                    .unwrap(),
                    Representation::Variant,
                    vec![PhysicalType::parse(BOOL).unwrap(), sequence.clone()],
                )
                .unwrap();
            if leaf {
                b.add_wire_permission(scalar, WireCodec::Native).unwrap();
            }
            if parent {
                b.add_wire_permission(sequence.clone(), WireCodec::Native)
                    .unwrap();
                b.add_wire_permission(variant.clone(), WireCodec::Native)
                    .unwrap();
            }
            let contracts = b.finish(ExecutionPolicy::general_purpose());
            for ty in [&sequence, &variant] {
                assert_eq!(
                    contracts.permits_wire(ty, WireCodec::Native),
                    parent && leaf
                );
            }
        }
    }
    for grant in [false, true] {
        let mut b = ContractsBuilder::empty();
        let scalar = b
            .add_representation(SCALAR, LogicalType::parse("field:koala-bear").unwrap())
            .unwrap();
        b.add_wire_permission(scalar.clone(), WireCodec::Native)
            .unwrap();
        let storage = b
            .add_aggregate_representation(
                "control/sequence",
                Type::Sequence,
                AggregateChildRule::AnyAdmitted,
            )
            .unwrap();
        let sequence = b
            .aggregate_type(
                LogicalType::parse("sequence<field:koala-bear>").unwrap(),
                storage,
                vec![scalar],
            )
            .unwrap();
        if grant {
            b.allow_aggregate_native_message(storage).unwrap();
        }
        let contracts = b.finish(ExecutionPolicy::general_purpose());
        assert_eq!(contracts.permits_wire(&sequence, WireCodec::Native), grant);
    }
}

#[test]
fn contributed_storage_names_use_the_shared_identifier_grammar() {
    let mut b = ContractsBuilder::empty();
    for name in [
        "",
        "0bad",
        "bad:layout",
        "bad<layout>",
        "bad@layout",
        "bad layout",
        "bad[layout]",
        "bad,layout",
        "bad\\layout",
        "é",
    ] {
        assert_eq!(
            b.add_representation(name, LogicalType::parse("field:koala-bear").unwrap())
                .unwrap_err()
                .detail,
            "representation-identity"
        );
        assert_eq!(
            b.add_aggregate_representation(name, Type::Sequence, AggregateChildRule::AnyAdmitted)
                .unwrap_err()
                .detail,
            "representation-identity"
        );
    }
}

#[test]
fn constructed_layouts_roundtrip_at_the_exact_physical_spelling_limit() {
    const NAME_BYTES: [u8; 256] = [b'a'; 256];
    let name: &'static str = std::str::from_utf8(&NAME_BYTES).unwrap();
    let mut b = ContractsBuilder::empty();
    let element = LogicalType::parse("field:koala-bear").unwrap();
    let long = b.add_representation(name, element.clone()).unwrap();
    assert!(
        b.add_representation(
            concat!(
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
            ),
            element.clone()
        )
        .is_err()
    );
    let short = b.add_representation("x", element.clone()).unwrap();
    let longer = b.add_representation("xx", element.clone()).unwrap();
    let alternatives: Vec<_> = (0..32)
        .map(|i| json!([format!("arm_{i}"), vec!["field:koala-bear"; 128]]))
        .collect();
    let logical = LogicalType::parse(&zkc_test_support::variants::logical(
        "SpellingBoundary",
        json!(alternatives),
    ))
    .unwrap();
    let count = 32 * 128;
    let mut children = vec![long; count];
    assert_eq!(
        b.aggregate_type(logical.clone(), Representation::Variant, children.clone())
            .unwrap_err()
            .detail,
        "physical type spelling limit"
    );
    let limit = 1024 * 1024;
    let base =
        logical.spelling().len() + 1 + Representation::Variant.name().len() + 2 + count * 257 - 1;
    let reduction = base - limit;
    assert!(reduction >= 255);
    for child in &mut children[..reduction / 255] {
        *child = short.clone();
    }
    if !reduction.is_multiple_of(255) {
        children[reduction / 255] = b
            .add_representation(&name[..256 - reduction % 255], element)
            .unwrap();
    }
    let ty = b
        .aggregate_type(logical.clone(), Representation::Variant, children.clone())
        .unwrap();
    assert_eq!(ty.spelling().len(), limit);
    children[0] = longer;
    assert_eq!(
        b.aggregate_type(logical, Representation::Variant, children)
            .unwrap_err()
            .detail,
        "physical type spelling limit"
    );
    let contracts = b.finish(ExecutionPolicy::general_purpose());
    let spelling = ty.spelling();
    assert_eq!(contracts.physical_type(&spelling).unwrap(), ty);
    let prefix = "@logical.variant/0[";
    let mut oversized = spelling;
    oversized.insert(oversized.find(prefix).unwrap() + prefix.len(), 'x');
    assert_eq!(oversized.len(), limit + 1);
    assert_eq!(
        contracts.physical_type(&oversized).unwrap_err().detail,
        "physical type spelling limit"
    );
}
