//! Typed literal preparation through real Runner frames and boundary probes.
#[path = "vector_literal_tests.rs"]
mod vectors;
use super::{CallBinding, CallPayload, CpuCall};
use crate::operations::field::LITERAL_DECODES;
use crate::{CpuBackend, CpuOperation, Domain, EntryPolicy, Policy, Result, Value};
use serde_json::{Value as Json, json};
use std::sync::Arc;
use zkc_runtime::interpreter::Runner;
use zkc_runtime::vm::{
    Action, Backend, BoundSignature, CallContext, Frame, FrameExit, FrameKind, Identity,
    Invocation, LocalContext, OperationBinding, Origin, PathElement, PhysicalType, Program, Stop,
    StopKind, Usage, Value as RuntimeValue, ValueBudget, WorkBudget,
};

fn backend() -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        Default::default(),
    )
    .unwrap()
}

fn binding(field: &str, name: &str) -> OperationBinding {
    let provider = match field {
        "bls12-381.fr" | "bn254.fr" => "arkworks",
        "ristretto255.scalar" => "dalek",
        _ => "plonky3",
    };
    OperationBinding {
        contract: name.into(),
        arguments: vec![field.into()],
        implementation: format!("{provider}/{name}"),
        physical_arguments: vec![],
    }
}

// Same carrier and Runner-minted-frame pattern as tests/domains/support.rs.
fn program(
    bindings: &[OperationBinding],
    inputs: &[PhysicalType],
    mut operations: Vec<Json>,
    outputs: &[PhysicalType],
    returns: &[String],
) -> Vec<u8> {
    let ports: Vec<_> = inputs
        .iter()
        .enumerate()
        .map(|(i, t)| json!([format!("a{i}"), t.spelling()]))
        .collect();
    let names: Vec<_> = (0..inputs.len()).map(|i| format!("a{i}")).collect();
    let types: Vec<_> = outputs.iter().map(PhysicalType::spelling).collect();
    let result_names: Vec<_> = (0..outputs.len()).map(|i| format!("result{i}")).collect();
    let rows: Vec<_> = bindings
        .iter()
        .enumerate()
        .map(|(i, b)| {
            json!([
                format!("b{i}"),
                b.contract,
                b.arguments,
                b.implementation,
                b.physical_arguments
            ])
        })
        .collect();
    operations.push(json!(["return", returns]));
    serde_json::to_vec(&json!([
        "zkc.program/0",
        rows,
        [[
            "function",
            "testfn",
            ports,
            types,
            operations,
            ["testfn", []]
        ]],
        [[
            "participant",
            "actor",
            "instance",
            "P",
            ports,
            types,
            [
                ["local", "local", "testfn", names, result_names],
                ["return", result_names]
            ],
            []
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]))
    .unwrap()
}

struct Caller {
    inner: CpuBackend,
    call: Option<CpuCall>,
    prepared: bool,
    attributes: Option<Vec<String>>,
    arguments: Option<Vec<Value>>,
    operation: Option<OperationBinding>,
    signature: Option<BoundSignature>,
    output_limit: Option<usize>,
    attempts: usize,
    leaves: Vec<(FrameKind, FrameExit)>,
    cleanup_error: bool,
    revoke: bool,
}
impl Caller {
    fn new(prepared: bool) -> Self {
        Self {
            inner: backend(),
            call: None,
            prepared,
            attributes: None,
            arguments: None,
            operation: None,
            signature: None,
            output_limit: None,
            attempts: 0,
            leaves: vec![],
            cleanup_error: false,
            revoke: false,
        }
    }
}
impl Backend for Caller {
    type Value = Value;
    type Operation = CpuOperation;
    type Call = ();
    type Checkpoint = ();
    fn prepare_binding(&self, binding: &OperationBinding) -> Option<CpuOperation> {
        self.inner.prepare_binding(binding)
    }
    fn validate_value(&self, value: &Value) -> Result<()> {
        self.inner.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, args: &[Value]) -> Result<()> {
        self.inner.enter_frame(frame, args)
    }
    fn leave_frame(&mut self, frame: &Frame, exit: FrameExit, outputs: &[Value]) -> Result<()> {
        self.leaves.push((frame.kind().clone(), exit));
        self.inner.leave_frame(frame, exit, outputs)?;
        if self.cleanup_error && matches!(frame.kind(), FrameKind::Local { .. }) {
            return Err(crate::refused("literal-test-cleanup"));
        }
        Ok(())
    }
    fn apply(
        &mut self,
        operation: &CpuOperation,
        i: &Invocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>> {
        if !matches!(
            i.binding.declaration().contract.as_str(),
            "field.constant" | "vector.constant"
        ) {
            return self.inner.apply(operation, i, args);
        }
        self.attempts += 1;
        let replacement = (self.operation.is_some() || self.signature.is_some()).then(|| {
            let mut replacement = self
                .inner
                .prepare_binding(self.operation.as_ref().unwrap_or(i.binding.declaration()))
                .expect("installed test binding");
            if let Some(signature) = &self.signature {
                Arc::make_mut(&mut replacement.binding).signature = signature.clone();
            }
            replacement
        });
        let operation = replacement.as_ref().unwrap_or(operation);
        if self.revoke {
            self.inner.contracts = self
                .inner
                .contracts
                .with_policy(zkc_runtime::vm::ExecutionPolicy::operand_independent());
        }
        let i = Invocation {
            context: CallContext {
                attributes: self.attributes.as_deref().unwrap_or(i.attributes),
                ..i.context
            },
            max_output_bytes: self.output_limit.unwrap_or(i.max_output_bytes),
            ..*i
        };
        let args = self.arguments.as_deref().unwrap_or(args);
        if self.prepared {
            self.inner
                .apply_prepared(operation, &mut self.call, &i, args)
        } else {
            self.inner.apply(operation, &i, args)
        }
    }
}

fn run<B: Backend<Value = Value>>(
    caller: B,
    bytes: &[u8],
    args: Vec<Value>,
    values: ValueBudget,
    work: WorkBudget,
) -> (std::result::Result<Vec<Value>, Stop>, Usage, B) {
    let admitted = Program::decode(bytes, crate::cpu_contracts()).unwrap();
    admitted.check_installation(&caller).unwrap();
    let mut runner = Runner::new_with_budgets(
        &admitted, "main", "P", "session", caller, args, values, work,
    )
    .unwrap_or_else(|e| panic!("{}", e.error));
    for _ in 0..100 {
        match runner.poll() {
            Action::Local(action) => runner.execute_local(&action.cut).unwrap(),
            Action::Returned(values) => return (Ok(values), runner.usage(), runner.into_backend()),
            Action::Stopped(stop) => return (Err(stop), runner.usage(), runner.into_backend()),
            other => panic!("unexpected {other:?}"),
        }
    }
    panic!("test driver limit")
}

fn one(caller: Caller, field: &str, text: &str) -> (std::result::Result<Vec<Value>, Stop>, Caller) {
    let b = binding(field, "field.constant");
    let signature = b.signature().unwrap();
    let bytes = program(
        &[b],
        &[],
        vec![json!(["op", "literal", "b0", [text], [], ["n"]])],
        &signature.outputs,
        &["n".into()],
    );
    let (result, _, caller) = run(
        caller,
        &bytes,
        vec![],
        Default::default(),
        Default::default(),
    );
    assert_eq!(caller.inner.active_frames(), 0);
    (result, caller)
}

fn code(stop: &Stop) -> &str {
    let StopKind::Backend(error) = &stop.kind else {
        panic!("unexpected {stop:?}")
    };
    &error.code
}

fn equal(actual: &Value, expected: &Value) {
    assert_eq!(actual.physical_type(), expected.physical_type());
    let b = backend();
    assert_eq!(
        b.encode_native_value(actual).unwrap(),
        b.encode_native_value(expected).unwrap()
    );
}

struct FieldCase {
    field: &'static str,
    maximum: &'static str,
    value: Value,
    overflow: &'static str,
    error: &'static str,
}
fn cases() -> Vec<FieldCase> {
    use p3_field::PrimeCharacteristicRing;
    vec![
        FieldCase {
            field: "bls12-381.fr",
            maximum: "52435875175126190479447740508185965837690552500527637822603658699938581184512",
            value: Value::Field(-crate::Scalar::from(1)),
            overflow: zkc_kernels::arkworks::bls12_381::SCALAR_MODULUS_DECIMAL,
            error: "refused:invalid-encoding",
        },
        FieldCase {
            field: "bn254.fr",
            maximum: "21888242871839275222246405745257275088548364400416034343698204186575808495616",
            value: Value::Bn254Field(-crate::Bn254Scalar::from(1)),
            overflow: zkc_kernels::arkworks::bn254::MODULUS,
            error: "refused:noncanonical-encoding",
        },
        FieldCase {
            field: "ristretto255.scalar",
            maximum: "7237005577332262213973186563042994240857116359379907606001950938285454250988",
            value: Value::RistrettoField(-crate::RistrettoScalar::ONE),
            overflow: zkc_kernels::dalek::ristretto255::SCALAR_MODULUS_DECIMAL,
            error: "refused:noncanonical-scalar",
        },
        FieldCase {
            field: "koala-bear",
            maximum: "2130706432",
            value: Value::KoalaBearField(-crate::KoalaBear::ONE),
            overflow: "2130706433",
            error: "refused:noncanonical-scalar",
        },
        FieldCase {
            field: "koala-bear.ext4-binomial3",
            maximum: "2130706432",
            value: Value::KoalaBearExt4Field(-crate::KoalaBearExt4::ONE),
            overflow: "2130706433",
            error: "refused:noncanonical-scalar",
        },
        FieldCase {
            field: "koala-bear.ext8-binomial3",
            maximum: "2130706432",
            value: Value::KoalaBearExt8Field(-crate::KoalaBearExt8::ONE),
            overflow: "2130706433",
            error: "refused:noncanonical-scalar",
        },
        FieldCase {
            field: "gf2-64.pentanomial-4-3-1",
            maximum: "0xffffffffffffffff",
            value: Value::Binary64Field(zkc_kernels::plonky3::binary::from_bits(u64::MAX)),
            overflow: "0x10000000000000000",
            error: "refused:noncanonical-scalar",
        },
        FieldCase {
            field: "gf2-64.pentanomial-4-3-1.ext3-trinomial1",
            maximum: "0xffffffffffffffffffffffffffffffffffffffffffffffff",
            value: Value::Binary64Ext3Field(zkc_kernels::plonky3::binary::ext3_from_bits(
                [u64::MAX; 3],
            )),
            overflow: "0x1000000000000000000000000000000000000000000000000",
            error: "refused:noncanonical-scalar",
        },
    ]
}

fn small(field: &str, one: bool) -> Value {
    use p3_field::PrimeCharacteristicRing;
    let n = u64::from(one);
    match field {
        "bls12-381.fr" => Value::Field(crate::Scalar::from(n)),
        "bn254.fr" => Value::Bn254Field(crate::Bn254Scalar::from(n)),
        "ristretto255.scalar" => Value::RistrettoField(crate::RistrettoScalar::from(n)),
        "koala-bear" => Value::KoalaBearField(crate::KoalaBear::from_u64(n)),
        "koala-bear.ext4-binomial3" => Value::KoalaBearExt4Field(crate::KoalaBearExt4::from_u64(n)),
        "koala-bear.ext8-binomial3" => Value::KoalaBearExt8Field(crate::KoalaBearExt8::from_u64(n)),
        "gf2-64.pentanomial-4-3-1" => {
            Value::Binary64Field(zkc_kernels::plonky3::binary::from_bits(n))
        }
        "gf2-64.pentanomial-4-3-1.ext3-trinomial1" => {
            Value::Binary64Ext3Field(zkc_kernels::plonky3::binary::ext3_from_bits([n, 0, 0]))
        }
        _ => panic!("unexpected test field"),
    }
}

// Use the VM's real per-site slots while observing the installed owner and the
// returned scalar. The ordinary Caller above deliberately probes one reused slot.
struct RecordingBackend {
    inner: CpuBackend,
    reached: Vec<(String, Arc<CallBinding>, Value)>,
}
impl Backend for RecordingBackend {
    type Value = Value;
    type Operation = CpuOperation;
    type Call = CpuCall;
    type Checkpoint = ();

    fn prepare_binding(&self, binding: &OperationBinding) -> Option<CpuOperation> {
        self.inner.prepare_binding(binding)
    }
    fn validate_value(&self, value: &Value) -> Result<()> {
        self.inner.validate_value(value)
    }
    fn enter_frame(&mut self, frame: &Frame, args: &[Value]) -> Result<()> {
        self.inner.enter_frame(frame, args)
    }
    fn leave_frame(&mut self, frame: &Frame, exit: FrameExit, outputs: &[Value]) -> Result<()> {
        self.inner.leave_frame(frame, exit, outputs)
    }
    fn apply(
        &mut self,
        operation: &CpuOperation,
        i: &Invocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>> {
        self.inner.apply(operation, i, args)
    }
    fn apply_prepared(
        &mut self,
        operation: &CpuOperation,
        call: &mut Option<CpuCall>,
        i: &Invocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>> {
        let outputs = self.inner.apply_prepared(operation, call, i, args)?;
        let CallPayload::Literal(literal) = &call.as_ref().unwrap().payload else {
            panic!("prepared literal");
        };
        assert!(Arc::ptr_eq(&literal.binding, &operation.binding));
        self.reached.push((
            i.site.into(),
            Arc::clone(&literal.binding),
            outputs[0].clone(),
        ));
        Ok(outputs)
    }
}

#[test]
fn distinct_literal_sites_share_installed_metadata_and_keep_instance_preparation_independent() {
    let index = Value::Index(0).physical_type();
    let bytes = program(
        &[binding("koala-bear", "field.constant")],
        &[index.clone(), index],
        vec![json!([
            "for",
            "repeat",
            "i",
            "a0",
            "a1",
            [],
            [],
            [
                ["op", "zero", "b0", ["0"], [], ["z"]],
                ["op", "one", "b0", ["1"], [], ["o"]],
                ["yield", []]
            ],
            []
        ])],
        &[],
        &[],
    );
    let admitted = Program::decode(&bytes, crate::cpu_contracts()).unwrap();
    LITERAL_DECODES.set(0);
    let mut runners: Vec<_> = (0..2)
        .map(|_| {
            Runner::new(
                &admitted,
                "main",
                "P",
                "session",
                RecordingBackend {
                    inner: backend(),
                    reached: vec![],
                },
                vec![Value::Index(0), Value::Index(3)],
            )
            .unwrap_or_else(|e| panic!("{}", e.error))
        })
        .collect();
    // Installing both instances must leave even valid literal attributes dormant.
    assert_eq!(LITERAL_DECODES.get(), 0);
    let mut observations = vec![];
    for (instance, runner) in runners.iter_mut().enumerate() {
        loop {
            match runner.poll() {
                Action::Local(action) => runner.execute_local(&action.cut).unwrap(),
                Action::Returned(values) => {
                    assert!(values.is_empty());
                    break;
                }
                other => panic!("unexpected {other:?}"),
            }
        }
        assert_eq!(LITERAL_DECODES.get(), 2 * (instance + 1));
    }
    for runner in runners {
        let recorder = runner.into_backend();
        assert_eq!(recorder.inner.active_frames(), 0);
        assert_eq!(recorder.reached.len(), 6);
        for (visit, (site, owner, value)) in recorder.reached.iter().enumerate() {
            assert_eq!(site, if visit % 2 == 0 { "zero" } else { "one" });
            equal(value, &small("koala-bear", visit % 2 == 1));
            assert!(Arc::ptr_eq(owner, &recorder.reached[0].1));
        }
        observations.push(recorder.reached);
    }
    assert!(!Arc::ptr_eq(&observations[0][0].1, &observations[1][0].1));
    assert!(observations[0][0].1 == observations[1][0].1);
}

#[test]
fn separately_installed_equal_literal_metadata_reuses_the_retained_value() {
    let declaration = binding("koala-bear", "field.constant");
    let first = backend().prepare_binding(&declaration).unwrap();
    let second = backend().prepare_binding(&declaration).unwrap();
    assert!(!Arc::ptr_eq(&first.binding, &second.binding));
    let mut slot = None;
    let attributes = ["1".into()];
    LITERAL_DECODES.set(0);
    CpuCall::prepare_literal(
        &mut slot,
        &first.binding,
        &attributes,
        &Policy::default(),
        usize::MAX,
    )
    .unwrap();
    let value = std::ptr::from_ref(slot.as_ref().unwrap().literal().unwrap());
    CpuCall::prepare_literal(
        &mut slot,
        &second.binding,
        &attributes,
        &Policy::default(),
        usize::MAX,
    )
    .unwrap();
    assert_eq!(LITERAL_DECODES.get(), 1);
    assert_eq!(
        value,
        std::ptr::from_ref(slot.as_ref().unwrap().literal().unwrap())
    );
    equal(
        slot.as_ref().unwrap().literal().unwrap(),
        &small("koala-bear", true),
    );
}

#[test]
fn all_scalar_families_decode_once_per_retained_key_and_once_per_direct_call() {
    for case in cases() {
        for prepared in [false, true] {
            let mut caller = Caller::new(prepared);
            for (text, expected) in [
                ("0", small(case.field, false)),
                ("1", small(case.field, true)),
                (case.maximum, case.value.clone()),
            ] {
                LITERAL_DECODES.set(0);
                for visit in 1..=3 {
                    let (result, next) = one(caller, case.field, text);
                    equal(&result.unwrap()[0], &expected);
                    caller = next;
                    assert_eq!(caller.call.is_some(), prepared);
                    assert_eq!(LITERAL_DECODES.get(), if prepared { 1 } else { visit });
                }
            }
        }
    }
}

#[test]
fn decoder_counter_covers_attribute_validation_as_well_as_ordinary_decode() {
    for case in cases() {
        let b = binding(case.field, "field.constant");
        let attributes = [case.maximum.into()];
        LITERAL_DECODES.set(0);
        CpuCall::check(b.signature().unwrap().attributes, &attributes).unwrap();
        assert_eq!(LITERAL_DECODES.get(), 1);
        crate::operations::field::decode_literal(
            b.signature().unwrap().outputs[0].logical().identity(),
            &attributes,
        )
        .unwrap();
        assert_eq!(LITERAL_DECODES.get(), 2);
    }
}

#[test]
fn failed_replacement_keeps_old_slot_but_never_returns_its_scalar() {
    for case in cases() {
        for prepared in [false, true] {
            let (result, mut caller) = one(Caller::new(prepared), case.field, "1");
            result.unwrap();
            let old = caller
                .call
                .as_ref()
                .map(|call| std::ptr::from_ref(call.literal().unwrap()));
            for attributes in [
                vec![],
                vec!["1", "0"],
                vec![""],
                vec!["00"],
                vec!["+1"],
                vec!["-1"],
                vec!["1 "],
                vec!["１"],
                vec![case.overflow],
            ] {
                let arity = attributes.len();
                caller.attributes = Some(attributes.into_iter().map(String::from).collect());
                caller.output_limit = Some(0);
                let (result, mut next) = one(caller, case.field, "1");
                let stop = result.unwrap_err();
                assert_eq!(
                    code(&stop),
                    if arity == 1 {
                        case.error
                    } else {
                        "refused:kernel-attributes"
                    }
                );
                assert!(stop.cleanup_errors.is_empty());
                assert_eq!(
                    next.call
                        .as_ref()
                        .map(|call| std::ptr::from_ref(call.literal().unwrap())),
                    old
                );
                next.attributes = None;
                next.output_limit = None;
                let (result, next) = one(next, case.field, "1");
                equal(&result.unwrap()[0], &small(case.field, true));
                caller = next;
            }
        }
    }
}

#[test]
fn binding_and_operand_faults_precede_attributes_and_output_exhaustion() {
    for case in cases() {
        for prepared in [false, true] {
            let (_, mut caller) = one(Caller::new(prepared), case.field, "1");
            caller.attributes = Some(vec![case.overflow.into()]);
            caller.output_limit = Some(0);
            caller.operation = Some(binding(case.field, "field.add"));
            LITERAL_DECODES.set(0);
            let (result, mut caller) = one(caller, case.field, "1");
            assert_eq!(code(&result.unwrap_err()), "refused:kernel-binding");
            assert_eq!(LITERAL_DECODES.get(), 0);
            caller.operation = None;
            caller.arguments = Some(vec![Value::Index(0)]);
            let (result, mut caller) = one(caller, case.field, "1");
            assert_eq!(code(&result.unwrap_err()), "refused:kernel-operands");
            assert_eq!(LITERAL_DECODES.get(), 0);
            caller.arguments = None;
            let (result, _) = one(caller, case.field, "1");
            assert_eq!(code(&result.unwrap_err()), case.error);
            assert_eq!(LITERAL_DECODES.get(), 1);
        }
    }
}

#[test]
fn output_preflight_and_current_policy_apply_to_every_scalar_use() {
    for case in cases() {
        for prepared in [false, true] {
            let mut caller = Caller::new(prepared);
            LITERAL_DECODES.set(0);
            // A cold output failure may retain successfully decoded facts.
            for limit in [511, 512, 511, 512] {
                caller.output_limit = Some(limit);
                let (result, next) = one(caller, case.field, "1");
                if limit == 511 {
                    assert_eq!(code(&result.unwrap_err()), "exhausted:output-bytes");
                } else {
                    let value = result.unwrap().remove(0);
                    equal(&value, &small(case.field, true));
                    assert_eq!(value.retained_bytes(), 512);
                }
                caller = next;
            }
            assert_eq!(LITERAL_DECODES.get(), if prepared { 1 } else { 4 });
            caller.output_limit = Some(512);
            caller.inner.core.policy.max_value_bytes = 511;
            let (result, mut caller) = one(caller, case.field, "1");
            assert_eq!(code(&result.unwrap_err()), "exhausted:output-bytes");
            caller.inner.core.policy.max_value_bytes = 512;
            let (result, _) = one(caller, case.field, "1");
            equal(&result.unwrap()[0], &small(case.field, true));
        }
    }
}

#[test]
fn one_slot_distinguishes_nominal_fields_and_provider_implementations() {
    let mut caller = Caller::new(true);
    // Base/Ext4/Ext8 share the literal rule and spelling; all providers also
    // share the operation name. Every transition must replace the typed key.
    for case in cases().into_iter().chain(cases().into_iter().rev()) {
        let before = caller
            .call
            .as_ref()
            .map(|call| std::ptr::from_ref(call.literal().unwrap()));
        let same = caller.call.as_ref().is_some_and(|call| {
            matches!(&call.payload, CallPayload::Literal(literal)
                if literal.binding.declaration == binding(case.field, "field.constant"))
        });
        LITERAL_DECODES.set(0);
        let (result, next) = one(caller, case.field, "1");
        equal(&result.unwrap()[0], &small(case.field, true));
        caller = next;
        assert_eq!(LITERAL_DECODES.get(), usize::from(!same));
        if !same {
            assert_ne!(
                before,
                caller
                    .call
                    .as_ref()
                    .map(|call| std::ptr::from_ref(call.literal().unwrap()))
            );
        }
    }
}

#[test]
fn exact_prepared_signature_and_binding_are_required_for_a_hit() {
    use zkc_runtime::vm::AttributeRule;
    let (_, mut caller) = one(Caller::new(true), "koala-bear", "1");
    for changed in 0..6 {
        // Perturb only the retained key. The next invocation is still valid;
        // it must decode again rather than accepting partial-key equality.
        let CallPayload::Literal(literal) = &mut caller.call.as_mut().unwrap().payload else {
            panic!("prepared literal");
        };
        let mut owner = Arc::clone(&literal.binding);
        let snapshot = Arc::make_mut(&mut owner);
        match changed {
            0 => snapshot.signature.attributes = AttributeRule::None,
            1 => snapshot
                .signature
                .inputs
                .push(Value::Index(0).physical_type()),
            2 => {
                snapshot.signature.outputs[0] =
                    small("koala-bear.ext4-binomial3", true).physical_type()
            }
            3 => snapshot.declaration.implementation = "other/field.constant".into(),
            4 => snapshot.declaration.contract = "field.add".into(),
            5 => snapshot.declaration.arguments[0] = "koala-bear.ext4-binomial3".into(),
            _ => unreachable!(),
        }
        literal.binding = owner;
        LITERAL_DECODES.set(0);
        let (result, next) = one(caller, "koala-bear", "1");
        equal(&result.unwrap()[0], &small("koala-bear", true));
        assert_eq!(LITERAL_DECODES.get(), 1);
        caller = next;
    }
}

#[test]
fn incompatible_signatures_and_uninstalled_implementations_do_not_use_warm_literals() {
    use zkc_runtime::vm::Representation;
    for case in cases() {
        for prepared in [false, true] {
            let (result, mut caller) = one(Caller::new(prepared), case.field, "1");
            result.unwrap();
            let declaration = binding(case.field, "field.constant");
            let signature = declaration.signature().unwrap();
            let mut uninstalled = declaration.clone();
            uninstalled.implementation = "uninstalled/field.constant".into();
            assert!(caller.inner.prepare_binding(&uninstalled).is_none());
            // Scalar fields have exactly one installed representation. A
            // different domain's physical representation is refused by type
            // construction; a changed installed signature is refused before
            // parsing, even when the retained scalar would have been valid.
            let other = if case.field == "bls12-381.fr" {
                Representation::Bn254Fr
            } else {
                Representation::Fr
            };
            assert!(PhysicalType::new(signature.outputs[0].logical().clone(), other).is_err());
            let mut wrong = signature.clone();
            wrong.outputs[0] = Value::Index(0).physical_type();
            caller.signature = Some(wrong);
            caller.attributes = Some(vec![case.overflow.into()]);
            caller.output_limit = Some(0);
            LITERAL_DECODES.set(0);
            let (result, mut caller) = one(caller, case.field, "1");
            assert_eq!(code(&result.unwrap_err()), "refused:kernel-operands");
            assert_eq!(LITERAL_DECODES.get(), 0);
            caller.signature = None;
            caller.attributes = None;
            caller.output_limit = None;
            let (result, _) = one(caller, case.field, "1");
            equal(&result.unwrap()[0], &small(case.field, true));
            assert_eq!(LITERAL_DECODES.get(), usize::from(!prepared));
        }
    }
}

#[test]
fn attribute_rule_mismatch_refuses_before_cold_or_warm_literal_preparation() {
    use zkc_runtime::vm::AttributeRule;
    for prepared in [false, true] {
        for warm in [false, true] {
            for attributes in [vec![], vec!["invalid-field".into()]] {
                let mut caller = Caller::new(prepared);
                if warm {
                    let (result, next) = one(caller, "koala-bear", "1");
                    result.unwrap();
                    caller = next;
                }
                let mut signature = binding("koala-bear", "field.constant").signature().unwrap();
                signature.attributes = AttributeRule::None;
                caller.signature = Some(signature);
                caller.attributes = Some(attributes);
                caller.output_limit = Some(0);
                LITERAL_DECODES.set(0);
                let (result, mut caller) = one(caller, "koala-bear", "1");
                assert_eq!(code(&result.unwrap_err()), "refused:kernel-operands");
                assert_eq!(LITERAL_DECODES.get(), 0);
                caller.signature = None;
                caller.attributes = None;
                caller.output_limit = None;
                let (result, _) = one(caller, "koala-bear", "1");
                equal(&result.unwrap()[0], &small("koala-bear", true));
                assert_eq!(LITERAL_DECODES.get(), usize::from(!prepared || !warm));
            }
        }
    }
}

#[test]
fn dormant_backend_faults_do_not_decode_or_initialize_a_slot() {
    for case in cases() {
        let bytes = program(
            &[binding(case.field, "field.constant")],
            &[Value::Bool(false).physical_type()],
            vec![json!([
                "if",
                "branch",
                "a0",
                [],
                [["op", "literal", "b0", ["1"], [], ["n"]], ["yield", []]],
                [["yield", []]],
                []
            ])],
            &[],
            &[],
        );
        for prepared in [false, true] {
            let mut caller = Caller::new(prepared);
            // Program admission validates every static attribute. Only the
            // reached backend boundary receives this deliberately bad value.
            caller.attributes = Some(vec![case.overflow.into()]);
            LITERAL_DECODES.set(0);
            let (result, _, caller) = run(
                caller,
                &bytes,
                vec![Value::Bool(false)],
                Default::default(),
                Default::default(),
            );
            result.unwrap();
            assert_eq!(caller.attempts, 0);
            assert!(caller.call.is_none());
            assert_eq!(LITERAL_DECODES.get(), 0);
            assert_eq!(caller.inner.active_frames(), 0);
            let (result, _, caller) = run(
                caller,
                &bytes,
                vec![Value::Bool(true)],
                Default::default(),
                Default::default(),
            );
            assert_eq!(code(&result.unwrap_err()), case.error);
            assert_eq!(caller.attempts, 1);
            assert!(caller.call.is_none());
            assert_eq!(LITERAL_DECODES.get(), 1);
            assert_eq!(caller.inner.active_frames(), 0);
        }
    }
}

// Fixed receipts from index_preparation apply independently: every scalar
// constant has the same 512-byte owned charge, and no operands are read.
fn repeated_observation(fail: bool, budget_case: usize) -> (Usage, Option<Stop>) {
    let literal_limit = budget_case == 1 || (!fail && budget_case == 3);
    let (instructions, total_value_bytes, logical_bytes) = if literal_limit {
        (9, 5632, 1536)
    } else {
        match (fail, budget_case) {
            (false, 0) => (12, 6144, 2048),
            (false, 2) | (true, 3) => (11, 6144, 2048),
            (true, 0) => (11, 6144, 3072),
            (true, 2) => (10, 6144, 2048),
            _ => panic!("unknown observation"),
        }
    };
    let usage = Usage {
        instructions,
        iterations: 4,
        total_value_bytes,
        logical_bytes,
        ..Usage::default()
    };
    if !fail && budget_case == 0 {
        return (usage, None);
    }
    let mut stop = Stop {
        origin: Origin {
            session: "session".into(),
            entry: "main".into(),
            instance: "instance".into(),
            path: vec![],
        },
        role: "P".into(),
        site: None,
        kind: StopKind::Limit,
        cleanup_errors: vec![],
        local: None,
    };
    if literal_limit {
        stop.origin.path.push(PathElement::For {
            site: "repeat".into(),
            index: 3,
        });
        stop.site = Some("literal".into());
        stop.kind = StopKind::Backend(crate::exhausted("output-bytes"));
        stop.local = Some(Box::new(LocalContext {
            site: "local".into(),
            function: "testfn".into(),
            instruction: Some("literal".into()),
        }));
    } else if fail {
        stop.site = Some("local".into());
        stop.local = Some(Box::new(LocalContext {
            site: "local".into(),
            function: "testfn".into(),
            instruction: None,
        }));
        if budget_case == 0 {
            stop.kind = StopKind::Backend(crate::refused("index-zero-divisor"));
        }
    }
    (usage, Some(stop))
}

#[test]
fn real_runner_slots_preserve_exact_usage_exhaustion_and_later_failure() {
    let index = Value::Index(0).physical_type();
    for case in cases() {
        for fail in [false, true] {
            let mut body = vec![json!([
                "for",
                "repeat",
                "i",
                "a0",
                "a1",
                [],
                [],
                [["op", "literal", "b0", ["1"], [], ["n"]], ["yield", []]],
                []
            ])];
            if fail {
                body.push(json!(["op", "divide", "b1", [], ["a0", "a0"], ["unused"]]));
            }
            let bytes = program(
                &[
                    binding(case.field, "field.constant"),
                    OperationBinding {
                        contract: "index.div".into(),
                        arguments: vec![],
                        implementation: "native/index.div".into(),
                        physical_arguments: vec![],
                    },
                ],
                &[index.clone(), index.clone()],
                body,
                &[],
                &[],
            );
            let (full, _) = repeated_observation(fail, 0);
            for (budget_case, (values, work)) in [
                (ValueBudget::default(), WorkBudget::default()),
                (
                    ValueBudget {
                        total_bytes: full.total_value_bytes - 1,
                        ..Default::default()
                    },
                    WorkBudget::default(),
                ),
                (
                    ValueBudget::default(),
                    WorkBudget {
                        instructions: full.instructions - 1,
                        ..Default::default()
                    },
                ),
                (
                    ValueBudget::default(),
                    WorkBudget {
                        logical_bytes: full.logical_bytes - 1,
                        ..Default::default()
                    },
                ),
            ]
            .into_iter()
            .enumerate()
            {
                let (expected_usage, expected_stop) = repeated_observation(fail, budget_case);
                for prepared in [false, true] {
                    LITERAL_DECODES.set(0);
                    let (result, usage, caller) = run(
                        Caller::new(prepared),
                        &bytes,
                        vec![Value::Index(0), Value::Index(4)],
                        values,
                        work,
                    );
                    assert_eq!(usage, expected_usage);
                    assert_eq!(
                        result.as_ref().map(Vec::len),
                        expected_stop.as_ref().map_or(Ok(0), Err)
                    );
                    assert_eq!(LITERAL_DECODES.get(), if prepared { 1 } else { 4 });
                    assert_eq!(caller.inner.active_frames(), 0);
                    assert_eq!(
                        caller.leaves.last(),
                        Some(&(
                            FrameKind::Entry,
                            if result.is_ok() {
                                FrameExit::Returned
                            } else {
                                FrameExit::Stopped
                            }
                        ))
                    );
                }
                LITERAL_DECODES.set(0);
                let (result, usage, native) = run(
                    backend(),
                    &bytes,
                    vec![Value::Index(0), Value::Index(4)],
                    values,
                    work,
                );
                assert_eq!(usage, expected_usage);
                assert_eq!(
                    result.as_ref().map(Vec::len),
                    expected_stop.as_ref().map_or(Ok(0), Err)
                );
                assert_eq!(LITERAL_DECODES.get(), 1);
                assert_eq!(native.active_frames(), 0);
            }
        }
    }
}

#[test]
fn literal_failure_preserves_preceding_rng_effect_and_reverse_cleanup() {
    let field = "bls12-381.fr";
    let draw = binding(field, "random.draw");
    let ports = draw.signature().unwrap();
    let bytes = program(
        &[draw, binding(field, "field.constant")],
        &ports.inputs,
        vec![
            json!(["op", "draw", "b0", [], ["a0"], ["sample", "next"]]),
            json!(["op", "literal", "b1", ["1"], [], ["n"]]),
        ],
        &[ports.outputs[1].clone()],
        &["next".into()],
    );
    for prepared in [false, true] {
        for fault in 0..5 {
            for cleanup_error in [false, true] {
                let (result, mut caller) = one(Caller::new(prepared), field, "1");
                result.unwrap();
                caller.leaves.clear();
                caller.cleanup_error = cleanup_error;
                caller.output_limit = Some(511);
                let error = match fault {
                    0 => {
                        caller.operation = Some(binding(field, "field.add"));
                        caller.attributes = Some(vec!["01".into()]);
                        crate::refused("kernel-binding")
                    }
                    1 => {
                        caller.arguments = Some(vec![Value::Index(0)]);
                        caller.attributes = Some(vec!["01".into()]);
                        crate::refused("kernel-operands")
                    }
                    2 => {
                        caller.attributes = Some(vec![]);
                        crate::refused("kernel-attributes")
                    }
                    3 => {
                        caller.attributes = Some(vec!["01".into()]);
                        crate::refused("invalid-encoding")
                    }
                    4 => crate::exhausted("output-bytes"),
                    _ => unreachable!(),
                };
                let rng = caller
                    .inner
                    .issue_rng_for(
                        Identity::Bls12381Fr,
                        Domain::new("P", "session", "main", None),
                        3,
                    )
                    .unwrap();
                let outside = caller
                    .inner
                    .issue_rng_for(
                        Identity::Bls12381Fr,
                        Domain::new("P", "session", "main", None),
                        9,
                    )
                    .unwrap();
                let Value::Rng(token) = &rng else { panic!() };
                let Value::Rng(outside) = &outside else {
                    panic!()
                };
                let before = caller.inner.observe(outside).unwrap();
                let (result, usage, caller) = run(
                    caller,
                    &bytes,
                    vec![rng.clone()],
                    Default::default(),
                    Default::default(),
                );
                let stop = result.unwrap_err();
                assert_eq!(
                    stop,
                    Stop {
                        origin: Origin {
                            session: "session".into(),
                            entry: "main".into(),
                            instance: "instance".into(),
                            path: vec![]
                        },
                        role: "P".into(),
                        site: Some("local".into()),
                        kind: StopKind::Backend(error),
                        cleanup_errors: if cleanup_error {
                            vec![crate::refused("literal-test-cleanup")]
                        } else {
                            vec![]
                        },
                        local: Some(Box::new(LocalContext {
                            site: "local".into(),
                            function: "testfn".into(),
                            instruction: None
                        })),
                    }
                );
                let observed = caller.inner.observe(token).unwrap();
                assert_eq!(
                    (observed.generation, observed.draw_count, observed.budget),
                    (1, 1, 2)
                );
                assert_eq!(caller.inner.observe(outside).unwrap(), before);
                assert!(caller.inner.validate_value(&rng).is_err());
                assert_eq!((usage.live_values, usage.live_value_bytes), (0, 0));
                assert_eq!(
                    caller.leaves,
                    vec![
                        (
                            FrameKind::Local {
                                site: "local".into(),
                                function: "testfn".into()
                            },
                            FrameExit::Stopped
                        ),
                        (FrameKind::Entry, FrameExit::Stopped),
                    ]
                );
                assert_eq!(caller.inner.active_frames(), 0);
            }
        }
    }
}

#[test]
fn binary_kernel_literals_match_independent_vm_admission() {
    use zkc_kernels::plonky3::binary;
    for width in [64, 192] {
        let maximum = format!("0x{}", "f".repeat(width / 4));
        let overflow = format!("0x1{}", "0".repeat(width / 4));
        for text in [
            "0", "1", "", "2", "00", "0x0", "0x1", "0x2", "0xff", "0x00", "0xFF", "-1", " 1",
            &maximum, &overflow,
        ] {
            let admitted = matches!(text, "0" | "1")
                || zkc_runtime::vm::bit_pattern_literal(text, width as u32).is_some();
            let accepted = if width == 64 {
                binary::parse_literal(text).is_ok()
            } else {
                binary::parse_ext3_literal(text).is_ok()
            };
            assert_eq!(admitted, accepted, "{text} in {width} bits");
        }
    }
}

#[test]
fn resident_literal_cold_warm_failures_preserve_usage_and_typed_retained_facts() {
    for (field, provider, expected) in [
        (
            "bls12-381.fr",
            "blst",
            Value::BlstField(zkc_kernels::blst::bls12_381::Scalar::from(7)),
        ),
        (
            "bn254.fr",
            "halo2curves-axiom",
            Value::HaloField(zkc_kernels::halo2curves::bn254::Scalar::from(7)),
        ),
    ] {
        let binding = OperationBinding {
            contract: "field.constant".into(),
            arguments: vec![field.into()],
            implementation: format!("{provider}/resident/field.constant"),
            physical_arguments: vec![],
        };
        let operation = backend().prepare_binding(&binding).unwrap();
        let bytes = program(
            &[binding],
            &[],
            vec![json!(["op", "literal", "b0", ["7"], [], ["n"]])],
            &operation.binding.signature.outputs,
            &["n".into()],
        );
        let mut observations = Vec::new();
        for prepared in [false, true] {
            let mut caller = Caller::new(prepared);
            LITERAL_DECODES.set(0);
            let mut retained = None;
            let mut usages = Vec::new();
            for (visit, limit) in [511, 512, 511, 512].into_iter().enumerate() {
                caller.output_limit = Some(limit);
                let (result, usage, next) = run(
                    caller,
                    &bytes,
                    vec![],
                    Default::default(),
                    Default::default(),
                );
                caller = next;
                assert_eq!(caller.inner.active_frames(), 0);
                usages.push(usage);
                if limit == 511 {
                    assert_eq!(code(&result.unwrap_err()), "exhausted:output-bytes");
                } else {
                    equal(&result.unwrap()[0], &expected);
                }
                assert_eq!(LITERAL_DECODES.get(), if prepared { 1 } else { visit + 1 });
                if prepared {
                    let literal = caller.call.as_ref().unwrap().literal().unwrap();
                    equal(literal, &expected);
                    let pointer = std::ptr::from_ref(literal);
                    assert_eq!(*retained.get_or_insert(pointer), pointer);
                }
            }
            // A failed replacement retains old facts but must never execute them.
            caller.attributes = Some(vec!["00".into()]);
            let (result, _, caller) = run(
                caller,
                &bytes,
                vec![],
                Default::default(),
                Default::default(),
            );
            assert_eq!(code(&result.unwrap_err()), "refused:noncanonical-scalar");
            if prepared {
                assert_eq!(
                    std::ptr::from_ref(caller.call.as_ref().unwrap().literal().unwrap()),
                    retained.unwrap()
                );
            }
            observations.push(usages);
        }
        assert_eq!(observations[0], observations[1]);
    }
}
