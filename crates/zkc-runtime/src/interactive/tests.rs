mod joint;
mod storage;
use joint::{DriverCut, DriverEvent, drive_cut};
// Explicit reference/mock service. None of these tests is cryptographic evidence.
use super::*;
use serde_json::{Value as Json, json};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
enum V {
    Variant(std::sync::Arc<VariantDescriptor>, usize, Vec<V>),
    Field(u64),
    Bool(bool),
    Cap {
        slot: usize,
        generation: u64,
        owner: String,
        seal: u64,
    },
    PrivateAsField,
    Sized(usize),
}
impl V {
    fn leaves(&self) -> Vec<&Self> {
        match self {
            Self::Variant(_, _, payload) => payload.iter().flat_map(Self::leaves).collect(),
            _ => vec![self],
        }
    }
}
/// How a faulty trusted value misreports itself when unpacked, so the runner's
/// own consistency checks on a match scrutinee can be exercised.
#[derive(Clone)]
enum Forgery {
    Descriptor(std::sync::Arc<VariantDescriptor>),
    Alternative(usize),
    Payload,
}
thread_local! {
    static FORGERY: std::cell::RefCell<Option<Forgery>> = const { std::cell::RefCell::new(None) };
}
/// Installs a forgery for the current test thread and removes it on drop.
struct Forging;
impl Forging {
    fn install(forgery: Forgery) -> Self {
        FORGERY.with(|f| *f.borrow_mut() = Some(forgery));
        Self
    }
}
impl Drop for Forging {
    fn drop(&mut self) {
        FORGERY.with(|f| *f.borrow_mut() = None);
    }
}
impl Value for V {
    fn pack_variant(
        descriptor: std::sync::Arc<VariantDescriptor>,
        alternative: usize,
        payload: Vec<Self>,
    ) -> Result<Self, BackendError> {
        let arm = descriptor
            .alternatives()
            .get(alternative)
            .ok_or_else(|| BackendError::new("variant-alternative"))?;
        if arm.payload().len() != payload.len()
            || arm
                .payload()
                .iter()
                .zip(&payload)
                .any(|(t, v)| PhysicalType::default_for(t.clone()).unwrap() != v.physical_type())
        {
            return Err(BackendError::new("variant-payload"));
        }
        Ok(Self::Variant(descriptor, alternative, payload))
    }
    fn unpack_variant(
        &self,
    ) -> Result<(std::sync::Arc<VariantDescriptor>, usize, Vec<Self>), BackendError> {
        match self {
            Self::Variant(d, a, p) => Ok(match FORGERY.with(|f| f.borrow().clone()) {
                None => (d.clone(), *a, p.clone()),
                Some(Forgery::Descriptor(other)) => (other, *a, p.clone()),
                Some(Forgery::Alternative(other)) => (d.clone(), other, p.clone()),
                Some(Forgery::Payload) => {
                    let mut extra = p.clone();
                    extra.push(V::Bool(true));
                    (d.clone(), *a, extra)
                }
            }),
            _ => Err(BackendError::new("variant-type")),
        }
    }

    fn physical_type(&self) -> PhysicalType {
        if let Self::Variant(d, _, _) = self {
            return PhysicalType::default_for(LogicalType::variant(d.clone())).unwrap();
        }
        let logical = match self {
            Self::Bool(_) => "bool",
            Self::Cap { .. } => "rng:bls12-381.fr",
            _ => "field:bls12-381.fr",
        };
        PhysicalType::default_for(LogicalType::parse(logical).unwrap()).unwrap()
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        match self {
            Self::Field(_) | Self::Bool(_) => Ok(()),
            _ => Err(BackendError::new("private-wire-value")),
        }
    }
    fn retained_bytes(&self) -> usize {
        match self {
            Self::Variant(d, _, p) => {
                256 + d.retained_bytes() + p.iter().map(Value::retained_bytes).sum::<usize>()
            }
            Self::Sized(bytes) => *bytes,
            _ => 16,
        }
    }
}
#[derive(Debug)]
struct Slot {
    generation: u64,
    draws: u64,
    owner: String,
    seal: u64,
}
#[derive(Debug)]
struct Mock {
    slots: BTreeMap<usize, Slot>,
    frames: Vec<(FrameId, BTreeSet<usize>)>,
    trace: Vec<String>,
    domains: Vec<Vec<u8>>,
    fail_draw: bool,
    wrong_signature: bool,
    wrong_output: bool,
    intrude: Option<usize>,
    fail_leave: bool,
    fail_enter: Option<FrameKind>,
    refused_frame: Option<Frame>,
    close_count: Option<std::rc::Rc<std::cell::Cell<usize>>>,
}
impl Mock {
    fn new() -> Self {
        Self {
            slots: BTreeMap::new(),
            frames: vec![],
            trace: vec![],
            domains: vec![],
            fail_draw: false,
            wrong_signature: false,
            wrong_output: false,
            intrude: None,
            fail_leave: false,
            fail_enter: None,
            refused_frame: None,
            close_count: None,
        }
    }
    fn issue(&mut self, slot: usize, role: &str) -> V {
        let seal = 4321 + slot as u64;
        self.slots.insert(
            slot,
            Slot {
                generation: 0,
                draws: 0,
                owner: role.into(),
                seal,
            },
        );
        V::Cap {
            slot,
            generation: 0,
            owner: role.into(),
            seal,
        }
    }
    fn check_cap(&self, value: &V, role: Option<&str>) -> Result<Option<usize>, BackendError> {
        if let V::Cap {
            slot,
            generation,
            owner,
            seal,
        } = value
        {
            let state = self
                .slots
                .get(slot)
                .ok_or_else(|| BackendError::new("unissued"))?;
            if state.seal != *seal || state.owner != *owner || role.is_some_and(|r| r != owner) {
                return Err(BackendError::new("authority"));
            }
            if state.generation != *generation {
                return Err(BackendError::new("stale"));
            }
            Ok(Some(*slot))
        } else {
            Ok(None)
        }
    }
}
impl Backend for Mock {
    type Value = V;
    fn binding_signature(&self, binding: &OperationBinding) -> Option<BoundSignature> {
        let mut signature = binding.signature().ok()?;
        if self.wrong_signature {
            signature.outputs = vec![];
        }
        Some(signature)
    }
    fn validate_value(&self, _value: &V) -> Result<(), BackendError> {
        // PrivateAsField deliberately passes local representation validation;
        // independent public-value validation must still reject it at a message.
        Ok(())
    }
    fn enter_frame(&mut self, frame: &Frame, arguments: &[V]) -> Result<(), BackendError> {
        assert_eq!(frame.inputs().len(), arguments.len());
        assert_eq!(frame.parent(), self.frames.last().map(|(id, _)| *id));
        let mut view = BTreeSet::new();
        for value in arguments.iter().flat_map(V::leaves) {
            if let Some(slot) = self.check_cap(value, Some(frame.role()))? {
                if self.frames.last().is_some_and(|(_, v)| !v.contains(&slot)) {
                    return Err(BackendError::new("outside-parent-view"));
                }
                view.insert(slot);
            }
        }
        if self.fail_enter.as_ref() == Some(frame.kind()) {
            self.refused_frame = Some(frame.clone());
            return Err(BackendError::new("enter-refused"));
        }
        self.trace
            .push(format!("enter:{:?}:{}", frame.kind(), arguments.len()));
        self.frames.push((frame.id(), view));
        Ok(())
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        outputs: &[V],
    ) -> Result<(), BackendError> {
        if let Some(count) = &self.close_count {
            count.set(count.get() + 1);
        }
        let (id, view) = self.frames.pop().expect("balanced frame");
        assert_eq!(id, frame.id());
        self.trace.push(format!("leave:{exit:?}"));
        for value in outputs.iter().flat_map(V::leaves) {
            if let Some(slot) = self.check_cap(value, Some(frame.role()))?
                && !view.contains(&slot)
            {
                return Err(BackendError::new("forged-output-capability"));
            }
        }
        if self.fail_leave {
            return Err(BackendError::new("leave-failed"));
        }
        Ok(())
    }
    fn apply(
        &mut self,
        invocation: &Invocation<'_>,
        arguments: &[V],
    ) -> Result<Vec<V>, BackendError> {
        self.trace.push(invocation.kernel.to_owned());
        self.domains.push(invocation.domain_bytes());
        let (_, view) = self.frames.last().expect("active frame");
        let mut argument_view = BTreeSet::new();
        for value in arguments.iter().flat_map(V::leaves) {
            if let Some(slot) = self.check_cap(value, Some(invocation.frame.role()))? {
                if !view.contains(&slot) {
                    return Err(BackendError::new("outside-frame"));
                }
                argument_view.insert(slot);
            }
        }
        if self
            .intrude
            .is_some_and(|slot| !argument_view.contains(&slot))
        {
            return Err(BackendError::new("outside-operands"));
        }
        if self.wrong_output {
            return Ok(vec![V::Bool(false)]);
        }
        let result = match (invocation.kernel, arguments) {
            ("arkworks/field.constant", []) => {
                vec![V::Field(invocation.attributes[0].parse().unwrap())]
            }
            ("arkworks/field.add", [V::Field(a), V::Field(b)]) => vec![V::Field(a + b)],
            ("arkworks/field.mul", [V::Field(a), V::Field(b)]) => vec![V::Field(a * b)],
            ("arkworks/field.equal", [V::Field(a), V::Field(b)]) => vec![V::Bool(a == b)],
            ("arkworks/bool.and", [V::Bool(a), V::Bool(b)]) => vec![V::Bool(*a && *b)],
            ("arkworks/control.require", [V::Bool(true)]) => vec![],
            ("arkworks/control.require", [V::Bool(false)]) => {
                return Err(BackendError::new("require-failed"));
            }
            (
                "arkworks/random.draw",
                [
                    V::Cap {
                        slot, owner, seal, ..
                    },
                ],
            ) => {
                let state = self.slots.get_mut(slot).unwrap();
                state.generation += 1;
                state.draws += 1;
                if self.fail_draw {
                    return Err(BackendError::new("failed-after-consume"));
                }
                vec![
                    V::Field(state.draws),
                    V::Cap {
                        slot: *slot,
                        generation: state.generation,
                        owner: owner.clone(),
                        seal: *seal,
                    },
                ]
            }
            _ => return Err(BackendError::new("mock-unimplemented")),
        };
        Ok(result)
    }
}
// This test authoring helper fixes one nominal BLS installation and emits only
// /2. The runner never receives shorthand types or implicit operation contracts.
fn fixture_type(kind: &str) -> String {
    if kind.contains('@') {
        return kind.into();
    }
    let identity = match kind {
        "bool" => {
            return PhysicalType::default_for(LogicalType::parse("bool").unwrap())
                .unwrap()
                .spelling();
        }
        "field" | "scalar" => "bls12-381.fr",
        "group" | "groups" => "bls12-381.g1",
        "transcript" => "merlin3.bls12-381.fr64be/0",
        "prover_key" | "verifier_key" | "opening_state" | "commitment" | "proof" => {
            "multilinear.kzg.bls12-381/0"
        }
        _ => "bls12-381.fr",
    };
    let kind = if kind == "scalar" { "field" } else { kind };
    PhysicalType::default_for(LogicalType::parse(&format!("{kind}:{identity}")).unwrap())
        .unwrap()
        .spelling()
}
fn fixture_body(body: &mut Json) {
    if let Some(body) = body.as_array_mut() {
        for instruction in body {
            match instruction[0].as_str() {
                Some("op") => {
                    if let Some(key) = instruction[2]
                        .as_str()
                        .and_then(|k| k.strip_prefix("arkworks/"))
                    {
                        instruction[2] = json!(key);
                    }
                }
                Some("receive") => {
                    instruction[5] = json!(fixture_type(instruction[5].as_str().unwrap()))
                }
                Some("loop") => fixture_body(&mut instruction[5]),
                _ => {}
            }
        }
    }
}
fn module(mut functions: Json, mut participants: Json, entries: Json) -> Json {
    for f in functions.as_array_mut().unwrap() {
        for p in f[2].as_array_mut().unwrap() {
            p[1] = json!(fixture_type(p[1].as_str().unwrap()));
        }
        for ty in f[3].as_array_mut().unwrap() {
            *ty = json!(fixture_type(ty.as_str().unwrap()));
        }
        fixture_body(&mut f[4]);
        let name = f[1].clone();
        if f.as_array().unwrap().len() == 5 {
            f.as_array_mut().unwrap().push(json!([name, []]));
        }
    }
    for p in participants.as_array_mut().unwrap() {
        for port in p[4].as_array_mut().unwrap() {
            port[1] = json!(fixture_type(port[1].as_str().unwrap()));
        }
        for ty in p[5].as_array_mut().unwrap() {
            *ty = json!(fixture_type(ty.as_str().unwrap()));
        }
        fixture_body(&mut p[6]);
    }
    let bindings: Vec<_> = [
        "field.constant",
        "field.add",
        "field.mul",
        "field.equal",
        "random.draw",
        "bool.and",
        "control.require",
        "curve.generator",
        "curve.scale",
        "curve.add",
        "curve.equal",
        "curve.empty",
        "curve.append",
        "curve.at",
        "curve.commit",
        "curve.response",
    ]
    .iter()
    .map(|key| {
        let args = if ["bool.and", "control.require"].contains(key) {
            vec![]
        } else if key.starts_with("curve.") && *key != "curve.response" {
            vec!["bls12-381.g1"]
        } else {
            vec!["bls12-381.fr"]
        };
        json!([key, key, args, format!("arkworks/{key}")])
    })
    .collect();
    json!(["zkc.program/0", bindings, functions, participants, entries])
}

fn participant(
    symbol: &str,
    instance: &str,
    role: &str,
    inputs: Json,
    outputs: Json,
    body: Json,
) -> Json {
    json!([
        "participant",
        symbol,
        instance,
        role,
        inputs,
        outputs,
        body,
        []
    ])
}
fn one(functions: Json, inputs: Json, outputs: Json, body: Json) -> Json {
    module(
        functions,
        json!([participant("mainP", "root", "P", inputs, outputs, body)]),
        json!([["entry", "main", [["P", "mainP"]]]]),
    )
}
fn bytes(j: &Json) -> Vec<u8> {
    serde_json::to_vec(j).unwrap()
}
fn admitted(j: &Json) -> Admitted {
    admit_supplied(&bytes(j), &Mock::new()).unwrap()
}
fn runner(j: &Json, role: &str, backend: Mock, inputs: Vec<V>) -> Runner<Mock> {
    Runner::new(&admitted(j), "main", role, "test-session", backend, inputs).unwrap()
}
fn local(r: &mut Runner<Mock>) {
    let Action::Local(a) = r.poll() else {
        panic!("expected local")
    };
    r.execute_local(&a.cut).unwrap();
}
fn reject(j: &Json, code: ErrorCode) {
    assert_eq!(
        admit_supplied(&bytes(j), &Mock::new()).unwrap_err().code,
        code
    );
}
fn identity() -> Json {
    one(
        json!([]),
        json!([["x", "field"]]),
        json!(["field"]),
        json!([["return", ["x"]]]),
    )
}
fn add_fn() -> Json {
    json!([
        "function",
        "add",
        [["a", "field"], ["b", "field"]],
        ["field"],
        [
            ["op", "plus", "arkworks/field.add", [], ["a", "b"], ["c"]],
            ["return", ["c"]]
        ]
    ])
}
fn draw_fn() -> Json {
    json!([
        "function",
        "draw",
        [["r", "rng"]],
        ["field", "rng"],
        [
            [
                "op",
                "drawOp",
                "arkworks/random.draw",
                [],
                ["r"],
                ["x", "r1"]
            ],
            ["return", ["x", "r1"]]
        ]
    ])
}
fn exchange() -> Json {
    module(
        json!([]),
        json!([
            participant(
                "mainP",
                "root",
                "P",
                json!([["x", "field"]]),
                json!([]),
                json!([["send", "msg", "scalar", "V", "x"], ["return", []]])
            ),
            participant(
                "mainV",
                "root",
                "V",
                json!([]),
                json!(["field"]),
                json!([
                    ["receive", "msg", "scalar", "P", "y", "field"],
                    ["return", ["y"]]
                ])
            )
        ]),
        json!([["entry", "main", [["P", "mainP"], ["V", "mainV"]]]]),
    )
}

#[test]
fn strict_json_scalars_objects_trailing_and_truncation() {
    for bad in [
        b"{}".as_slice(),
        b"1",
        b"1.0",
        b"true",
        b"null",
        b"[] []",
        b"[",
        b"[\"unterminated]",
        b"[[]",
        b"]",
        b"[\"x\",{}]",
    ] {
        assert!(admit_supplied(bad, &Mock::new()).is_err(), "{bad:?}");
    }
    let mut data = bytes(&identity());
    data.push(b'0');
    assert!(admit_supplied(&data, &Mock::new()).is_err());
    for length in 0..bytes(&identity()).len() {
        assert!(admit_supplied(&bytes(&identity())[..length], &Mock::new()).is_err());
    }
}
#[test]
fn exact_tags_arities_names_and_limits() {
    let mut j = identity();
    j[0] = json!("invalid.program");
    reject(&j, ErrorCode::Record);
    let mut j = identity();
    j.as_array_mut().unwrap().push(json!([]));
    reject(&j, ErrorCode::Record);
    let mut j = identity();
    j[3][0][1] = json!("bad/name");
    reject(&j, ErrorCode::Name);
    let mut j = identity();
    j[3][0][1] = json!("é");
    reject(&j, ErrorCode::Name);
    let mut j = identity();
    j[3][0][1] = json!("x".repeat(129));
    reject(&j, ErrorCode::Name);
    let mut j = identity();
    j[3][0][6][0].as_array_mut().unwrap().push(json!([]));
    reject(&j, ErrorCode::Record);
    let mut j = identity();
    j[3][0][6] = json!([["opaque", "anything"]]);
    reject(&j, ErrorCode::Record);
    let huge = vec![b' '; Limits::ARTIFACT_BYTES + 1];
    assert_eq!(
        admit_supplied(&huge, &Mock::new()).unwrap_err().code,
        ErrorCode::Limit
    );
    let deep = format!("{}{}", "[".repeat(100), "]".repeat(100));
    assert_eq!(
        admit_supplied(deep.as_bytes(), &Mock::new())
            .unwrap_err()
            .code,
        ErrorCode::Limit
    );
}
#[test]
fn unknown_program_format_and_extra_fields_are_distinct_refusals() {
    let mut unknown_format = identity();
    unknown_format[0] = json!("invalid.program");
    reject(&unknown_format, ErrorCode::Record);
    for extra in [json!("extra"), json!([]), json!([["n", "4"]])] {
        let mut root = identity();
        root.as_array_mut().unwrap().insert(2, extra.clone());
        reject(&root, ErrorCode::Record);
        let mut participant = identity();
        participant[3][0].as_array_mut().unwrap().insert(4, extra);
        reject(&participant, ErrorCode::Record);
    }
}
#[test]
fn binding_records_and_non_nominal_types_rejected() {
    let mut j = identity();
    j[1] = json!("caller.backend/0");
    reject(&j, ErrorCode::Record);
    for ty in ["opaque:Secret", "nonce", "custom", "arkworks.field"] {
        let mut j = identity();
        j[3][0][4][0][1] = json!(ty);
        reject(&j, ErrorCode::Type);
    }
}
#[test]
fn symbol_and_signature_admission() {
    let mut j = identity();
    let duplicate = j[3][0].clone();
    j[3].as_array_mut().unwrap().push(duplicate);
    reject(&j, ErrorCode::Symbol);
    let mut j = identity();
    j[4][0][2][0][1] = json!("missing");
    reject(&j, ErrorCode::Symbol);
    let mut j = identity();
    j[4][0][2][0][0] = json!("V");
    reject(&j, ErrorCode::Role);
    let j = one(
        json!([add_fn()]),
        json!([["x", "field"]]),
        json!(["field"]),
        json!([["local", "a", "add", ["x"], ["z"]], ["return", ["z"]]]),
    );
    reject(&j, ErrorCode::Signature);
    let j = one(
        json!([add_fn()]),
        json!([["x", "bool"]]),
        json!(["field"]),
        json!([["local", "a", "add", ["x", "x"], ["z"]], ["return", ["z"]]]),
    );
    reject(&j, ErrorCode::Signature);
    let j = one(
        json!([add_fn()]),
        json!([["x", "field"]]),
        json!(["field"]),
        json!([["local", "a", "add", ["x", "x"], []], ["return", ["x"]]]),
    );
    reject(&j, ErrorCode::Signature);
}
#[test]
fn installed_signatures_are_not_artifact_authority() {
    let j = one(
        json!([add_fn()]),
        json!([["x", "field"]]),
        json!(["field"]),
        json!([["local", "a", "add", ["x", "x"], ["z"]], ["return", ["z"]]]),
    );
    let mut backend = Mock::new();
    backend.wrong_signature = true;
    assert_eq!(
        admit_supplied(&bytes(&j), &backend).unwrap_err().code,
        ErrorCode::Backend
    );
    assert!(
        Runner::new(
            &admitted(&j),
            "main",
            "P",
            "session",
            backend,
            vec![V::Field(1)]
        )
        .is_err()
    );
    for kernel in [
        "arkworks/field.add",
        "reference/field.add",
        "arkworks/prover",
        "arkworks/poly.sumcheck",
        "external",
        "arkworks/unknown",
    ] {
        let mut j = j.clone();
        j[2][0][4][0][2] = json!(kernel);
        reject(
            &j,
            if kernel.contains('/') {
                ErrorCode::Name
            } else {
                ErrorCode::Symbol
            },
        );
    }
}
#[test]
fn exact_attributes_and_canonical_field_constants() {
    let base = one(
        json!([[
            "function",
            "constant",
            [],
            ["field"],
            [
                ["op", "c", "arkworks/field.constant", ["0"], [], ["x"]],
                ["return", ["x"]]
            ]
        ]]),
        json!([]),
        json!(["field"]),
        json!([["local", "c", "constant", [], ["x"]], ["return", ["x"]]]),
    );
    admitted(&base);
    for s in [
        "00",
        "01",
        "-1",
        "+1",
        " 1",
        "1.0",
        "1e2",
        "",
        "52435875175126190479447740508185965837690552500527637822603658699938581184513",
    ] {
        let mut j = base.clone();
        j[2][0][4][0][3] = json!([s]);
        reject(&j, ErrorCode::Attributes);
    }
    for attrs in [json!([]), json!(["1", "2"])] {
        let mut j = base.clone();
        j[2][0][4][0][3] = attrs;
        reject(&j, ErrorCode::Attributes);
    }
    let mut j = one(
        json!([add_fn()]),
        json!([]),
        json!([]),
        json!([["return", []]]),
    );
    j[2][0][4][0][3] = json!(["0"]);
    reject(&j, ErrorCode::Attributes);
}
#[test]
fn ssa_terminal_and_site_checks() {
    let mut j = identity();
    j[3][0][6][0][1] = json!(["foreign"]);
    reject(&j, ErrorCode::Ssa);
    let mut j = identity();
    j[3][0][4]
        .as_array_mut()
        .unwrap()
        .push(json!(["x", fixture_type("field")]));
    reject(&j, ErrorCode::Ssa);
    let mut j = identity();
    j[3][0][6]
        .as_array_mut()
        .unwrap()
        .push(json!(["return", ["x"]]));
    reject(&j, ErrorCode::Terminal);
    let mut j = identity();
    j[3][0][6] = json!([]);
    reject(&j, ErrorCode::Terminal);
    let mut j = identity();
    j[3][0][6][0][0] = json!("yield");
    reject(&j, ErrorCode::Terminal);
    let j = one(
        json!([add_fn()]),
        json!([["x", "field"]]),
        json!(["field"]),
        json!([
            ["local", "same", "add", ["x", "x"], ["y"]],
            ["local", "same", "add", ["y", "x"], ["z"]],
            ["return", ["z"]]
        ]),
    );
    reject(&j, ErrorCode::Site);
    let mut j = j;
    j[3][0][6][1][1] = json!("other");
    j[3][0][6][1][4] = json!(["x"]);
    reject(&j, ErrorCode::Ssa);
}
#[test]
fn consumed_ssa_and_returned_aliases_are_both_ssa_refusals() {
    let j = one(
        json!([draw_fn()]),
        json!([["r", "rng"]]),
        json!([]),
        json!([
            ["local", "a", "draw", ["r"], ["x", "r1"]],
            ["local", "b", "draw", ["r"], ["y", "r2"]],
            ["return", []]
        ]),
    );
    reject(&j, ErrorCode::Ssa);
    let j = one(
        json!([]),
        json!([["r", "rng"]]),
        json!(["rng", "rng"]),
        json!([["return", ["r", "r"]]]),
    );
    reject(&j, ErrorCode::Ssa);
}
#[test]
fn entry_inputs_are_exact_and_role_owned() {
    let j = identity();
    let a = admitted(&j);
    assert!(matches!(
        Runner::new(&a, "main", "P", "s", Mock::new(), vec![])
            .err()
            .unwrap()
            .error,
        RuntimeError::Inputs
    ));
    assert!(matches!(
        Runner::new(&a, "main", "P", "s", Mock::new(), vec![V::Bool(true)])
            .err()
            .unwrap()
            .error,
        RuntimeError::Payload
    ));
    assert!(matches!(
        Runner::new(&a, "main", "V", "s", Mock::new(), vec![V::Field(1)])
            .err()
            .unwrap()
            .error,
        RuntimeError::Role
    ));
    assert!(matches!(
        Runner::new(&a, "main", "P", "", Mock::new(), vec![V::Field(1)])
            .err()
            .unwrap()
            .error,
        RuntimeError::Session
    ));
    let mut r = runner(&j, "P", Mock::new(), vec![V::Field(9)]);
    assert_eq!(r.poll(), Action::Returned(vec![V::Field(9)]));
    assert!(r.backend().frames.is_empty());
}
#[test]
fn local_is_one_whole_function_and_pending_is_stable() {
    let j = one(
        json!([add_fn()]),
        json!([["x", "field"]]),
        json!(["field"]),
        json!([
            ["local", "first", "add", ["x", "x"], ["y"]],
            ["local", "second", "add", ["y", "x"], ["z"]],
            ["return", ["z"]]
        ]),
    );
    let mut r = runner(&j, "P", Mock::new(), vec![V::Field(4)]);
    let pending = r.poll();
    let usage = r.usage();
    let trace = r.backend().trace.clone();
    for _ in 0..10 {
        assert_eq!(r.poll(), pending);
    }
    assert_eq!(usage, r.usage());
    assert_eq!(trace, r.backend().trace);
    local(&mut r);
    assert_eq!(r.backend().domains.len(), 1);
    assert!(matches!(r.poll(), Action::Local(_)));
    local(&mut r);
    assert_eq!(r.poll(), Action::Returned(vec![V::Field(12)]));
    assert_eq!(r.backend().domains.len(), 2);
}
#[test]
fn send_receive_pending_delivery_and_type_checks() {
    let j = exchange();
    let mut p = runner(&j, "P", Mock::new(), vec![V::Field(17)]);
    let mut v = runner(&j, "V", Mock::new(), vec![]);
    let pending = v.poll();
    let usage = v.usage();
    let trace = v.backend().trace.clone();
    for _ in 0..20 {
        assert_eq!(v.poll(), pending);
    }
    assert_eq!(v.usage(), usage);
    assert_eq!(v.backend().trace, trace);
    let cut = p.poll().cut().unwrap();
    let packet = p.take_send(&cut).unwrap();
    let mut wrong = packet.clone();
    wrong.ty = PhysicalType::default_for(LogicalType::parse("bool").unwrap()).unwrap();
    assert_eq!(v.deliver(wrong), Err(RuntimeError::Payload));
    let mut wrong = packet.clone();
    wrong.payload = V::Bool(false);
    assert_eq!(v.deliver(wrong), Err(RuntimeError::Payload));
    assert_eq!(v.poll(), pending);
    assert_eq!(v.usage(), usage);
    v.deliver(packet.clone()).unwrap();
    assert_eq!(v.poll(), Action::Returned(vec![V::Field(17)]));
    assert_eq!(v.deliver(packet), Err(RuntimeError::WrongAction));
    assert_eq!(p.poll(), Action::Returned(vec![]));
}
#[test]
fn every_envelope_dimension_is_matched() {
    let j = exchange();
    let mut p = runner(&j, "P", Mock::new(), vec![V::Field(1)]);
    let mut v = runner(&j, "V", Mock::new(), vec![]);
    let Action::Send(packet) = p.poll() else {
        panic!()
    };
    let before = v.poll();
    let mut variants = vec![];
    let mut q = packet.clone();
    q.envelope.origin.entry = "different".into();
    variants.push(q);
    let mut q = packet.clone();
    q.envelope.origin.instance = "different".into();
    variants.push(q);
    let mut q = packet.clone();
    q.envelope.origin.session = "different".into();
    variants.push(q);
    let mut q = packet.clone();
    q.envelope.origin.path.push(PathElement::Match {
        site: "case".into(),
        alternative: "child".into(),
    });
    variants.push(q);
    let mut q = packet.clone();
    q.envelope.site = "different".into();
    variants.push(q);
    let mut q = packet.clone();
    q.envelope.schema = "different".into();
    variants.push(q);
    let mut q = packet.clone();
    q.envelope.sender = "different".into();
    variants.push(q);
    let mut q = packet.clone();
    q.envelope.receiver = "different".into();
    variants.push(q);
    for q in variants {
        assert_eq!(v.deliver(q), Err(RuntimeError::Envelope));
        assert_eq!(v.poll(), before);
    }
}
#[test]
fn malicious_private_public_disguise_rejected_at_both_message_edges() {
    let j = exchange();
    let mut p = runner(&j, "P", Mock::new(), vec![V::PrivateAsField]);
    assert!(matches!(
        p.poll(),
        Action::Stopped(Stop {
            kind: StopKind::Backend(_),
            ..
        })
    ));
    let mut v = runner(&j, "V", Mock::new(), vec![]);
    let Action::Receive(request) = v.poll() else {
        panic!()
    };
    let packet = Packet {
        envelope: request.envelope,
        ty: PhysicalType::default_for(LogicalType::parse("field:bls12-381.fr").unwrap()).unwrap(),
        payload: V::PrivateAsField,
    };
    assert!(matches!(v.deliver(packet), Err(RuntimeError::Backend(_))));
    assert!(matches!(v.poll(), Action::Receive(_)));
    let mut j = exchange();
    j[3][0][4][0][1] = json!("rng");
    reject(&j, ErrorCode::Type);
}

#[test]
fn failure_inside_consuming_kernel_keeps_successor_and_runs_no_suffix() {
    let j = resource_child(true);
    let mut b = Mock::new();
    let r = b.issue(0, "P");
    let other = b.issue(1, "P");
    b.fail_draw = true;
    let mut runner = runner(&j, "P", b, vec![r, other, V::Bool(true)]);
    local(&mut runner);
    assert!(
        matches!(runner.poll(),Action::Stopped(Stop{kind:StopKind::Backend(BackendError{code}),..})if code=="failed-after-consume")
    );
    assert_eq!(runner.backend().slots[&0].generation, 1);
    assert_eq!(runner.backend().slots[&0].draws, 1);
    assert!(
        !runner
            .backend()
            .trace
            .iter()
            .any(|s| s == "arkworks/control.require")
    );
    assert_eq!(runner.backend().slots[&1].draws, 0);
}
#[test]
fn unissued_wrong_owner_and_stale_capabilities_fail_entry_admission() {
    let j = one(
        json!([]),
        json!([["r", "rng"]]),
        json!(["rng"]),
        json!([["return", ["r"]]]),
    );
    let a = admitted(&j);
    let fake = V::Cap {
        slot: 0,
        generation: 0,
        owner: "P".into(),
        seal: 4321,
    };
    assert!(matches!(
        Runner::new(&a, "main", "P", "s", Mock::new(), vec![fake])
            .err()
            .unwrap()
            .error,
        RuntimeError::Backend(_)
    ));
    let mut b = Mock::new();
    let wrong = b.issue(0, "V");
    assert!(Runner::new(&a, "main", "P", "s", b, vec![wrong]).is_err());
    let mut b = Mock::new();
    let stale = b.issue(0, "P");
    b.slots.get_mut(&0).unwrap().generation = 1;
    assert!(Runner::new(&a, "main", "P", "s", b, vec![stale]).is_err());
    let mut b = Mock::new();
    let mut forged = b.issue(0, "P");
    if let V::Cap { seal, .. } = &mut forged {
        *seal = 0;
    }
    assert!(Runner::new(&a, "main", "P", "s", b, vec![forged]).is_err());
}
#[test]
fn backend_output_contract_and_cleanup_errors_fail_closed() {
    let j = one(
        json!([add_fn()]),
        json!([["x", "field"]]),
        json!(["field"]),
        json!([["local", "a", "add", ["x", "x"], ["z"]], ["return", ["z"]]]),
    );
    let mut b = Mock::new();
    b.wrong_output = true;
    let mut r = runner(&j, "P", b, vec![V::Field(2)]);
    local(&mut r);
    assert!(matches!(r.poll(), Action::Stopped(_)));
    assert!(r.backend().frames.is_empty());
    let mut b = Mock::new();
    b.fail_leave = true;
    let mut r = runner(&j, "P", b, vec![V::Field(2)]);
    local(&mut r);
    let Action::Stopped(stop) = r.poll() else {
        panic!()
    };
    assert!(!stop.cleanup_errors.is_empty());
    assert!(r.backend().frames.is_empty());
}
#[test]
fn cancellation_unwinds_and_preserves_resource_state() {
    let j = resource_child(false);
    let mut b = Mock::new();
    let r = b.issue(0, "P");
    let other = b.issue(1, "P");
    let mut r = runner(&j, "P", b, vec![r, other, V::Bool(true)]);
    assert!(matches!(r.poll(), Action::Local(_)));
    r.cancel();
    assert!(matches!(
        r.poll(),
        Action::Stopped(Stop {
            kind: StopKind::Cancelled,
            ..
        })
    ));
    assert!(r.backend().frames.is_empty());
    assert_eq!(r.backend().slots[&0].draws, 0);
}
#[test]
fn unrelated_peer_stop_does_not_cancel_or_advance_role() {
    let j = exchange();
    let mut p = runner(&j, "P", Mock::new(), vec![V::Field(1)]);
    let mut v = runner(&j, "V", Mock::new(), vec![]);
    let pending = v.poll();
    let usage = v.usage();
    p.cancel();
    assert!(matches!(p.poll(), Action::Stopped(_)));
    assert_eq!(v.poll(), pending);
    assert_eq!(v.usage(), usage);
}

#[test]
fn explicit_driver_preserves_selected_order_after_peer_failure() {
    let guard = json!([
        "function",
        "guard",
        [["ok", "bool"]],
        [],
        [
            ["op", "require", "arkworks/control.require", [], ["ok"], []],
            ["return", []]
        ]
    ]);
    let j = module(
        json!([add_fn(), guard]),
        json!([
            participant(
                "mainP",
                "root",
                "P",
                json!([["x", "field"]]),
                json!(["field"]),
                json!([
                    ["local", "a", "add", ["x", "x"], ["y"]],
                    ["local", "b", "add", ["y", "x"], ["z"]],
                    ["return", ["z"]]
                ])
            ),
            participant(
                "mainV",
                "root",
                "V",
                json!([["ok", "bool"]]),
                json!([]),
                json!([["local", "check", "guard", ["ok"], []], ["return", []]])
            )
        ]),
        json!([["entry", "main", [["P", "mainP"], ["V", "mainV"]]]]),
    );
    let mut p = runner(&j, "P", Mock::new(), vec![V::Field(2)]);
    let mut v = runner(&j, "V", Mock::new(), vec![V::Bool(false)]);
    let a = p.poll().cut().unwrap();
    drive_cut(&mut p, &mut v, &DriverCut::Local(a)).unwrap();
    let check = v.poll().cut().unwrap();
    assert!(matches!(
        drive_cut(&mut p, &mut v, &DriverCut::Local(check)).unwrap(),
        DriverEvent::Local { stopped: true, .. }
    ));
    assert_eq!(p.backend().domains.len(), 1);
    let Action::Local(b) = p.poll() else { panic!() };
    assert_eq!(b.cut.site, "b");
    // An independent scheduler may subsequently advance P; V's stop is not an implicit wait/cancel.
    drive_cut(&mut p, &mut v, &DriverCut::Local(b.cut)).unwrap();
    assert_eq!(p.poll(), Action::Returned(vec![V::Field(6)]));
}
#[test]
fn wrong_driver_cut_and_cross_session_fail_without_local_execution() {
    let j = exchange();
    let mut p = runner(&j, "P", Mock::new(), vec![V::Field(1)]);
    let mut v = runner(&j, "V", Mock::new(), vec![]);
    let send = p.poll().cut().unwrap();
    let mut receive = v.poll().cut().unwrap();
    receive.site = "bad".into();
    assert_eq!(
        drive_cut(
            &mut p,
            &mut v,
            &DriverCut::Message {
                send: send.clone(),
                receive
            }
        ),
        Err(RuntimeError::WrongCut)
    );
    assert_eq!(p.poll().cut(), Some(send));
    let mut other = Runner::new(
        &admitted(&j),
        "main",
        "V",
        "another-session",
        Mock::new(),
        vec![],
    )
    .unwrap();
    let cut = DriverCut::Message {
        send: p.poll().cut().unwrap(),
        receive: other.poll().cut().unwrap(),
    };
    assert_eq!(
        drive_cut(&mut p, &mut other, &cut),
        Err(RuntimeError::Envelope)
    );
}

#[test]
fn failed_root_result_reservation_never_reports_returned_frame() {
    let j = one(
        json!([]),
        json!([["x", "field"]]),
        json!(["field", "field", "field"]),
        json!([["return", ["x", "x", "x"]]]),
    );
    for cleanup_failure in [false, true] {
        let mut backend = Mock::new();
        backend.fail_leave = cleanup_failure;
        let mut r = runner(&j, "P", backend, vec![V::Sized(34 * 1024 * 1024)]);
        let Action::Stopped(stop) = r.poll() else {
            panic!("oversized result must stop");
        };
        assert_eq!(stop.kind, StopKind::Limit);
        assert_eq!(stop.cleanup_errors.len(), usize::from(cleanup_failure));
        assert_eq!(r.backend().trace.last().unwrap(), "leave:Stopped");
        assert!(!r.backend().trace.iter().any(|s| s == "leave:Returned"));
        assert!(r.backend().frames.is_empty());
        assert_eq!(r.usage().live_values, 0);
        assert_eq!(r.usage().live_value_bytes, 0);
    }
}

// A second, deliberately tiny NONCRYPTOGRAPHIC value/service implementation
// demonstrates that the runner has no field-table or all-role environment ABI.
#[derive(Clone, Debug, PartialEq, Eq)]
enum G {
    Scalar(u64),
    Group(u64),
    Groups(Vec<u64>),
    Nonce(u64),
    Bool(bool),
}
impl Value for G {
    fn physical_type(&self) -> PhysicalType {
        PhysicalType::parse(&fixture_type(match self {
            Self::Scalar(_) => "field",
            Self::Group(_) => "group",
            Self::Groups(_) => "groups",
            Self::Nonce(_) => "nonce",
            Self::Bool(_) => "bool",
        }))
        .unwrap()
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        if matches!(self, Self::Nonce(_)) {
            Err(BackendError::new("private-nonce"))
        } else {
            Ok(())
        }
    }
    fn retained_bytes(&self) -> usize {
        16
    }
}
#[derive(Debug)]
struct GroupMock {
    generation: u64,
    consumed: u64,
    frames: Vec<(FrameId, bool)>,
}
impl GroupMock {
    fn new() -> Self {
        Self {
            generation: 0,
            consumed: 0,
            frames: vec![],
        }
    }
}
impl Backend for GroupMock {
    type Value = G;
    fn binding_signature(&self, binding: &OperationBinding) -> Option<BoundSignature> {
        binding.signature().ok()
    }
    fn validate_value(&self, value: &G) -> Result<(), BackendError> {
        if matches!(value,G::Scalar(n)|G::Group(n) if *n>=17) {
            Err(BackendError::new("reference-range"))
        } else {
            Ok(())
        }
    }
    fn enter_frame(&mut self, frame: &Frame, args: &[G]) -> Result<(), BackendError> {
        let mut nonce = false;
        for arg in args {
            if let G::Nonce(generation) = arg {
                if frame.role() != "P"
                    || *generation != self.generation
                    || self.frames.last().is_some_and(|(_, allowed)| !*allowed)
                {
                    return Err(BackendError::new("nonce-authority"));
                }
                nonce = true;
            }
        }
        self.frames.push((frame.id(), nonce));
        Ok(())
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        _: FrameExit,
        outputs: &[G],
    ) -> Result<(), BackendError> {
        let (id, allowed) = self.frames.pop().unwrap();
        assert_eq!(id, frame.id());
        for value in outputs {
            if let G::Nonce(generation) = value
                && (!allowed || *generation != self.generation)
            {
                return Err(BackendError::new("nonce-return"));
            }
        }
        Ok(())
    }
    fn apply(&mut self, i: &Invocation<'_>, args: &[G]) -> Result<Vec<G>, BackendError> {
        for arg in args {
            if let G::Nonce(generation) = arg {
                if *generation != self.generation || !self.frames.last().unwrap().1 {
                    return Err(BackendError::new("nonce-replay"));
                }
                self.generation += 1;
                self.consumed += 1;
            }
        }
        match (i.kernel, args) {
            ("arkworks/curve.generator", []) => Ok(vec![G::Group(3)]),
            ("arkworks/curve.empty", []) => Ok(vec![G::Groups(vec![])]),
            ("arkworks/curve.append", [G::Groups(gs), G::Group(g)]) => {
                let mut gs = gs.clone();
                gs.push(*g);
                Ok(vec![G::Groups(gs)])
            }
            ("arkworks/curve.at", [G::Groups(gs)]) => Ok(vec![G::Group(gs[0])]),
            ("arkworks/curve.commit", [G::Groups(gs), G::Nonce(_)]) => Ok(vec![
                G::Groups(gs.iter().map(|g| 5 * g % 17).collect()),
                G::Nonce(self.generation),
            ]),
            ("arkworks/curve.response", [G::Scalar(s), G::Scalar(c), G::Nonce(_)]) => {
                Ok(vec![G::Scalar((5 + s * c) % 17)])
            }
            ("arkworks/curve.scale", [G::Group(g), G::Scalar(s)]) => Ok(vec![G::Group(g * s % 17)]),
            ("arkworks/curve.add", [G::Group(a), G::Group(b)]) => Ok(vec![G::Group((a + b) % 17)]),
            ("arkworks/curve.equal", [G::Group(a), G::Group(b)]) => Ok(vec![G::Bool(a == b)]),
            ("arkworks/control.require", [G::Bool(true)]) => Ok(vec![]),
            ("arkworks/control.require", [G::Bool(false)]) => {
                Err(BackendError::new("reference-check-failed"))
            }
            _ => Err(BackendError::new("reference-unimplemented")),
        }
    }
}
fn group_exchange() -> Json {
    // A test-only numeric group mock exercises the real installed signatures;
    // it is not an implementation or cryptographic claim about BLS G1.
    module(
        json!([
            [
                "function",
                "commit",
                [["nonce", "nonce"]],
                ["group", "nonce"],
                [
                    ["op", "base", "curve.generator", [], [], ["g"]],
                    ["op", "empty", "curve.empty", [], [], ["empty"]],
                    [
                        "op",
                        "append",
                        "curve.append",
                        [],
                        ["empty", "g"],
                        ["bases"]
                    ],
                    [
                        "op",
                        "commitOp",
                        "curve.commit",
                        [],
                        ["bases", "nonce"],
                        ["points", "next"]
                    ],
                    ["op", "at", "curve.at", ["0"], ["points"], ["r"]],
                    ["return", ["r", "next"]]
                ]
            ],
            [
                "function",
                "response",
                [
                    ["secret", "field"],
                    ["challenge", "field"],
                    ["nonce", "nonce"]
                ],
                ["field"],
                [
                    [
                        "op",
                        "respond",
                        "curve.response",
                        [],
                        ["secret", "challenge", "nonce"],
                        ["z"]
                    ],
                    ["return", ["z"]]
                ]
            ],
            [
                "function",
                "check",
                [
                    ["y", "group"],
                    ["r", "group"],
                    ["c", "field"],
                    ["z", "field"]
                ],
                [],
                [
                    ["op", "base", "curve.generator", [], [], ["g"]],
                    ["op", "left", "curve.scale", [], ["g", "z"], ["left"]],
                    ["op", "scaled", "curve.scale", [], ["y", "c"], ["cy"]],
                    ["op", "right", "curve.add", [], ["r", "cy"], ["right"]],
                    [
                        "op",
                        "checkOp",
                        "curve.equal",
                        [],
                        ["left", "right"],
                        ["ok"]
                    ],
                    ["op", "guard", "control.require", [], ["ok"], []],
                    ["return", []]
                ]
            ]
        ]),
        json!([
            participant(
                "mainP",
                "root",
                "P",
                json!([["secret", "field"], ["nonce", "nonce"]]),
                json!([]),
                json!([
                    ["local", "commitCut", "commit", ["nonce"], ["r", "next"]],
                    ["send", "commitMsg", "groupSchema", "V", "r"],
                    [
                        "receive",
                        "challengeMsg",
                        "scalarSchema",
                        "V",
                        "challenge",
                        "field"
                    ],
                    [
                        "local",
                        "responseCut",
                        "response",
                        ["secret", "challenge", "next"],
                        ["z"]
                    ],
                    ["send", "responseMsg", "scalarSchema", "V", "z"],
                    ["return", []]
                ])
            ),
            participant(
                "mainV",
                "root",
                "V",
                json!([["public", "group"], ["challenge", "field"]]),
                json!([]),
                json!([
                    ["receive", "commitMsg", "groupSchema", "P", "r", "group"],
                    ["send", "challengeMsg", "scalarSchema", "P", "challenge"],
                    ["receive", "responseMsg", "scalarSchema", "P", "z", "field"],
                    [
                        "local",
                        "verifyCut",
                        "check",
                        ["public", "r", "challenge", "z"],
                        []
                    ],
                    ["return", []]
                ])
            )
        ]),
        json!([["entry", "main", [["P", "mainP"], ["V", "mainV"]]]]),
    )
}
#[test]
fn nonpolynomial_group_roles_use_distinct_typed_backend_and_consumed_nonce() {
    let j = group_exchange();
    let a = admit_supplied(&bytes(&j), &GroupMock::new()).unwrap();
    for hostile in [false, true] {
        let mut p = Runner::new(
            &a,
            "main",
            "P",
            "group-session",
            GroupMock::new(),
            vec![G::Scalar(2), G::Nonce(0)],
        )
        .unwrap();
        let mut v = Runner::new(
            &a,
            "main",
            "V",
            "group-session",
            GroupMock::new(),
            vec![G::Group(6), G::Scalar(4)],
        )
        .unwrap();
        let cut = p.poll().cut().unwrap();
        drive_cut(&mut p, &mut v, &DriverCut::Local(cut)).unwrap();
        let cut = DriverCut::Message {
            send: p.poll().cut().unwrap(),
            receive: v.poll().cut().unwrap(),
        };
        drive_cut(&mut p, &mut v, &cut).unwrap();
        let cut = DriverCut::Message {
            send: v.poll().cut().unwrap(),
            receive: p.poll().cut().unwrap(),
        };
        drive_cut(&mut p, &mut v, &cut).unwrap();
        let cut = p.poll().cut().unwrap();
        drive_cut(&mut p, &mut v, &DriverCut::Local(cut)).unwrap();
        if hostile {
            let cut = p.poll().cut().unwrap();
            let mut packet = p.take_send(&cut).unwrap();
            packet.payload = G::Scalar(0);
            v.deliver(packet).unwrap();
        } else {
            let cut = DriverCut::Message {
                send: p.poll().cut().unwrap(),
                receive: v.poll().cut().unwrap(),
            };
            drive_cut(&mut p, &mut v, &cut).unwrap();
        }
        let cut = v.poll().cut().unwrap();
        drive_cut(&mut p, &mut v, &DriverCut::Local(cut)).unwrap();
        if hostile {
            assert!(matches!(
                v.poll(),
                Action::Stopped(Stop {
                    kind: StopKind::Backend(_),
                    ..
                })
            ));
        } else {
            assert_eq!(v.poll(), Action::Returned(vec![]));
        }
        assert_eq!(p.poll(), Action::Returned(vec![]));
        assert_eq!(p.backend().consumed, 2);
        assert_eq!(v.backend().consumed, 0);
        assert!(p.backend().frames.is_empty());
        assert!(v.backend().frames.is_empty());
    }
}

#[test]
fn closed_profile_participants_are_not_an_execution_format() {
    let mut candidate = identity();
    for profile in [
        "arkworks.multilinear.bls12-381/0",
        "arkworks.bls12-381/0",
        "reference.group/0",
    ] {
        // Keep the format valid so the malformed bindings field is checked.
        candidate[0] = json!("zkc.program/0");
        candidate[1] = json!(profile);
        reject(&candidate, ErrorCode::Record);
    }
}

#[test]
fn reference_variant_selects_only_active_resource_and_preserves_stop_trace() {
    let ty = format!(
        "{}@logical.variant/0",
        zkc_test_support::variants::logical(
            "Reference",
            json!([["draw", ["rng:bls12-381.fr"]], ["empty", []]])
        )
    );
    for stop in [false, true] {
        let terminal = if stop {
            json!(["stop", "terminal", "exhausted"])
        } else {
            json!(["yield", ["x", "next"]])
        };
        let names = if stop {
            json!([])
        } else {
            json!(["x", "next"])
        };
        let tail = if stop {
            json!(["stop", "outer", "abort"])
        } else {
            json!(["return", ["x", "next"]])
        };
        let j = one(
            json!([[
                "function",
                "Variant",
                [["r", "rng"]],
                ["field", "rng"],
                [
                    ["variant", "pack", ty, "draw", ["r"], "v"],
                    [
                        "match",
                        "case",
                        "v",
                        [],
                        [
                            [
                                "draw",
                                ["active"],
                                [
                                    ["op", "draw", "random.draw", [], ["active"], ["x", "next"]],
                                    terminal
                                ]
                            ],
                            ["empty", [], [["stop", "inactive", "reject"]]]
                        ],
                        names
                    ],
                    tail
                ]
            ]]),
            json!([["r", "rng"]]),
            json!(["field", "rng"]),
            json!([
                ["local", "work", "Variant", ["r"], ["x", "next"]],
                ["return", ["x", "next"]]
            ]),
        );
        let mut backend = Mock::new();
        let rng = backend.issue(0, "P");
        let mut r = runner(&j, "P", backend, vec![rng]);
        local(&mut r);
        if stop {
            let Action::Stopped(stopped) = r.poll() else {
                panic!("terminal stop");
            };
            assert_eq!(stopped.kind, StopKind::Explicit("exhausted".into()));
            assert_eq!(stopped.site.as_deref(), Some("terminal"));
            assert_eq!(
                stopped.origin.path,
                vec![PathElement::Match {
                    site: "case".into(),
                    alternative: "draw".into()
                }]
            );
        } else {
            let Action::Returned(values) = r.poll() else {
                panic!("return");
            };
            assert_eq!(values[0], V::Field(1));
            assert!(matches!(&values[1], V::Cap { generation: 1, .. }));
        }
        assert_eq!(r.backend().slots[&0].generation, 1);
        assert_eq!(r.backend().slots[&0].draws, 1);
        assert_eq!(
            r.backend()
                .trace
                .iter()
                .filter(|s| s.as_str() == "arkworks/random.draw")
                .count(),
            1
        );
        assert!(r.backend().frames.is_empty());
        assert_eq!(
            r.backend()
                .trace
                .iter()
                .filter(|s| s.starts_with("leave:"))
                .count(),
            3
        );
    }
}

/// The runner does not trust a value's own account of its variant: a
/// descriptor, alternative or payload that disagrees with the value's type or
/// the matched arms stops the protocol.
#[test]
fn runner_refuses_a_variant_that_misreports_itself() {
    let j = one(
        json!([[
            "function",
            "Pick",
            [],
            [],
            [
                ["variant", "pack", tag_type(&[]), "yes", [], "v"],
                [
                    "match",
                    "case",
                    "v",
                    [],
                    [["yes", [], [["yield", []]]], ["no", [], [["yield", []]]]],
                    []
                ],
                ["return", []]
            ]
        ]]),
        json!([]),
        json!([]),
        json!([["local", "pick", "Pick", [], []], ["return", []]]),
    );
    let other = LogicalType::parse(&zkc_test_support::variants::logical(
        "Other",
        json!([["yes", []], ["no", []]]),
    ))
    .unwrap()
    .variant_descriptor()
    .unwrap()
    .clone();
    for (forgery, expected) in [
        (Forgery::Descriptor(other), "variant-descriptor"),
        (Forgery::Alternative(2), "variant-alternative"),
        (Forgery::Payload, "variant-payload"),
    ] {
        let _forging = Forging::install(forgery);
        let mut r = runner(&j, "P", Mock::new(), vec![]);
        local(&mut r);
        let Action::Stopped(stop) = r.poll() else {
            panic!("{expected}: expected a stop");
        };
        assert_eq!(stop.kind, StopKind::Backend(BackendError::new(expected)));
        assert!(r.backend().frames.is_empty(), "{expected}");
    }
}

const INDICES: &str = "indices@native.indices/0";
const INDEX: &str = "index@native.index/0";
const TRANSCRIPT: &str = "transcript:merlin3.bls12-381.fr64be/0@host.resource/0";

fn tag_type(payload: &[&str]) -> String {
    format!(
        "{}@logical.variant/0",
        zkc_test_support::variants::logical("Tag", json!([["yes", payload], ["no", []]]))
    )
}

/// A hand-written participant, not compiler output: one arm holds the body under
/// test over four data ports, and both arms yield an `indices` value.
fn data_arm(binding: Json, arm: Json) -> Json {
    let ports = json!([["s", INDICES], ["w", INDICES], ["n", INDEX], ["m", INDEX]]);
    let mut j = one(
        json!([[
            "function",
            "Work",
            ports,
            [INDICES],
            [
                ["variant", "pack", tag_type(&[]), "yes", [], "v"],
                [
                    "match",
                    "case",
                    "v",
                    ["s", "w", "n", "m"],
                    [["yes", [], arm], ["no", [], [["yield", ["s"]]]]],
                    ["out"]
                ],
                ["return", ["out"]]
            ]
        ]]),
        json!([["s", INDICES], ["w", INDICES], ["n", INDEX], ["m", INDEX]]),
        json!([INDICES]),
        json!([
            ["local", "work", "Work", ["s", "w", "n", "m"], ["out"]],
            ["return", ["out"]]
        ]),
    );
    j[1].as_array_mut().unwrap().push(binding);
    j
}

fn external_binding(contract: &str) -> Json {
    json!(["kernel", contract, [], format!("native/{contract}")])
}

fn external_arm(contract: &str, inputs: Json, outputs: Json, yielded: &str) -> Json {
    data_arm(
        external_binding(contract),
        json!([
            ["op", "effect", "kernel", [], inputs, outputs],
            ["yield", [yielded]]
        ]),
    )
}

/// Every external contract that carries transcript history is refused inside a
/// match arm. These states are ordinary checked data with no origin attribute,
/// so an attribute rule cannot see them:
/// docs/spec/realization/external-constructions.md.
#[test]
fn private_match_refuses_every_external_history_effect() {
    for (contract, inputs, outputs, yielded) in [
        (
            "external.openvm.observe",
            json!(["s", "w"]),
            json!(["s2"]),
            "s2",
        ),
        (
            "external.openvm.sample",
            json!(["s"]),
            json!(["s2", "i"]),
            "s2",
        ),
        (
            "external.openvm.sample_ext",
            json!(["s"]),
            json!(["s2", "c"]),
            "s2",
        ),
        (
            "external.openvm.sample_bits",
            json!(["s", "n"]),
            json!(["s2", "i"]),
            "s2",
        ),
        (
            "external.openvm.check_witness",
            json!(["s", "n", "m"]),
            json!(["s2", "ok"]),
            "s2",
        ),
        (
            "external.monero.update",
            json!(["s", "w"]),
            json!(["s2", "h"]),
            "s2",
        ),
    ] {
        let j = external_arm(contract, inputs, outputs, yielded);
        let error = admit_supplied(&bytes(&j), &Mock::new()).unwrap_err();
        assert_eq!(
            (error.code, error.detail.as_str()),
            (ErrorCode::Signature, "match-protocol-effect"),
            "{contract}"
        );
    }
}

/// The same arm admits the external operations that touch no history: a state
/// constructor and a stateless hash. The refusal above is about the effect, not
/// about the `external.` name or the shape of the fixture.
#[test]
fn private_match_admits_external_construction_and_stateless_hash() {
    for (contract, inputs) in [
        ("external.monero.init", json!(["s"])),
        ("external.monero.hash", json!(["s"])),
        ("external.openvm.init", json!([])),
    ] {
        let j = external_arm(contract, inputs, json!(["s2"]), "s2");
        admit_supplied(&bytes(&j), &Mock::new())
            .unwrap_or_else(|e| panic!("{contract}: {}", e.detail));
    }
}

/// A history effect nested in local control inside the arm is the same effect.
#[test]
fn private_match_refuses_a_history_effect_under_nested_local_control() {
    let j = data_arm(
        external_binding("external.openvm.sample"),
        json!([
            [
                "for",
                "repeat",
                "i",
                "n",
                "m",
                [["carried", "s"]],
                [],
                [
                    ["op", "effect", "kernel", [], ["carried"], ["next", "drawn"]],
                    ["yield", ["next"]]
                ],
                ["sampled"]
            ],
            ["yield", ["sampled"]]
        ]),
    );
    let error = admit_supplied(&bytes(&j), &Mock::new()).unwrap_err();
    assert_eq!(
        (error.code, error.detail.as_str()),
        (ErrorCode::Signature, "match-protocol-effect")
    );
}

/// The internal transcript family stays refused for absorption as well as for
/// sampling, now that the arm restriction reads the contract rather than the
/// operation's attribute rule.
#[test]
fn private_match_refuses_internal_transcript_observation_and_challenge() {
    let suite = "merlin3.bls12-381.fr64be/0";
    for (contract, arguments, inputs, outputs) in [
        (
            "transcript.native.indexed.observe.data",
            json!([suite, "index"]),
            json!(["t", "n", "coordinates"]),
            json!(["t2"]),
        ),
        (
            "transcript.native.indexed.challenge",
            json!([suite]),
            json!(["t", "coordinates"]),
            json!(["x", "t2"]),
        ),
    ] {
        let mut j = one(
            json!([[
                "function",
                "Work",
                [
                    ["t", TRANSCRIPT],
                    ["n", INDEX],
                    ["coordinates", "indices@native.indices/0"]
                ],
                [TRANSCRIPT],
                [
                    ["variant", "pack", tag_type(&[]), "yes", [], "v"],
                    [
                        "match",
                        "case",
                        "v",
                        ["t", "n", "coordinates"],
                        [
                            [
                                "yes",
                                [],
                                [
                                    [
                                        "op",
                                        "effect",
                                        "kernel",
                                        [zkc_test_support::hex(
                                            &crate::logical::encode_tree(&json!([
                                                "zkc.native-origin-template/0",
                                                "main",
                                                [],
                                                [],
                                                if contract.ends_with("data") {
                                                    json!([
                                                        "message", "Source", "site", "Schema", "P",
                                                        "V"
                                                    ])
                                                } else {
                                                    json!([
                                                        "query",
                                                        "Source",
                                                        "draw",
                                                        "input_0",
                                                        "random.bls12-381.fr/0",
                                                        "draw",
                                                        "V"
                                                    ])
                                                }
                                            ]))
                                            .unwrap()
                                        )],
                                        inputs,
                                        outputs
                                    ],
                                    ["yield", ["t2"]]
                                ]
                            ],
                            ["no", [], [["yield", ["t"]]]]
                        ],
                        ["out"]
                    ],
                    ["return", ["out"]]
                ]
            ]]),
            json!([
                ["t", TRANSCRIPT],
                ["n", INDEX],
                ["coordinates", "indices@native.indices/0"]
            ]),
            json!([TRANSCRIPT]),
            json!([
                ["local", "work", "Work", ["t", "n", "coordinates"], ["out"]],
                ["return", ["out"]]
            ]),
        );
        j[1].as_array_mut().unwrap().push(json!([
            "kernel",
            contract,
            arguments,
            format!("arkworks/{contract}")
        ]));
        let mut outside_match = j.clone();
        outside_match[2][0][4] = json!([j[2][0][4][1][4][0][2][0], ["return", ["t2"]]]);
        admitted(&outside_match);
        let error = admit_supplied(&bytes(&j), &Mock::new()).unwrap_err();
        assert_eq!(
            (error.code, error.detail.as_str()),
            (ErrorCode::Signature, "match-protocol-effect"),
            "{contract}"
        );
    }
}

/// A candidate whose only difference is the payload leaf spelling. The witness
/// check runs outside the arm, where it is allowed, and supplies the `bool` the
/// descriptor carries.
fn tagged_witness(leaf: &str) -> Json {
    let ports = json!([["s", INDICES], ["n", INDEX], ["m", INDEX]]);
    let mut j = one(
        json!([[
            "function",
            "Work",
            ports,
            [INDICES],
            [
                ["op", "witness", "kernel", [], ["s", "n", "m"], ["s2", "ok"]],
                ["variant", "pack", tag_type(&[leaf]), "yes", ["ok"], "v"],
                [
                    "match",
                    "case",
                    "v",
                    ["s2"],
                    [
                        ["yes", ["b"], [["yield", ["s2"]]]],
                        ["no", [], [["yield", ["s2"]]]]
                    ],
                    ["out"]
                ],
                ["return", ["out"]]
            ]
        ]]),
        json!([["s", INDICES], ["n", INDEX], ["m", INDEX]]),
        json!([INDICES]),
        json!([
            ["local", "work", "Work", ["s", "n", "m"], ["out"]],
            ["return", ["out"]]
        ]),
    );
    j[1].as_array_mut()
        .unwrap()
        .push(external_binding("external.openvm.check_witness"));
    j
}

/// One logical type has one spelling. `bool:` parses to the same type as `bool`,
/// and a descriptor keeps the text it was given, so admitting both would mint a
/// second nominal identity for one payload. Readers do not silently normalize a
/// different identity to an admitted spelling:
/// docs/spec/profiles/compiler/local-variants.md.
#[test]
fn leaf_payload_types_have_a_single_canonical_spelling() {
    for alias in ["bool:", "index:", "indices:"] {
        let error = LogicalType::parse(alias).unwrap_err();
        assert_eq!(
            (error.code, error.detail.as_str()),
            (ErrorCode::Type, "noncanonical nominal spelling"),
            "{alias}"
        );
    }
    for canonical in ["bool", "index", "indices", "field:bls12-381.fr"] {
        assert_eq!(LogicalType::parse(canonical).unwrap().spelling(), canonical);
    }
    admitted(&tagged_witness("bool"));
    assert_eq!(
        admit_supplied(&bytes(&tagged_witness("bool:")), &Mock::new())
            .unwrap_err()
            .code,
        ErrorCode::Type
    );
}

#[test]
fn program_ports_admit_copyable_variants_and_refuse_affine_payloads() {
    let logical = zkc_test_support::variants::logical("Local", json!([["empty", []]]));
    let ty = format!("{logical}@logical.variant/0");
    let mut program = json!([
        "zkc.program/0",
        [],
        [],
        [[
            "participant",
            "p",
            "root",
            "P",
            [["x", ty]],
            [ty],
            [["return", ["x"]]],
            []
        ]],
        [["entry", "main", [["P", "p"]]]]
    ]);
    admit_supplied(&bytes(&program), &Mock::new()).unwrap();
    let affine = zkc_test_support::variants::logical(
        "Local",
        json!([["empty", []], ["owned", ["rng:bls12-381.fr"]]]),
    );
    let affine = format!("{affine}@logical.variant/0");
    program[3][0][4][0][1] = json!(affine);
    program[3][0][5][0] = json!(affine);
    let error = admit_supplied(&bytes(&program), &Mock::new()).unwrap_err();
    assert_eq!(error.code, ErrorCode::Type);
    assert_eq!(error.detail, "variant-participant-boundary");
}

#[test]
fn local_stop_identifies_its_namespace_when_a_participant_site_collides() {
    let j = one(
        json!([["function", "check", [], [], [["stop", "message", "reject"]]]]),
        json!([["x", "field"]]),
        json!([]),
        json!([
            ["local", "guard", "check", [], []],
            ["send", "message", "schema", "V", "x"],
            ["return", []]
        ]),
    );
    let mut r = runner(&j, "P", Mock::new(), vec![V::Field(3)]);
    let cut = r.poll().cut().unwrap();
    r.execute_local(&cut).unwrap();
    let Action::Stopped(stop) = r.poll() else {
        panic!("stop")
    };
    assert_eq!(stop.site.as_deref(), Some("message"));
    assert_eq!(
        stop.local,
        Some(Box::new(LocalContext {
            site: "guard".into(),
            function: "check".into(),
            instruction: Some("message".into())
        }))
    );
    assert!(r.backend().frames.is_empty());
}

#[test]
fn admitted_program_owns_its_bytes() {
    let mut data = bytes(&identity());
    let expected = data.clone();
    let admitted = admit_supplied(&data, &Mock::new()).unwrap();
    data.fill(b' ');
    assert_eq!(admitted.bytes(), expected);
}

// Two independently owned resources; only the actual local operand enters its frame.
fn resource_child(_failing: bool) -> Json {
    one(
        json!([draw_fn()]),
        json!([["r", "rng"], ["other", "rng"], ["ok", "bool"]]),
        json!([]),
        json!([
            ["local", "draw", "draw", ["r"], ["value", "next"]],
            ["return", []]
        ]),
    )
}
