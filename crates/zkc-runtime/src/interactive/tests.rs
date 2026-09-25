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
    Oversize,
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
                .any(|(t, v)| PhysicalType::default_for(t.clone()) != v.physical_type())
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
            return PhysicalType::default_for(LogicalType::variant(d.clone()));
        }
        let logical = match self {
            Self::Bool(_) => "bool",
            Self::Cap { .. } => "rng:bls12-381.fr",
            _ => "field:bls12-381.fr",
        };
        PhysicalType::default_for(LogicalType::parse(logical).unwrap())
    }
    fn type_name(&self) -> &str {
        match self {
            Self::Variant(..) => "variant",
            Self::Bool(_) => "bool",
            Self::Cap { .. } => "rng",
            _ => "field",
        }
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
            Self::Oversize => usize::MAX,
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
    fn validate_value(&self, value: &V) -> Result<(), BackendError> {
        // PrivateAsField deliberately passes local representation validation;
        // independent public-value validation must still reject it at a message.
        if matches!(value, V::Oversize) {
            return Err(BackendError::new("size"));
        }
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
        "bool" => return PhysicalType::default_for(LogicalType::parse("bool").unwrap()).spelling(),
        "field" | "scalar" => "bls12-381.fr",
        "group" | "groups" => "bls12-381.g1",
        "transcript" => "merlin3.bls12-381.fr64be/1",
        "prover_key" | "verifier_key" | "opening_state" | "commitment" | "proof" => {
            "multilinear.kzg.bls12-381/1"
        }
        _ => "bls12-381.fr",
    };
    let kind = if kind == "scalar" { "field" } else { kind };
    PhysicalType::default_for(LogicalType::parse(&format!("{kind}:{identity}")).unwrap()).spelling()
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
        for port in p[5].as_array_mut().unwrap() {
            port[1] = json!(fixture_type(port[1].as_str().unwrap()));
        }
        for ty in p[6].as_array_mut().unwrap() {
            *ty = json!(fixture_type(ty.as_str().unwrap()));
        }
        fixture_body(&mut p[7]);
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
    json!([
        "zkc.participants/1",
        bindings,
        "physical",
        functions,
        participants,
        entries
    ])
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
        [],
        inputs,
        outputs,
        body
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
    j[0] = json!("zkc.protocol/2");
    reject(&j, ErrorCode::Record);
    let mut j = identity();
    j.as_array_mut().unwrap().push(json!([]));
    reject(&j, ErrorCode::Record);
    let mut j = identity();
    j[4][0][1] = json!("bad/name");
    reject(&j, ErrorCode::Name);
    let mut j = identity();
    j[4][0][1] = json!("é");
    reject(&j, ErrorCode::Name);
    let mut j = identity();
    j[4][0][1] = json!("x".repeat(129));
    reject(&j, ErrorCode::Name);
    let mut j = identity();
    j[4][0][7][0].as_array_mut().unwrap().push(json!([]));
    reject(&j, ErrorCode::Record);
    let mut j = identity();
    j[4][0][7] = json!([["opaque", "anything"]]);
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
fn stage_binding_records_and_non_nominal_types_rejected() {
    for stage in ["logical", "source", "Physical", ""] {
        let mut j = identity();
        j[2] = json!(stage);
        reject(&j, ErrorCode::Stage);
    }
    let mut j = identity();
    j[1] = json!("caller.backend/1");
    reject(&j, ErrorCode::Record);
    for ty in ["opaque:Secret", "nonce", "custom", "arkworks.field"] {
        let mut j = identity();
        j[4][0][5][0][1] = json!(ty);
        reject(&j, ErrorCode::Type);
    }
}
#[test]
fn symbol_and_signature_admission() {
    let mut j = identity();
    let duplicate = j[4][0].clone();
    j[4].as_array_mut().unwrap().push(duplicate);
    reject(&j, ErrorCode::Symbol);
    let mut j = identity();
    j[5][0][2][0][1] = json!("missing");
    reject(&j, ErrorCode::Symbol);
    let mut j = identity();
    j[5][0][2][0][0] = json!("V");
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
        j[3][0][4][0][2] = json!(kernel);
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
        j[3][0][4][0][3] = json!([s]);
        reject(&j, ErrorCode::Attributes);
    }
    for attrs in [json!([]), json!(["1", "2"])] {
        let mut j = base.clone();
        j[3][0][4][0][3] = attrs;
        reject(&j, ErrorCode::Attributes);
    }
    let mut j = one(
        json!([add_fn()]),
        json!([]),
        json!([]),
        json!([["return", []]]),
    );
    j[3][0][4][0][3] = json!(["0"]);
    reject(&j, ErrorCode::Attributes);
}
#[test]
fn ssa_terminal_and_site_checks() {
    let mut j = identity();
    j[4][0][7][0][1] = json!(["foreign"]);
    reject(&j, ErrorCode::Ssa);
    let mut j = identity();
    j[4][0][5]
        .as_array_mut()
        .unwrap()
        .push(json!(["x", fixture_type("field")]));
    reject(&j, ErrorCode::Ssa);
    let mut j = identity();
    j[4][0][7]
        .as_array_mut()
        .unwrap()
        .push(json!(["return", ["x"]]));
    reject(&j, ErrorCode::Terminal);
    let mut j = identity();
    j[4][0][7] = json!([]);
    reject(&j, ErrorCode::Terminal);
    let mut j = identity();
    j[4][0][7][0][0] = json!("yield");
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
    j[4][0][7][1][1] = json!("other");
    j[4][0][7][1][4] = json!(["x"]);
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
fn immutable_custody_and_explicit_source_checker() {
    struct Exact {
        source: Vec<u8>,
        candidate: Vec<u8>,
    }
    impl Correspondence for Exact {
        fn check(&self, s: &[u8], c: &[u8], _: ArtifactFormat) -> Result<(), AdmissionError> {
            if s == self.source && c == self.candidate {
                Ok(())
            } else {
                Err(AdmissionError::new(ErrorCode::Correspondence, "mock-check"))
            }
        }
        fn check_with_mapping(
            &self,
            s: &[u8],
            c: &[u8],
            format: ArtifactFormat,
        ) -> Result<Option<SourceMap>, AdmissionError> {
            self.check(s, c, format)?;
            Ok(Some(SourceMap {
                ports: vec![PortMapping {
                    instance: "root".into(),
                    role: "P".into(),
                    participant: "mainP".into(),
                    arguments: vec![("x".into(), "x".into())],
                }],
                calls: vec![],
            }))
        }
    }
    let mut data = bytes(&identity());
    let expected = data.clone();
    let checker = Exact {
        source: b"source fixture".to_vec(),
        candidate: expected.clone(),
    };
    let a = admit_physical(b"source fixture", &data, &Mock::new(), &checker).unwrap();
    data.fill(b' ');
    assert_eq!(a.bytes(), expected);
    assert_eq!(a.checked_source(), Some(b"source fixture".as_slice()));
    assert!(admit_physical(b"wrong", &expected, &Mock::new(), &checker).is_err());
    assert!(admitted(&identity()).checked_source().is_none());
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
    wrong.ty = PhysicalType::default_for(LogicalType::parse("bool").unwrap());
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
    q.envelope.origin.path.push(PathElement::Call {
        site: "call".into(),
        instance: "child".into(),
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
        ty: PhysicalType::default_for(LogicalType::parse("field:bls12-381.fr").unwrap()),
        payload: V::PrivateAsField,
    };
    assert!(matches!(v.deliver(packet), Err(RuntimeError::Backend(_))));
    assert!(matches!(v.poll(), Action::Receive(_)));
    let mut j = exchange();
    j[4][0][5][0][1] = json!("rng");
    reject(&j, ErrorCode::Type);
}

#[test]
fn instance_identity_parameters_and_call_graph() {
    let mut j = exchange();
    j[4][0][4] = json!([["n", "2"]]);
    j[4][1][4] = json!([["n", "3"]]);
    reject(&j, ErrorCode::Parameters);
    let mut j = identity();
    j[4][0][4] = json!([["n", "1"], ["n", "1"]]);
    reject(&j, ErrorCode::Parameters);
    for n in ["01", "-1", "+0", "18446744073709551616"] {
        let mut j = identity();
        j[4][0][4] = json!([["n", n]]);
        reject(&j, ErrorCode::Natural);
    }
    let mut j = identity();
    j[4][0][4] = json!([["n", "1048577"]]);
    reject(&j, ErrorCode::Limit);
    let mut j = exchange();
    let mut duplicate = j[4][0].clone();
    duplicate[1] = json!("aliasP");
    j[4].as_array_mut().unwrap().push(duplicate);
    reject(&j, ErrorCode::Symbol);
    let mut j = exchange();
    j[4][0][7] = json!([["call", "child", "mainV", [], ["z"]], ["return", []]]);
    reject(&j, ErrorCode::Role);
    let mut j = identity();
    j[4][0][7] = json!([
        ["call", "recursive", "mainP", ["x"], ["z"]],
        ["return", ["z"]]
    ]);
    reject(&j, ErrorCode::Cycle);
    let j = module(
        json!([]),
        json!([
            participant(
                "mainP",
                "root",
                "P",
                json!([]),
                json!([]),
                json!([["call", "a", "childP", [], []], ["return", []]])
            ),
            participant(
                "childP",
                "child",
                "P",
                json!([]),
                json!([]),
                json!([["call", "b", "mainP", [], []], ["return", []]])
            )
        ]),
        json!([["entry", "main", [["P", "mainP"]]]]),
    );
    reject(&j, ErrorCode::Cycle);
}
fn repeated_exchange(count: &str) -> Json {
    let mut participants = vec![];
    for role in ["P", "V"] {
        let is_p = role == "P";
        participants.push(participant(
            &format!("main{role}"),
            "root",
            role,
            if is_p {
                json!([["x", "field"]])
            } else {
                json!([])
            },
            json!([]),
            json!([
                [
                    "loop",
                    "outer",
                    count,
                    [],
                    if is_p { json!(["x"]) } else { json!([]) },
                    [
                        [
                            "call",
                            "first",
                            format!("wrapper{role}"),
                            if is_p { json!(["x"]) } else { json!([]) },
                            []
                        ],
                        [
                            "call",
                            "second",
                            format!("wrapper{role}"),
                            if is_p { json!(["x"]) } else { json!([]) },
                            []
                        ],
                        ["yield", []]
                    ],
                    []
                ],
                ["return", []]
            ]),
        ));
        participants.push(participant(
            &format!("wrapper{role}"),
            "wrapper",
            role,
            if is_p {
                json!([["x", "field"]])
            } else {
                json!([])
            },
            json!([]),
            json!([
                [
                    "call",
                    "nested",
                    format!("leaf{role}"),
                    if is_p { json!(["x"]) } else { json!([]) },
                    []
                ],
                ["return", []]
            ]),
        ));
        participants.push(participant(
            &format!("leaf{role}"),
            "leaf",
            role,
            if is_p {
                json!([["x", "field"]])
            } else {
                json!([])
            },
            json!([]),
            if is_p {
                json!([["send", "wire", "fieldSchema", "V", "x"], ["return", []]])
            } else {
                json!([
                    ["receive", "wire", "fieldSchema", "P", "y", "field"],
                    ["return", []]
                ])
            },
        ));
    }
    module(
        json!([]),
        json!(participants),
        json!([["entry", "main", [["P", "mainP"], ["V", "mainV"]]]]),
    )
}
#[test]
fn repeated_nested_calls_share_definitions_and_reject_cross_call_packets() {
    let j = repeated_exchange("2");
    let a = admitted(&j);
    assert_eq!(a.program.participants.len(), 6);
    let mut p = runner(&j, "P", Mock::new(), vec![V::Field(5)]);
    let mut v = runner(&j, "V", Mock::new(), vec![]);
    let mut previous: Option<Packet<V>> = None;
    let mut origins = vec![];
    for iteration in 0..2 {
        for call in ["first", "second"] {
            let Action::Send(packet) = p.poll() else {
                panic!()
            };
            assert_eq!(packet.envelope.origin.instance, "leaf");
            assert_eq!(
                packet.envelope.origin.path,
                vec![
                    PathElement::Loop {
                        site: "outer".into(),
                        iteration
                    },
                    PathElement::Call {
                        site: call.into(),
                        instance: "wrapper".into()
                    },
                    PathElement::Call {
                        site: "nested".into(),
                        instance: "leaf".into()
                    }
                ]
            );
            let pending = v.poll();
            let usage = v.usage();
            let trace = v.backend().trace.clone();
            for _ in 0..3 {
                assert_eq!(v.poll(), pending);
            }
            assert_eq!(v.usage(), usage);
            assert_eq!(v.backend().trace, trace);
            if let Some(old) = &previous {
                assert_eq!(v.deliver(old.clone()), Err(RuntimeError::Envelope));
            }
            let cut = DriverCut::Message {
                send: p.poll().cut().unwrap(),
                receive: v.poll().cut().unwrap(),
            };
            drive_cut(&mut p, &mut v, &cut).unwrap();
            origins.push(packet.envelope.domain_bytes());
            previous = Some(packet);
        }
    }
    assert_eq!(origins.iter().collect::<BTreeSet<_>>().len(), 4);
    assert_eq!(p.poll(), Action::Returned(vec![]));
    assert_eq!(v.poll(), Action::Returned(vec![]));
    assert_eq!(p.usage().calls, 8);
    assert_eq!(v.usage().calls, 8);
    assert!(p.backend().frames.is_empty());
    assert!(v.backend().frames.is_empty());
}
#[test]
fn zero_and_empty_loop_state_preserve_control() {
    let mut j = one(
        json!([]),
        json!([["x", "field"]]),
        json!(["field"]),
        json!([
            [
                "loop",
                "zero",
                "0",
                [["a", "x"]],
                [],
                [["stop", "bodyStop", "abort"]],
                ["z"]
            ],
            ["return", ["z"]]
        ]),
    );
    let mut r = runner(&j, "P", Mock::new(), vec![V::Field(7)]);
    assert_eq!(r.poll(), Action::Returned(vec![V::Field(7)]));
    assert_eq!(r.usage().iterations, 0);
    j[4][0][7][0][2] = json!("1");
    let mut r = runner(&j, "P", Mock::new(), vec![V::Field(7)]);
    assert!(matches!(
        r.poll(),
        Action::Stopped(Stop {
            kind: StopKind::Explicit(_),
            ..
        })
    ));
    let j = one(
        json!([]),
        json!([]),
        json!([]),
        json!([
            ["loop", "empty", "3", [], [], [["yield", []]], []],
            ["return", []]
        ]),
    );
    let mut r = runner(&j, "P", Mock::new(), vec![]);
    assert_eq!(r.poll(), Action::Returned(vec![]));
    assert_eq!(r.usage().iterations, 3);
    let j = repeated_exchange("0");
    let mut r = runner(&j, "V", Mock::new(), vec![]);
    assert_eq!(r.poll(), Action::Returned(vec![]));
    assert_eq!(r.usage().calls, 0);
}
#[test]
fn nested_loops_carried_state_closed_captures_and_iteration_order() {
    let j = one(
        json!([add_fn()]),
        json!([["x", "field"], ["increment", "field"]]),
        json!(["field"]),
        json!([
            [
                "loop",
                "outer",
                "2",
                [["a", "x"]],
                ["increment"],
                [
                    [
                        "loop",
                        "inner",
                        "3",
                        [["b", "a"]],
                        ["increment"],
                        [
                            ["local", "step", "add", ["b", "increment"], ["c"]],
                            ["yield", ["c"]]
                        ],
                        ["d"]
                    ],
                    ["yield", ["d"]]
                ],
                ["z"]
            ],
            ["return", ["z"]]
        ]),
    );
    let mut r = runner(&j, "P", Mock::new(), vec![V::Field(2), V::Field(3)]);
    for outer in 0..2 {
        for inner in 0..3 {
            let Action::Local(a) = r.poll() else { panic!() };
            assert_eq!(
                a.cut.origin.path,
                vec![
                    PathElement::Loop {
                        site: "outer".into(),
                        iteration: outer
                    },
                    PathElement::Loop {
                        site: "inner".into(),
                        iteration: inner
                    }
                ]
            );
            r.execute_local(&a.cut).unwrap();
        }
    }
    assert_eq!(r.poll(), Action::Returned(vec![V::Field(20)]));
    assert_eq!(r.usage().iterations, 8);
    let mut bad = j.clone();
    bad[4][0][7][0][4] = json!([]);
    reject(&bad, ErrorCode::Ssa);
    let mut bad = j.clone();
    bad[4][0][7][0][5][0][4] = json!(["increment", "increment"]);
    reject(&bad, ErrorCode::Capture);
    let mut bad = j.clone();
    bad[4][0][7][0][5][0][5][1][1] = json!([]);
    reject(&bad, ErrorCode::Signature);
    let mut bad = j;
    bad[4][0][7][0][5][0][5][1][0] = json!("return");
    reject(&bad, ErrorCode::Terminal);
}
#[test]
fn loop_count_and_parameter_admission_limits() {
    for value in [
        json!("01"),
        json!("-1"),
        json!("1.0"),
        json!("1048577"),
        json!(["constant", "1"]),
        json!(1),
    ] {
        let j = one(
            json!([]),
            json!([]),
            json!([]),
            json!([
                ["loop", "l", value, [], [], [["yield", []]], []],
                ["return", []]
            ]),
        );
        assert!(admit_supplied(&bytes(&j), &Mock::new()).is_err());
    }
}
#[test]
fn call_signature_and_instance_parameter_context_survive_execution() {
    let mut j = module(
        json!([add_fn()]),
        json!([
            participant(
                "mainP",
                "root",
                "P",
                json!([["x", "field"]]),
                json!(["field"]),
                json!([
                    ["call", "childCall", "childP", ["x"], ["y"]],
                    ["call", "again", "childP", ["y"], ["z"]],
                    ["return", ["z"]]
                ])
            ),
            participant(
                "childP",
                "selected",
                "P",
                json!([["arg", "field"]]),
                json!(["field"]),
                json!([
                    ["local", "twice", "add", ["arg", "arg"], ["out"]],
                    ["return", ["out"]]
                ])
            )
        ]),
        json!([["entry", "main", [["P", "mainP"]]]]),
    );
    j[4][0][4] = json!([["n", "4"]]);
    j[4][1][4] = json!([["n", "2"]]);
    let mut r = runner(&j, "P", Mock::new(), vec![V::Field(3)]);
    local(&mut r);
    local(&mut r);
    assert_eq!(r.poll(), Action::Returned(vec![V::Field(12)]));
    assert_ne!(r.backend().domains[0], r.backend().domains[1]);
    assert!(
        String::from_utf8(r.backend().domains[0].clone())
            .unwrap()
            .contains("[\"n\",\"2\"]")
    );
    let mut bad = j.clone();
    bad[4][0][7][0][3] = json!([]);
    reject(&bad, ErrorCode::Signature);
    let mut bad = j;
    bad[4][0][7][0][2] = json!("missing");
    reject(&bad, ErrorCode::Symbol);
}
fn resource_child(failing: bool) -> Json {
    let f = if failing {
        json!([
            "function",
            "resource",
            [["r", "rng"], ["ok", "bool"]],
            ["rng"],
            [
                [
                    "op",
                    "prefix",
                    "arkworks/random.draw",
                    [],
                    ["r"],
                    ["x", "r1"]
                ],
                ["op", "guard", "arkworks/control.require", [], ["ok"], []],
                [
                    "op",
                    "suffix",
                    "arkworks/random.draw",
                    [],
                    ["r1"],
                    ["y", "r2"]
                ],
                ["return", ["r2"]]
            ]
        ])
    } else {
        json!([
            "function",
            "resource",
            [["r", "rng"], ["ok", "bool"]],
            ["rng"],
            [
                [
                    "op",
                    "prefix",
                    "arkworks/random.draw",
                    [],
                    ["r"],
                    ["x", "r1"]
                ],
                ["return", ["r1"]]
            ]
        ])
    };
    module(
        json!([f]),
        json!([
            participant(
                "mainP",
                "root",
                "P",
                json!([["r", "rng"], ["other", "rng"], ["ok", "bool"]]),
                json!(["rng", "rng"]),
                json!([
                    ["call", "focus", "childP", ["r", "ok"], ["next"]],
                    ["return", ["next", "other"]]
                ])
            ),
            participant(
                "childP",
                "child",
                "P",
                json!([["r", "rng"], ["ok", "bool"]]),
                json!(["rng"]),
                json!([
                    ["local", "work", "resource", ["r", "ok"], ["next"]],
                    ["return", ["next"]]
                ])
            )
        ]),
        json!([["entry", "main", [["P", "mainP"]]]]),
    )
}
#[test]
fn focused_child_success_and_failure_preserve_unaffected_frame() {
    for succeeds in [true, false] {
        let j = resource_child(true);
        let mut b = Mock::new();
        let r = b.issue(0, "P");
        let other = b.issue(1, "P");
        let mut runner = runner(&j, "P", b, vec![r, other.clone(), V::Bool(succeeds)]);
        local(&mut runner);
        if succeeds {
            let Action::Returned(values) = runner.poll() else {
                panic!()
            };
            assert_eq!(values[1], other);
        } else {
            assert!(
                matches!(runner.poll(),Action::Stopped(Stop{kind:StopKind::Backend(BackendError{code}),..})if code=="require-failed")
            );
        }
        assert_eq!(
            runner.backend().slots[&0].draws,
            if succeeds { 2 } else { 1 }
        );
        assert_eq!(runner.backend().slots[&1].draws, 0);
        assert_eq!(runner.backend().slots[&1].generation, 0);
        assert!(runner.backend().frames.is_empty());
        let backend = runner.into_backend();
        assert_eq!(backend.slots[&0].generation, if succeeds { 2 } else { 1 });
    }
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
fn aliased_actual_arguments_fail_after_real_focused_prefix() {
    let f = json!([
        "function",
        "alias",
        [["a", "rng"], ["b", "rng"]],
        [],
        [
            [
                "op",
                "first",
                "arkworks/random.draw",
                [],
                ["a"],
                ["x", "a1"]
            ],
            [
                "op",
                "second",
                "arkworks/random.draw",
                [],
                ["b"],
                ["y", "b1"]
            ],
            ["return", []]
        ]
    ]);
    let j = module(
        json!([f]),
        json!([
            participant(
                "mainP",
                "root",
                "P",
                json!([["a", "rng"], ["b", "rng"], ["other", "rng"]]),
                json!([]),
                json!([["call", "focus", "childP", ["a", "b"], []], ["return", []]])
            ),
            participant(
                "childP",
                "child",
                "P",
                json!([["a", "rng"], ["b", "rng"]]),
                json!([]),
                json!([["local", "work", "alias", ["a", "b"], []], ["return", []]])
            )
        ]),
        json!([["entry", "main", [["P", "mainP"]]]]),
    );
    let mut b = Mock::new();
    let a = b.issue(0, "P");
    let other = b.issue(1, "P");
    let mut r = runner(&j, "P", b, vec![a.clone(), a, other]);
    local(&mut r);
    assert!(
        matches!(r.poll(),Action::Stopped(Stop{kind:StopKind::Backend(BackendError{code}),..})if code=="stale")
    );
    assert_eq!(r.backend().slots[&0].draws, 1);
    assert_eq!(r.backend().slots[&1].draws, 0);
    assert!(r.backend().frames.is_empty());
}
#[test]
fn child_cannot_access_resource_outside_actual_operands() {
    let j = resource_child(false);
    let mut b = Mock::new();
    let r = b.issue(0, "P");
    let other = b.issue(1, "P");
    b.intrude = Some(1);
    let mut runner = runner(&j, "P", b, vec![r, other, V::Bool(true)]);
    local(&mut runner);
    assert!(
        matches!(runner.poll(),Action::Stopped(Stop{kind:StopKind::Backend(BackendError{code}),..})if code=="outside-operands")
    );
    assert_eq!(runner.backend().slots[&0].draws, 0);
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
fn loop_carried_resource_advances_without_minting_fresh_tapes() {
    let j = one(
        json!([draw_fn()]),
        json!([["r", "rng"]]),
        json!(["rng"]),
        json!([
            [
                "loop",
                "rounds",
                "3",
                [["current", "r"]],
                [],
                [
                    ["local", "drawSite", "draw", ["current"], ["x", "next"]],
                    ["yield", ["next"]]
                ],
                ["out"]
            ],
            ["return", ["out"]]
        ]),
    );
    let mut b = Mock::new();
    let r = b.issue(0, "P");
    let mut runner = runner(&j, "P", b, vec![r]);
    for _ in 0..3 {
        local(&mut runner);
    }
    let Action::Returned(values) = runner.poll() else {
        panic!()
    };
    assert!(matches!(
        values[0],
        V::Cap {
            slot: 0,
            generation: 3,
            ..
        }
    ));
    assert_eq!(runner.backend().slots[&0].draws, 3);
    assert_eq!(
        runner
            .backend()
            .domains
            .iter()
            .collect::<BTreeSet<_>>()
            .len(),
        3
    );
    let mut bad = j;
    bad[4][0][7][0][3] = json!([]);
    bad[4][0][7][0][4] = json!(["r"]);
    reject(&bad, ErrorCode::Capture);
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
    let mut j = exchange();
    j[4][0][7] = json!([["stop", "privateStop", "abort"]]);
    let mut p = runner(&j, "P", Mock::new(), vec![V::Field(1)]);
    let mut v = runner(&j, "V", Mock::new(), vec![]);
    let pending = v.poll();
    let usage = v.usage();
    assert!(matches!(p.poll(), Action::Stopped(_)));
    assert_eq!(v.poll(), pending);
    assert_eq!(v.usage(), usage);
    let mut j = identity();
    j[4][0][7] = json!([["incomplete", "foreign"]]);
    let mut r = runner(&j, "P", Mock::new(), vec![V::Field(1)]);
    assert!(matches!(
        r.poll(),
        Action::Stopped(Stop {
            kind: StopKind::Incomplete,
            ..
        })
    ));
}
#[test]
fn source_order_driver_preserves_p_a_v_fail_p_b_cut() {
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
fn runtime_value_and_iteration_limits_are_real_stops() {
    let a = admitted(&identity());
    assert!(matches!(
        Runner::new(&a, "main", "P", "s", Mock::new(), vec![V::Oversize])
            .err()
            .unwrap()
            .error,
        RuntimeError::Limit
    ));
    let j = one(
        json!([]),
        json!([]),
        json!([]),
        json!([
            ["loop", "many", "100001", [], [], [["yield", []]], []],
            ["return", []]
        ]),
    );
    let mut r = runner(&j, "P", Mock::new(), vec![]);
    assert!(matches!(
        r.poll(),
        Action::Stopped(Stop {
            kind: StopKind::Limit,
            ..
        })
    ));
    assert_eq!(r.usage().iterations, Limits::ITERATIONS);
    assert!(r.backend().frames.is_empty());
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
        let mut r = runner(&j, "P", backend, vec![V::Sized(30 * 1024 * 1024)]);
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

fn child_entry_program(loop_count: Option<u64>) -> Json {
    let child = match loop_count {
        None => json!(["call", "childSite", "childP", ["next", "x"], ["out"]]),
        Some(count) => json!([
            "loop",
            "childSite",
            count.to_string(),
            [["current", "next"]],
            ["x"],
            [
                [
                    "local",
                    "drawSite",
                    "draw",
                    ["current"],
                    ["sample", "successor"]
                ],
                ["yield", ["successor"]]
            ],
            ["out"]
        ]),
    };
    module(
        json!([draw_fn()]),
        json!([
            participant(
                "mainP",
                "root",
                "P",
                json!([["r", "rng"], ["x", "field"]]),
                json!(["rng"]),
                json!([
                    ["local", "prefix", "draw", ["r"], ["prefixSample", "next"]],
                    child,
                    ["return", ["out"]]
                ])
            ),
            participant(
                "childP",
                "child",
                "P",
                json!([["r", "rng"], ["x", "field"]]),
                json!(["rng"]),
                json!([["return", ["r"]]])
            )
        ]),
        json!([["entry", "main", [["P", "mainP"]]]]),
    )
}

fn child_origin(mut base: Origin, iteration: Option<u64>) -> Origin {
    base.path.push(match iteration {
        Some(iteration) => PathElement::Loop {
            site: "childSite".into(),
            iteration,
        },
        None => {
            base.instance = "child".into();
            PathElement::Call {
                site: "childSite".into(),
                instance: "child".into(),
            }
        }
    });
    base
}

fn assert_child_stop(r: &mut Runner<Mock>, stop: Stop, expected: Origin, draws: u64) {
    assert_eq!(stop.origin, expected);
    assert_eq!(stop.site.as_deref(), Some("childSite"));
    assert_eq!(stop.role, "P");
    assert!(stop.cleanup_errors.is_empty());
    assert!(r.backend().frames.is_empty());
    assert_eq!(r.usage().live_values, 0);
    assert_eq!(r.usage().live_value_bytes, 0);
    assert_eq!(r.backend().slots[&0].generation, draws);
    assert_eq!(r.backend().slots[&0].draws, draws);
    assert_eq!(r.backend().slots[&1].generation, 0);
    assert_eq!(r.backend().slots[&1].draws, 0);
    let trace = r.backend().trace.clone();
    assert_eq!(
        trace.iter().filter(|s| s.starts_with("enter:")).count(),
        trace.iter().filter(|s| s.starts_with("leave:")).count()
    );
    let usage = r.usage();
    assert_eq!(r.poll(), Action::Stopped(stop.clone()));
    r.cancel();
    assert_eq!(r.poll(), Action::Stopped(stop));
    assert_eq!(r.usage(), usage);
    assert_eq!(r.backend().trace, trace);
}

#[test]
fn child_entry_refusal_preserves_attempted_origin_and_completed_prefix() {
    for iteration in [None, Some(0), Some(1)] {
        let mut j = child_entry_program(iteration.map(|_| 2));
        // Keep an admitted ancestor to check the full nested origin and unwind order.
        let body = j[4][0][7].as_array_mut().unwrap();
        let child_body = json!([body[1].clone(), body[2].clone()]);
        body[1] = json!(["call", "outerSite", "outerP", ["next", "x"], ["out"]]);
        j[4].as_array_mut().unwrap().push(participant(
            "outerP",
            "outer",
            "P",
            json!([["next", fixture_type("rng")], ["x", fixture_type("field")]]),
            json!([fixture_type("rng")]),
            child_body,
        ));
        let mut b = Mock::new();
        b.fail_enter = Some(match iteration {
            None => FrameKind::Call {
                site: "childSite".into(),
            },
            Some(iteration) => FrameKind::Loop {
                site: "childSite".into(),
                iteration,
            },
        });
        let cap = b.issue(0, "P");
        b.issue(1, "P");
        let mut r = runner(&j, "P", b, vec![cap, V::Field(7)]);
        let mut base = r.root_origin().clone();
        base.instance = "outer".into();
        base.path.push(PathElement::Call {
            site: "outerSite".into(),
            instance: "outer".into(),
        });
        local(&mut r);
        for _ in 0..iteration.unwrap_or(0) {
            local(&mut r);
        }
        let Action::Stopped(stop) = r.poll() else {
            panic!("child admission must stop")
        };
        let expected = child_origin(base, iteration);
        assert_eq!(
            r.backend().refused_frame.as_ref().unwrap().origin(),
            &expected
        );
        assert_eq!(
            stop.kind,
            StopKind::Backend(BackendError::new("enter-refused"))
        );
        assert_eq!(
            r.backend()
                .trace
                .iter()
                .filter(|s| *s == "leave:Stopped")
                .count(),
            2
        );
        assert_child_stop(&mut r, stop, expected, 1 + iteration.unwrap_or(0));
        let trace = r.backend().trace.clone();
        assert_eq!(r.into_backend().trace, trace);
    }
}

#[test]
fn child_entry_reservation_failure_preserves_origin_without_entering_backend() {
    // Call and initial-loop live-byte limits, then cumulative bytes on a later push.
    for (count, size_mib, iteration, draws) in [
        (None, 34, None, 1),
        (Some(1), 22, Some(0), 1),
        (Some(6), 20, Some(5), 6),
    ] {
        for failure in [true, false] {
            let count = if !failure && count == Some(6) {
                Some(5)
            } else {
                count
            };
            let size_mib = if !failure && size_mib != 20 {
                size_mib - 4
            } else {
                size_mib
            };
            let mut b = Mock::new();
            let cap = b.issue(0, "P");
            b.issue(1, "P");
            let mut r = runner(
                &child_entry_program(count),
                "P",
                b,
                vec![cap, V::Sized(size_mib * 1024 * 1024)],
            );
            let expected = child_origin(r.root_origin().clone(), iteration);
            let terminal = loop {
                match r.poll() {
                    Action::Local(action) => r.execute_local(&action.cut).unwrap(),
                    terminal => break terminal,
                }
            };
            if failure {
                let Action::Stopped(stop) = terminal else {
                    panic!("reservation must stop")
                };
                assert_eq!(stop.kind, StopKind::Limit);
                assert_eq!(
                    r.backend()
                        .trace
                        .iter()
                        .filter(|s| s.starts_with("enter:"))
                        .count(),
                    (2 * draws) as usize
                );
                assert_eq!(
                    r.backend()
                        .trace
                        .iter()
                        .filter(|s| *s == "leave:Stopped")
                        .count(),
                    1
                );
                assert_child_stop(&mut r, stop, expected, draws);
            } else {
                assert!(matches!(terminal, Action::Returned(_)));
                assert_eq!(r.backend().slots[&0].draws, 1 + count.unwrap_or(0));
                assert!(r.backend().frames.is_empty());
            }
        }
    }
}

#[test]
fn owned_incomplete_stop_is_distinct_from_foreign_leaf() {
    for reason in ["reject", "abort", "exhausted", "incomplete", "refused"] {
        let j = one(
            json!([]),
            json!([]),
            json!([]),
            json!([["stop", "owned", reason]]),
        );
        let mut r = runner(&j, "P", Mock::new(), vec![]);
        let Action::Stopped(stop) = r.poll() else {
            panic!("expected owned stop")
        };
        assert_eq!(stop.kind, StopKind::Explicit(reason.into()));
        assert_eq!(stop.site.as_deref(), Some("owned"));
    }
    let j = one(
        json!([]),
        json!([]),
        json!([]),
        json!([["incomplete", "foreign"]]),
    );
    let mut r = runner(&j, "P", Mock::new(), vec![]);
    let Action::Stopped(stop) = r.poll() else {
        panic!("expected foreign leaf")
    };
    assert_eq!(stop.kind, StopKind::Incomplete);
    assert_eq!(stop.site, None);
    let unknown = one(
        json!([]),
        json!([]),
        json!([]),
        json!([["stop", "owned", "unknown"]]),
    );
    assert!(admit_supplied(&serde_json::to_vec(&unknown).unwrap(), &Mock::new()).is_err());
}

#[test]
fn combined_loop_capture_allocation_fails_before_child_entry() {
    let j = one(
        json!([]),
        json!([["x", "field"]]),
        json!([]),
        json!([
            ["loop", "l", "1", [], ["x"], [["yield", []]], []],
            ["return", []]
        ]),
    );
    let mut r = runner(&j, "P", Mock::new(), vec![V::Sized(30 * 1024 * 1024)]);
    assert!(matches!(
        r.poll(),
        Action::Stopped(Stop {
            kind: StopKind::Limit,
            ..
        })
    ));
    assert_eq!(
        r.backend()
            .trace
            .iter()
            .filter(|s| s.starts_with("enter:"))
            .count(),
        1
    );
    assert!(r.backend().frames.is_empty());
    assert_eq!(r.usage().live_values, 0);
    assert_eq!(r.usage().live_value_bytes, 0);
}
#[test]
fn runtime_stack_checks_combined_calls_and_loops() {
    let mut participants = vec![];
    for index in 0..24 {
        let mut body = if index == 23 {
            json!([["yield", []]])
        } else {
            json!([
                ["call", "child", format!("p{}", index + 1), [], []],
                ["yield", []]
            ])
        };
        for nesting in 0..3 {
            body = json!([
                ["loop", format!("loop{nesting}"), "1", [], [], body, []],
                ["yield", []]
            ]);
        }
        body.as_array_mut().unwrap().last_mut().unwrap()[0] = json!("return");
        participants.push(participant(
            &format!("p{index}"),
            &format!("i{index}"),
            "P",
            json!([]),
            json!([]),
            body,
        ));
    }
    let j = module(
        json!([]),
        json!(participants),
        json!([["entry", "main", [["P", "p0"]]]]),
    );
    let mut r = runner(&j, "P", Mock::new(), vec![]);
    assert!(matches!(
        r.poll(),
        Action::Stopped(Stop {
            kind: StopKind::Limit,
            ..
        })
    ));
    assert!(r.backend().frames.is_empty());
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
        PhysicalType::parse(&fixture_type(self.type_name())).unwrap()
    }
    fn type_name(&self) -> &str {
        match self {
            Self::Scalar(_) => "field",
            Self::Group(_) => "group",
            Self::Groups(_) => "groups",
            Self::Nonce(_) => "nonce",
            Self::Bool(_) => "bool",
        }
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
fn dropping_pending_runner_unwinds_every_frame_even_on_cleanup_error() {
    for fail_cleanup in [false, true] {
        let counter = std::rc::Rc::new(std::cell::Cell::new(0));
        let j = resource_child(false);
        let mut b = Mock::new();
        b.close_count = Some(counter.clone());
        b.fail_leave = fail_cleanup;
        let r = b.issue(0, "P");
        let other = b.issue(1, "P");
        let mut runner = runner(&j, "P", b, vec![r, other, V::Bool(true)]);
        assert!(matches!(runner.poll(), Action::Local(_)));
        assert_eq!(counter.get(), 0);
        drop(runner);
        assert_eq!(counter.get(), 2);
    }
}

#[path = "storage_tests.rs"]
mod storage_tests;

#[test]
fn closed_profile_participants_are_not_an_execution_format() {
    let mut candidate = identity();
    for profile in [
        "arkworks.multilinear.bls12-381/1",
        "arkworks.bls12-381/1",
        "reference.group/1",
    ] {
        // The tag has to be one the decoder accepts. Written with a retired
        // tag the record would be refused for its tag alone, which is a
        // different refusal from the one this is about. The three
        // profiles say the answer does not turn on which profile the record
        // names; they are not three different refusals.
        candidate[0] = json!("zkc.participants/1");
        candidate[1] = json!(profile);
        reject(&candidate, ErrorCode::Record);
    }
}

#[test]
fn reference_variant_selects_only_active_resource_and_preserves_stop_trace() {
    let ty = format!(
        "{}@logical.variant/1",
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

const INDICES: &str = "indices@native.indices/1";
const INDEX: &str = "index@native.index/1";
const TRANSCRIPT: &str = "transcript:merlin3.bls12-381.fr64be/1@host.resource/1";

fn tag_type(payload: &[&str]) -> String {
    format!(
        "{}@logical.variant/1",
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
    let suite = "merlin3.bls12-381.fr64be/1";
    for (contract, arguments, inputs, outputs) in [
        (
            "transcript.observe.index",
            json!([suite, "zkcv.index/1"]),
            json!(["t", "n"]),
            json!(["t2"]),
        ),
        (
            "transcript.challenge",
            json!([suite]),
            json!(["t"]),
            json!(["x", "t2"]),
        ),
    ] {
        let mut j = one(
            json!([[
                "function",
                "Work",
                [["t", TRANSCRIPT], ["n", INDEX]],
                [TRANSCRIPT],
                [
                    ["variant", "pack", tag_type(&[]), "yes", [], "v"],
                    [
                        "match",
                        "case",
                        "v",
                        ["t", "n"],
                        [
                            [
                                "yes",
                                [],
                                [
                                    [
                                        "op",
                                        "effect",
                                        "kernel",
                                        ["Protocol", "instance", "P", "V", "site"],
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
            json!([["t", TRANSCRIPT], ["n", INDEX]]),
            json!([TRANSCRIPT]),
            json!([
                ["local", "work", "Work", ["t", "n"], ["out"]],
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
        outside_match[3][0][4] = json!([j[3][0][4][1][4][0][2][0], ["return", ["t2"]]]);
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
