//! Proof-entry admission over the executable program format.
//! These checks establish executable shape and one complete transcript chain;
//! they do not authenticate compilation or establish Fiat–Shamir soundness.
use super::{Admitted, EntryRole, PhysicalType, ProgramAction, Type, model::*};
use std::collections::{BTreeMap, BTreeSet};
mod codec;
mod construction;
pub use construction::ConstructionPlan;

/// Construction facts authenticated by the caller's selected deployment.
/// Source-input indices are checked by the Host against participant ports.
pub struct ProofConstruction<'a> {
    pub suite: Option<&'a str>,
    pub events: &'a [NativeTranscriptEvent],
    pub plan: Option<&'a ConstructionPlan>,
    pub source_inputs: &'a BTreeMap<String, Vec<usize>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeTranscriptEvent {
    pub contract: String,
    pub origin: String,
    pub payload: Option<super::LogicalType>,
    /// The static UniformIndex domain of an index transition.
    pub bound: Option<u64>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeProofError(pub &'static str);
impl std::fmt::Display for NativeProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}
impl std::error::Error for NativeProofError {}
type Result<T> = std::result::Result<T, NativeProofError>;
fn refuse(reason: &'static str) -> NativeProofError {
    NativeProofError(reason)
}

#[derive(Clone, Debug)]
pub struct NativeProofEntry {
    admitted: Admitted,
    entry: String,
    producer: EntryRole,
    validator: EntryRole,
    acceptance: usize,
    transcript: Option<PhysicalType>,
    native_binding: bool,
    record_codec: bool,
}
type LoopPath = Vec<[String; 3]>;
struct Helper<'a> {
    events: Vec<NativeTranscriptEvent>,
    message: Option<(String, String)>,
    function: &'a Function,
    loops: Vec<LoopPath>,
}
fn helper<'a>(
    function: &'a Function,
    transcript: Option<&PhysicalType>,
    entry: &str,
    validator: &str,
) -> Result<Option<Helper<'a>>> {
    let uses_state = function
        .inputs
        .iter()
        .any(|(_, t)| t.kind() == Type::Transcript)
        || function
            .outputs
            .iter()
            .any(|t| t.kind() == Type::Transcript);
    let mut native = None;
    for instruction in LocalInstruction::walk(&function.body) {
        if let LocalInstruction::Op { binding, .. } = instruction {
            let name = binding.declaration().contract.as_str();
            if name.starts_with("transcript.") {
                if !matches!(
                    name,
                    "transcript.native.indexed.challenge"
                        | "transcript.native.indexed.index"
                        | "transcript.native.indexed.observe.data"
                ) || native.is_some()
                {
                    return Err(refuse("native-proof-transcript-operation"));
                }
                native = Some(instruction);
            }
        }
    }
    let Some(instruction) = native else {
        return if uses_state {
            Err(refuse("native-proof-hidden-state"))
        } else {
            Ok(None)
        };
    };
    let state = transcript.ok_or_else(|| refuse("native-proof-unselected-transcript"))?;
    let LocalInstruction::Op {
        binding,
        attributes,
        inputs,
        outputs,
        ..
    } = instruction
    else {
        unreachable!()
    };
    let contract = binding.declaration().contract.as_str();
    let index = contract == "transcript.native.indexed.index";
    // Both query transitions return a sample; the origin's service method
    // must name the same distribution as the transition contract.
    let challenge = index || contract == "transcript.native.indexed.challenge";
    let encoded = if challenge {
        crate::logical::native_query_template(attributes, if index { "index" } else { "draw" })
    } else {
        crate::logical::native_origin_template(attributes, "message")
    }
    .map_err(|_| refuse("native-proof-origin"))?;
    let origin =
        crate::logical::decode_tree(&encoded).map_err(|_| refuse("native-proof-origin"))?;
    if origin[1].as_str() != Some(entry) || challenge && origin[4][6].as_str() != Some(validator) {
        return Err(refuse("native-proof-origin"));
    }
    let mut path = Vec::new();
    let mut loops = Vec::new();
    {
        for step in origin[2]
            .as_array()
            .ok_or_else(|| refuse("native-proof-origin"))?
        {
            let frame = [
                step[0].as_str().unwrap().to_owned(),
                step[1].as_str().unwrap().to_owned(),
                step[2].as_str().unwrap().to_owned(),
            ];
            path.push(frame);
            if step[0] == "repeat" {
                loops.push(path.clone());
            }
        }
    }
    let ordinary = if challenge { 1 } else { 2 };
    if attributes.len() != 1
        || function.inputs.len() != ordinary + loops.len()
        || function.outputs.len() != if challenge { 2 } else { 1 }
        || function.inputs[0].1 != *state
        || function.outputs.last() != Some(state)
        || inputs.len() != ordinary + usize::from(index) + 1
        || outputs.len() != function.outputs.len()
        || !inputs[..ordinary]
            .iter()
            .zip(&function.inputs)
            .all(|(v, (p, _))| v == p)
        || function.inputs[ordinary..]
            .iter()
            .any(|(_, t)| t.kind() != Type::Index)
        || binding.declaration().arguments.first().map(String::as_str)
            != Some(state.logical().identity().name())
    {
        return Err(refuse("native-proof-helper-signature"));
    }
    // A fixed grammar assembles coordinates from the helper's induction
    // operands. No arbitrary computation can manufacture an occurrence index.
    let mut coordinates: Option<&str> = None;
    let mut coordinate = 0;
    let mut transition = false;
    // An index helper first materializes its static domain, so both roles
    // absorb the same deployment-fixed bound.
    let mut bound: Option<(&str, u64)> = None;
    for operation in function.body.iter() {
        match operation {
            LocalInstruction::Op { .. } if std::ptr::eq(operation, instruction) && !transition => {
                if coordinates != inputs.last().map(String::as_str)
                    || coordinate != loops.len()
                    || index && bound.map(|b| b.0) != inputs.get(1).map(String::as_str)
                {
                    return Err(refuse("native-proof-helper-coordinates"));
                }
                transition = true;
            }
            LocalInstruction::Op {
                binding,
                attributes,
                inputs,
                outputs,
                ..
            } if index
                && !transition
                && bound.is_none()
                && coordinates.is_none()
                && binding.declaration().contract == "index.constant" =>
            {
                let [value] = attributes.as_slice() else {
                    return Err(refuse("native-proof-index-bound"));
                };
                let value = crate::logical::uniform_index_bound(value)
                    .map_err(|_| refuse("native-proof-index-bound"))?;
                if !inputs.is_empty() || outputs.len() != 1 {
                    return Err(refuse("native-proof-index-bound"));
                }
                bound = Some((&outputs[0], value));
            }
            LocalInstruction::Op {
                binding,
                inputs,
                outputs,
                ..
            } if !transition => match binding.declaration().contract.as_str() {
                "indices.empty"
                    if coordinates.is_none() && inputs.is_empty() && outputs.len() == 1 =>
                {
                    coordinates = Some(&outputs[0]);
                }
                "indices.append"
                    if coordinates.is_some()
                        && inputs.len() == 2
                        && outputs.len() == 1
                        && inputs.first().map(String::as_str) == coordinates
                        && function.inputs.get(ordinary + coordinate).map(|(n, _)| n)
                            == inputs.get(1) =>
                {
                    coordinates = Some(&outputs[0]);
                    coordinate += 1;
                }
                _ => return Err(refuse("native-proof-helper-coordinates")),
            },
            LocalInstruction::Release(values)
                if !values.contains(&inputs[0]) && !values.contains(outputs.last().unwrap()) => {}
            LocalInstruction::Return(values) if transition && values == outputs => {}
            _ => return Err(refuse("native-proof-helper-body")),
        }
    }
    if !transition
        || !matches!(function.body.last(), Some(LocalInstruction::Return(values)) if values == outputs)
    {
        return Err(refuse("native-proof-helper-body"));
    }
    let message = if challenge {
        None
    } else {
        Some((
            origin[4][4].as_str().unwrap().into(),
            origin[4][5].as_str().unwrap().into(),
        ))
    };
    Ok(Some(Helper {
        message,
        loops,
        events: vec![NativeTranscriptEvent {
            contract: contract.into(),
            origin: attributes[0].clone(),
            payload: if challenge {
                None
            } else {
                Some(function.inputs[1].1.logical())
            },
            bound: bound.map(|b| b.1),
        }],
        function,
    }))
}

fn custom_helper<'a>(
    function: &'a Function,
    state: &[PhysicalType],
    events: &[NativeTranscriptEvent],
    entry: &str,
    validator: &str,
) -> Result<Helper<'a>> {
    let first = events
        .first()
        .ok_or_else(|| refuse("native-proof-construction-coverage"))?;
    let query = first.payload.is_none();
    let mut loops = Vec::new();
    let mut message = None;
    let mut expected_inputs = state.to_vec();
    let mut expected_outputs = Vec::new();
    for (index, event) in events.iter().enumerate() {
        let expected = if !query {
            "transcript.native.indexed.observe.data"
        } else if event.bound.is_some() {
            "transcript.native.indexed.index"
        } else {
            "transcript.native.indexed.challenge"
        };
        if event.contract != expected || !query && event.bound.is_some() {
            return Err(refuse("native-proof-event"));
        }
        if let Some(bound) = event.bound
            && (bound == 0 || !bound.is_power_of_two() || bound > (1u64 << 63))
        {
            return Err(refuse("native-proof-index-bound"));
        }
        if event.payload.is_none() != query || query && events.len() != 1 {
            return Err(refuse("native-proof-construction-coverage"));
        }
        let bytes = crate::logical::native_origin_template(
            std::slice::from_ref(&event.origin),
            if query { "query" } else { "message" },
        )
        .map_err(|_| refuse("native-proof-origin"))?;
        let origin =
            crate::logical::decode_tree(&bytes).map_err(|_| refuse("native-proof-origin"))?;
        if origin[1].as_str() != Some(entry) {
            return Err(refuse("native-proof-origin"));
        }
        let mut path = Vec::new();
        let mut event_loops = Vec::new();
        for step in origin[2]
            .as_array()
            .ok_or_else(|| refuse("native-proof-origin"))?
        {
            path.push([
                step[0].as_str().unwrap().into(),
                step[1].as_str().unwrap().into(),
                step[2].as_str().unwrap().into(),
            ]);
            if step[0] == "repeat" {
                event_loops.push(path.clone());
            }
        }
        let event_message = if query {
            None
        } else {
            Some((
                origin[4][4].as_str().unwrap().to_owned(),
                origin[4][5].as_str().unwrap().to_owned(),
            ))
        };
        if index != 0 && (event_loops != loops || event_message != message) {
            return Err(refuse("native-proof-construction-coverage"));
        }
        loops = event_loops;
        message = event_message;
        if let Some(payload) = &event.payload {
            expected_inputs.push(
                PhysicalType::default_for(payload.clone())
                    .map_err(|_| refuse("native-proof-helper-signature"))?,
            );
        } else {
            let contract = super::ServiceContract::parse(origin[4][4].as_str().unwrap())
                .map_err(|_| refuse("native-proof-query-origin"))?;
            if origin[4][6].as_str() != Some(validator)
                || origin[4][5].as_str()
                    != Some(if event.bound.is_some() {
                        "index"
                    } else {
                        "draw"
                    })
            {
                return Err(refuse("native-proof-query-origin"));
            }
            let logical = if event.bound.is_some() {
                "index".into()
            } else {
                format!("field:{}", contract.field().name())
            };
            expected_outputs.push(
                PhysicalType::default_for(
                    super::LogicalType::parse(&logical)
                        .map_err(|_| refuse("native-proof-helper-signature"))?,
                )
                .map_err(|_| refuse("native-proof-helper-signature"))?,
            );
        }
    }
    expected_inputs.extend(std::iter::repeat_n(
        PhysicalType::default_for(super::LogicalType::parse("index").unwrap()).unwrap(),
        loops.len(),
    ));
    expected_outputs.extend_from_slice(state);
    if !function
        .inputs
        .iter()
        .map(|(_, t)| t)
        .eq(expected_inputs.iter())
        || function.outputs != expected_outputs
    {
        return Err(refuse("native-proof-helper-signature"));
    }
    if let Some(bound) = first.bound {
        check_index_range(function, bound)?;
    }
    Ok(Helper {
        events: events.to_vec(),
        message,
        function,
        loops,
    })
}

/// The arbitrary handler's successful return is followed by an independently
/// checked range guard. Sampling quality remains the provider's obligation.
fn check_index_range(function: &Function, bound: u64) -> Result<()> {
    let body: Vec<_> = function
        .body
        .iter()
        .filter(|op| !matches!(op, LocalInstruction::Release(_)))
        .collect();
    if matches!(body.last(), Some(LocalInstruction::Stop { .. })) {
        return Ok(());
    }
    let Some(
        [
            LocalInstruction::Op {
                binding: less,
                attributes: a,
                inputs,
                outputs,
                ..
            },
            LocalInstruction::Op {
                binding: guard,
                attributes: b,
                inputs: condition,
                outputs: none,
                ..
            },
            LocalInstruction::Return(returned),
        ],
    ) = tail(&body, 3)
    else {
        return Err(refuse("native-proof-index-range"));
    };
    if less.declaration().contract != "index.less"
        || guard.declaration().contract != "control.require"
        || !a.is_empty()
        || !b.is_empty()
        || inputs.len() != 2
        || outputs.len() != 1
        || condition != outputs
        || !none.is_empty()
        || returned.first() != inputs.first()
    {
        return Err(refuse("native-proof-index-range"));
    }
    if !body[..body.len() - 3].iter().any(|op| {
        matches!(op,
        LocalInstruction::Op {binding, attributes, inputs: args, outputs: values, ..}
            if binding.declaration().contract == "index.constant" && args.is_empty()
                && values.as_slice() == [inputs[1].clone()]
                && attributes.as_slice() == [bound.to_string()])
    }) {
        return Err(refuse("native-proof-index-bound"));
    }
    Ok(())
}

fn verifier_function(function: &Function) -> Result<()> {
    construction_function(function, &[])
}
fn source_transcript_function(function: &Function, state: Option<&PhysicalType>) -> Result<()> {
    let mut managed = function
        .inputs
        .iter()
        .any(|(_, t)| t.kind() == Type::Transcript)
        || function
            .outputs
            .iter()
            .any(|t| t.kind() == Type::Transcript);
    for op in LocalInstruction::walk(&function.body) {
        if let LocalInstruction::Op { binding, .. } = op {
            let declaration = binding.declaration();
            if declaration.contract.starts_with("transcript.") {
                if !matches!(
                    declaration.contract.as_str(),
                    "transcript.observe" | "transcript.challenge" | "transcript.index"
                ) || declaration.arguments.first().map(String::as_str)
                    != state.map(|t| t.logical().identity().name())
                {
                    return Err(refuse("native-proof-transcript-operation"));
                }
                managed = true;
            }
        }
    }
    if managed {
        construction_function(function, state.map(std::slice::from_ref).unwrap_or(&[]))?;
    }
    Ok(())
}
fn construction_function(function: &Function, state: &[PhysicalType]) -> Result<()> {
    let permitted = |t: &PhysicalType| verifier_data(t) || state.contains(t);
    if function.inputs.iter().any(|(_, t)| !permitted(t))
        || function.outputs.iter().any(|t| !permitted(t))
    {
        return Err(refuse("native-proof-verifier-resource"));
    }
    for op in LocalInstruction::walk(&function.body) {
        if let LocalInstruction::Op { binding, .. } = op {
            let signature = binding.signature();
            if signature
                .inputs
                .iter()
                .chain(&signature.outputs)
                .any(|t| !permitted(t))
            {
                return Err(refuse("native-proof-verifier-resource"));
            }
        }
    }
    Ok(())
}

fn verifier_data(ty: &PhysicalType) -> bool {
    // Private copyable snapshots are local computation data. Wire admission
    // remains a separate boundary; a verifier can initialize its own snapshot.
    if ty.kind() == Type::Shake128State {
        return true;
    }
    let local = |logical: &super::LogicalType| {
        PhysicalType::default_for(logical.clone()).is_ok_and(|t| verifier_data(&t))
    };
    if let Some(element) = ty.logical().sequence_element() {
        return local(element);
    }
    if let Some(descriptor) = ty.logical().variant_descriptor() {
        return descriptor
            .alternatives()
            .iter()
            .flat_map(|a| a.payload())
            .all(local);
    }
    ty.is_serializable()
        || ty.has_native_array_frame()
        || verifier_key(ty)
        || ty.has_native_data_frame()
}
fn verifier_key(ty: &PhysicalType) -> bool {
    ty.logical().spelling() == "verifier_key:multilinear.kzg.bls12-381/0"
        && PhysicalType::default_for(ty.logical()).ok().as_ref() == Some(ty)
}
// General admission checks SSA, exact signatures and resource use. This walk
// adds ordered construction-state and event-occurrence correspondence.
struct ProofWalk<'a> {
    admitted: &'a Admitted,
    helpers: &'a BTreeMap<String, Helper<'a>>,
    producer: &'a str,
    validator: &'a str,
    validating: bool,
    transcript: bool,
    affine_state: bool,
    calls: BTreeSet<String>,
    reached: Vec<NativeTranscriptEvent>,
    loops: BTreeMap<LoopPath, (String, u64)>,
    loop_sites: BTreeMap<String, LoopPath>,
}
fn tail<T>(values: &[T], count: usize) -> Option<&[T]> {
    values
        .len()
        .checked_sub(count)
        .map(|start| &values[start..])
}
impl ProofWalk<'_> {
    fn has_events(&self, body: &Body) -> bool {
        body.iter().any(|op| match op {
            Instruction::Local { function, .. } => self.helpers.contains_key(function),
            Instruction::Send { .. }
            | Instruction::Receive { .. }
            | Instruction::ReturnIf { .. } => self.transcript,
            Instruction::Loop { body, .. } => self.has_events(body),
            _ => false,
        })
    }
    fn block(
        &mut self,
        body: &[Instruction],
        mut current: Option<Vec<String>>,
        coordinates: &[String],
        parents: &[(String, u64)],
        depth: usize,
    ) -> Result<()> {
        if depth > 64 {
            return Err(refuse("native-proof-loop-limit"));
        }
        let mut pending_message = Vec::new();
        let mut pending_challenge = Vec::new();
        for instruction in body.iter() {
            match instruction {
                Instruction::Local {
                    function,
                    inputs,
                    outputs,
                    ..
                } => {
                    if let Some(checked) = self.helpers.get(function) {
                        let state = current
                            .as_ref()
                            .ok_or_else(|| refuse("native-proof-state-chain"))?;
                        if !self.calls.insert(function.clone())
                            || inputs.get(..state.len()) != Some(state.as_slice())
                            || outputs.len() != checked.function.outputs.len()
                        {
                            return Err(refuse("native-proof-state-chain"));
                        }
                        let payloads = if checked.message.is_some() {
                            checked.events.len()
                        } else {
                            0
                        };
                        let ordinary = state.len() + payloads;
                        if inputs.get(ordinary..) != Some(coordinates)
                            || checked.loops.len() != parents.len()
                        {
                            return Err(refuse("native-proof-coordinate-operand"));
                        }
                        for (prefix, actual) in checked.loops.iter().zip(parents) {
                            if self.loops.get(prefix).is_some_and(|known| known != actual)
                                || self
                                    .loop_sites
                                    .get(&actual.0)
                                    .is_some_and(|known| known != prefix)
                            {
                                return Err(refuse("native-proof-loop-origin"));
                            }
                            self.loops.insert(prefix.clone(), actual.clone());
                            self.loop_sites.insert(actual.0.clone(), prefix.clone());
                        }
                        if let Some((sender, receiver)) = &checked.message {
                            let payload = if sender == self.producer && receiver == self.validator {
                                &mut pending_message
                            } else if sender == self.validator && receiver == self.producer {
                                &mut pending_challenge
                            } else {
                                return Err(refuse("native-proof-message-origin"));
                            };
                            if inputs.get(state.len()..ordinary) != Some(payload.as_slice())
                                || payload.is_empty()
                            {
                                return Err(refuse("native-proof-observation-payload"));
                            }
                            payload.clear();
                        } else {
                            if !pending_message.is_empty() || !pending_challenge.is_empty() {
                                return Err(refuse("native-proof-observation-order"));
                            }
                            pending_challenge.push(outputs[0].clone());
                        }
                        current = Some(tail(outputs, state.len()).unwrap().to_vec());
                        self.reached.extend_from_slice(&checked.events);
                    } else {
                        if self.validating {
                            verifier_function(&self.admitted.program.functions[function])?;
                        }
                    }
                }
                Instruction::Send { peer, input, .. }
                    if !self.validating && peer == self.validator =>
                {
                    if self.transcript && current.is_none() {
                        return Err(refuse("native-proof-loop-state"));
                    }
                    if current.is_some() {
                        if !pending_challenge.is_empty() {
                            return Err(refuse("native-proof-observation-order"));
                        }
                        pending_message.push(input.clone());
                    }
                }
                Instruction::Receive { peer, output, .. }
                    if self.validating && peer == self.producer =>
                {
                    if self.transcript && current.is_none() {
                        return Err(refuse("native-proof-loop-state"));
                    }
                    if current.is_some() {
                        if !pending_challenge.is_empty() {
                            return Err(refuse("native-proof-observation-order"));
                        }
                        pending_message.push(output.clone());
                    }
                }
                Instruction::Query { .. } if !self.validating => {}
                Instruction::Loop {
                    site,
                    count,
                    carried,
                    captures,
                    body,
                    outputs,
                } => {
                    if !pending_message.is_empty() || !pending_challenge.is_empty() {
                        return Err(refuse("native-proof-observation-order"));
                    }
                    let before = self.reached.len();
                    if self.has_events(body) {
                        let state = current
                            .as_ref()
                            .ok_or_else(|| refuse("native-proof-loop-state"))?;
                        let slots = tail(carried, state.len())
                            .ok_or_else(|| refuse("native-proof-loop-state"))?;
                        if !slots.iter().map(|(_, value)| value).eq(state.iter())
                            || coordinates.iter().any(|v| !captures.contains(v))
                        {
                            return Err(refuse("native-proof-loop-state"));
                        }
                        let mut child_coordinates = coordinates.to_vec();
                        child_coordinates.push(count.induction.clone());
                        let mut child_parents = parents.to_vec();
                        child_parents.push((site.clone(), count.maximum));
                        self.block(
                            body,
                            Some(slots.iter().map(|(name, _)| name.clone()).collect()),
                            &child_coordinates,
                            &child_parents,
                            depth + 1,
                        )?;
                        current = Some(
                            tail(outputs, state.len())
                                .ok_or_else(|| refuse("native-proof-loop-state"))?
                                .to_vec(),
                        );
                    } else {
                        self.block(body, None, &[], &[], depth + 1)?;
                        if self.reached.len() != before {
                            return Err(refuse("native-proof-loop-state"));
                        }
                    }
                }
                Instruction::ReturnIf {
                    values,
                    continuations,
                    ..
                } => {
                    if !pending_message.is_empty() || !pending_challenge.is_empty() {
                        return Err(refuse("native-proof-observation-order"));
                    }
                    if self.transcript {
                        let state = current
                            .as_ref()
                            .ok_or_else(|| refuse("native-proof-state-chain"))?;
                        if tail(values, state.len()) != Some(state.as_slice()) {
                            return Err(refuse("native-proof-state-chain"));
                        }
                        if self.affine_state {
                            current = Some(
                                tail(continuations, state.len())
                                    .ok_or_else(|| refuse("native-proof-state-chain"))?
                                    .to_vec(),
                            );
                        }
                    }
                }
                Instruction::Yield(values)
                    if depth != 0
                        && current
                            .as_ref()
                            .is_none_or(|s| tail(values, s.len()) == Some(s.as_slice())) => {}
                Instruction::Return(values)
                    if depth == 0
                        && current
                            .as_ref()
                            .is_none_or(|s| tail(values, s.len()) == Some(s.as_slice())) => {}
                _ => return Err(refuse("native-proof-state-chain")),
            }
        }
        if !pending_message.is_empty()
            || !pending_challenge.is_empty()
            || !(if depth != 0 {
                matches!(body.last(), Some(Instruction::Yield(_)))
            } else {
                matches!(body.last(), Some(Instruction::Return(_)))
            })
        {
            return Err(refuse("native-proof-state-chain"));
        }
        Ok(())
    }
}

impl NativeProofEntry {
    /// Admit the current structured proof rules, including configured PCS
    /// values and authored or derived transcript boundaries.
    pub fn new(
        admitted: Admitted,
        entry: &str,
        producer: &str,
        validator: &str,
        acceptance: usize,
        construction: ProofConstruction<'_>,
    ) -> Result<Self> {
        let ProofConstruction {
            suite,
            events,
            plan,
            source_inputs,
        } = construction;
        if producer == validator {
            return Err(refuse("native-proof-profile"));
        }
        let transcript = suite
            .map(|suite| {
                PhysicalType::default_for(
                    super::LogicalType::parse(&format!("transcript:{suite}"))
                        .map_err(|_| refuse("native-proof-suite"))?,
                )
                .map_err(|_| refuse("native-proof-suite"))
            })
            .transpose()?;
        if events.len() > 2048 || transcript.is_none() && plan.is_none() && !events.is_empty() {
            return Err(refuse("native-proof-events"));
        }
        let mut event_origins = BTreeSet::new();
        for event in events {
            if !event_origins.insert(&event.origin) {
                return Err(refuse("native-proof-duplicate-origin"));
            }
        }
        let mut helpers = BTreeMap::new();
        for (name, function) in &admitted.program.functions {
            if let Some(plan) = plan
                && !plan.adapters.iter().any(|a| a.native && a.symbol == *name)
            {
                // Ordinary source definitions may remain after adapter cloning.
                // They can use checked managed methods, never generated origins.
                // Only planned adapter/start calls may consume the live chain.
                source_transcript_function(function, transcript.as_ref())?;
                continue;
            }
            if let Some(checked) = helper(function, transcript.as_ref(), entry, validator)? {
                helpers.insert(name.clone(), checked);
            }
        }
        let state: Vec<_> = if let Some(plan) = plan {
            if plan.host != transcript.is_some()
                || plan.host && plan.state.first() != transcript.as_ref()
            {
                return Err(refuse("native-proof-construction-root"));
            }
            let mut offset = 0;
            for adapter in &plan.adapters {
                let group = events
                    .get(offset..offset + adapter.origins.len())
                    .ok_or_else(|| refuse("native-proof-construction-coverage"))?;
                if !group
                    .iter()
                    .map(|event| &event.origin)
                    .eq(adapter.origins.iter())
                {
                    return Err(refuse("native-proof-construction-coverage"));
                }
                offset += group.len();
                if adapter.native {
                    let helper = helpers
                        .get(&adapter.symbol)
                        .ok_or_else(|| refuse("native-proof-construction-helper"))?;
                    if helper.events != group {
                        return Err(refuse("native-proof-construction-helper"));
                    }
                } else {
                    if helpers.contains_key(&adapter.symbol) {
                        return Err(refuse("native-proof-construction-helper"));
                    }
                    let function = admitted
                        .program
                        .functions
                        .get(&adapter.symbol)
                        .ok_or_else(|| refuse("native-proof-construction-helper"))?;
                    let helper = custom_helper(function, &plan.state, group, entry, validator)?;
                    construction_function(function, &plan.state)?;
                    helpers.insert(adapter.symbol.clone(), helper);
                }
            }
            if offset != events.len() || helpers.len() != plan.adapters.len() {
                return Err(refuse("native-proof-construction-coverage"));
            }
            plan.state.clone()
        } else {
            transcript.iter().cloned().collect()
        };
        let codec = plan
            .and_then(|p| p.codec.as_ref())
            .map(|codec| {
                codec::CheckedCodec::new(&admitted, codec, &state, &helpers, producer, validator)
            })
            .transpose()?;
        let has_codec = codec.is_some();
        let roles = admitted
            .entry(entry)
            .ok_or_else(|| refuse("native-proof-entry"))?;
        if roles.len() != 2
            || admitted.program.entries.len() != 1
            || admitted.program.participants.len() != 2
        {
            return Err(refuse("native-proof-entry"));
        }
        let find = |name: &str| {
            roles
                .iter()
                .find(|r| r.role == name)
                .cloned()
                .ok_or_else(|| refuse("native-proof-role"))
        };
        let producer = find(producer)?;
        let validator = find(validator)?;
        if validator
            .outputs
            .get(acceptance)
            .is_none_or(|t| t.kind() != Type::Bool)
            || !validator.services.is_empty()
        {
            return Err(refuse("native-proof-validator"));
        }
        let layout = admitted
            .program_entry(entry)
            .map_err(|_| refuse("native-proof-layout"))?;
        let messages = |role: &str| -> Result<Vec<(String, String, PhysicalType)>> {
            let mut messages = Vec::new();
            for action in &layout
                .iter()
                .find(|r| r.entry.role == role)
                .ok_or_else(|| refuse("native-proof-role"))?
                .actions
            {
                if let ProgramAction::Send {
                    site, schema, ty, ..
                }
                | ProgramAction::Receive {
                    site, schema, ty, ..
                } = action
                {
                    if !ty.logical().is_native_message_data()
                        || PhysicalType::default_for(ty.logical()).ok().as_ref() != Some(ty)
                    {
                        return Err(refuse("native-proof-wire-type"));
                    }
                    messages.push((site.clone(), schema.clone(), ty.clone()));
                }
            }
            Ok(messages)
        };
        if messages(&producer.role)? != messages(&validator.role)?
            || has_codec && !messages(&producer.role)?.is_empty()
        {
            return Err(refuse("native-proof-wire-layout"));
        }
        let mut used_helpers = BTreeSet::new();
        let mut previous_loops = None;
        for endpoint in [&producer, &validator] {
            let participant = &admitted.program.participants[&endpoint.participant];
            let validating = endpoint.role == validator.role;
            let state_inputs = if transcript.is_some() { state.len() } else { 0 };
            let state_outputs = state.len();
            let hidden_input = usize::from(has_codec && validating);
            let hidden_output = usize::from(has_codec && !validating);
            let inputs_end = participant
                .inputs
                .len()
                .checked_sub(hidden_input)
                .ok_or_else(|| refuse("native-proof-codec-ports"))?;
            let outputs_end = participant
                .outputs
                .len()
                .checked_sub(hidden_output)
                .ok_or_else(|| refuse("native-proof-codec-ports"))?;
            if hidden_input != 0 && participant.inputs[inputs_end].1.kind() != Type::Bytes
                || hidden_output != 0 && participant.outputs[outputs_end].kind() != Type::Bytes
            {
                return Err(refuse("native-proof-codec-ports"));
            }
            let input_ports = &participant.inputs[..inputs_end];
            let output_ports = &participant.outputs[..outputs_end];
            if !tail(input_ports, state_inputs).is_some_and(|ports| {
                ports
                    .iter()
                    .map(|(_, t)| t)
                    .eq(state.iter().take(state_inputs))
            }) || tail(output_ports, state_outputs) != Some(state.as_slice())
            {
                return Err(refuse("native-proof-state-ports"));
            }
            let mut current = transcript.as_ref().map(|_| {
                tail(input_ports, state_inputs)
                    .unwrap()
                    .iter()
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>()
            });
            let mut body = participant.body.as_ref();
            if let Some(plan) = plan {
                let mut invoke = |symbol: &str,
                                  inputs: &[String],
                                  output_types: &[PhysicalType]|
                 -> Result<Vec<String>> {
                    let Some(Instruction::Local {
                        function,
                        inputs: actual,
                        outputs,
                        ..
                    }) = body.first()
                    else {
                        return Err(refuse("native-proof-construction-root"));
                    };
                    if function != symbol
                        || actual != inputs
                        || admitted.program.functions[function].outputs != output_types
                    {
                        return Err(refuse("native-proof-construction-root"));
                    }
                    if validating {
                        construction_function(&admitted.program.functions[function], &plan.state)?;
                    }
                    body = &body[1..];
                    Ok(outputs.clone())
                };
                if !plan.host {
                    current = Some(invoke(&plan.initializer, &[], &state)?);
                }
                if !plan.start.is_empty() {
                    let mut arguments = current
                        .clone()
                        .ok_or_else(|| refuse("native-proof-construction-root"))?;
                    let ports = source_inputs
                        .get(&endpoint.role)
                        .ok_or_else(|| refuse("native-proof-construction-start"))?;
                    for original in &plan.inputs {
                        let position = ports
                            .iter()
                            .position(|p| p == original)
                            .ok_or_else(|| refuse("native-proof-construction-start"))?;
                        arguments.push(
                            participant
                                .inputs
                                .get(position)
                                .ok_or_else(|| refuse("native-proof-construction-start"))?
                                .0
                                .clone(),
                        );
                    }
                    current = Some(invoke(&plan.start, &arguments, &state)?);
                }
            }
            let normalized;
            if let Some(codec) = &codec {
                let inputs = source_inputs
                    .get(&endpoint.role)
                    .ok_or_else(|| refuse("native-proof-codec-layout"))?;
                normalized = codec.normalize(
                    participant,
                    body,
                    inputs,
                    validating,
                    &producer.role,
                    &validator.role,
                )?;
                body = &normalized;
            }
            let ordinary_inputs = inputs_end - state_inputs;
            let ordinary_outputs = outputs_end - state_outputs;
            if participant.inputs[..ordinary_inputs]
                .iter()
                .any(|(_, t)| t.kind() == Type::Transcript || validating && !verifier_data(t))
                || participant.outputs[..ordinary_outputs]
                    .iter()
                    .any(|t| t.kind() == Type::Transcript || validating && !verifier_data(t))
            {
                return Err(refuse("native-proof-state-ports"));
            }
            let mut walk = ProofWalk {
                admitted: &admitted,
                helpers: &helpers,
                producer: &producer.role,
                validator: &validator.role,
                validating,
                transcript: transcript.is_some() || plan.is_some(),
                affine_state: transcript.is_some(),
                calls: BTreeSet::new(),
                reached: Vec::new(),
                loops: BTreeMap::new(),
                loop_sites: BTreeMap::new(),
            };
            walk.block(body, current, &[], &[], 0)?;
            if walk.reached != events {
                return Err(refuse("native-proof-state-chain"));
            }
            if previous_loops
                .as_ref()
                .is_some_and(|known| known != &walk.loops)
            {
                return Err(refuse("native-proof-loop-layout"));
            }
            previous_loops = Some(walk.loops);
            used_helpers.extend(walk.calls);
        }
        if used_helpers.len() != helpers.len() {
            return Err(refuse("native-proof-state-chain"));
        }
        Ok(Self {
            admitted,
            entry: entry.into(),
            producer,
            validator,
            acceptance,
            transcript,
            native_binding: suite.is_some(),
            record_codec: has_codec,
        })
    }
    pub fn admitted(&self) -> &Admitted {
        &self.admitted
    }
    pub fn entry(&self) -> &str {
        &self.entry
    }
    pub fn producer(&self) -> &EntryRole {
        &self.producer
    }
    pub fn validator(&self) -> &EntryRole {
        &self.validator
    }
    pub fn acceptance(&self) -> usize {
        self.acceptance
    }
    /// The managed root absorbs the canonical invocation. This does not
    /// establish that arbitrary handlers use their state or sample securely.
    pub fn binds_invocation(&self) -> bool {
        self.native_binding
    }
    pub fn has_record_codec(&self) -> bool {
        self.record_codec
    }
    pub fn transcript(&self) -> Option<&PhysicalType> {
        self.transcript.as_ref()
    }
}
