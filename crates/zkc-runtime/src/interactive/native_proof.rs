//! Proof-entry admission over the executable program format.
//! These checks establish executable shape and one complete transcript chain;
//! they do not authenticate compilation or establish Fiat–Shamir soundness.
use super::{Admitted, EntryRole, PhysicalType, ProgramAction, Type, model::*};
use std::collections::{BTreeMap, BTreeSet};

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
}
type LoopPath = Vec<[String; 3]>;
struct Helper<'a> {
    event: NativeTranscriptEvent,
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
        event: NativeTranscriptEvent {
            contract: contract.into(),
            origin: attributes[0].clone(),
            payload: if challenge {
                None
            } else {
                Some(function.inputs[1].1.logical())
            },
            bound: bound.map(|b| b.1),
        },
        function,
    }))
}

fn verifier_data(ty: &PhysicalType) -> bool {
    ty.is_serializable()
        || ty.has_native_array_frame()
        || verifier_key(ty)
        || ty.has_native_data_frame()
}
fn verifier_key(ty: &PhysicalType) -> bool {
    ty.logical().spelling() == "verifier_key:multilinear.kzg.bls12-381/0"
        && PhysicalType::default_for(ty.logical()).ok().as_ref() == Some(ty)
}
// General admission already checks SSA uniqueness, exact call/result arity,
// affine use and loop-carried types, including nested regions. This walk adds
// the proof-specific transcript and occurrence constraints over that program.
struct ProofWalk<'a> {
    admitted: &'a Admitted,
    helpers: &'a BTreeMap<String, Helper<'a>>,
    producer: &'a str,
    validator: &'a str,
    validating: bool,
    transcript: bool,
    calls: BTreeSet<String>,
    reached: Vec<NativeTranscriptEvent>,
    // A bijection between original loop prefixes and actual compact loops.
    loops: BTreeMap<LoopPath, (String, u64)>,
    loop_sites: BTreeMap<String, LoopPath>,
    state_returns: usize,
}
impl ProofWalk<'_> {
    fn block(
        &mut self,
        body: &Body,
        mut current: Option<String>,
        coordinates: &[String],
        parents: &[(String, u64)],
        depth: usize,
    ) -> Result<()> {
        if depth > 64 {
            return Err(refuse("native-proof-loop-limit"));
        }
        let mut pending_message: Option<String> = None;
        let mut pending_challenge: Option<String> = None;
        for instruction in body.iter() {
            match instruction {
                Instruction::Local {
                    function,
                    inputs,
                    outputs,
                    ..
                } => {
                    if let Some(checked) = self.helpers.get(function) {
                        if !self.calls.insert(function.clone())
                            || inputs.first() != current.as_ref()
                            || outputs.len() != checked.function.outputs.len()
                        {
                            return Err(refuse("native-proof-state-chain"));
                        }
                        let ordinary = if checked.message.is_some() { 2 } else { 1 };
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
                                pending_message.take()
                            } else if sender == self.validator && receiver == self.producer {
                                pending_challenge.take()
                            } else {
                                return Err(refuse("native-proof-message-origin"));
                            };
                            if inputs.get(1) != payload.as_ref() || payload.is_none() {
                                return Err(refuse("native-proof-observation-payload"));
                            }
                        } else {
                            if pending_message.is_some() || pending_challenge.is_some() {
                                return Err(refuse("native-proof-observation-order"));
                            }
                            pending_challenge = outputs.first().cloned();
                        }
                        current = outputs.last().cloned();
                        self.reached.push(checked.event.clone());
                    } else if self.validating {
                        let f = &self.admitted.program.functions[function];
                        if f.inputs.iter().any(|(_, t)| !verifier_data(t))
                            || f.outputs.iter().any(|t| !verifier_data(t))
                        {
                            return Err(refuse("native-proof-verifier-resource"));
                        }
                        for op in LocalInstruction::walk(&f.body) {
                            if let LocalInstruction::Op { binding, .. } = op {
                                let signature = binding.signature();
                                if signature
                                    .inputs
                                    .iter()
                                    .chain(&signature.outputs)
                                    .any(|t| !verifier_data(t))
                                {
                                    return Err(refuse("native-proof-verifier-resource"));
                                }
                            }
                        }
                    }
                }
                Instruction::Send { peer, input, .. }
                    if !self.validating && peer == self.validator =>
                {
                    if self.transcript && current.is_none() {
                        return Err(refuse("native-proof-loop-state"));
                    }
                    if current.is_some()
                        && (pending_message.replace(input.clone()).is_some()
                            || pending_challenge.is_some())
                    {
                        return Err(refuse("native-proof-observation-order"));
                    }
                }
                Instruction::Receive { peer, output, .. }
                    if self.validating && peer == self.producer =>
                {
                    if self.transcript && current.is_none() {
                        return Err(refuse("native-proof-loop-state"));
                    }
                    if current.is_some()
                        && (pending_message.replace(output.clone()).is_some()
                            || pending_challenge.is_some())
                    {
                        return Err(refuse("native-proof-observation-order"));
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
                    if pending_message.is_some() || pending_challenge.is_some() {
                        return Err(refuse("native-proof-observation-order"));
                    }
                    let LoopCount {
                        maximum, induction, ..
                    } = count;
                    let state_positions: Vec<_> = carried
                        .iter()
                        .enumerate()
                        .filter(|(_, (_, initial))| Some(initial) == current.as_ref())
                        .map(|(n, _)| n)
                        .collect();
                    if current.as_ref().is_some_and(|s| captures.contains(s))
                        || state_positions.len() > 1
                    {
                        return Err(refuse("native-proof-state-capture"));
                    }
                    let before = self.reached.len();
                    let returns_before = self.state_returns;
                    if let Some(&position) = state_positions.first() {
                        if position + 1 != carried.len()
                            || coordinates.iter().any(|v| !captures.contains(v))
                        {
                            return Err(refuse("native-proof-loop-state"));
                        }
                        let mut child_coordinates = coordinates.to_vec();
                        child_coordinates.push(induction.clone());
                        let mut child_parents = parents.to_vec();
                        child_parents.push((site.clone(), *maximum));
                        self.block(
                            body,
                            Some(carried[position].0.clone()),
                            &child_coordinates,
                            &child_parents,
                            depth + 1,
                        )?;
                        if self.reached.len() == before && self.state_returns == returns_before {
                            return Err(refuse("native-proof-empty-state-loop"));
                        }
                        current = Some(
                            outputs
                                .get(position)
                                .cloned()
                                .ok_or_else(|| refuse("native-proof-loop-state"))?,
                        );
                    } else {
                        // Owner-local pure work has no transcript. Any hidden
                        // helper in this subtree fails its state-chain check.
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
                    if pending_message.is_some() || pending_challenge.is_some() {
                        return Err(refuse("native-proof-observation-order"));
                    }
                    if self.transcript {
                        if current.is_none() || values.last() != current.as_ref() {
                            return Err(refuse("native-proof-state-chain"));
                        }
                        current = Some(
                            continuations
                                .last()
                                .cloned()
                                .ok_or_else(|| refuse("native-proof-state-chain"))?,
                        );
                        self.state_returns += 1;
                    }
                }
                Instruction::Yield(values)
                    if depth != 0 && (current.is_none() || values.last() == current.as_ref()) => {}
                Instruction::Return(values)
                    if depth == 0 && (current.is_none() || values.last() == current.as_ref()) => {}
                _ => return Err(refuse("native-proof-state-chain")),
            }
        }
        if pending_message.is_some()
            || pending_challenge.is_some()
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
        suite: Option<&str>,
        events: &[NativeTranscriptEvent],
    ) -> Result<Self> {
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
        if events.len() > 2048 || transcript.is_none() && !events.is_empty() {
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
            if let Some(checked) = helper(function, transcript.as_ref(), entry, validator)? {
                helpers.insert(name.clone(), checked);
            }
        }
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
        if messages(&producer.role)? != messages(&validator.role)? {
            return Err(refuse("native-proof-wire-layout"));
        }
        let mut used_helpers = BTreeSet::new();
        let mut previous_loops = None;
        for endpoint in [&producer, &validator] {
            let participant = &admitted.program.participants[&endpoint.participant];
            let validating = endpoint.role == validator.role;
            let state_input = if let Some(state) = &transcript {
                if participant.inputs.last().map(|(_, t)| t) != Some(state)
                    || participant.outputs.last() != Some(state)
                {
                    return Err(refuse("native-proof-state-ports"));
                }
                Some(participant.inputs.last().unwrap().0.as_str())
            } else {
                None
            };

            let ordinary_inputs = participant.inputs.len() - usize::from(transcript.is_some());
            let ordinary_outputs = participant.outputs.len() - usize::from(transcript.is_some());
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
                transcript: transcript.is_some(),
                calls: BTreeSet::new(),
                reached: Vec::new(),
                loops: BTreeMap::new(),
                loop_sites: BTreeMap::new(),
                state_returns: 0,
            };
            walk.block(
                &participant.body,
                state_input.map(str::to_owned),
                &[],
                &[],
                0,
            )?;
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
    pub fn transcript(&self) -> Option<&PhysicalType> {
        self.transcript.as_ref()
    }
}
