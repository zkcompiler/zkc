//! Proof-entry admission over the executable program format.
//! These checks establish executable shape and one complete transcript chain;
//! they do not authenticate compilation or establish Fiat–Shamir soundness.
use super::{Admitted, ArtifactFormat, EntryRole, PhysicalType, ProgramAction, Type, model::*};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeTranscriptEvent {
    pub contract: String,
    pub origin: String,
    pub payload: Option<super::LogicalType>,
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
    version: u8,
) -> Result<Option<Helper<'a>>> {
    let iterated = version >= 2;
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
                if !name.starts_with("transcript.native.") || native.is_some() {
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
    let prefix = if iterated {
        "transcript.native.indexed."
    } else {
        "transcript.native."
    };
    let tail = contract
        .strip_prefix(prefix)
        .ok_or_else(|| refuse("native-proof-transcript-operation"))?;
    let challenge = tail == "challenge";
    if version == 4 && !matches!(tail, "challenge" | "observe.data") {
        return Err(refuse("native-proof-transcript-operation"));
    }
    if !matches!(
        tail,
        "challenge" | "observe.bool" | "observe.field" | "observe.group"
    ) && !(iterated && matches!(tail, "observe.index" | "observe.field_array"))
        && !(matches!(version, 3 | 4) && matches!(tail, "observe.commitment" | "observe.proof"))
        && !(version == 4 && tail == "observe.data")
    {
        return Err(refuse("native-proof-transcript-operation"));
    }
    let encoded = if iterated {
        crate::logical::native_origin_template(
            attributes,
            if challenge { "query" } else { "message" },
        )
    } else {
        crate::logical::native_origin(attributes, if challenge { "query" } else { "message" })
    }
    .map_err(|_| refuse("native-proof-origin"))?;
    let origin =
        crate::logical::decode_tree(&encoded).map_err(|_| refuse("native-proof-origin"))?;
    if origin[1].as_str() != Some(entry) || challenge && origin[4][6].as_str() != Some(validator) {
        return Err(refuse("native-proof-origin"));
    }
    let mut path = Vec::new();
    let mut loops = Vec::new();
    if iterated {
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
        || inputs.len() != ordinary + usize::from(iterated)
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
    for operation in function.body.iter() {
        match operation {
            LocalInstruction::Op { .. } if std::ptr::eq(operation, instruction) && !transition => {
                if iterated
                    && (coordinates != inputs.last().map(String::as_str)
                        || coordinate != loops.len())
                {
                    return Err(refuse("native-proof-helper-coordinates"));
                }
                transition = true;
            }
            LocalInstruction::Op {
                binding,
                inputs,
                outputs,
                ..
            } if iterated && !transition => match binding.declaration().contract.as_str() {
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
        },
        function,
    }))
}

fn verifier_data(ty: &PhysicalType, keys: bool, structured: bool) -> bool {
    ty.is_serializable()
        || ty.has_native_array_frame()
        || keys && verifier_key(ty)
        || structured && ty.has_native_data_frame()
}
fn verifier_key(ty: &PhysicalType) -> bool {
    ty.logical().spelling() == "verifier_key:multilinear.kzg.bls12-381/1"
        && PhysicalType::default_for(ty.logical()).ok().as_ref() == Some(ty)
}
fn pcs_wire(ty: &PhysicalType) -> bool {
    matches!(
        ty.logical().spelling().as_str(),
        "commitment:multilinear.kzg.bls12-381/1" | "proof:multilinear.kzg.bls12-381/1"
    ) && PhysicalType::default_for(ty.logical()).ok().as_ref() == Some(ty)
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
    iterated: bool,
    keys: bool,
    structured: bool,
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
                        if f.inputs
                            .iter()
                            .any(|(_, t)| !verifier_data(t, self.keys, self.structured))
                            || f.outputs
                                .iter()
                                .any(|t| !verifier_data(t, self.keys, self.structured))
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
                                    .any(|t| !verifier_data(t, self.keys, self.structured))
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
                } if self.iterated => {
                    if pending_message.is_some() || pending_challenge.is_some() {
                        return Err(refuse("native-proof-observation-order"));
                    }
                    let Count::Value {
                        maximum, induction, ..
                    } = count
                    else {
                        return Err(refuse("native-proof-loop-profile"));
                    };
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
    pub fn new(
        admitted: Admitted,
        entry: &str,
        producer: &str,
        validator: &str,
        acceptance: usize,
        suite: Option<&str>,
        events: &[NativeTranscriptEvent],
    ) -> Result<Self> {
        Self::admit(
            admitted,
            entry,
            (producer, validator),
            acceptance,
            suite,
            events,
            1,
        )
    }
    pub fn new_iterated(
        admitted: Admitted,
        entry: &str,
        producer: &str,
        validator: &str,
        acceptance: usize,
        suite: Option<&str>,
        events: &[NativeTranscriptEvent],
    ) -> Result<Self> {
        Self::admit(
            admitted,
            entry,
            (producer, validator),
            acceptance,
            suite,
            events,
            2,
        )
    }
    /// Configured PCS values and authored or derived proof boundaries. Keys
    /// remain immutable local operands; proof messages cannot transport them.
    pub fn new_committed(
        admitted: Admitted,
        entry: &str,
        producer: &str,
        validator: &str,
        acceptance: usize,
        suite: Option<&str>,
        events: &[NativeTranscriptEvent],
    ) -> Result<Self> {
        Self::admit(
            admitted,
            entry,
            (producer, validator),
            acceptance,
            suite,
            events,
            3,
        )
    }
    pub fn new_structured(
        admitted: Admitted,
        entry: &str,
        producer: &str,
        validator: &str,
        acceptance: usize,
        suite: Option<&str>,
        events: &[NativeTranscriptEvent],
    ) -> Result<Self> {
        Self::admit(
            admitted,
            entry,
            (producer, validator),
            acceptance,
            suite,
            events,
            4,
        )
    }
    fn admit(
        admitted: Admitted,
        entry: &str,
        roles: (&str, &str),
        acceptance: usize,
        suite: Option<&str>,
        events: &[NativeTranscriptEvent],
        version: u8,
    ) -> Result<Self> {
        let iterated = version >= 2;
        let keys = matches!(version, 3 | 4);
        let (producer, validator) = roles;
        if admitted.format() != ArtifactFormat::Program
            || producer == validator
            || (version == 2 && suite.is_none())
        {
            return Err(refuse("native-proof-profile"));
        }
        let transcript = suite
            .map(|suite| {
                if !matches!(
                    suite,
                    "merlin3.bls12-381.fr64be/1" | "spongefish0.7.4.keccak.bls12-381.fr64be/1"
                ) && !(version == 4
                    && matches!(
                        suite,
                        "merlin3.ristretto255.scalar64le/1"
                            | "merlin3.koala-bear.ext8-binomial3.rejection31le/1"
                    ))
                {
                    return Err(refuse("native-proof-suite"));
                }
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
            if let Some(checked) = helper(function, transcript.as_ref(), entry, validator, version)?
            {
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
                    if !matches!(
                        ty.logical().spelling().as_str(),
                        "bool" | "field:bls12-381.fr" | "group:bls12-381.g1"
                    ) && !(iterated && (ty.kind() == Type::Index || ty.has_native_array_frame()))
                        && !(keys && pcs_wire(ty))
                        && !(version == 4
                            && ty.logical().is_native_message_data()
                            && PhysicalType::default_for(ty.logical()).ok().as_ref() == Some(ty))
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
            if !participant.parameters.is_empty() || !participant.families.is_empty() {
                return Err(refuse("native-proof-flat-profile"));
            }
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
            if participant.inputs[..ordinary_inputs].iter().any(|(_, t)| {
                t.kind() == Type::Transcript || validating && !verifier_data(t, keys, version == 4)
            }) || participant.outputs[..ordinary_outputs].iter().any(|t| {
                t.kind() == Type::Transcript || validating && !verifier_data(t, keys, version == 4)
            }) {
                return Err(refuse("native-proof-state-ports"));
            }
            let mut walk = ProofWalk {
                admitted: &admitted,
                helpers: &helpers,
                producer: &producer.role,
                validator: &validator.role,
                validating,
                iterated,
                keys,
                structured: version == 4,
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
