//! Proof-entry admission over the executable program format.
//! These checks establish executable shape and one complete transcript chain;
//! they do not authenticate compilation or establish Fiat–Shamir soundness.
use super::{EntryRole, PhysicalType, Program, ProgramAction, Type, model::*};
use std::collections::{BTreeMap, BTreeSet};
mod codec;
mod construction;
mod dependencies;
#[cfg(test)]
mod tests;
pub use construction::ConstructionPlan;

/// The executable endpoint required by an independent proof invocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeProofOperation {
    Prove,
    Verify,
}

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
    /// Authenticated compiler classification, associated only after checking the
    /// actual native helper's origin, payload and ordinary transition metadata.
    /// This does not prove equality with source or an absent endpoint.
    pub reconstructed: bool,
    pub contract: String,
    pub origin: String,
    pub payload: Option<super::LogicalType>,
    /// The static UniformIndex domain of an index transition.
    pub bound: Option<u64>,
    /// Exact block output count, distinct from a scalar UniformIndex draw.
    pub count: Option<u64>,
    /// Construction-selected difficulty; Some(0) still owns a witness slot.
    pub difficulty: Option<u8>,
    /// Actual shared argument types of a child start; Some([]) is an empty start.
    pub start_inputs: Option<Vec<super::LogicalType>>,
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
    admitted: Program,
    entry: String,
    producer_role: String,
    validator_role: String,
    producer: Option<EntryRole>,
    validator: Option<EntryRole>,
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
    /// Search produces a witness; checking consumes the construction witness.
    gate_search: Option<bool>,
}
fn witness_slot(event: &NativeTranscriptEvent) -> Result<String> {
    Ok(format!(
        "gate.{}",
        native_origin_site(&event.origin, "query")?
    ))
}

/// Resolve a checked source occurrence using the native application-site law.
/// Repeat frames supply coordinates and do not alter the static site spelling.
pub fn native_origin_site(origin: &str, kind: &str) -> Result<String> {
    let bytes = zkc_format::logical::native_origin_template(&[origin.into()], kind)
        .map_err(|_| refuse("native-proof-origin"))?;
    let origin =
        zkc_format::logical::decode_tree(&bytes).map_err(|_| refuse("native-proof-origin"))?;
    // Generated realization events keep authored apply/repeat frames for
    // loop identity, while their checked common site is already expanded.
    if let Some(digest) = origin[4][1]
        .as_str()
        .and_then(|protocol| protocol.strip_prefix("zkc.oracle."))
    {
        if kind != "message"
            || digest.len() != 64
            || !digest
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(refuse("native-proof-origin"));
        }
        return origin[4][2]
            .as_str()
            .map(str::to_owned)
            .ok_or_else(|| refuse("native-proof-origin"));
    }
    let mut prefix: Option<String> = None;
    for step in origin[2]
        .as_array()
        .ok_or_else(|| refuse("native-proof-origin"))?
    {
        if step[0] == "apply" {
            let site = step[2]
                .as_str()
                .ok_or_else(|| refuse("native-proof-origin"))?;
            prefix = Some(match prefix {
                None => site.into(),
                Some(parent) => format!("apply_{}_{}_{}", parent.len(), parent, site),
            });
            if prefix.as_ref().unwrap().len() > 4096 {
                return Err(refuse("native-proof-origin-limit"));
            }
        }
    }
    let site = origin[4][2]
        .as_str()
        .ok_or_else(|| refuse("native-proof-origin"))?;
    let site = match prefix {
        None => site.into(),
        Some(parent) => format!("apply_{}_{}_{}", parent.len(), parent, site),
    };
    if site.len() > 4096 {
        return Err(refuse("native-proof-origin-limit"));
    }
    Ok(site)
}
fn query_result(origin: &serde_json::Value, index: bool) -> Result<PhysicalType> {
    let contract = origin[4][4]
        .as_str()
        .and_then(|name| super::ServiceContract::parse(name).ok())
        .ok_or_else(|| refuse("native-proof-query-origin"))?;
    let logical = if index {
        "index".into()
    } else {
        format!("field:{}", contract.field().name())
    };
    PhysicalType::default_for(
        super::LogicalType::parse(&logical).map_err(|_| refuse("native-proof-helper-signature"))?,
    )
    .map_err(|_| refuse("native-proof-helper-signature"))
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
                        | "transcript.native.indexed.indices"
                        | "transcript.native.indexed.indices.search"
                        | "transcript.native.indexed.indices.gated"
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
    let block = matches!(
        contract,
        "transcript.native.indexed.indices"
            | "transcript.native.indexed.indices.search"
            | "transcript.native.indexed.indices.gated"
    );
    let search = contract == "transcript.native.indexed.indices.search";
    let gated = search || contract == "transcript.native.indexed.indices.gated";
    // Query transitions return a sample; the origin's service method
    // must name the same distribution as the transition contract.
    let challenge = block || index || contract == "transcript.native.indexed.challenge";
    let encoded = if challenge {
        zkc_format::logical::native_query_template(
            if block { &attributes[..1] } else { attributes },
            if block {
                "indices"
            } else if index {
                "index"
            } else {
                "draw"
            },
        )
    } else {
        zkc_format::logical::native_origin_template(attributes, "message")
    }
    .map_err(|_| refuse("native-proof-origin"))?;
    let origin =
        zkc_format::logical::decode_tree(&encoded).map_err(|_| refuse("native-proof-origin"))?;
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
    let ordinary = if !challenge || gated && !search { 2 } else { 1 };
    let sample = if block {
        PhysicalType::default_for(super::LogicalType::parse("indices").unwrap()).unwrap()
    } else if challenge {
        query_result(&origin, index)?
    } else {
        state.clone()
    };
    if attributes.len() != if block { if gated { 4 } else { 3 } } else { 1 }
        || function.inputs.len() != ordinary + loops.len()
        || function.outputs.len()
            != if search {
                3
            } else if challenge {
                2
            } else {
                1
            }
        || challenge && function.outputs[0] != sample
        || search && function.outputs[1].kind() != Type::Index
        || gated && !search && function.inputs[1].1.kind() != Type::Index
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
    if block && !state.logical().identity().has_index_block_transcript() {
        return Err(refuse("native-proof-suite"));
    }
    if block
        && origin[4][4]
            .as_str()
            .and_then(|name| super::ServiceContract::parse(name).ok())
            .map(|c| c.field())
            != state.logical().identity().scalar_field()
    {
        return Err(refuse("native-proof-query-origin"));
    }
    let block_values = if block {
        let numbers = attributes[1..]
            .iter()
            .map(|value| {
                if !super::decode::canonical_decimal(value) {
                    return Err(refuse("native-proof-index-block"));
                }
                value
                    .parse::<u64>()
                    .map_err(|_| refuse("native-proof-index-block"))
            })
            .collect::<Result<Vec<_>>>()?;
        if !numbers[0].is_power_of_two()
            || numbers[0] > 1 << 63
            || !(1..=1 << 20).contains(&numbers[1])
            || gated && numbers[2] > 64
        {
            return Err(refuse("native-proof-index-block"));
        }
        Some(numbers)
    } else {
        None
    };
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
                let value = zkc_format::logical::uniform_index_bound(value)
                    .map_err(|_| refuse("native-proof-index-bound"))?;
                if !value.is_power_of_two() {
                    return Err(refuse("native-proof-index-bound"));
                }
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
        gate_search: gated.then_some(search),
        events: vec![NativeTranscriptEvent {
            reconstructed: false,
            contract: if gated {
                "transcript.native.indexed.indices.gated".into()
            } else {
                contract.into()
            },
            origin: attributes[0].clone(),
            payload: if challenge {
                None
            } else {
                Some(function.inputs[1].1.logical().clone())
            },
            bound: block_values.as_ref().map(|v| v[0]).or(bound.map(|b| b.1)),
            count: block_values.as_ref().map(|v| v[1]),
            difficulty: if gated {
                Some(block_values.as_ref().unwrap()[2] as u8)
            } else {
                None
            },
            start_inputs: None,
        }],
        function,
    }))
}

// Construction descriptors specify logical events. Their executable helpers
// retain the exact admitted layouts; ports never imply an implicit conversion.
fn selected_port(
    port: Option<&PhysicalType>,
    logical: &super::LogicalType,
) -> Result<PhysicalType> {
    port.filter(|ty| ty.logical() == logical)
        .cloned()
        .ok_or_else(|| refuse("native-proof-helper-signature"))
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
    if events
        .iter()
        .any(|event| event.count.is_some() || event.difficulty.is_some())
    {
        return Err(refuse("native-proof-uninstalled-block-construction"));
    }
    let start = first.start_inputs.is_some();
    let query = !start && first.payload.is_none();
    let mut loops = Vec::new();
    let mut message = None;
    let mut expected_inputs = state.to_vec();
    let mut expected_outputs = Vec::new();
    for (index, event) in events.iter().enumerate() {
        let expected = if start {
            "construction.start"
        } else if !query {
            "transcript.native.indexed.observe.data"
        } else if event.bound.is_some() {
            "transcript.native.indexed.index"
        } else {
            "transcript.native.indexed.challenge"
        };
        if event.contract != expected
            || !query && event.bound.is_some()
            || start && event.payload.is_some()
        {
            return Err(refuse("native-proof-event"));
        }
        if let Some(bound) = event.bound
            && bound == 0
        {
            return Err(refuse("native-proof-index-bound"));
        }
        if event.start_inputs.is_some() != start
            || !start && event.payload.is_none() != query
            || (query || start) && events.len() != 1
        {
            return Err(refuse("native-proof-construction-coverage"));
        }
        let bytes = zkc_format::logical::native_origin_template(
            std::slice::from_ref(&event.origin),
            if start {
                "start"
            } else if query {
                "query"
            } else {
                "message"
            },
        )
        .map_err(|_| refuse("native-proof-origin"))?;
        let origin =
            zkc_format::logical::decode_tree(&bytes).map_err(|_| refuse("native-proof-origin"))?;
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
        let event_message = if query || start {
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
        if let Some(inputs) = &event.start_inputs {
            if inputs.len() > 1024 {
                return Err(refuse("native-proof-helper-signature"));
            }
            for input in inputs {
                expected_inputs.push(selected_port(
                    function.inputs.get(expected_inputs.len()).map(|(_, ty)| ty),
                    input,
                )?);
            }
        } else if let Some(payload) = &event.payload {
            expected_inputs.push(selected_port(
                function.inputs.get(expected_inputs.len()).map(|(_, ty)| ty),
                payload,
            )?);
        } else {
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
            expected_outputs.push(selected_port(
                function.outputs.get(expected_outputs.len()),
                query_result(&origin, event.bound.is_some())?.logical(),
            )?);
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
        gate_search: None,
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

fn verifier_function(function: &Function, contracts: &super::Contracts) -> Result<()> {
    construction_function(function, &[], contracts)
}
fn source_transcript_function(
    function: &Function,
    state: Option<&PhysicalType>,
    contracts: &super::Contracts,
) -> Result<()> {
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
        construction_function(
            function,
            state.map(std::slice::from_ref).unwrap_or(&[]),
            contracts,
        )?;
    }
    Ok(())
}
fn construction_function(
    function: &Function,
    state: &[PhysicalType],
    contracts: &super::Contracts,
) -> Result<()> {
    let permitted = |t: &PhysicalType| verifier_data(t, contracts) || state.contains(t);
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

fn verifier_data(ty: &PhysicalType, contracts: &super::Contracts) -> bool {
    // Selected storage, including every aggregate child, needs its own exact
    // permission. Logical default children cannot authorize selected storage.
    if PhysicalType::default_for(ty.logical().clone())
        .ok()
        .as_ref()
        != Some(ty)
    {
        return contracts.permits_wire(ty, super::WireCodec::Native);
    }
    // Private copyable snapshots are local computation data. Wire admission
    // remains a separate boundary; a verifier can initialize its own snapshot.
    if matches!(ty.kind(), Type::Shake128State | Type::QuotientMatrix) {
        return true;
    }
    let local = |logical: &super::LogicalType| {
        PhysicalType::default_for(logical.clone()).is_ok_and(|t| verifier_data(&t, contracts))
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
    contracts.permits_wire(ty, super::WireCodec::Native)
        || ty.is_serializable()
        || ty.has_native_array_frame()
        || verifier_key(ty)
        || ty.has_native_data_frame()
}
fn verifier_key(ty: &PhysicalType) -> bool {
    ty.logical().spelling() == "verifier_key:multilinear.kzg.bls12-381/0"
        && PhysicalType::default_for(ty.logical().clone())
            .ok()
            .as_ref()
            == Some(ty)
}
// General admission checks SSA, exact signatures and resource use. This walk
// adds ordered construction-state and event-occurrence correspondence.
struct ProofWalk<'a> {
    admitted: &'a Program,
    helpers: &'a BTreeMap<String, Helper<'a>>,
    producer: &'a str,
    validator: &'a str,
    validating: bool,
    transcript: bool,
    affine_state: bool,
    calls: BTreeSet<String>,
    states: BTreeSet<String>,
    reached: Vec<NativeTranscriptEvent>,
    loops: BTreeMap<LoopPath, (String, u64)>,
    loop_sites: BTreeMap<String, LoopPath>,
    witness_slots: BTreeSet<String>,
    delivered_witnesses: BTreeSet<String>,
    witness_values: BTreeSet<String>,
}
fn tail<T>(values: &[T], count: usize) -> Option<&[T]> {
    values
        .len()
        .checked_sub(count)
        .map(|start| &values[start..])
}
impl ProofWalk<'_> {
    fn ordinary<'a>(&self, values: impl IntoIterator<Item = &'a String>) -> Result<()> {
        if values
            .into_iter()
            .any(|name| self.states.contains(name) || self.witness_values.contains(name))
        {
            return Err(refuse("native-proof-state-escape"));
        }
        Ok(())
    }
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
        if let Some(state) = &current {
            self.states.extend(state.iter().cloned());
        }
        let mut pending_message = Vec::new();
        let mut pending_challenge = Vec::new();
        let mut witness_input: Option<(String, String)> = None;
        let mut witness_output: Option<(String, String)> = None;
        for instruction in body.iter() {
            if witness_output.is_some() && !matches!(instruction, Instruction::Send { .. })
                || witness_input.is_some() && !matches!(instruction, Instruction::Local { .. })
            {
                return Err(refuse("native-proof-witness-order"));
            }
            match instruction {
                Instruction::Local {
                    function,
                    inputs,
                    outputs,
                    ..
                } => {
                    if let Some(checked) = self.helpers.get(function) {
                        if let Some(search) = checked.gate_search {
                            if search == self.validating {
                                return Err(refuse("native-proof-witness-direction"));
                            }
                            let slot = witness_slot(&checked.events[0])?;
                            if search {
                                if witness_input.is_some() {
                                    return Err(refuse("native-proof-witness-order"));
                                }
                                witness_output = Some((slot, outputs[1].clone()));
                                self.witness_values.insert(outputs[1].clone());
                            } else if witness_input.take() != Some((slot, inputs[1].clone())) {
                                return Err(refuse("native-proof-witness-input"));
                            }
                        } else if witness_input.is_some() {
                            return Err(refuse("native-proof-witness-order"));
                        }
                        let state = current
                            .as_ref()
                            .ok_or_else(|| refuse("native-proof-state-chain"))?;
                        if !self.calls.insert(function.clone())
                            || inputs.get(..state.len()) != Some(state.as_slice())
                            || outputs.len() != checked.function.outputs.len()
                        {
                            return Err(refuse("native-proof-state-chain"));
                        }
                        self.ordinary(
                            &inputs
                                [state.len() + usize::from(checked.gate_search == Some(false))..],
                        )?;
                        let start_inputs = checked.events[0].start_inputs.as_ref();
                        let payloads = if let Some(inputs) = start_inputs {
                            inputs.len()
                        } else if checked.message.is_some() {
                            checked.events.len()
                        } else {
                            0
                        };
                        let ordinary = state.len()
                            + payloads
                            + usize::from(checked.gate_search == Some(false));
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
                        if checked.events[0].reconstructed {
                            if !pending_message.is_empty() || !pending_challenge.is_empty() {
                                return Err(refuse("native-proof-observation-order"));
                            }
                            // These exact ordinary payload positions were checked
                            // against the actual helper signature above. There is
                            // no transport operand or new challenge to consume.
                            if checked.message.as_ref().is_none_or(|(sender, receiver)| {
                                sender != self.validator || receiver != self.producer
                            }) || payloads != 1
                            {
                                return Err(refuse("native-proof-reconstructed-message"));
                            }
                        } else if let Some((sender, receiver)) = &checked.message {
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
                            if start_inputs.is_none() {
                                pending_challenge.push(outputs[0].clone());
                            }
                        }
                        let next = tail(outputs, state.len()).unwrap();
                        self.states.extend(next.iter().cloned());
                        current = Some(next.to_vec());
                        self.reached.extend_from_slice(&checked.events);
                    } else {
                        if witness_input.is_some() {
                            return Err(refuse("native-proof-witness-order"));
                        }
                        self.ordinary(inputs)?;
                        if self.validating {
                            verifier_function(
                                &self.admitted.program.functions[function],
                                self.admitted.contracts(),
                            )?;
                        }
                    }
                }
                Instruction::Send {
                    site,
                    schema,
                    peer,
                    input,
                } if !self.validating && peer == self.validator => {
                    if self.witness_slots.contains(site) || witness_output.is_some() {
                        if schema != site
                            || witness_output.take() != Some((site.clone(), input.clone()))
                            || !self.delivered_witnesses.insert(site.clone())
                        {
                            return Err(refuse("native-proof-witness-output"));
                        }
                        continue;
                    }
                    self.ordinary([input])?;
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
                Instruction::Receive {
                    site,
                    schema,
                    peer,
                    output,
                    ty,
                } if self.validating && peer == self.producer => {
                    if self.witness_slots.contains(site) {
                        if schema != site
                            || ty.logical().spelling() != "index"
                            || !self.delivered_witnesses.insert(site.clone())
                            || !pending_message.is_empty()
                            || !pending_challenge.is_empty()
                        {
                            return Err(refuse("native-proof-witness-input"));
                        }
                        witness_input = Some((site.clone(), output.clone()));
                        self.witness_values.insert(output.clone());
                        continue;
                    }
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
                Instruction::Query { inputs, .. } => {
                    self.ordinary(inputs)?;
                    if !pending_message.is_empty() || !pending_challenge.is_empty() {
                        return Err(refuse("native-proof-observation-order"));
                    }
                }
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
                    self.ordinary([&count.value])?;
                    self.ordinary(captures.iter().map(|(_, parent)| parent))?;
                    let before = self.reached.len();
                    if self.has_events(body) {
                        let state = current
                            .as_ref()
                            .ok_or_else(|| refuse("native-proof-loop-state"))?;
                        let slots = tail(carried, state.len())
                            .ok_or_else(|| refuse("native-proof-loop-state"))?;
                        if !slots.iter().map(|(_, value)| value).eq(state.iter())
                            || coordinates
                                .iter()
                                .any(|v| !captures.iter().any(|(_, parent)| parent == v))
                        {
                            return Err(refuse("native-proof-loop-state"));
                        }
                        self.ordinary(
                            carried[..carried.len() - state.len()]
                                .iter()
                                .map(|(_, v)| v),
                        )?;
                        let mut child_coordinates = coordinates
                            .iter()
                            .map(|coordinate| {
                                captures
                                    .iter()
                                    .find(|(_, parent)| parent == coordinate)
                                    .expect("checked coordinate capture")
                                    .0
                                    .clone()
                            })
                            .collect::<Vec<_>>();
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
                        let next = tail(outputs, state.len())
                            .ok_or_else(|| refuse("native-proof-loop-state"))?;
                        self.states.extend(next.iter().cloned());
                        current = Some(next.to_vec());
                    } else {
                        self.ordinary(carried.iter().map(|(_, v)| v))?;
                        self.block(body, None, &[], &[], depth + 1)?;
                        if self.reached.len() != before {
                            return Err(refuse("native-proof-loop-state"));
                        }
                    }
                }
                Instruction::ReturnIf {
                    condition,
                    values,
                    continuations,
                    ..
                } => {
                    self.ordinary([condition])?;
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
                        self.ordinary(&values[..values.len() - state.len()])?;
                        if self.affine_state {
                            current = Some(
                                tail(continuations, state.len())
                                    .ok_or_else(|| refuse("native-proof-state-chain"))?
                                    .to_vec(),
                            );
                            self.states
                                .extend(current.as_ref().unwrap().iter().cloned());
                        }
                    } else {
                        self.ordinary(values)?;
                    }
                }
                Instruction::Yield(values)
                    if depth != 0
                        && current
                            .as_ref()
                            .is_none_or(|s| tail(values, s.len()) == Some(s.as_slice())) =>
                {
                    let states = current.as_ref().map_or(0, Vec::len);
                    self.ordinary(&values[..values.len() - states])?;
                }
                Instruction::Return(values)
                    if depth == 0
                        && current
                            .as_ref()
                            .is_none_or(|s| tail(values, s.len()) == Some(s.as_slice())) =>
                {
                    let states = current.as_ref().map_or(0, Vec::len);
                    self.ordinary(&values[..values.len() - states])?;
                }
                _ => return Err(refuse("native-proof-state-chain")),
            }
        }
        if !pending_message.is_empty()
            || !pending_challenge.is_empty()
            || witness_input.is_some()
            || witness_output.is_some()
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
        admitted: Program,
        entry: &str,
        producer: &str,
        validator: &str,
        acceptance: usize,
        construction: ProofConstruction<'_>,
    ) -> Result<Self> {
        Self::admit(
            admitted,
            entry,
            producer,
            validator,
            acceptance,
            construction,
            None,
        )
    }

    /// Admit exactly one executable endpoint. Public source indices come from
    /// the authenticated descriptor, independently of the absent endpoint.
    #[allow(clippy::too_many_arguments)]
    pub fn new_for_operation(
        admitted: Program,
        entry: &str,
        producer: &str,
        validator: &str,
        acceptance: usize,
        construction: ProofConstruction<'_>,
        operation: NativeProofOperation,
        public_inputs: &[usize],
    ) -> Result<Self> {
        Self::admit(
            admitted,
            entry,
            producer,
            validator,
            acceptance,
            construction,
            Some((operation, public_inputs)),
        )
    }

    fn admit(
        admitted: Program,
        entry: &str,
        producer_role: &str,
        validator_role: &str,
        acceptance: usize,
        construction: ProofConstruction<'_>,
        selection: Option<(NativeProofOperation, &[usize])>,
    ) -> Result<Self> {
        let (producer, validator) = (producer_role, validator_role);
        let operation = selection.map(|(operation, _)| operation);
        let ProofConstruction {
            suite,
            events,
            plan,
            source_inputs,
        } = construction;
        if producer == validator
            || !super::decode::valid_name(producer)
            || !super::decode::valid_name(validator)
        {
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
        let mut witness_slots = BTreeSet::new();
        for event in events {
            if !event_origins.insert(&event.origin) {
                return Err(refuse("native-proof-duplicate-origin"));
            }
            if event.reconstructed {
                if transcript.is_none() || plan.is_some() {
                    return Err(refuse("native-proof-reconstructed-profile"));
                }
                if event.contract != "transcript.native.indexed.observe.data"
                    || event.payload.is_none()
                    || event.bound.is_some()
                    || event.count.is_some()
                    || event.difficulty.is_some()
                    || event.start_inputs.is_some()
                {
                    return Err(refuse("native-proof-reconstructed-message"));
                }
                let bytes = zkc_format::logical::native_origin_template(
                    std::slice::from_ref(&event.origin),
                    "message",
                )
                .map_err(|_| refuse("native-proof-origin"))?;
                let origin = zkc_format::logical::decode_tree(&bytes)
                    .map_err(|_| refuse("native-proof-origin"))?;
                if origin[1].as_str() != Some(entry)
                    || origin[4][4].as_str() != Some(validator)
                    || origin[4][5].as_str() != Some(producer)
                {
                    return Err(refuse("native-proof-reconstructed-message"));
                }
            }
            if let Some(count) = event.count {
                if plan.is_some()
                    || !matches!(
                        event.contract.as_str(),
                        "transcript.native.indexed.indices"
                            | "transcript.native.indexed.indices.gated"
                    )
                    || !(1..=1 << 20).contains(&count)
                    || event
                        .bound
                        .is_none_or(|bound| !bound.is_power_of_two() || bound > 1 << 63)
                    || event.payload.is_some()
                    || event.start_inputs.is_some()
                    || event.difficulty.is_some()
                        != (event.contract == "transcript.native.indexed.indices.gated")
                    || event.difficulty.is_some_and(|bits| bits > 64)
                {
                    return Err(refuse("native-proof-index-block"));
                }
                if event.difficulty.is_some() && !witness_slots.insert(witness_slot(event)?) {
                    return Err(refuse("native-proof-duplicate-witness"));
                }
            } else if event.difficulty.is_some()
                || event
                    .contract
                    .starts_with("transcript.native.indexed.indices")
            {
                return Err(refuse("native-proof-index-block"));
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
                source_transcript_function(function, transcript.as_ref(), admitted.contracts())?;
                continue;
            }
            if let Some(mut checked) = helper(function, transcript.as_ref(), entry, validator)? {
                if let Some(expected) = events
                    .iter()
                    .find(|event| event.reconstructed && event.origin == checked.events[0].origin)
                {
                    let mut ordinary = expected.clone();
                    ordinary.reconstructed = false;
                    if checked.events.as_slice() != [ordinary] {
                        return Err(refuse("native-proof-state-chain"));
                    }
                    checked.events[0].reconstructed = true;
                }
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
                    construction_function(function, &plan.state, admitted.contracts())?;
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
                codec::CheckedCodec::new(
                    &admitted, codec, &state, &helpers, producer, validator, operation,
                )
            })
            .transpose()?;
        let has_codec = codec.is_some();
        let roles = admitted
            .entry(entry)
            .ok_or_else(|| refuse("native-proof-entry"))?;
        let endpoint_count = if operation.is_some() { 1 } else { 2 };
        if roles.len() != endpoint_count
            || admitted.program.entries.len() != 1
            || admitted.program.participants.len() != endpoint_count
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
        let producer = (operation != Some(NativeProofOperation::Verify))
            .then(|| find(producer))
            .transpose()?;
        let validator = (operation != Some(NativeProofOperation::Prove))
            .then(|| find(validator))
            .transpose()?;
        if validator.as_ref().is_some_and(|endpoint| {
            endpoint
                .outputs
                .get(acceptance)
                .is_none_or(|t| t.kind() != Type::Bool)
        }) {
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
                        || !admitted
                            .contracts()
                            .permits_wire(ty, super::WireCodec::Native)
                    {
                        return Err(refuse("native-proof-wire-type"));
                    }
                    messages.push((site.clone(), schema.clone(), ty.clone()));
                }
            }
            Ok(messages)
        };
        let producer_messages = producer.as_ref().map(|r| messages(&r.role)).transpose()?;
        let validator_messages = validator.as_ref().map(|r| messages(&r.role)).transpose()?;
        if producer_messages
            .as_ref()
            .zip(validator_messages.as_ref())
            .is_some_and(|(producer, validator)| producer != validator)
            || has_codec
                && producer_messages
                    .iter()
                    .chain(&validator_messages)
                    .any(|m| !m.is_empty())
        {
            return Err(refuse("native-proof-wire-layout"));
        }
        if let Some((_, public)) = selection
            && (source_inputs.len() != endpoint_count
                || public.len() > 1024
                || !public.windows(2).all(|pair| pair[0] < pair[1])
                || public.iter().any(|i| *i >= 1024))
        {
            return Err(refuse("native-proof-source-map"));
        }
        if producer.is_some()
            && let Some(plan) = plan
        {
            let shared = match selection {
                Some((_, public)) => public,
                None => source_inputs
                    .get(validator_role)
                    .ok_or_else(|| refuse("native-proof-construction-start"))?,
            };
            // Combined admission also has a real verifier that must supply
            // these root inputs. Preserve that obligation when it is absent.
            if plan
                .inputs
                .iter()
                .chain(plan.codec.iter().flat_map(|codec| &codec.inputs))
                .any(|input| !shared.contains(input))
            {
                return Err(refuse("native-proof-private-dependency"));
            }
        }
        let mut used_helpers = BTreeSet::new();
        let mut previous_loops = None;
        for endpoint in producer.iter().chain(&validator) {
            let participant = &admitted.program.participants[&endpoint.participant];
            let validating = endpoint.role == validator_role;
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
            // Copyable values from the checked root prefix remain in ordinary
            // scope even after a later start operation produces the live state.
            let mut root_definitions = current.clone().unwrap_or_default();
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
                    // These are shared construction roots even in a producer-only
                    // deployment; the absent verifier cannot supply this check.
                    construction_function(
                        &admitted.program.functions[function],
                        &plan.state,
                        admitted.contracts(),
                    )?;
                    root_definitions.extend(outputs.iter().cloned());
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
                    producer_role,
                    validator_role,
                )?;
                body = &normalized;
            }
            let ordinary_inputs = inputs_end - state_inputs;
            let ordinary_outputs = outputs_end - state_outputs;
            if let Some((_, public)) = selection {
                let actual = source_inputs
                    .get(&endpoint.role)
                    .ok_or_else(|| refuse("native-proof-source-map"))?;
                if actual.len() != ordinary_inputs
                    || !actual.windows(2).all(|pair| pair[0] < pair[1])
                    || actual.iter().any(|i| *i >= 1024)
                    || validating && actual.as_slice() != public
                {
                    return Err(refuse("native-proof-source-map"));
                }
            }
            if transcript.is_some()
                || plan.is_some()
                || (validating && !participant.services.is_empty())
            {
                let mut private = BTreeSet::new();
                if !validating {
                    let actual = source_inputs
                        .get(&endpoint.role)
                        .ok_or_else(|| refuse("native-proof-construction-start"))?;
                    let public = match selection {
                        Some((_, public)) => public,
                        None => source_inputs
                            .get(validator_role)
                            .ok_or_else(|| refuse("native-proof-construction-start"))?,
                    };
                    if actual.len() != ordinary_inputs {
                        return Err(refuse("native-proof-construction-start"));
                    }
                    for (position, original) in actual.iter().enumerate() {
                        if !public.contains(original) {
                            private.insert(
                                participant
                                    .inputs
                                    .get(position)
                                    .ok_or_else(|| refuse("native-proof-construction-start"))?
                                    .0
                                    .clone(),
                            );
                        }
                    }
                }
                // Codec normalization removes the hidden proof port from
                // ReturnIf and Return. Pair that body with the same logical
                // output ports when tracking affine continuations.
                let env = participant
                    .inputs
                    .iter()
                    .map(|(name, _)| name)
                    .chain(&root_definitions)
                    .map(|name| (name.clone(), private.contains(name)))
                    .collect();
                dependencies::check_participant(
                    &admitted,
                    body,
                    output_ports,
                    &helpers,
                    env,
                    !validating,
                )?;
            }
            if participant.inputs[..ordinary_inputs].iter().any(|(_, t)| {
                t.kind() == Type::Transcript
                    || validating && !verifier_data(t, admitted.contracts())
            }) || participant.outputs[..ordinary_outputs].iter().any(|t| {
                t.kind() == Type::Transcript
                    || validating && !verifier_data(t, admitted.contracts())
            }) {
                return Err(refuse("native-proof-state-ports"));
            }
            let mut walk = ProofWalk {
                admitted: &admitted,
                helpers: &helpers,
                producer: producer_role,
                validator: validator_role,
                validating,
                transcript: transcript.is_some() || plan.is_some(),
                affine_state: transcript.is_some(),
                calls: BTreeSet::new(),
                states: root_definitions.into_iter().collect(),
                reached: Vec::new(),
                loops: BTreeMap::new(),
                loop_sites: BTreeMap::new(),
                witness_slots: witness_slots.clone(),
                delivered_witnesses: BTreeSet::new(),
                witness_values: BTreeSet::new(),
            };
            walk.block(body, current, &[], &[], 0)?;
            if walk.reached != events || walk.delivered_witnesses != witness_slots {
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
            producer_role: producer_role.into(),
            validator_role: validator_role.into(),
            producer,
            validator,
            acceptance,
            transcript,
            native_binding: suite.is_some(),
            record_codec: has_codec,
        })
    }
    pub fn admitted(&self) -> &Program {
        &self.admitted
    }
    pub fn entry(&self) -> &str {
        &self.entry
    }
    /// The admitted producer endpoint, if this deployment includes it.
    pub fn producer(&self) -> Option<&EntryRole> {
        self.producer.as_ref()
    }
    /// The admitted validator endpoint, if this deployment includes it.
    pub fn validator(&self) -> Option<&EntryRole> {
        self.validator.as_ref()
    }
    /// Descriptor identity, including when no producer endpoint is admitted.
    pub fn producer_role(&self) -> &str {
        &self.producer_role
    }
    /// Descriptor identity, including when no validator endpoint is admitted.
    pub fn validator_role(&self) -> &str {
        &self.validator_role
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
