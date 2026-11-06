//! Check record transport independently, then expose its mathematical messages
//! to the transcript checker. This normalized body is admission evidence only;
//! the Runner always executes the original admitted program.
use super::{
    construction::{CodecMessage, RecordCodec},
    *,
};
use crate::vm::LogicalType;
use std::{cell::RefCell, sync::Arc};

type Names = BTreeMap<String, String>;
type RegionInputs = (usize, Vec<String>, Option<String>, BTreeSet<String>);
fn charge(work: &mut usize, amount: usize) -> Result<()> {
    AdmissionWork::charge(work, amount)
}
// Charge before copying or traversing vectors. Recursion charges each static
// arm once; no dynamic branch paths are expanded by normalization.
fn instruction_cost(op: &Instruction) -> usize {
    1 + 8 * match op {
        Instruction::Local {
            inputs, outputs, ..
        }
        | Instruction::Query {
            inputs, outputs, ..
        } => inputs.len() + outputs.len(),
        Instruction::Conditional {
            captures, outputs, ..
        } => 1 + 2 * captures.len() + outputs.len(),
        Instruction::Match {
            captures,
            arms,
            outputs,
            ..
        } => 1 + 2 * captures.len() + arms.len() + outputs.len(),
        Instruction::Loop {
            carried,
            captures,
            outputs,
            ..
        } => 2 + 2 * (carried.len() + captures.len()) + outputs.len(),
        Instruction::ReturnIf {
            values,
            continuations,
            ..
        } => 1 + values.len() + continuations.len(),
        Instruction::Yield(values) | Instruction::Return(values) => values.len(),
        Instruction::Send { .. } | Instruction::Receive { .. } => 1,
    }
}
// The original capture prefix includes the transcript state threaded by the
// proof pass. Codec appends Record, then validator proof; Match payloads live
// separately and precede all of these captures in each physical arm row.
fn region_inputs(
    captures: &[(String, String)],
    record: &[String],
    proof: Option<&String>,
    work: &mut usize,
) -> Result<RegionInputs> {
    charge(
        work,
        4 * captures.len() + 3 * record.len() + usize::from(proof.is_some()),
    )?;
    let prefix = captures
        .len()
        .checked_sub(record.len() + usize::from(proof.is_some()))
        .ok_or_else(|| refuse("native-proof-codec-record-chain"))?;
    if !captures[prefix..prefix + record.len()]
        .iter()
        .map(|(_, parent)| parent)
        .eq(record)
        || proof.is_some_and(|p| captures.last().map(|(_, parent)| parent) != Some(p))
    {
        return Err(refuse("native-proof-codec-record-chain"));
    }
    let nested: Vec<_> = captures[prefix..prefix + record.len()]
        .iter()
        .map(|(local, _)| local.clone())
        .collect();
    let child_proof = proof.map(|_| captures.last().unwrap().0.clone());
    let mut internal: BTreeSet<_> = nested.iter().cloned().collect();
    internal.extend(child_proof.iter().cloned());
    Ok((prefix, nested, child_proof, internal))
}
fn available(op: &Instruction, internal: &BTreeSet<String>) -> Result<()> {
    let allowed = |values: &[String]| values.iter().all(|v| !internal.contains(v));
    let valid = match op {
        Instruction::Conditional {
            condition,
            captures,
            ..
        } => {
            !internal.contains(condition)
                && captures
                    .iter()
                    .all(|(_, parent)| !internal.contains(parent))
        }
        Instruction::Match {
            input, captures, ..
        } => {
            !internal.contains(input)
                && captures
                    .iter()
                    .all(|(_, parent)| !internal.contains(parent))
        }
        Instruction::Local { inputs, .. } | Instruction::Query { inputs, .. } => allowed(inputs),
        Instruction::Send { input, .. } => !internal.contains(input),
        Instruction::Receive { .. } => true,
        Instruction::Loop {
            count,
            carried,
            captures,
            ..
        } => {
            !internal.contains(&count.value)
                && carried.iter().all(|(_, v)| !internal.contains(v))
                && captures
                    .iter()
                    .all(|(_, parent)| !internal.contains(parent))
        }
        Instruction::ReturnIf {
            condition, values, ..
        } => !internal.contains(condition) && allowed(values),
        Instruction::Return(values) | Instruction::Yield(values) => allowed(values),
    };
    if valid {
        Ok(())
    } else {
        Err(refuse("native-proof-codec-internal-use"))
    }
}
fn mapped(names: &Names, value: &str) -> String {
    names.get(value).cloned().unwrap_or_else(|| value.into())
}
fn values(names: &Names, input: &[String]) -> Vec<String> {
    input.iter().map(|v| mapped(names, v)).collect()
}
fn data_function(
    function: &Function,
    contracts: &crate::vm::Contracts,
    work: &mut impl AdmissionWork,
) -> Result<()> {
    construction_function(function, &[], contracts, work)?;
    source_transcript_function(function, None, contracts, work)
}
fn type_list_work(types: &[PhysicalType], work: &mut impl AdmissionWork) -> Result<()> {
    work.charge(types.len())?;
    for ty in types {
        type_work::comparison_work(ty, work)?;
    }
    Ok(())
}
fn copy_types(types: &[PhysicalType], work: &mut impl AdmissionWork) -> Result<Vec<PhysicalType>> {
    work.charge(2 * types.len())?;
    Ok(types.to_vec())
}
fn extend_types(
    target: &mut Vec<PhysicalType>,
    types: &[PhysicalType],
    work: &mut impl AdmissionWork,
) -> Result<()> {
    work.charge(target.len() + 2 * types.len())?;
    target.extend_from_slice(types);
    Ok(())
}
fn repeated_type(
    name: &str,
    count: usize,
    work: &mut impl AdmissionWork,
) -> Result<Vec<PhysicalType>> {
    work.charge(count + 2)?;
    Ok(vec![ty(name); count])
}
fn signature(
    function: &Function,
    inputs: &[PhysicalType],
    outputs: &[PhysicalType],
    work: &mut impl AdmissionWork,
) -> Result<()> {
    work.charge(function.inputs.len())?;
    for (_, ty) in &function.inputs {
        type_work::comparison_work(ty, work)?;
    }
    type_list_work(&function.outputs, work)?;
    type_list_work(inputs, work)?;
    type_list_work(outputs, work)?;
    if !function.inputs.iter().map(|(_, t)| t).eq(inputs.iter()) || function.outputs != outputs {
        return Err(refuse("native-proof-codec-signature"));
    }
    Ok(())
}
fn ty(name: &str) -> PhysicalType {
    PhysicalType::default_for(LogicalType::parse(name).unwrap()).unwrap()
}
fn operation<'a>(
    op: &'a LocalInstruction,
    contract: &str,
    inputs: &[String],
) -> Option<&'a [String]> {
    let LocalInstruction::Op {
        binding,
        attributes,
        inputs: actual,
        outputs,
        ..
    } = op
    else {
        return None;
    };
    (binding.declaration().contract == contract
        && binding.declaration().arguments.is_empty()
        && attributes.is_empty()
        && actual == inputs)
        .then_some(outputs)
}
fn no_releases(body: &[LocalInstruction]) -> impl Iterator<Item = &LocalInstruction> {
    body.iter()
        .filter(|op| !matches!(op, LocalInstruction::Release(_)))
}
fn bind(env: &mut Names, source: &[String], target: &[String]) -> bool {
    if source.len() != target.len() {
        return false;
    }
    env.extend(source.iter().cloned().zip(target.iter().cloned()));
    true
}
// Compare ordinary bodies modulo SSA names, the return/yield boundary and
// storage-release instructions inserted by lowering. No operation is reordered.
fn same_body(
    source: &[LocalInstruction],
    target: &[LocalInstruction],
    mut env: Names,
    depth: usize,
    work: &mut usize,
) -> bool {
    if depth > 64 {
        return false;
    }
    if charge(work, source.len() + target.len()).is_err() {
        return false;
    }
    let mut left = no_releases(source);
    let mut right = no_releases(target);
    loop {
        let (a, b) = match (left.next(), right.next()) {
            (None, None) => return true,
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };
        if *work == 0 {
            return false;
        }
        *work -= 1;
        // Charge operand vectors where they are traversed and environments
        // where they are copied. Ordinary instructions do not copy the map.
        let valid = match (a, b) {
            (
                LocalInstruction::Op {
                    binding: a,
                    attributes: aa,
                    inputs: ai,
                    outputs: ao,
                    ..
                },
                LocalInstruction::Op {
                    binding: b,
                    attributes: ba,
                    inputs: bi,
                    outputs: bo,
                    ..
                },
            ) => {
                charge(
                    work,
                    ai.len() + bi.len() + ao.len() + bo.len() + aa.len() + ba.len(),
                )
                .is_ok()
                    && a.declaration() == b.declaration()
                    && aa == ba
                    && values(&env, ai) == *bi
                    && bind(&mut env, ao, bo)
            }
            (
                LocalInstruction::BoolConstant {
                    output: a,
                    value: x,
                    ..
                },
                LocalInstruction::BoolConstant {
                    output: b,
                    value: y,
                    ..
                },
            ) => {
                env.insert(a.clone(), b.clone());
                x == y
            }
            (
                LocalInstruction::Variant {
                    ty: a,
                    alternative: aa,
                    payload: ai,
                    output: ao,
                    ..
                },
                LocalInstruction::Variant {
                    ty: b,
                    alternative: ba,
                    payload: bi,
                    output: bo,
                    ..
                },
            ) => {
                let same = charge(work, ai.len() + bi.len()).is_ok()
                    && a == b
                    && aa == ba
                    && values(&env, ai) == *bi;
                env.insert(ao.clone(), bo.clone());
                same
            }
            (
                LocalInstruction::Stop { reason: a, .. },
                LocalInstruction::Stop { reason: b, .. },
            ) => a == b,
            (
                LocalInstruction::Conditional {
                    condition: a,
                    captures: ac,
                    then_body: at,
                    else_body: ae,
                    outputs: ao,
                    ..
                },
                LocalInstruction::Conditional {
                    condition: b,
                    captures: bc,
                    then_body: bt,
                    else_body: be,
                    outputs: bo,
                    ..
                },
            ) => {
                charge(work, ac.len() + bc.len() + ao.len() + bo.len()).is_ok()
                    && mapped(&env, a) == *b
                    && values(&env, ac) == *bc
                    && charge(work, ac.len()).is_ok()
                    && same_body(
                        at,
                        bt,
                        ac.iter().cloned().zip(bc.iter().cloned()).collect(),
                        depth + 1,
                        work,
                    )
                    && charge(work, ac.len()).is_ok()
                    && same_body(
                        ae,
                        be,
                        ac.iter().cloned().zip(bc.iter().cloned()).collect(),
                        depth + 1,
                        work,
                    )
                    && bind(&mut env, ao, bo)
            }
            (
                LocalInstruction::For {
                    conditional: a,
                    induction: ai,
                    lower: al,
                    upper: au,
                    carried: ac,
                    captures: ap,
                    body: ab,
                    outputs: ao,
                    ..
                },
                LocalInstruction::For {
                    conditional: b,
                    induction: bi,
                    lower: bl,
                    upper: bu,
                    carried: bc,
                    captures: bp,
                    body: bb,
                    outputs: bo,
                    ..
                },
            ) => {
                if charge(
                    work,
                    ac.len() + bc.len() + 2 * ap.len() + bp.len() + ao.len() + bo.len(),
                )
                .is_err()
                {
                    return false;
                }
                let mut inner: Names = ap.iter().cloned().zip(bp.iter().cloned()).collect();
                inner.insert(ai.clone(), bi.clone());
                let same = a == b
                    && mapped(&env, al) == *bl
                    && mapped(&env, au) == *bu
                    && values(&env, ap) == *bp
                    && ac.len() == bc.len()
                    && ac.iter().zip(bc).all(|((name, value), (other, actual))| {
                        inner.insert(name.clone(), other.clone());
                        mapped(&env, value) == *actual
                    });
                same && same_body(ab, bb, inner, depth + 1, work) && bind(&mut env, ao, bo)
            }
            (
                LocalInstruction::Match {
                    input: a,
                    captures: ac,
                    arms: aa,
                    outputs: ao,
                    ..
                },
                LocalInstruction::Match {
                    input: b,
                    captures: bc,
                    arms: ba,
                    outputs: bo,
                    ..
                },
            ) => {
                charge(
                    work,
                    ac.len() + bc.len() + aa.len() + ba.len() + ao.len() + bo.len(),
                )
                .is_ok()
                    && mapped(&env, a) == *b
                    && values(&env, ac) == *bc
                    && aa.len() == ba.len()
                    && aa.iter().zip(ba).all(|(a, b)| {
                        if charge(work, ac.len() + a.payload.len() + b.payload.len()).is_err() {
                            return false;
                        }
                        let mut inner: Names = ac.iter().cloned().zip(bc.iter().cloned()).collect();
                        a.alternative == b.alternative
                            && bind(&mut inner, &a.payload, &b.payload)
                            && same_body(&a.body, &b.body, inner, depth + 1, work)
                    })
                    && bind(&mut env, ao, bo)
            }
            (LocalInstruction::Return(a), LocalInstruction::Yield(b)) if depth == 0 => {
                charge(work, a.len() + b.len()).is_ok() && values(&env, a) == *b
            }
            (LocalInstruction::Yield(a), LocalInstruction::Yield(b))
            | (LocalInstruction::Return(a), LocalInstruction::Return(b)) => {
                charge(work, a.len() + b.len()).is_ok() && values(&env, a) == *b
            }
            _ => false,
        };
        if !valid {
            return false;
        }
    }
}
fn conditional(
    function: &Function,
    source: &Function,
    writing: bool,
    contracts: &crate::vm::Contracts,
    work: &mut impl AdmissionWork,
) -> Result<()> {
    let mut inputs = repeated_type("bool", 1, work)?;
    work.charge(1 + 2 * source.inputs.len())?;
    inputs.extend(source.inputs.iter().map(|(_, t)| t.clone()));
    signature(function, &inputs, &source.outputs, work)?;
    data_function(function, contracts, work)?;
    let mut ops = no_releases(&function.body);
    let Some(LocalInstruction::Conditional {
        condition,
        captures,
        then_body,
        else_body,
        outputs,
        ..
    }) = ops.next()
    else {
        return Err(refuse("native-proof-codec-finalizer"));
    };
    if *condition != function.inputs[0].0
        || !captures
            .iter()
            .eq(function.inputs[1..].iter().map(|(n, _)| n))
        || !matches!(ops.next(),Some(LocalInstruction::Return(values)) if values==outputs)
        || ops.next().is_some()
    {
        return Err(refuse("native-proof-codec-finalizer"));
    }
    work.charge(source.inputs.iter().map(|(n, _)| n.len() + 2).sum())?;
    let env = source
        .inputs
        .iter()
        .map(|(n, _)| n.clone())
        .zip(captures.iter().cloned())
        .collect();
    if !same_body(&source.body, then_body, env, 0, &mut 1_000_000) {
        return Err(refuse("native-proof-codec-finalizer-body"));
    }
    let mut otherwise = no_releases(else_body);
    let empty = if writing {
        operation(
            otherwise
                .next()
                .ok_or_else(|| refuse("native-proof-codec-finalizer"))?,
            "bytes.empty",
            &[],
        )
        .filter(|v| v.len() == 1)
        .ok_or_else(|| refuse("native-proof-codec-finalizer"))?
    } else {
        &[]
    };
    if !matches!(otherwise.next(),Some(LocalInstruction::Yield(values)) if values==empty)
        || otherwise.next().is_some()
    {
        return Err(refuse("native-proof-codec-finalizer"));
    }
    Ok(())
}
struct Message<'a> {
    selection: &'a CodecMessage,
    observations: Vec<String>,
    payload: Vec<PhysicalType>,
    chunks: usize,
}
pub(super) struct CheckedCodec<'a> {
    admitted: &'a Program,
    codec: &'a RecordCodec,
    state: &'a [PhysicalType],
    messages: Vec<Message<'a>>,
    reserved: BTreeSet<String>,
    transitions: BTreeSet<String>,
    message_functions: BTreeMap<String, Vec<usize>>,
    data_functions: RefCell<BTreeSet<String>>,
}
impl<'a> CheckedCodec<'a> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        admitted: &'a Program,
        codec: &'a RecordCodec,
        state: &'a [PhysicalType],
        helpers: &BTreeMap<String, Helper<'_>>,
        producer: &str,
        validator: &str,
        selection: Option<NativeProofOperation>,
        work: &mut impl AdmissionWork,
    ) -> Result<Self> {
        work.charge(codec.record.len() + state.len() + codec.inputs.len() + 12)?;
        let producing = selection != Some(NativeProofOperation::Verify);
        let validating = selection != Some(NativeProofOperation::Prove);
        let function = |name: &str| {
            admitted
                .program
                .functions
                .get(name)
                .map(Arc::as_ref)
                .ok_or_else(|| refuse("native-proof-codec-function"))
        };
        // Plans describe both transport directions. Only the selected direction
        // requires its executable helpers; every retained declaration is checked.
        let selected_function = |name: &str, required: bool| {
            let found = admitted.program.functions.get(name).map(Arc::as_ref);
            if required && found.is_none() {
                Err(refuse("native-proof-codec-function"))
            } else {
                Ok(found)
            }
        };
        let initialize = function(&codec.initialize)?;
        type_list_work(&initialize.outputs, work)?;
        type_list_work(&codec.record, work)?;
        if initialize.outputs != codec.record {
            return Err(refuse("native-proof-codec-signature"));
        }
        let mut data_functions = BTreeSet::new();
        let mut wire_functions = BTreeSet::new();
        for name in [&codec.initialize, &codec.write, &codec.finish] {
            work.charge(type_work::lookup_work(name, data_functions.len()))?;
            if let Some(function) = selected_function(name, false)?
                && data_functions.insert(name.clone())
            {
                data_function(function, admitted.contracts(), work)?;
            }
        }
        if let Some(write) = selected_function(&codec.write, producing)? {
            signature(
                write,
                &codec.record,
                &repeated_type("bytes", 1, work)?,
                work,
            )?;
        }
        let mut inputs = copy_types(&codec.record, work)?;
        extend_types(&mut inputs, &repeated_type("bytes", 1, work)?, work)?;
        if let Some(finish) = selected_function(&codec.finish, validating)? {
            signature(finish, &inputs, &[], work)?;
        }
        if codec.conditional_write.is_empty() != codec.conditional_finish.is_empty() {
            return Err(refuse("native-proof-codec-finalizer"));
        }
        if !codec.conditional_write.is_empty() {
            if let Some(write) = selected_function(&codec.conditional_write, producing)? {
                conditional(
                    write,
                    function(&codec.write)?,
                    true,
                    admitted.contracts(),
                    work,
                )?;
            }
            if let Some(finish) = selected_function(&codec.conditional_finish, validating)? {
                conditional(
                    finish,
                    function(&codec.finish)?,
                    false,
                    admitted.contracts(),
                    work,
                )?;
            }
        }
        let mut messages = Vec::new();
        let mut seen = BTreeSet::new();
        work.charge(helpers.values().map(|h| h.events[0].origin.len() + 2).sum())?;
        let origins: BTreeMap<_, _> = helpers
            .iter()
            .map(|(n, h)| (h.events[0].origin.as_str(), (n, h)))
            .collect();
        work.charge(codec.conditional_write.len() + codec.conditional_finish.len() + 2)?;
        let mut reserved = BTreeSet::from([
            codec.conditional_write.clone(),
            codec.conditional_finish.clone(),
        ]);
        work.charge(codec.messages.len())?;
        for selection in &codec.messages {
            work.charge(
                selection
                    .origins
                    .iter()
                    .map(|origin| origin.len() + 1)
                    .sum(),
            )?;
            let mut observations = Vec::new();
            let mut payload = Vec::new();
            let mut offset = 0;
            while offset < selection.origins.len() {
                let (name, helper) = origins
                    .get(selection.origins[offset].as_str())
                    .copied()
                    .ok_or_else(|| refuse("native-proof-codec-coverage"))?;
                work.charge(
                    type_work::lookup_work(name, seen.len())
                        + helper
                            .events
                            .iter()
                            .map(|e| e.origin.len() + 1)
                            .sum::<usize>(),
                )?;
                if helper
                    .message
                    .as_ref()
                    .map(|(s, r)| (s.as_str(), r.as_str()))
                    != Some((producer, validator))
                    || !seen.insert(name.clone())
                    || !helper
                        .events
                        .iter()
                        .map(|e| &e.origin)
                        .eq(selection.origins[offset..].iter().take(helper.events.len()))
                {
                    return Err(refuse("native-proof-codec-coverage"));
                }
                offset += helper.events.len();
                work.charge(
                    name.len() + observations.len() + payload.len() + 2 * helper.events.len() + 1,
                )?;
                observations.push(name.clone());
                payload.extend(
                    helper.function.inputs[state.len()..state.len() + helper.events.len()]
                        .iter()
                        .map(|(_, t)| t.clone()),
                );
            }
            for ty in &payload {
                type_work::comparison_work(ty, work)?;
                if !ty.logical().is_native_message_data()
                    || !type_work::wire_data(ty, admitted.contracts(), work)?
                {
                    return Err(refuse("native-proof-wire-type"));
                }
            }
            let encode = selected_function(&selection.encode, producing)?;
            let decode = selected_function(&selection.decode, validating)?;
            let chunks = if let Some(decode) = decode {
                decode.inputs.len()
            } else {
                encode
                    .ok_or_else(|| refuse("native-proof-codec-function"))?
                    .outputs
                    .len()
                    .checked_sub(codec.record.len())
                    .ok_or_else(|| refuse("native-proof-codec-signature"))?
            };
            if chunks == 0 || chunks > 1024 {
                return Err(refuse("native-proof-codec-signature"));
            }
            let chunk_types = repeated_type("bytes", chunks, work)?;
            if let Some(decode) = decode {
                signature(decode, &chunk_types, &payload, work)?;
            }
            let mut inputs = copy_types(&codec.record, work)?;
            extend_types(&mut inputs, &payload, work)?;
            let mut outputs = copy_types(&codec.record, work)?;
            extend_types(&mut outputs, &chunk_types, work)?;
            if let Some(encode) = encode {
                signature(encode, &inputs, &outputs, work)?;
            }
            inputs = copy_types(&codec.record, work)?;
            extend_types(&mut inputs, &repeated_type("bytes", 1, work)?, work)?;
            outputs = copy_types(&codec.record, work)?;
            extend_types(
                &mut outputs,
                &repeated_type("index", 2 * chunks, work)?,
                work,
            )?;
            if let Some(receive) = selected_function(&selection.receive, validating)? {
                signature(receive, &inputs, &outputs, work)?;
            }
            inputs = repeated_type("bytes", 1, work)?;
            extend_types(
                &mut inputs,
                &repeated_type("index", 2 * chunks, work)?,
                work,
            )?;
            if let Some(slice) = selected_function(&selection.slice, validating)? {
                signature(slice, &inputs, &chunk_types, work)?;
                let mut ops = no_releases(&slice.body);
                let mut slices = Vec::new();
                for i in 0..chunks {
                    work.charge(4 * super::super::Limits::IDENTIFIER_BYTES + slices.len() + 4)?;
                    let values = operation(
                        ops.next()
                            .ok_or_else(|| refuse("native-proof-codec-slice"))?,
                        "bytes.slice",
                        &[
                            slice.inputs[0].0.clone(),
                            slice.inputs[1 + 2 * i].0.clone(),
                            slice.inputs[2 + 2 * i].0.clone(),
                        ],
                    )
                    .filter(|v| v.len() == 1)
                    .ok_or_else(|| refuse("native-proof-codec-slice"))?;
                    slices.push(values[0].clone());
                }
                work.charge(chunks * (super::super::Limits::IDENTIFIER_BYTES + 1))?;
                if !matches!(ops.next(),Some(LocalInstruction::Return(values)) if *values==slices)
                    || ops.next().is_some()
                {
                    return Err(refuse("native-proof-codec-slice"));
                }
            }
            for name in [
                &selection.encode,
                &selection.receive,
                &selection.decode,
                &selection.slice,
            ] {
                work.charge(
                    type_work::lookup_work(name, data_functions.len())
                        + type_work::lookup_work(name, reserved.len()),
                )?;
                if let Some(function) = selected_function(name, false)?
                    && data_functions.insert(name.clone())
                {
                    data_function(function, admitted.contracts(), work)?;
                }
                reserved.insert(name.clone());
            }
            if !selection.wire.is_empty() {
                let mut inputs = copy_types(state, work)?;
                extend_types(&mut inputs, &chunk_types, work)?;
                signature(function(&selection.wire)?, &inputs, state, work)?;
                work.charge(
                    type_work::lookup_work(&selection.wire, wire_functions.len())
                        + type_work::lookup_work(&selection.wire, reserved.len()),
                )?;
                if wire_functions.insert(selection.wire.clone()) {
                    construction_function(
                        function(&selection.wire)?,
                        state,
                        admitted.contracts(),
                        work,
                    )?;
                }
                reserved.insert(selection.wire.clone());
            }
            work.charge(messages.len() + 1)?;
            messages.push(Message {
                selection,
                observations,
                payload,
                chunks,
            });
        }
        work.charge(helpers.len() * (super::super::Limits::IDENTIFIER_BYTES + 4))?;
        if helpers.iter().any(|(n, h)| {
            h.message
                .as_ref()
                .is_some_and(|(s, r)| s == producer && r == validator)
                && !seen.contains(n)
        }) {
            return Err(refuse("native-proof-codec-coverage"));
        }
        let mut message_functions: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for (index, message) in messages.iter().enumerate() {
            for name in [&message.selection.encode, &message.selection.receive] {
                work.charge(
                    type_work::lookup_work(name, message_functions.len()) + messages.len(),
                )?;
                message_functions
                    .entry(name.clone())
                    .or_default()
                    .push(index);
            }
        }
        work.charge(
            helpers
                .keys()
                .map(|name| type_work::lookup_work(name, helpers.len()))
                .sum(),
        )?;
        Ok(Self {
            admitted,
            codec,
            state,
            messages,
            reserved,
            transitions: helpers.keys().cloned().collect(),
            message_functions,
            data_functions: RefCell::new(data_functions),
        })
    }
    pub fn normalize(
        &self,
        participant: &Participant,
        body: &[Instruction],
        inputs: &[usize],
        validating: bool,
        producer: &str,
        validator: &str,
    ) -> Result<Body> {
        let mut work = 1_000_000;
        charge(
            &mut work,
            participant.inputs.len() + self.codec.inputs.len() * (inputs.len() + 1),
        )?;
        let proof = if validating {
            Some(
                participant
                    .inputs
                    .last()
                    .ok_or_else(|| refuse("native-proof-codec-ingress"))?
                    .0
                    .clone(),
            )
        } else {
            None
        };
        let layout = self
            .codec
            .inputs
            .iter()
            .map(|i| {
                inputs
                    .iter()
                    .position(|x| x == i)
                    .and_then(|index| participant.inputs.get(index))
                    .map(|(n, _)| n.clone())
                    .ok_or_else(|| refuse("native-proof-codec-layout"))
            })
            .collect::<Result<Vec<_>>>()?;
        let mut cursor = 0;
        let record = self.invoke(
            body,
            &mut cursor,
            &self.codec.initialize,
            &layout,
            &mut work,
        )?;
        if record.len() != self.codec.record.len() {
            return Err(refuse("native-proof-codec-record-chain"));
        }
        charge(&mut work, record.len() + usize::from(proof.is_some()))?;
        let mut walk = Walk {
            checked: self,
            validating,
            producer,
            validator,
            seen: BTreeSet::new(),
            work,
        };
        let mut internal: BTreeSet<_> = record.iter().cloned().collect();
        internal.extend(proof.iter().cloned());
        let normalized = walk.block(
            &body[cursor..],
            record,
            proof,
            Names::new(),
            internal,
            0,
            0,
            None,
        )?;
        if walk.seen.len() != self.messages.len() {
            return Err(refuse("native-proof-codec-coverage"));
        }
        Ok(normalized)
    }
    fn check_data(&self, name: &str, work: &mut usize) -> Result<()> {
        charge(
            work,
            type_work::lookup_work(name, self.data_functions.borrow().len()),
        )?;
        if !self.data_functions.borrow().contains(name) {
            data_function(
                &self.admitted.program.functions[name],
                self.admitted.contracts(),
                work,
            )?;
            charge(
                work,
                type_work::lookup_work(name, self.data_functions.borrow().len()),
            )?;
            self.data_functions.borrow_mut().insert(name.into());
        }
        Ok(())
    }
    fn invoke(
        &self,
        body: &[Instruction],
        cursor: &mut usize,
        name: &str,
        inputs: &[String],
        work: &mut usize,
    ) -> Result<Vec<String>> {
        if let Some(op) = body.get(*cursor) {
            charge(work, instruction_cost(op))?;
        }
        let Some(Instruction::Local {
            function,
            inputs: actual,
            outputs,
            ..
        }) = body.get(*cursor)
        else {
            return Err(refuse("native-proof-codec-order"));
        };
        if function != name || actual != inputs {
            return Err(refuse("native-proof-codec-operand"));
        }
        *cursor += 1;
        Ok(outputs.clone())
    }
}
struct Pending<'a> {
    message: &'a Message<'a>,
    payload: Vec<String>,
    observer: usize,
    offset: usize,
    wire: Option<Vec<String>>,
}
struct Walk<'a, 'b> {
    checked: &'b CheckedCodec<'a>,
    validating: bool,
    producer: &'b str,
    validator: &'b str,
    seen: BTreeSet<usize>,
    work: usize,
}
impl Walk<'_, '_> {
    fn returns_proof(&mut self, body: &[Instruction], value: Option<&String>) -> Result<bool> {
        for op in body {
            charge(&mut self.work, instruction_cost(op))?;
            match op {
                Instruction::Local { .. } => {}
                Instruction::Return(values) => return Ok(values.last() == value),
                _ => return Ok(false),
            }
        }
        Ok(false)
    }
    #[allow(clippy::too_many_arguments)]
    fn block(
        &mut self,
        body: &[Instruction],
        mut record: Vec<String>,
        proof: Option<String>,
        mut aliases: Names,
        mut internal: BTreeSet<String>,
        depth: usize,
        repeat_depth: usize,
        yield_arity: Option<usize>,
    ) -> Result<Body> {
        if depth > 64 {
            return Err(refuse("native-proof-codec-limit"));
        }
        if !matches!(
            (body.last(), yield_arity),
            (Some(Instruction::Yield(_)), Some(_)) | (Some(Instruction::Return(_)), None)
        ) {
            return Err(refuse("native-proof-codec-exit"));
        }
        let codec = self.checked.codec;
        let slots = codec.record.len();
        let mut output = Vec::new();
        let mut cursor = 0;
        let mut pending: Option<Pending<'_>> = None;
        while let Some(op) = body.get(cursor) {
            charge(&mut self.work, instruction_cost(op))?;
            if let Instruction::Local {
                function,
                inputs,
                outputs,
                ..
            } = op
            {
                if let Some(indices) = self.checked.message_functions.get(function) {
                    charge(&mut self.work, indices.len())?;
                }
                if let Some(index) = self
                    .checked
                    .message_functions
                    .get(function)
                    .and_then(|indices| indices.iter().copied().find(|i| !self.seen.contains(i)))
                {
                    let message = &self.checked.messages[index];
                    if function
                        != if self.validating {
                            &message.selection.receive
                        } else {
                            &message.selection.encode
                        }
                    {
                        return Err(refuse("native-proof-codec-order"));
                    }
                    if pending.is_some()
                        || !self.seen.insert(index)
                        || inputs.get(..slots) != Some(record.as_slice())
                    {
                        return Err(refuse("native-proof-codec-record-chain"));
                    }
                    if outputs.len() < slots {
                        return Err(refuse("native-proof-codec-record-chain"));
                    }
                    internal.extend(outputs.iter().cloned());
                    let mut payload = Vec::new();
                    let chunks = if self.validating {
                        if inputs.get(slots..) != proof.as_ref().map(std::slice::from_ref) {
                            return Err(refuse("native-proof-codec-ingress"));
                        }
                        cursor += 1;
                        record = outputs[..slots].to_vec();
                        let mut selected = vec![proof.clone().unwrap()];
                        selected.extend_from_slice(&outputs[slots..]);
                        self.checked.invoke(
                            body,
                            &mut cursor,
                            &message.selection.slice,
                            &selected,
                            &mut self.work,
                        )?
                    } else {
                        payload = inputs[slots..].to_vec();
                        cursor += 1;
                        record = outputs[..slots].to_vec();
                        outputs[slots..].to_vec()
                    };
                    if chunks.len() != message.chunks {
                        return Err(refuse("native-proof-codec-chunks"));
                    }
                    internal.extend(chunks.iter().cloned());
                    let wire = if !message.selection.wire.is_empty() {
                        let Some(Instruction::Local {
                            function,
                            inputs,
                            outputs,
                            ..
                        }) = body.get(cursor)
                        else {
                            return Err(refuse("native-proof-codec-wire-order"));
                        };
                        charge(&mut self.work, inputs.len() + outputs.len())?;
                        if function != &message.selection.wire
                            || inputs.get(self.checked.state.len()..) != Some(chunks.as_slice())
                        {
                            return Err(refuse("native-proof-codec-wire-operand"));
                        }
                        for (to, from) in outputs.iter().zip(inputs) {
                            aliases.insert(to.clone(), mapped(&aliases, from));
                        }
                        cursor += 1;
                        Some(outputs.clone())
                    } else {
                        None
                    };
                    if self.validating {
                        payload = self.checked.invoke(
                            body,
                            &mut cursor,
                            &message.selection.decode,
                            &chunks,
                            &mut self.work,
                        )?;
                    }
                    pending = Some(Pending {
                        message,
                        payload,
                        observer: 0,
                        offset: 0,
                        wire,
                    });
                    continue;
                }
                if let Some(group) = pending.as_mut() {
                    // The compiler groups the transport and its observers as
                    // one sequence. Moving unrelated computation here could
                    // hide a stop or effect behind the synthetic transport.
                    if group.message.observations.get(group.observer) != Some(function) {
                        available(op, &internal)?;
                        return Err(refuse("native-proof-codec-order"));
                    }
                    if group.message.observations.get(group.observer) == Some(function) {
                        let f = &self.checked.admitted.program.functions[function];
                        let count = f
                            .inputs
                            .len()
                            .checked_sub(self.checked.state.len() + repeat_depth)
                            .ok_or_else(|| refuse("native-proof-codec-payload"))?;
                        if inputs.get(self.checked.state.len()..self.checked.state.len() + count)
                            != group.payload.get(group.offset..group.offset + count)
                            || group.observer == 0
                                && group.wire.as_ref().is_some_and(|wire| {
                                    inputs.get(..wire.len()) != Some(wire.as_slice())
                                })
                        {
                            return Err(refuse("native-proof-codec-payload"));
                        }
                        charge(&mut self.work, count)?;
                        for i in group.offset..group.offset + count {
                            output.push(if self.validating {
                                Instruction::Receive {
                                    site: "codec".into(),
                                    schema: "codec".into(),
                                    peer: self.producer.into(),
                                    output: group.payload[i].clone(),
                                    ty: group.message.payload[i].clone(),
                                }
                            } else {
                                Instruction::Send {
                                    site: "codec".into(),
                                    schema: "codec".into(),
                                    peer: self.validator.into(),
                                    input: group.payload[i].clone(),
                                }
                            });
                        }
                        group.offset += count;
                        group.observer += 1;
                        if group.observer == group.message.observations.len() {
                            if group.offset != group.payload.len() {
                                return Err(refuse("native-proof-codec-payload"));
                            }
                            pending = None;
                        }
                    }
                }
                let writing = !self.validating;
                let normal = if writing { &codec.write } else { &codec.finish };
                let conditional = if writing {
                    &codec.conditional_write
                } else {
                    &codec.conditional_finish
                };
                let internal_inputs = inputs.iter().any(|v| internal.contains(v));
                let finalizing = function == conditional
                    || function == normal
                        && (internal_inputs
                            || !self.validating
                                && slots == 0
                                && self.returns_proof(&body[cursor + 1..], outputs.first())?);
                if finalizing {
                    if pending.is_some() {
                        return Err(refuse("native-proof-codec-order"));
                    }
                    // Mathematical return expressions are outlined at their
                    // use, so data-only calculations can lie between this
                    // finalizer and its exit. No record or transcript step may.
                    internal.extend(outputs.iter().cloned());
                    let mut exit = cursor + 1;
                    while let Some(calculation @ Instruction::Local { function, .. }) =
                        body.get(exit)
                    {
                        charge(&mut self.work, instruction_cost(calculation))?;
                        if self.checked.reserved.contains(function)
                            || self.checked.transitions.contains(function)
                        {
                            return Err(refuse("native-proof-codec-exit"));
                        }
                        self.checked.check_data(function, &mut self.work)?;
                        if self.work == 0 {
                            return Err(refuse("native-proof-codec-limit"));
                        }
                        self.work -= 1;
                        exit += 1;
                    }
                    let next = body
                        .get(exit)
                        .ok_or_else(|| refuse("native-proof-codec-exit"))?;
                    charge(&mut self.work, instruction_cost(next) + record.len())?;
                    let (condition, values, continuations) = match next {
                        Instruction::Return(values) if function == normal => (None, values, None),
                        Instruction::ReturnIf {
                            condition,
                            values,
                            continuations,
                            ..
                        } if function == conditional => {
                            (Some(condition), values, Some(continuations))
                        }
                        _ => return Err(refuse("native-proof-codec-exit")),
                    };
                    let mut expected = condition.into_iter().cloned().collect::<Vec<_>>();
                    expected.extend_from_slice(&record);
                    if self.validating {
                        expected.push(proof.clone().unwrap());
                    }
                    if *inputs != expected
                        || writing && (outputs.len() != 1 || values.last() != outputs.first())
                    {
                        return Err(refuse("native-proof-codec-finalizer-operand"));
                    }
                    for calculation in &body[cursor + 1..exit] {
                        let mut calculation = calculation.clone();
                        rename(&mut calculation, &aliases);
                        available(&calculation, &internal)?;
                        output.push(calculation);
                    }
                    let mut normalized = next.clone();
                    match &mut normalized {
                        Instruction::Return(values) => {
                            if writing {
                                values.pop();
                            }
                        }
                        Instruction::ReturnIf { values, .. } => {
                            if writing {
                                values.pop();
                            }
                        }
                        _ => unreachable!(),
                    }
                    // Mapping removes only checked wire-state successors, never
                    // the ordinary successor state returned by an observer.
                    rename(&mut normalized, &aliases);
                    available(&normalized, &internal)?;
                    output.push(normalized);
                    cursor = exit + 1;
                    if continuations.is_none() && cursor != body.len() {
                        return Err(refuse("native-proof-codec-exit"));
                    }
                    continue;
                }
                if self.checked.reserved.contains(function) {
                    return Err(refuse("native-proof-codec-order"));
                }
            }
            if pending.is_some() && matches!(op, Instruction::Query { .. }) {
                return Err(refuse("native-proof-codec-order"));
            }
            match op {
                Instruction::Conditional {
                    site,
                    condition,
                    captures,
                    then_body,
                    else_body,
                    outputs,
                } => {
                    if pending.is_some() {
                        return Err(refuse("native-proof-codec-order"));
                    }
                    let split = outputs
                        .len()
                        .checked_sub(slots)
                        .ok_or_else(|| refuse("native-proof-codec-record-chain"))?;
                    let (prefix, nested, child_proof, child_internal) =
                        region_inputs(captures, &record, proof.as_ref(), &mut self.work)?;
                    charge(
                        &mut self.work,
                        nested.len() + child_internal.len() + usize::from(child_proof.is_some()),
                    )?;
                    let then_body = self.block(
                        then_body,
                        nested.clone(),
                        child_proof.clone(),
                        Names::new(),
                        child_internal.clone(),
                        depth + 1,
                        repeat_depth,
                        Some(outputs.len()),
                    )?;
                    let else_body = self.block(
                        else_body,
                        nested,
                        child_proof,
                        Names::new(),
                        child_internal,
                        depth + 1,
                        repeat_depth,
                        Some(outputs.len()),
                    )?;
                    let mut transformed = Instruction::Conditional {
                        site: site.clone(),
                        condition: condition.clone(),
                        captures: captures[..prefix].to_vec(),
                        then_body,
                        else_body,
                        outputs: outputs[..split].to_vec(),
                    };
                    rename(&mut transformed, &aliases);
                    available(&transformed, &internal)?;
                    record = outputs[split..].to_vec();
                    internal.extend(record.iter().cloned());
                    output.push(transformed);
                }
                Instruction::Match {
                    site,
                    input,
                    captures,
                    arms,
                    outputs,
                } => {
                    if pending.is_some() {
                        return Err(refuse("native-proof-codec-order"));
                    }
                    if arms.is_empty() || arms.len() > 512 {
                        return Err(refuse("native-proof-codec-limit"));
                    }
                    let split = outputs
                        .len()
                        .checked_sub(slots)
                        .ok_or_else(|| refuse("native-proof-codec-record-chain"))?;
                    let mut normalized = Vec::new();
                    let mut prefix = 0;
                    for arm in arms {
                        charge(&mut self.work, arm.payload.len())?;
                        let (start, nested, child_proof, child_internal) =
                            region_inputs(captures, &record, proof.as_ref(), &mut self.work)?;
                        prefix = start;
                        let body = self.block(
                            &arm.body,
                            nested,
                            child_proof,
                            Names::new(),
                            child_internal,
                            depth + 1,
                            repeat_depth,
                            Some(outputs.len()),
                        )?;
                        normalized.push(crate::vm::code::ParticipantArm {
                            alternative: arm.alternative.clone(),
                            payload: arm.payload.clone(),
                            body,
                        });
                    }
                    let mut transformed = Instruction::Match {
                        site: site.clone(),
                        input: input.clone(),
                        captures: captures[..prefix].to_vec(),
                        arms: normalized,
                        outputs: outputs[..split].to_vec(),
                    };
                    rename(&mut transformed, &aliases);
                    available(&transformed, &internal)?;
                    record = outputs[split..].to_vec();
                    internal.extend(record.iter().cloned());
                    output.push(transformed);
                }
                Instruction::Loop {
                    site,
                    count,
                    carried,
                    captures,
                    body,
                    outputs,
                } => {
                    if pending.is_some() {
                        return Err(refuse("native-proof-codec-order"));
                    }
                    let start = carried
                        .len()
                        .checked_sub(slots)
                        .ok_or_else(|| refuse("native-proof-codec-record-chain"))?;
                    if !carried[start..].iter().map(|(_, v)| v).eq(record.iter()) {
                        return Err(refuse("native-proof-codec-record-chain"));
                    }
                    let (capture_prefix, _, child_proof, mut nested_internal) =
                        region_inputs(captures, &[], proof.as_ref(), &mut self.work)?;
                    charge(&mut self.work, 2 * slots)?;
                    let nested: Vec<_> = carried[start..].iter().map(|(n, _)| n.clone()).collect();
                    nested_internal.extend(nested.iter().cloned());
                    let normalized = self.block(
                        body,
                        nested,
                        child_proof,
                        Names::new(),
                        nested_internal,
                        depth + 1,
                        repeat_depth + 1,
                        Some(carried.len()),
                    )?;
                    let split = outputs
                        .len()
                        .checked_sub(slots)
                        .ok_or_else(|| refuse("native-proof-codec-record-chain"))?;
                    if outputs.len() != carried.len() {
                        return Err(refuse("native-proof-codec-record-chain"));
                    }
                    let mut transformed = Instruction::Loop {
                        site: site.clone(),
                        count: count.clone(),
                        carried: carried[..start].to_vec(),
                        captures: captures[..capture_prefix].to_vec(),
                        body: normalized,
                        outputs: outputs[..split].to_vec(),
                    };
                    rename(&mut transformed, &aliases);
                    available(&transformed, &internal)?;
                    record = outputs[split..].to_vec();
                    internal.extend(record.iter().cloned());
                    output.push(transformed);
                }
                Instruction::Yield(values) => {
                    if pending.is_some()
                        || yield_arity != Some(values.len())
                        || cursor + 1 != body.len()
                        || tail(values, slots) != Some(record.as_slice())
                    {
                        return Err(refuse("native-proof-codec-record-chain"));
                    }
                    let op =
                        Instruction::Yield(self::values(&aliases, &values[..values.len() - slots]));
                    available(&op, &internal)?;
                    output.push(op);
                }
                Instruction::Send { .. }
                | Instruction::Receive { .. }
                | Instruction::Return(_)
                | Instruction::ReturnIf { .. } => return Err(refuse("native-proof-codec-exit")),
                _ => {
                    let mut op = op.clone();
                    rename(&mut op, &aliases);
                    available(&op, &internal)?;
                    output.push(op);
                }
            }
            cursor += 1;
        }
        if pending.is_some() {
            return Err(refuse("native-proof-codec-order"));
        }
        Ok(output.into())
    }
}
fn rename(op: &mut Instruction, names: &Names) {
    let map = |values: &mut Vec<String>| {
        for value in values {
            *value = mapped(names, value);
        }
    };
    match op {
        Instruction::Conditional {
            condition,
            captures,
            ..
        } => {
            *condition = mapped(names, condition);
            for (_, parent) in captures {
                *parent = mapped(names, parent);
            }
        }
        Instruction::Match {
            input, captures, ..
        } => {
            *input = mapped(names, input);
            for (_, parent) in captures {
                *parent = mapped(names, parent);
            }
        }
        Instruction::Local { inputs, .. } | Instruction::Query { inputs, .. } => map(inputs),
        Instruction::Send { input, .. } => *input = mapped(names, input),
        Instruction::Receive { .. } => {}
        Instruction::Loop {
            count,
            carried,
            captures,
            ..
        } => {
            count.value = mapped(names, &count.value);
            for (_, value) in carried {
                *value = mapped(names, value);
            }
            for (_, parent) in captures {
                *parent = mapped(names, parent);
            }
        }
        Instruction::ReturnIf {
            condition, values, ..
        } => {
            *condition = mapped(names, condition);
            map(values);
        }
        Instruction::Return(values) | Instruction::Yield(values) => map(values),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn long_finalizer_correspondence_charges_instructions_and_operands() {
        let make = |prefix: &str, returned: bool| {
            let mut body: Vec<_> = (0..2000)
                .map(|i| LocalInstruction::BoolConstant {
                    site: format!("{prefix}_site_{i}"),
                    output: format!("{prefix}_{i}"),
                    value: true,
                })
                .collect();
            let output = vec![format!("{prefix}_1999")];
            body.push(if returned {
                LocalInstruction::Return(output)
            } else {
                LocalInstruction::Yield(output)
            });
            body
        };
        let source = make("source", true);
        let mut candidate = make("candidate", false);
        let mut work = 1_000_000;
        assert!(same_body(&source, &candidate, Names::new(), 0, &mut work));
        assert!(work > 990_000);
        let LocalInstruction::BoolConstant { value, .. } = &mut candidate[1999] else {
            unreachable!()
        };
        *value = false;
        assert!(!same_body(
            &source,
            &candidate,
            Names::new(),
            0,
            &mut 1_000_000
        ));
        assert!(!same_body(&source, &source, Names::new(), 0, &mut 100));
    }

    #[test]
    fn conditional_finalizer_charges_both_branch_environments() {
        let env: Names = (0..100)
            .map(|i| (format!("v{i}"), format!("v{i}")))
            .collect();
        let body = vec![
            LocalInstruction::Conditional {
                site: "branch".into(),
                condition: "v0".into(),
                captures: env.keys().cloned().collect(),
                then_body: vec![LocalInstruction::Yield(vec![])].into(),
                else_body: vec![LocalInstruction::Yield(vec![])].into(),
                outputs: vec![],
            },
            LocalInstruction::Return(vec![]),
        ];
        assert!(!same_body(&body, &body, env.clone(), 0, &mut 150));
        assert!(same_body(&body, &body, env, 0, &mut 1000));
    }

    fn names(values: &[&str]) -> Vec<String> {
        values.iter().map(|v| (*v).into()).collect()
    }
    fn call(function: &str, inputs: &[&str], outputs: &[&str]) -> Instruction {
        Instruction::Local {
            site: function.into(),
            function: function.into(),
            inputs: names(inputs),
            outputs: names(outputs),
        }
    }
    fn captures(values: &[(&str, &str)]) -> Vec<(String, String)> {
        values
            .iter()
            .map(|(a, b)| ((*a).into(), (*b).into()))
            .collect()
    }
    fn selected(
        captures: Vec<(String, String)>,
        left: Vec<Instruction>,
        right: Vec<Instruction>,
        outputs: &[&str],
    ) -> Instruction {
        Instruction::Conditional {
            site: "branch".into(),
            condition: "condition".into(),
            captures,
            then_body: left.into(),
            else_body: right.into(),
            outputs: names(outputs),
        }
    }
    fn yielded(values: &[&str]) -> Vec<Instruction> {
        vec![Instruction::Yield(names(values))]
    }
    fn close(
        mut body: Vec<Instruction>,
        record: Option<&str>,
        validating: bool,
    ) -> Vec<Instruction> {
        let mut inputs = record.into_iter().collect::<Vec<_>>();
        if validating {
            inputs.push("proof");
        }
        body.push(call(
            if validating { "finish" } else { "write" },
            &inputs,
            if validating { &[] } else { &["bytes"] },
        ));
        body.push(Instruction::Return(if validating {
            vec![]
        } else {
            names(&["bytes"])
        }));
        body
    }
    // These fixtures isolate actual-body normalization. General Program
    // admission owns selector typing, exhaustive ordered alternatives, SSA
    // scope and signatures; public codec/helper admission is tested upstream.
    fn normalize_body(
        body: &[Instruction],
        slots: usize,
        validating: bool,
        message: bool,
        budget: usize,
    ) -> Result<Body> {
        use serde_json::json;
        let boolean = "bool@native.bool/0";
        let index = "index@native.index/0";
        let program = json!([
            "zkc.program/0",
            [],
            [
                [
                    "function",
                    "observe",
                    [["t", boolean], ["v", boolean]],
                    [boolean],
                    [["return", ["t"]]],
                    ["observe", []]
                ],
                [
                    "function",
                    "observe_loop",
                    [["t", boolean], ["v", boolean], ["i", index]],
                    [boolean],
                    [["return", ["t"]]],
                    ["observe_loop", []]
                ]
            ],
            [[
                "participant",
                "p",
                "root",
                "P",
                [],
                [],
                [["return", []]],
                []
            ]],
            [["entry", "main", [["P", "p"]]]]
        ]);
        let contracts =
            crate::vm::Contracts::standard(crate::vm::ExecutionPolicy::general_purpose());
        let admitted = Program::decode(program.to_string().as_bytes(), &contracts).unwrap();
        let selection = CodecMessage {
            encode: "encode".into(),
            receive: "receive".into(),
            decode: "decode".into(),
            wire: "wire".into(),
            slice: "slice".into(),
            origins: vec!["message".into()],
        };
        let codec = RecordCodec {
            record: vec![ty("index"); slots],
            initialize: "initialize".into(),
            write: "write".into(),
            finish: "finish".into(),
            conditional_write: "write_if".into(),
            conditional_finish: "finish_if".into(),
            inputs: vec![],
            messages: vec![],
        };
        let state = [ty("bool")];
        let observer = if body.iter().any(|op| matches!(op, Instruction::Loop { .. })) {
            "observe_loop"
        } else {
            "observe"
        };
        let checked = CheckedCodec {
            admitted: &admitted,
            codec: &codec,
            state: &state,
            messages: if message {
                vec![Message {
                    selection: &selection,
                    observations: names(&[observer]),
                    payload: vec![ty("bool")],
                    chunks: 1,
                }]
            } else {
                vec![]
            },
            reserved: names(&[
                "encode",
                "receive",
                "decode",
                "wire",
                "slice",
                "write_if",
                "finish_if",
            ])
            .into_iter()
            .collect(),
            transitions: names(&["observe", "observe_loop"]).into_iter().collect(),
            message_functions: if message {
                BTreeMap::from([("encode".into(), vec![0]), ("receive".into(), vec![0])])
            } else {
                BTreeMap::new()
            },
            data_functions: RefCell::new(BTreeSet::new()),
        };
        let mut walk = Walk {
            checked: &checked,
            validating,
            producer: "P",
            validator: "V",
            seen: BTreeSet::new(),
            work: budget,
        };
        let record = if slots == 0 {
            vec![]
        } else {
            names(&["record"])
        };
        let proof = validating.then(|| "proof".into());
        let mut internal: BTreeSet<_> = record.iter().cloned().collect();
        internal.extend(proof.iter().cloned());
        let result = walk.block(body, record, proof, Names::new(), internal, 0, 0, None)?;
        if message && walk.seen.len() != 1 {
            return Err(refuse("native-proof-codec-coverage"));
        }
        Ok(result)
    }

    #[test]
    fn event_free_branches_thread_record_with_zero_slot_support() {
        for validating in [false, true] {
            for slots in [0, 1] {
                let mut inputs = captures(&[("state", "state"), ("value", "value")]);
                let mut yielded_values = vec!["value", "state"];
                let mut outputs = vec!["result", "next_state"];
                if slots != 0 {
                    inputs.push(("r".into(), "record".into()));
                    yielded_values.push("r");
                    outputs.push("next_record");
                }
                if validating {
                    inputs.push(("p".into(), "proof".into()));
                }
                let branch = selected(
                    inputs,
                    yielded(&yielded_values),
                    yielded(&yielded_values),
                    &outputs,
                );
                let original = close(
                    vec![branch],
                    (slots != 0).then_some("next_record"),
                    validating,
                );
                let normalized =
                    normalize_body(&original, slots, validating, false, 10000).unwrap();
                let Instruction::Conditional {
                    captures,
                    outputs,
                    then_body,
                    else_body,
                    ..
                } = &normalized[0]
                else {
                    unreachable!()
                };
                assert_eq!(
                    captures,
                    &self::captures(&[("state", "state"), ("value", "value")])
                );
                assert_eq!(outputs, &names(&["result", "next_state"]));
                for arm in [then_body, else_body] {
                    assert_eq!(arm.len(), 1);
                    assert!(
                        matches!(&arm[0], Instruction::Yield(values) if *values == names(&["value", "state"]))
                    );
                }
                assert_eq!(normalized.len(), 2); // No arm-end finalizers.
                assert!(matches!(&normalized[1], Instruction::Return(values) if values.is_empty()));
                assert_eq!(original.len(), 3); // Evidence never replaces execution.
            }
        }
    }

    #[test]
    fn branch_capture_suffix_and_each_dormant_yield_are_checked() {
        for validating in [false, true] {
            let mut inputs = captures(&[("r", "record")]);
            if validating {
                inputs.push(("p".into(), "proof".into()));
            }
            for mutation in 0..4 {
                let mut branch = selected(
                    inputs.clone(),
                    yielded(&["r"]),
                    yielded(&["r"]),
                    &["next_record"],
                );
                let Instruction::Conditional {
                    captures,
                    else_body,
                    outputs,
                    ..
                } = &mut branch
                else {
                    unreachable!()
                };
                match mutation {
                    0 => captures[0].1 = "stale_record".into(),
                    1 => *else_body = yielded(&["stale_record"]).into(),
                    2 => *else_body = yielded(&["r", "r"]).into(),
                    _ => outputs.clear(),
                }
                assert_eq!(
                    normalize_body(
                        &close(vec![branch], Some("next_record"), validating),
                        1,
                        validating,
                        false,
                        10000
                    )
                    .unwrap_err()
                    .0,
                    "native-proof-codec-record-chain"
                );
            }
        }
        let branch = selected(
            captures(&[("p", "proof"), ("r", "record")]),
            yielded(&["r"]),
            yielded(&["r"]),
            &["next_record"],
        );
        assert_eq!(
            normalize_body(
                &close(vec![branch], Some("next_record"), true),
                1,
                true,
                false,
                10000
            )
            .unwrap_err()
            .0,
            "native-proof-codec-record-chain"
        );
        let branch = selected(
            captures(&[("leak", "proof"), ("r", "record"), ("p", "proof")]),
            yielded(&["r"]),
            yielded(&["r"]),
            &["next_record"],
        );
        assert_eq!(
            normalize_body(
                &close(vec![branch], Some("next_record"), true),
                1,
                true,
                false,
                10000
            )
            .unwrap_err()
            .0,
            "native-proof-codec-internal-use"
        );
    }

    #[test]
    fn match_preserves_payload_before_capture_prefix_and_checks_every_arm() {
        use crate::vm::code::ParticipantArm;
        let make = || Instruction::Match {
            site: "match".into(),
            input: "variant".into(),
            captures: captures(&[("state", "state"), ("r", "record"), ("p", "proof")]),
            arms: vec![
                ParticipantArm {
                    alternative: "some".into(),
                    payload: names(&["payload"]),
                    body: yielded(&["payload", "state", "r"]).into(),
                },
                ParticipantArm {
                    alternative: "none".into(),
                    payload: vec![],
                    body: yielded(&["state", "state", "r"]).into(),
                },
            ],
            outputs: names(&["out", "state_out", "next_record"]),
        };
        let normalized = normalize_body(
            &close(vec![make()], Some("next_record"), true),
            1,
            true,
            false,
            10000,
        )
        .unwrap();
        let Instruction::Match {
            captures,
            arms,
            outputs,
            ..
        } = &normalized[0]
        else {
            unreachable!()
        };
        assert_eq!(captures, &self::captures(&[("state", "state")]));
        assert_eq!(outputs, &names(&["out", "state_out"]));
        assert_eq!(arms[0].payload, names(&["payload"]));
        assert!(arms[1].payload.is_empty());
        assert!(
            matches!(&arms[0].body[0], Instruction::Yield(values) if *values == names(&["payload", "state"]))
        );
        let mut candidate = make();
        let Instruction::Match { arms, .. } = &mut candidate else {
            unreachable!()
        };
        arms[1].body = yielded(&["state", "state", "wrong"]).into();
        assert_eq!(
            normalize_body(
                &close(vec![candidate], Some("next_record"), true),
                1,
                true,
                false,
                10000
            )
            .unwrap_err()
            .0,
            "native-proof-codec-record-chain"
        );
    }

    #[test]
    fn conditional_finalization_preserves_false_edge_inside_an_arm() {
        for validating in [false, true] {
            let mut inputs = captures(&[
                ("condition", "condition"),
                ("resource", "resource"),
                ("r", "record"),
            ]);
            if validating {
                inputs.push(("p".into(), "proof".into()));
            }
            let mut finalize = vec!["condition", "r"];
            if validating {
                finalize.push("p");
            }
            let mut returned = vec!["resource"];
            if !validating {
                returned.push("conditional_bytes");
            }
            let arm = vec![
                call(
                    if validating { "finish_if" } else { "write_if" },
                    &finalize,
                    if validating {
                        &[]
                    } else {
                        &["conditional_bytes"]
                    },
                ),
                Instruction::ReturnIf {
                    site: "exit".into(),
                    condition: "condition".into(),
                    values: names(&returned),
                    continuations: names(&["continued"]),
                },
                Instruction::Yield(names(&["continued", "r"])),
            ];
            let branch = selected(
                inputs,
                arm,
                yielded(&["resource", "r"]),
                &["resource_out", "next_record"],
            );
            let body = close(vec![branch], Some("next_record"), validating);
            let normalized = normalize_body(&body, 1, validating, false, 10000).unwrap();
            let Instruction::Conditional { then_body, .. } = &normalized[0] else {
                unreachable!()
            };
            assert_eq!(then_body.len(), 2);
            assert!(
                matches!(&then_body[0], Instruction::ReturnIf { values, continuations, .. } if *values == names(&["resource"]) && *continuations == names(&["continued"]))
            );
            assert!(
                matches!(&then_body[1], Instruction::Yield(values) if *values == names(&["continued"]))
            );
            let mut mutated = body;
            let Instruction::Conditional { then_body, .. } = &mut mutated[0] else {
                unreachable!()
            };
            let mut ops = then_body.to_vec();
            let Instruction::Local { inputs, .. } = &mut ops[0] else {
                unreachable!()
            };
            inputs[0] = "other_condition".into();
            *then_body = ops.into();
            assert_eq!(
                normalize_body(&mutated, 1, validating, false, 10000)
                    .unwrap_err()
                    .0,
                "native-proof-codec-finalizer-operand"
            );
        }
    }

    #[test]
    fn message_observers_use_repeat_depth_not_branch_depth() {
        let arm = vec![
            call("encode", &["r", "value"], &["r1", "chunk"]),
            call("wire", &["state", "chunk"], &["wired"]),
            call("observe_loop", &["wired", "value", "iteration"], &["next"]),
            Instruction::Yield(names(&["next", "r1"])),
        ];
        let branch = selected(
            captures(&[
                ("state", "state"),
                ("value", "value"),
                ("iteration", "iteration"),
                ("r", "r"),
            ]),
            arm,
            yielded(&["state", "r"]),
            &["next_state", "next_record"],
        );
        let loop_op = Instruction::Loop {
            site: "loop".into(),
            count: LoopCount {
                value: "count".into(),
                maximum: 4,
                induction: "iteration".into(),
            },
            carried: captures(&[("state", "state"), ("r", "record")]),
            captures: captures(&[("value", "value"), ("condition", "condition")]),
            body: vec![
                branch,
                Instruction::Yield(names(&["next_state", "next_record"])),
            ]
            .into(),
            outputs: names(&["state_out", "record_out"]),
        };
        let normalized = normalize_body(
            &close(vec![loop_op], Some("record_out"), false),
            1,
            false,
            true,
            10000,
        )
        .unwrap();
        let Instruction::Loop { body, .. } = &normalized[0] else {
            unreachable!()
        };
        let Instruction::Conditional {
            then_body,
            else_body,
            ..
        } = &body[0]
        else {
            unreachable!()
        };
        assert!(matches!(&then_body[0], Instruction::Send { input, .. } if input == "value"));
        assert!(
            matches!(&then_body[1], Instruction::Local { inputs, .. } if *inputs == names(&["state", "value", "iteration"]))
        );
        assert!(
            matches!(&else_body[0], Instruction::Yield(values) if *values == names(&["state"]))
        );
    }

    #[test]
    fn validator_transport_in_an_arm_checks_proof_and_decoded_payload() {
        let arm = vec![
            call("receive", &["r", "p"], &["r1", "lo", "hi"]),
            call("slice", &["p", "lo", "hi"], &["chunk"]),
            call("wire", &["state", "chunk"], &["wired"]),
            call("decode", &["chunk"], &["decoded"]),
            call("observe", &["wired", "decoded"], &["next"]),
            Instruction::Yield(names(&["next", "r1"])),
        ];
        let make = |arm| {
            close(
                vec![selected(
                    captures(&[("state", "state"), ("r", "record"), ("p", "proof")]),
                    arm,
                    yielded(&["state", "r"]),
                    &["state_out", "record_out"],
                )],
                Some("record_out"),
                true,
            )
        };
        let normalized = normalize_body(&make(arm.clone()), 1, true, true, 10000).unwrap();
        let Instruction::Conditional { then_body, .. } = &normalized[0] else {
            unreachable!()
        };
        assert!(
            matches!(&then_body[0], Instruction::Receive { output, .. } if output == "decoded")
        );
        assert!(
            matches!(&then_body[1], Instruction::Local { inputs, .. } if *inputs == names(&["state", "decoded"]))
        );
        for mutation in 0..2 {
            let mut arm = arm.clone();
            let Instruction::Local { inputs, .. } = &mut arm[if mutation == 0 { 0 } else { 4 }]
            else {
                unreachable!()
            };
            inputs[1] = "wrong".into();
            assert_eq!(
                normalize_body(&make(arm), 1, true, true, 10000)
                    .unwrap_err()
                    .0,
                if mutation == 0 {
                    "native-proof-codec-ingress"
                } else {
                    "native-proof-codec-payload"
                }
            );
        }
    }

    #[test]
    fn transport_groups_cannot_cross_a_branch_boundary() {
        let body = close(
            vec![
                call("encode", &["record", "value"], &["r1", "chunk"]),
                call("wire", &["state", "chunk"], &["wired"]),
                selected(
                    captures(&[("r", "r1")]),
                    yielded(&["r"]),
                    yielded(&["r"]),
                    &["r2"],
                ),
            ],
            Some("r2"),
            false,
        );
        assert_eq!(
            normalize_body(&body, 1, false, true, 10000).unwrap_err().0,
            "native-proof-codec-order"
        );
    }

    #[test]
    fn arm_aliases_are_fresh_and_do_not_leak_to_siblings() {
        let arm = vec![
            call("encode", &["r", "value"], &["r1", "chunk"]),
            call("wire", &["state", "chunk"], &["wired"]),
            call("observe", &["wired", "value"], &["next"]),
            Instruction::Yield(names(&["next", "r1"])),
        ];
        let branch = selected(
            captures(&[("state", "state"), ("value", "value"), ("r", "record")]),
            arm,
            vec![
                Instruction::Query {
                    site: "private".into(),
                    port: "private".into(),
                    method: "draw".into(),
                    inputs: vec![],
                    outputs: names(&["wired"]),
                },
                Instruction::Yield(names(&["wired", "r"])),
            ],
            &["out", "r2"],
        );
        let normalized = normalize_body(
            &close(vec![branch], Some("r2"), false),
            1,
            false,
            true,
            10000,
        )
        .unwrap();
        let Instruction::Conditional { else_body, .. } = &normalized[0] else {
            unreachable!()
        };
        assert!(
            matches!(&else_body[1], Instruction::Yield(values) if *values == names(&["wired"]))
        );
    }

    #[test]
    fn recursive_and_wide_codec_traversals_are_charged_before_copying() {
        let body = close(
            vec![selected(
                captures(&[("r", "record")]),
                yielded(&["r"]),
                yielded(&["r"]),
                &["r2"],
            )],
            Some("r2"),
            false,
        );
        assert_eq!(
            normalize_body(&body, 1, false, false, 1).unwrap_err().0,
            "native-proof-codec-limit"
        );
        let mut nested = yielded(&["r"]);
        for _ in 0..65 {
            nested = vec![
                selected(captures(&[("r", "r")]), nested, yielded(&["r"]), &["next"]),
                Instruction::Yield(names(&["next"])),
            ];
        }
        let body = close(
            vec![selected(
                captures(&[("r", "record")]),
                nested,
                yielded(&["r"]),
                &["r2"],
            )],
            Some("r2"),
            false,
        );
        assert_eq!(
            normalize_body(&body, 1, false, false, 100000)
                .unwrap_err()
                .0,
            "native-proof-codec-limit"
        );
        let mut inputs: Vec<_> = (0..100)
            .map(|i| (format!("v{i}"), "value".into()))
            .collect();
        inputs.push(("r".into(), "record".into()));
        let body = close(
            vec![selected(inputs, yielded(&["r"]), yielded(&["r"]), &["r2"])],
            Some("r2"),
            false,
        );
        assert_eq!(
            normalize_body(&body, 1, false, false, 100).unwrap_err().0,
            "native-proof-codec-limit"
        );
    }

    #[test]
    fn arm_internal_values_cannot_escape_or_trigger_synthetic_completion() {
        let branch = selected(
            captures(&[("r", "record"), ("p", "proof")]),
            vec![
                Instruction::Query {
                    site: "leak".into(),
                    port: "private".into(),
                    method: "draw".into(),
                    inputs: names(&["p"]),
                    outputs: vec![],
                },
                Instruction::Yield(names(&["r"])),
            ],
            yielded(&["r"]),
            &["next_record"],
        );
        assert_eq!(
            normalize_body(
                &close(vec![branch], Some("next_record"), true),
                1,
                true,
                false,
                10000
            )
            .unwrap_err()
            .0,
            "native-proof-codec-internal-use"
        );
        let branch = selected(
            captures(&[("r", "record")]),
            vec![
                call("write", &["r"], &["bytes"]),
                Instruction::Yield(names(&["r"])),
            ],
            yielded(&["r"]),
            &["next_record"],
        );
        assert_eq!(
            normalize_body(
                &close(vec![branch], Some("next_record"), false),
                1,
                false,
                false,
                10000
            )
            .unwrap_err()
            .0,
            "native-proof-codec-exit"
        );
    }

    #[test]
    fn zero_record_match_still_captures_validator_proof() {
        let make = |parent: &str| Instruction::Match {
            site: "match".into(),
            input: "variant".into(),
            captures: captures(&[("p", parent)]),
            arms: vec![crate::vm::code::ParticipantArm {
                alternative: "unit".into(),
                payload: vec![],
                body: yielded(&[]).into(),
            }],
            outputs: vec![],
        };
        let normalized = normalize_body(
            &close(vec![make("proof")], None, true),
            0,
            true,
            false,
            10000,
        )
        .unwrap();
        assert!(
            matches!(&normalized[0], Instruction::Match { captures, outputs, .. } if captures.is_empty() && outputs.is_empty())
        );
        assert_eq!(
            normalize_body(
                &close(vec![make("other")], None, true),
                0,
                true,
                false,
                10000
            )
            .unwrap_err()
            .0,
            "native-proof-codec-record-chain"
        );
    }

    #[test]
    fn skipped_storage_releases_still_consume_correspondence_work() {
        let source: Vec<_> = (0..100)
            .map(|_| LocalInstruction::Release(vec![]))
            .collect();
        assert!(!same_body(&source, &[], Names::new(), 0, &mut 10));
        assert!(same_body(&source, &[], Names::new(), 0, &mut 1000));
    }
}
