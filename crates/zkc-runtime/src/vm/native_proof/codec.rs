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
fn charge(work: &mut usize, amount: usize) -> Result<()> {
    *work = work
        .checked_sub(amount)
        .ok_or_else(|| refuse("native-proof-codec-limit"))?;
    Ok(())
}
fn available(op: &Instruction, internal: &BTreeSet<String>) -> Result<()> {
    let allowed = |values: &[String]| values.iter().all(|v| !internal.contains(v));
    let valid = match op {
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
fn data_function(function: &Function, contracts: &crate::vm::Contracts) -> Result<()> {
    construction_function(function, &[], contracts)?;
    source_transcript_function(function, None, contracts)
}
fn signature(function: &Function, inputs: &[PhysicalType], outputs: &[PhysicalType]) -> Result<()> {
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
                    && charge(work, env.len()).is_ok()
                    && same_body(at, bt, env.clone(), depth + 1, work)
                    && charge(work, env.len()).is_ok()
                    && same_body(ae, be, env.clone(), depth + 1, work)
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
                    env.len() + ac.len() + bc.len() + ap.len() + bp.len() + ao.len() + bo.len(),
                )
                .is_err()
                {
                    return false;
                }
                let mut inner = env.clone();
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
                        if charge(work, env.len() + a.payload.len() + b.payload.len()).is_err() {
                            return false;
                        }
                        let mut inner = env.clone();
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
) -> Result<()> {
    let mut inputs = vec![ty("bool")];
    inputs.extend(source.inputs.iter().map(|(_, t)| t.clone()));
    signature(function, &inputs, &source.outputs)?;
    data_function(function, contracts)?;
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
    ) -> Result<Self> {
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
        if initialize.outputs != codec.record {
            return Err(refuse("native-proof-codec-signature"));
        }
        let mut data_functions = BTreeSet::new();
        let mut wire_functions = BTreeSet::new();
        for name in [&codec.initialize, &codec.write, &codec.finish] {
            if let Some(function) = selected_function(name, false)?
                && data_functions.insert(name.clone())
            {
                data_function(function, admitted.contracts())?;
            }
        }
        if let Some(write) = selected_function(&codec.write, producing)? {
            signature(write, &codec.record, &[ty("bytes")])?;
        }
        let mut inputs = codec.record.clone();
        inputs.push(ty("bytes"));
        if let Some(finish) = selected_function(&codec.finish, validating)? {
            signature(finish, &inputs, &[])?;
        }
        if codec.conditional_write.is_empty() != codec.conditional_finish.is_empty() {
            return Err(refuse("native-proof-codec-finalizer"));
        }
        if !codec.conditional_write.is_empty() {
            if let Some(write) = selected_function(&codec.conditional_write, producing)? {
                conditional(write, function(&codec.write)?, true, admitted.contracts())?;
            }
            if let Some(finish) = selected_function(&codec.conditional_finish, validating)? {
                conditional(
                    finish,
                    function(&codec.finish)?,
                    false,
                    admitted.contracts(),
                )?;
            }
        }
        let mut messages = Vec::new();
        let mut seen = BTreeSet::new();
        let origins: BTreeMap<_, _> = helpers
            .iter()
            .map(|(n, h)| (h.events[0].origin.as_str(), (n, h)))
            .collect();
        let mut reserved = BTreeSet::from([
            codec.conditional_write.clone(),
            codec.conditional_finish.clone(),
        ]);
        for selection in &codec.messages {
            let mut observations = Vec::new();
            let mut payload = Vec::new();
            let mut offset = 0;
            while offset < selection.origins.len() {
                let (name, helper) = origins
                    .get(selection.origins[offset].as_str())
                    .copied()
                    .ok_or_else(|| refuse("native-proof-codec-coverage"))?;
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
                observations.push(name.clone());
                payload.extend(
                    helper.function.inputs[state.len()..state.len() + helper.events.len()]
                        .iter()
                        .map(|(_, t)| t.clone()),
                );
            }
            if payload.iter().any(|ty| {
                !ty.logical().is_native_message_data()
                    || !admitted
                        .contracts()
                        .permits_wire(ty, crate::vm::WireCodec::Native)
            }) {
                return Err(refuse("native-proof-wire-type"));
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
            let chunk_types = vec![ty("bytes"); chunks];
            if let Some(decode) = decode {
                signature(decode, &chunk_types, &payload)?;
            }
            let mut inputs = codec.record.clone();
            inputs.extend_from_slice(&payload);
            let mut outputs = codec.record.clone();
            outputs.extend_from_slice(&chunk_types);
            if let Some(encode) = encode {
                signature(encode, &inputs, &outputs)?;
            }
            inputs = codec.record.clone();
            inputs.push(ty("bytes"));
            outputs = codec.record.clone();
            outputs.extend(vec![ty("index"); 2 * chunks]);
            if let Some(receive) = selected_function(&selection.receive, validating)? {
                signature(receive, &inputs, &outputs)?;
            }
            inputs = vec![ty("bytes")];
            inputs.extend(vec![ty("index"); 2 * chunks]);
            if let Some(slice) = selected_function(&selection.slice, validating)? {
                signature(slice, &inputs, &chunk_types)?;
                let mut ops = no_releases(&slice.body);
                let mut slices = Vec::new();
                for i in 0..chunks {
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
                if let Some(function) = selected_function(name, false)?
                    && data_functions.insert(name.clone())
                {
                    data_function(function, admitted.contracts())?;
                }
                reserved.insert(name.clone());
            }
            if !selection.wire.is_empty() {
                let mut inputs = state.to_vec();
                inputs.extend(chunk_types);
                signature(function(&selection.wire)?, &inputs, state)?;
                if wire_functions.insert(selection.wire.clone()) {
                    construction_function(function(&selection.wire)?, state, admitted.contracts())?;
                }
                reserved.insert(selection.wire.clone());
            }
            messages.push(Message {
                selection,
                observations,
                payload,
                chunks,
            });
        }
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
                message_functions
                    .entry(name.clone())
                    .or_default()
                    .push(index);
            }
        }
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
        let proof = validating.then(|| participant.inputs.last().unwrap().0.clone());
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
        let record = self.invoke(body, &mut cursor, &self.codec.initialize, &layout)?;
        let mut walk = Walk {
            checked: self,
            validating,
            producer,
            validator,
            seen: BTreeSet::new(),
            work: 1_000_000,
        };
        let mut internal: BTreeSet<_> = record.iter().cloned().collect();
        internal.extend(proof.iter().cloned());
        let normalized = walk.block(&body[cursor..], record, proof, Names::new(), internal, 0)?;
        if walk.seen.len() != self.messages.len() {
            return Err(refuse("native-proof-codec-coverage"));
        }
        Ok(normalized)
    }
    fn check_data(&self, name: &str) -> Result<()> {
        if !self.data_functions.borrow().contains(name) {
            data_function(
                &self.admitted.program.functions[name],
                self.admitted.contracts(),
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
    ) -> Result<Vec<String>> {
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
            charge(&mut self.work, 1)?;
            match op {
                Instruction::Local { .. } => {}
                Instruction::Return(values) => return Ok(values.last() == value),
                _ => return Ok(false),
            }
        }
        Ok(false)
    }
    fn block(
        &mut self,
        body: &[Instruction],
        mut record: Vec<String>,
        proof: Option<String>,
        mut aliases: Names,
        mut internal: BTreeSet<String>,
        depth: usize,
    ) -> Result<Body> {
        if depth > 64 {
            return Err(refuse("native-proof-codec-limit"));
        }
        let codec = self.checked.codec;
        let slots = codec.record.len();
        let mut output = Vec::new();
        let mut cursor = 0;
        let mut pending: Option<Pending<'_>> = None;
        while let Some(op) = body.get(cursor) {
            if self.work == 0 {
                return Err(refuse("native-proof-codec-limit"));
            }
            self.work -= 1;
            if let Instruction::Local {
                function,
                inputs,
                outputs,
                ..
            } = op
            {
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
                            .checked_sub(self.checked.state.len() + depth)
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
                    while let Some(Instruction::Local { function, .. }) = body.get(exit) {
                        if self.checked.reserved.contains(function)
                            || self.checked.transitions.contains(function)
                        {
                            return Err(refuse("native-proof-codec-exit"));
                        }
                        self.checked.check_data(function)?;
                        if self.work == 0 {
                            return Err(refuse("native-proof-codec-limit"));
                        }
                        self.work -= 1;
                        exit += 1;
                    }
                    let next = body
                        .get(exit)
                        .ok_or_else(|| refuse("native-proof-codec-exit"))?;
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
                    if !carried[start..].iter().map(|(_, v)| v).eq(record.iter())
                        || proof
                            .as_ref()
                            .is_some_and(|p| !captures.iter().any(|(_, parent)| parent == p))
                    {
                        return Err(refuse("native-proof-codec-record-chain"));
                    }
                    charge(&mut self.work, aliases.len() + internal.len())?;
                    let mut nested_internal = internal.clone();
                    nested_internal.extend(carried[start..].iter().map(|(n, _)| n.clone()));
                    let nested = carried[start..].iter().map(|(n, _)| n.clone()).collect();
                    let child_proof = proof.as_ref().map(|proof| {
                        captures
                            .iter()
                            .find(|(_, parent)| parent == proof)
                            .expect("checked proof capture")
                            .0
                            .clone()
                    });
                    nested_internal.extend(
                        captures
                            .iter()
                            .filter(|(_, parent)| internal.contains(parent))
                            .map(|(local, _)| local.clone()),
                    );
                    let normalized = self.block(
                        body,
                        nested,
                        child_proof,
                        aliases.clone(),
                        nested_internal,
                        depth + 1,
                    )?;
                    let split = outputs
                        .len()
                        .checked_sub(slots)
                        .ok_or_else(|| refuse("native-proof-codec-record-chain"))?;
                    record = outputs[split..].to_vec();
                    internal.extend(record.iter().cloned());
                    let mut transformed = Instruction::Loop {
                        site: site.clone(),
                        count: count.clone(),
                        carried: carried[..start].to_vec(),
                        captures: captures
                            .iter()
                            .filter(|(_, parent)| Some(parent) != proof.as_ref())
                            .cloned()
                            .collect(),
                        body: normalized,
                        outputs: outputs[..split].to_vec(),
                    };
                    rename(&mut transformed, &aliases);
                    available(&transformed, &internal)?;
                    output.push(transformed);
                }
                Instruction::Yield(values) => {
                    if pending.is_some() || tail(values, slots) != Some(record.as_slice()) {
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
                captures: vec![],
                then_body: vec![LocalInstruction::Yield(vec![])].into(),
                else_body: vec![LocalInstruction::Yield(vec![])].into(),
                outputs: vec![],
            },
            LocalInstruction::Return(vec![]),
        ];
        assert!(!same_body(&body, &body, env.clone(), 0, &mut 150));
        assert!(same_body(&body, &body, env, 0, &mut 1000));
    }
}
