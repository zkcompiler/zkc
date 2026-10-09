use super::model::*;
use super::{OperationBinding, PhysicalType, ResolvedBinding, ServiceContract, ServicePort};
use serde_json::Value as Json;
use std::{collections::BTreeMap, sync::Arc};

type Result<T> = std::result::Result<T, AdmissionError>;
fn err(code: ErrorCode, detail: &str) -> AdmissionError {
    AdmissionError::new(code, detail)
}

/// Preflight before serde allocation/recursion. Arrays, strings and bounded
/// Boolean tokens only; exact schema validation limits Booleans to native
/// literals. JSON syntax and trailing data remain serde's responsibility.
fn preflight(bytes: &[u8]) -> Result<()> {
    if bytes.len() > Limits::ARTIFACT_BYTES {
        return Err(err(ErrorCode::Limit, "artifact byte ceiling"));
    }
    let (mut depth, mut nodes, mut string, mut escape, mut start) =
        (0usize, 0usize, false, false, 0usize);
    let mut scalar_end = 0;
    for (i, b) in bytes.iter().copied().enumerate() {
        if i < scalar_end {
            continue;
        }
        if string {
            if i - start > 256 * 1024 + 19 {
                return Err(err(ErrorCode::Limit, "string byte ceiling"));
            }
            if escape {
                escape = false;
            } else if b == b'\\' {
                escape = true;
            } else if b == b'"' {
                string = false;
            }
            continue;
        }
        match b {
            b'"' => {
                string = true;
                start = i;
                nodes += 1;
            }
            b'[' => {
                depth += 1;
                nodes += 1;
            }
            b']' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| err(ErrorCode::Json, "unbalanced array"))?;
            }
            b't' | b'f' => {
                let token: &[u8] = if b == b't' { b"true" } else { b"false" };
                if !bytes[i..].starts_with(token) {
                    return Err(err(ErrorCode::Json, "invalid Boolean token"));
                }
                scalar_end = i + token.len();
                nodes += 1;
            }
            b',' | b' ' | b'\t' | b'\r' | b'\n' => (),
            _ => {
                return Err(err(
                    ErrorCode::Json,
                    "only arrays, strings and Boolean literals are permitted",
                ));
            }
        }
        if depth > Limits::JSON_DEPTH || nodes > Limits::JSON_NODES {
            return Err(err(ErrorCode::Limit, "JSON structural ceiling"));
        }
    }
    if string || depth != 0 {
        return Err(err(ErrorCode::Json, "unterminated JSON"));
    }
    Ok(())
}
fn array(v: &Json) -> Result<&[Json]> {
    let a = v
        .as_array()
        .ok_or_else(|| err(ErrorCode::Record, "expected array"))?;
    if a.len() > Limits::ARRAY_LENGTH {
        return Err(err(ErrorCode::Limit, "array length ceiling"));
    }
    Ok(a)
}
fn string(v: &Json) -> Result<&str> {
    let s = v
        .as_str()
        .ok_or_else(|| err(ErrorCode::Record, "expected string"))?;
    if s.len() > Limits::STRING_BYTES {
        return Err(err(ErrorCode::Limit, "string byte ceiling"));
    }
    Ok(s)
}
fn record<'a>(v: &'a Json, tag: &str, len: usize) -> Result<&'a [Json]> {
    let a = array(v)?;
    if a.len() != len || a.first().and_then(Json::as_str) != Some(tag) {
        return Err(err(ErrorCode::Record, "unknown tag or wrong exact arity"));
    }
    Ok(a)
}
pub(crate) fn valid_name(s: &str) -> bool {
    let b = s.as_bytes();
    !b.is_empty()
        && b.len() <= 128
        && (b[0].is_ascii_alphabetic() || b[0] == b'_')
        && b[1..]
            .iter()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
}
fn name(v: &Json) -> Result<String> {
    let s = string(v)?;
    if !valid_name(s) {
        return Err(err(ErrorCode::Name, "invalid ASCII identifier"));
    }
    Ok(s.to_owned())
}
pub(crate) fn canonical_decimal(s: &str) -> bool {
    !s.is_empty() && (s.len() == 1 || !s.starts_with('0')) && s.bytes().all(|b| b.is_ascii_digit())
}

fn natural(v: &Json) -> Result<u64> {
    let s = string(v)?;
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return Err(err(ErrorCode::Natural, "expected-natural"));
    }
    if !canonical_decimal(s) {
        return Err(err(ErrorCode::Natural, "noncanonical-natural"));
    }
    s.parse()
        .map_err(|_| err(ErrorCode::Natural, "natural exceeds u64"))
}
fn list(v: &Json, limit: usize) -> Result<&[Json]> {
    let a = array(v)?;
    if a.len() > limit {
        return Err(err(ErrorCode::Limit, "list ceiling"));
    }
    Ok(a)
}
fn names(v: &Json) -> Result<Vec<String>> {
    list(v, Limits::PORTS)?.iter().map(name).collect()
}
fn pairs(v: &Json) -> Result<Vec<(String, String)>> {
    list(v, Limits::PORTS)?
        .iter()
        .map(|v| {
            let a = array(v)?;
            if a.len() != 2 {
                return Err(err(ErrorCode::Record, "name pair arity"));
            }
            Ok((name(&a[0])?, name(&a[1])?))
        })
        .collect()
}
fn insert<T>(map: &mut BTreeMap<String, T>, key: String, value: T, code: ErrorCode) -> Result<()> {
    if map.insert(key, value).is_some() {
        return Err(err(code, "duplicate declaration"));
    }
    Ok(())
}
struct Decoder {
    bindings: BTreeMap<String, Arc<ResolvedBinding>>,
    instructions: usize,
    types: BTreeMap<String, PhysicalType>,
    type_bytes: usize,
}
impl Decoder {
    fn charge_type(&mut self, ty: &PhysicalType) -> Result<()> {
        self.type_bytes = self
            .type_bytes
            .checked_add(ty.logical().descriptor_bytes())
            .filter(|n| *n <= Limits::TYPE_BYTES)
            .ok_or_else(|| err(ErrorCode::Limit, "type descriptor byte ceiling"))?;
        Ok(())
    }
    fn physical_type(&mut self, value: &Json) -> Result<PhysicalType> {
        let spelling = value
            .as_str()
            .ok_or_else(|| err(ErrorCode::Record, "expected type string"))?;
        if let Some(ty) = self.types.get(spelling) {
            return Ok(ty.clone());
        }
        let ty = PhysicalType::parse(spelling).map_err(|error| {
            // The carrier-level reason agrees with source readers; keep the
            // descriptor parser's more specific reason for callers diagnosing it.
            if spelling.starts_with("variant:") && error.code != ErrorCode::Limit {
                AdmissionError::new(error.code, format!("binding-type: {}", error.detail))
            } else {
                error
            }
        })?;
        self.charge_type(&ty)?;
        self.types.insert(spelling.into(), ty.clone());
        Ok(ty)
    }
    fn types(&mut self, v: &Json) -> Result<Vec<PhysicalType>> {
        list(v, Limits::PORTS)?
            .iter()
            .map(|v| self.physical_type(v))
            .collect()
    }
    fn ports(&mut self, v: &Json) -> Result<Ports> {
        list(v, Limits::PORTS)?
            .iter()
            .map(|v| {
                let a = array(v)?;
                if a.len() != 2 {
                    return Err(err(ErrorCode::Record, "port pair arity"));
                }
                Ok((name(&a[0])?, self.physical_type(&a[1])?))
            })
            .collect()
    }

    fn charge(&mut self) -> Result<()> {
        self.instructions += 1;
        if self.instructions > Limits::STATIC_INSTRUCTIONS {
            return Err(err(ErrorCode::Limit, "static instruction ceiling"));
        }
        Ok(())
    }
    fn local_body(&mut self, v: &Json, depth: usize) -> Result<Arc<[LocalInstruction]>> {
        if depth > Limits::BLOCK_DEPTH {
            return Err(err(ErrorCode::Limit, "local block nesting ceiling"));
        }
        let mut body = Vec::new();
        for v in list(v, Limits::STATIC_INSTRUCTIONS)? {
            self.charge()?;
            let a = array(v)?;
            body.push(match a.first().and_then(Json::as_str) {
                Some("bool_constant") => {
                    let a = record(v, "bool_constant", 4)?;
                    LocalInstruction::BoolConstant {
                        site: name(&a[1])?,
                        output: name(&a[2])?,
                        value: a[3]
                            .as_bool()
                            .ok_or_else(|| err(ErrorCode::Record, "native Boolean literal"))?,
                    }
                }
                Some("variant") => {
                    let a = record(v, "variant", 6)?;
                    LocalInstruction::Variant {
                        site: name(&a[1])?,
                        ty: self.physical_type(&a[2])?,
                        alternative: name(&a[3])?,
                        payload: names(&a[4])?,
                        output: name(&a[5])?,
                    }
                }
                Some("match") => {
                    let a = record(v, "match", 6)?;
                    let mut arms = Vec::new();
                    for arm in list(&a[4], 32)? {
                        let arm = array(arm)?;
                        if arm.len() != 3 {
                            return Err(err(ErrorCode::Record, "match arm arity"));
                        }
                        arms.push(MatchArm {
                            alternative: name(&arm[0])?,
                            payload: names(&arm[1])?,
                            body: self.local_body(&arm[2], depth + 1)?,
                        });
                    }
                    LocalInstruction::Match {
                        site: name(&a[1])?,
                        input: name(&a[2])?,
                        captures: names(&a[3])?,
                        arms,
                        outputs: names(&a[5])?,
                    }
                }
                Some("stop") => {
                    let a = record(v, "stop", 3)?;
                    let reason = string(&a[2])?;
                    if !matches!(
                        reason,
                        "reject" | "abort" | "exhausted" | "incomplete" | "refused"
                    ) {
                        return Err(err(ErrorCode::Record, "unknown stop reason"));
                    }
                    LocalInstruction::Stop {
                        site: name(&a[1])?,
                        reason: reason.into(),
                    }
                }
                Some("op") => {
                    let a = record(v, "op", 6)?;
                    LocalInstruction::Op {
                        site: name(&a[1])?,
                        binding: self.bindings.get(&name(&a[2])?).cloned().ok_or_else(|| {
                            err(ErrorCode::Symbol, "unresolved operation binding")
                        })?,
                        attributes: list(&a[3], Limits::OPERATION_ATTRIBUTES)?
                            .iter()
                            .map(|v| Ok(string(v)?.to_owned()))
                            .collect::<Result<_>>()?,
                        inputs: names(&a[4])?,
                        outputs: names(&a[5])?,
                    }
                }
                Some("if") => {
                    let a = record(v, "if", 7)?;
                    LocalInstruction::Conditional {
                        site: name(&a[1])?,
                        condition: name(&a[2])?,
                        captures: names(&a[3])?,
                        then_body: self.local_body(&a[4], depth + 1)?,
                        else_body: self.local_body(&a[5], depth + 1)?,
                        outputs: names(&a[6])?,
                    }
                }
                Some(tag @ "for") | Some(tag @ "for_while") => {
                    let a = record(v, tag, 9)?;
                    LocalInstruction::For {
                        conditional: tag == "for_while",
                        site: name(&a[1])?,
                        induction: name(&a[2])?,
                        lower: name(&a[3])?,
                        upper: name(&a[4])?,
                        carried: pairs(&a[5])?,
                        captures: names(&a[6])?,
                        body: self.local_body(&a[7], depth + 1)?,
                        outputs: names(&a[8])?,
                    }
                }
                Some("yield") => LocalInstruction::Yield(names(&record(v, "yield", 2)?[1])?),
                Some("release") => LocalInstruction::Release(names(&record(v, "release", 2)?[1])?),
                Some("return") => LocalInstruction::Return(names(&record(v, "return", 2)?[1])?),
                _ => return Err(err(ErrorCode::Record, "unknown local instruction")),
            });
        }
        Ok(body.into())
    }
    fn function(&mut self, v: &Json) -> Result<Function> {
        let a = record(v, "function", 6)?;
        let body = self.local_body(&a[4], 0)?;
        Ok(Function {
            name: name(&a[1])?,
            origin: {
                let r = array(&a[5])?;
                if r.len() != 2 {
                    return Err(err(ErrorCode::Record, "logical origin arity"));
                }
                let mut seen = BTreeMap::new();
                let mut arguments = Vec::new();
                for pair in list(&r[1], 128)? {
                    let pair = array(pair)?;
                    if pair.len() != 2 {
                        return Err(err(ErrorCode::Record, "logical parameter arity"));
                    }
                    let parameter = name(&pair[0])?;
                    let identity = string(&pair[1])?;
                    if !super::bindings::valid_static_argument(identity) {
                        return Err(err(ErrorCode::Type, "logical origin static identity"));
                    }
                    insert(&mut seen, parameter.clone(), (), ErrorCode::Name)?;
                    arguments.push((parameter, identity.to_owned()));
                }
                LogicalOrigin {
                    definition: name(&r[0])?,
                    arguments,
                }
            },
            inputs: self.ports(&a[2])?,
            outputs: self.types(&a[3])?,
            body,
        })
    }
    fn body(&mut self, v: &Json, depth: usize) -> Result<Body> {
        if depth > Limits::BLOCK_DEPTH {
            return Err(err(ErrorCode::Limit, "block nesting ceiling"));
        }
        let mut body = Vec::new();
        for v in list(v, Limits::STATIC_INSTRUCTIONS)? {
            self.charge()?;
            let a = array(v)?;
            let i = match a.first().and_then(Json::as_str) {
                Some("local") => {
                    let a = record(v, "local", 5)?;
                    Instruction::Local {
                        site: name(&a[1])?,
                        function: name(&a[2])?,
                        inputs: names(&a[3])?,
                        outputs: names(&a[4])?,
                    }
                }
                Some("send") => {
                    let a = record(v, "send", 5)?;
                    Instruction::Send {
                        site: name(&a[1])?,
                        schema: name(&a[2])?,
                        peer: name(&a[3])?,
                        input: name(&a[4])?,
                    }
                }
                Some("receive") => {
                    let a = record(v, "receive", 6)?;
                    Instruction::Receive {
                        site: name(&a[1])?,
                        schema: name(&a[2])?,
                        peer: name(&a[3])?,
                        output: name(&a[4])?,
                        ty: self.physical_type(&a[5])?,
                    }
                }
                Some("loop") => {
                    let a = record(v, "loop", 7)?;
                    let parts = record(&a[2], "value", 4)?;
                    let maximum = natural(&parts[2])?;
                    if maximum > Limits::LOOP_COUNT {
                        return Err(err(ErrorCode::Limit, "loop count ceiling"));
                    }
                    let count = LoopCount {
                        value: name(&parts[1])?,
                        maximum,
                        induction: name(&parts[3])?,
                    };
                    Instruction::Loop {
                        site: name(&a[1])?,
                        count,
                        carried: pairs(&a[3])?,
                        captures: names(&a[4])?,
                        body: self.body(&a[5], depth + 1)?,
                        outputs: names(&a[6])?,
                    }
                }
                Some("return_if") => {
                    let a = record(v, "return_if", 5)?;
                    Instruction::ReturnIf {
                        site: name(&a[1])?,
                        condition: name(&a[2])?,
                        values: names(&a[3])?,
                        continuations: names(&a[4])?,
                    }
                }
                Some("yield") => Instruction::Yield(names(&record(v, "yield", 2)?[1])?),
                Some("return") => Instruction::Return(names(&record(v, "return", 2)?[1])?),
                Some("query") => {
                    let a = record(v, "query", 6)?;
                    Instruction::Query {
                        site: name(&a[1])?,
                        port: name(&a[2])?,
                        method: name(&a[3])?,
                        inputs: names(&a[4])?,
                        outputs: names(&a[5])?,
                    }
                }
                _ => return Err(err(ErrorCode::Record, "unknown participant instruction")),
            };
            body.push(i);
        }
        Ok(body.into())
    }
    fn participant(&mut self, v: &Json) -> Result<Participant> {
        let a = record(v, "participant", 8)?;
        let services = {
            list(&a[7], Limits::PORTS)?
                .iter()
                .map(|v| {
                    let port = array(v)?;
                    if port.len() != 3 {
                        return Err(err(ErrorCode::Record, "service port arity"));
                    }
                    Ok(ServicePort {
                        name: name(&port[0])?,
                        contract: ServiceContract::parse(string(&port[1])?)?,
                        input_index: usize::try_from(natural(&port[2])?)
                            .map_err(|_| err(ErrorCode::Limit, "service port index"))?,
                    })
                })
                .collect::<Result<Vec<_>>>()?
        };
        Ok(Participant {
            services,
            symbol: name(&a[1])?,
            instance: name(&a[2])?,
            role: name(&a[3])?,
            inputs: self.ports(&a[4])?,
            outputs: self.types(&a[5])?,
            body: self.body(&a[6], 0)?,
        })
    }
}
pub(crate) fn physical(bytes: &[u8]) -> Result<Program> {
    preflight(bytes)?;
    let json: Json = serde_json::from_slice(bytes)
        .map_err(|_| err(ErrorCode::Json, "invalid JSON or trailing input"))?;
    let a = array(&json)?;
    if a.len() != 5 {
        return Err(err(ErrorCode::Record, "participant module arity"));
    }
    let mut bindings = BTreeMap::new();
    let mut binding_type_bytes = 0usize;
    match string(&a[0])? {
        "zkc.program/0" => {
            for value in list(&a[1], Limits::DEFINITIONS)? {
                let r = array(value)?;
                if r.len() != 4 {
                    return Err(err(ErrorCode::Record, "operation binding arity"));
                }
                let declaration = OperationBinding {
                    contract: string(&r[1])?.into(),
                    arguments: list(&r[2], 128)?
                        .iter()
                        .map(|v| Ok(string(v)?.to_owned()))
                        .collect::<Result<_>>()?,
                    implementation: string(&r[3])?.into(),
                };
                let binding = ResolvedBinding::explicit(declaration)?;
                for ty in binding
                    .signature()
                    .inputs
                    .iter()
                    .chain(&binding.signature().outputs)
                {
                    binding_type_bytes = binding_type_bytes
                        .checked_add(ty.logical().descriptor_bytes())
                        .filter(|n| *n <= Limits::TYPE_BYTES)
                        .ok_or_else(|| err(ErrorCode::Limit, "type descriptor byte ceiling"))?;
                }
                insert(
                    &mut bindings,
                    name(&r[0])?,
                    Arc::new(binding),
                    ErrorCode::Symbol,
                )?;
            }
        }
        _ => return Err(err(ErrorCode::Record, "unknown participant module format")),
    };
    let mut decoder = Decoder {
        bindings,
        instructions: 0,
        types: BTreeMap::new(),
        type_bytes: binding_type_bytes,
    };
    let (mut functions, mut participants, mut entries) =
        (BTreeMap::new(), BTreeMap::new(), BTreeMap::new());
    for v in list(&a[2], Limits::DEFINITIONS)? {
        let f = decoder.function(v)?;
        insert(
            &mut functions,
            f.name.clone(),
            Arc::new(f),
            ErrorCode::Symbol,
        )?;
    }
    for v in list(&a[3], Limits::DEFINITIONS)? {
        let p = decoder.participant(v)?;
        insert(
            &mut participants,
            p.symbol.clone(),
            Arc::new(p),
            ErrorCode::Symbol,
        )?;
    }
    for v in list(&a[4], Limits::DEFINITIONS)? {
        let a = record(v, "entry", 3)?;
        let mut roles = BTreeMap::new();
        for (role, symbol) in pairs(&a[2])? {
            insert(&mut roles, role, symbol, ErrorCode::Role)?;
        }
        if roles.is_empty() {
            return Err(err(ErrorCode::Role, "entry has no roles"));
        }
        insert(&mut entries, name(&a[1])?, roles, ErrorCode::Symbol)?;
    }
    if entries.is_empty() {
        return Err(err(ErrorCode::Symbol, "module has no entry"));
    }
    for name in decoder.bindings.keys() {
        if functions.contains_key(name)
            || participants.contains_key(name)
            || entries.contains_key(name)
        {
            return Err(err(
                ErrorCode::Symbol,
                "operation binding namespace collision",
            ));
        }
    }
    Ok(Program {
        functions,
        participants,
        entries,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    fn nested(nominal: &str) -> String {
        let leaf = json!(["Leaf", [["item", ["bool"]]]]);
        let inner = json!(["Inner", [["many", vec![leaf; 32]]]]);
        let tree = json!([nominal, [["many", vec![inner; 32]]]]);
        format!(
            "{}@logical.variant/0",
            zkc_test_support::variants::encode_tree(tree)
        )
    }
    fn carrier(types: Vec<String>) -> Vec<u8> {
        let ports: Vec<_> = types
            .iter()
            .enumerate()
            .map(|(i, t)| json!([format!("x{i}"), t]))
            .collect();
        serde_json::to_vec(&json!([
            "zkc.program/0",
            [],
            [[
                "function",
                "unused",
                ports,
                [],
                [["return", []]],
                ["unused", []]
            ]],
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
        ]))
        .unwrap()
    }
    #[test]
    fn repeated_physical_and_nested_variant_descriptors_are_shared() {
        let bytes = carrier(vec![nested("Outer"); 1000]);
        assert!(bytes.len() < Limits::ARTIFACT_BYTES);
        let program = physical(&bytes).unwrap();
        let inputs = &program.functions["unused"].inputs;
        let first = inputs[0].1.logical().variant_descriptor().unwrap().clone();
        for (_, ty) in inputs {
            assert!(Arc::ptr_eq(
                &first,
                ty.logical().variant_descriptor().unwrap()
            ));
        }
        let payload = first.alternatives()[0].payload();
        for ty in payload {
            assert!(Arc::ptr_eq(
                payload[0].variant_descriptor().unwrap(),
                ty.variant_descriptor().unwrap()
            ));
        }
    }
    #[test]
    fn aggregate_distinct_descriptors_refuse_before_retaining_an_unbounded_program() {
        let bytes = carrier((0..128).map(|i| nested(&format!("Outer{i}"))).collect());
        assert!(bytes.len() < Limits::ARTIFACT_BYTES);
        let error = physical(&bytes).err().unwrap();
        assert_eq!(error.code, ErrorCode::Limit);
        assert_eq!(error.detail, "type descriptor byte ceiling");
    }
    #[test]
    fn unused_binding_signatures_share_the_installed_metadata_ceiling_with_ports() {
        let spelling = nested("Payload");
        let ty = PhysicalType::parse(&spelling).unwrap();
        let charge = ty.logical().descriptor_bytes();
        let count = Limits::TYPE_BYTES / charge;
        assert!(count > 0 && count < Limits::DEFINITIONS);
        let mut value: Json = serde_json::from_slice(&carrier(vec![])).unwrap();
        value[1] = Json::Array(
            (0..count)
                .map(|i| {
                    json!([
                        format!("observe{i}"),
                        "transcript.native.indexed.observe.data",
                        ["merlin3.bls12-381.fr64be/0", ty.logical().spelling()],
                        "arkworks/transcript.native.indexed.observe.data"
                    ])
                })
                .collect(),
        );
        let bytes = serde_json::to_vec(&value).unwrap();
        assert!(bytes.len() < Limits::ARTIFACT_BYTES);
        physical(&bytes).unwrap();
        value[2][0][2] = json!([["x", spelling]]);
        let error = physical(&serde_json::to_vec(&value).unwrap())
            .err()
            .unwrap();
        assert_eq!(error.code, ErrorCode::Limit);
        assert_eq!(error.detail, "type descriptor byte ceiling");
    }
}
