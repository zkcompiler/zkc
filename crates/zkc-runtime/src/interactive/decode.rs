use super::model::*;
use super::{ArtifactFormat, OperationBinding, PhysicalType, ResolvedBinding};
use serde_json::Value as Json;
use std::{collections::BTreeMap, sync::Arc};

type Result<T> = std::result::Result<T, AdmissionError>;
fn err(code: ErrorCode, detail: &str) -> AdmissionError {
    AdmissionError::new(code, detail)
}

/// Preflight before serde allocation/recursion. No non-string scalar is part of
/// this schema. JSON syntax (including escapes and trailing data) remains serde's job.
fn preflight(bytes: &[u8]) -> Result<()> {
    if bytes.len() > Limits::ARTIFACT_BYTES {
        return Err(err(ErrorCode::Limit, "artifact byte ceiling"));
    }
    let (mut depth, mut nodes, mut string, mut escape, mut start) =
        (0usize, 0usize, false, false, 0usize);
    for (i, b) in bytes.iter().copied().enumerate() {
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
            b',' | b' ' | b'\t' | b'\r' | b'\n' => (),
            _ => {
                return Err(err(
                    ErrorCode::Json,
                    "only arrays and strings are permitted",
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
fn family_ingress(value: &Json) -> Result<FamilyIngress> {
    let fields = record(value, "ingress", 3)?;
    let spelling = string(&fields[1])?;
    if !canonical_decimal(spelling) {
        return Err(err(ErrorCode::Parameters, "interactive-family-binding"));
    }
    // A canonical natural past the limit is out of bound however large.
    let bound = spelling
        .parse::<u64>()
        .ok()
        .filter(|bound| *bound <= Limits::PARAMETER)
        .ok_or_else(|| err(ErrorCode::Parameters, "interactive-family-bound"))?;
    let mut selectors = BTreeMap::new();
    for item in list(&fields[2], Limits::PORTS)? {
        let pair = array(item)?;
        if pair.len() != 3 {
            return Err(err(ErrorCode::Parameters, "interactive-family-binding"));
        }
        let role = name(&pair[0])?;
        if selectors.contains_key(&role) {
            return Err(err(ErrorCode::Parameters, "interactive-family-roles"));
        }
        let function = name(&pair[1])?;
        let arguments = names(&pair[2])?;
        if arguments
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            != arguments.len()
        {
            return Err(err(ErrorCode::Parameters, "interactive-family-argument"));
        }
        insert(
            &mut selectors,
            role,
            FamilySelector {
                function,
                arguments,
            },
            ErrorCode::Parameters,
        )?;
    }
    if selectors.is_empty() {
        return Err(err(ErrorCode::Parameters, "interactive-family-roles"));
    }
    Ok(FamilyIngress { bound, selectors })
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
fn physical_type(value: &Json, _format: ArtifactFormat) -> Result<PhysicalType> {
    let spelling = value
        .as_str()
        .ok_or_else(|| err(ErrorCode::Record, "expected type string"))?;
    PhysicalType::parse(spelling).map_err(|error| {
        // The carrier-level reason agrees with source readers; keep the
        // descriptor parser's more specific reason for callers diagnosing it.
        if spelling.starts_with("variant:") {
            AdmissionError::new(error.code, format!("binding-type: {}", error.detail))
        } else {
            error
        }
    })
}
fn types(v: &Json, p: ArtifactFormat) -> Result<Vec<PhysicalType>> {
    list(v, Limits::PORTS)?
        .iter()
        .map(|v| physical_type(v, p))
        .collect()
}
fn ports(v: &Json, p: ArtifactFormat) -> Result<Ports> {
    list(v, Limits::PORTS)?
        .iter()
        .map(|v| {
            let a = array(v)?;
            if a.len() != 2 {
                return Err(err(ErrorCode::Record, "port pair arity"));
            }
            Ok((name(&a[0])?, physical_type(&a[1], p)?))
        })
        .collect()
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
    format: ArtifactFormat,
    bindings: BTreeMap<String, Arc<ResolvedBinding>>,
    instructions: usize,
}
impl Decoder {
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
                Some("variant") => {
                    let a = record(v, "variant", 6)?;
                    LocalInstruction::Variant {
                        site: name(&a[1])?,
                        ty: physical_type(&a[2], self.format)?,
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
                Some("for") => {
                    let a = record(v, "for", 9)?;
                    LocalInstruction::For {
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
                    if !super::bindings::valid_static_identity(identity) {
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
            inputs: ports(&a[2], self.format)?,
            outputs: types(&a[3], self.format)?,
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
                        ty: physical_type(&a[5], self.format)?,
                    }
                }
                Some("call") => {
                    let a = record(v, "call", 5)?;
                    Instruction::Call {
                        site: name(&a[1])?,
                        participant: name(&a[2])?,
                        inputs: names(&a[3])?,
                        outputs: names(&a[4])?,
                    }
                }
                Some("loop") => {
                    let a = record(v, "loop", 7)?;
                    let count = if a[2].is_array() {
                        let parts = record(&a[2], "parameter", 2)?;
                        Count::Parameter(name(&parts[1])?)
                    } else {
                        let n = natural(&a[2])?;
                        if n > Limits::LOOP_COUNT {
                            return Err(err(ErrorCode::Limit, "loop count ceiling"));
                        }
                        Count::Constant(n)
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
                Some("yield") => Instruction::Yield(names(&record(v, "yield", 2)?[1])?),
                Some("return") => Instruction::Return(names(&record(v, "return", 2)?[1])?),
                Some("stop") => {
                    let a = record(v, "stop", 3)?;
                    let reason = string(&a[2])?;
                    if !matches!(
                        reason,
                        "reject" | "abort" | "exhausted" | "incomplete" | "refused"
                    ) {
                        return Err(err(ErrorCode::Record, "unknown stop reason"));
                    }
                    Instruction::Stop {
                        site: name(&a[1])?,
                        reason: reason.to_owned(),
                    }
                }
                Some("incomplete") => Instruction::Incomplete {
                    site: name(&record(v, "incomplete", 2)?[1])?,
                },
                _ => return Err(err(ErrorCode::Record, "unknown participant instruction")),
            };
            body.push(i);
        }
        Ok(body.into())
    }
    fn participant(&mut self, v: &Json) -> Result<Participant> {
        let a = record(v, "participant", 8)?;
        let mut parameters = BTreeMap::new();
        let mut families = BTreeMap::new();
        for v in list(&a[4], Limits::PORTS)? {
            let p = array(v)?;
            if p.len() != 2 {
                return Err(err(ErrorCode::Record, "parameter pair arity"));
            }
            let key = name(&p[0])?;
            if parameters.contains_key(&key) || families.contains_key(&key) {
                return Err(err(ErrorCode::Parameters, "duplicate family parameter"));
            }
            if p[1].is_array() {
                families.insert(key, family_ingress(&p[1])?);
                continue;
            }
            let value = natural(&p[1])?;
            if value > Limits::PARAMETER {
                return Err(err(ErrorCode::Limit, "public parameter ceiling"));
            }
            insert(&mut parameters, name(&p[0])?, value, ErrorCode::Parameters)?;
        }
        Ok(Participant {
            symbol: name(&a[1])?,
            instance: name(&a[2])?,
            role: name(&a[3])?,
            parameters,
            families,
            inputs: ports(&a[5], self.format)?,
            outputs: types(&a[6], self.format)?,
            body: self.body(&a[7], 0)?,
        })
    }
}
pub(crate) fn physical(bytes: &[u8]) -> Result<Program> {
    preflight(bytes)?;
    let json: Json = serde_json::from_slice(bytes)
        .map_err(|_| err(ErrorCode::Json, "invalid JSON or trailing input"))?;
    let a = array(&json)?;
    if a.len() != 6 {
        return Err(err(ErrorCode::Record, "participant module arity"));
    }
    let mut bindings = BTreeMap::new();
    let format = match string(&a[0])? {
        "zkc.participants/1" => {
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
                insert(
                    &mut bindings,
                    name(&r[0])?,
                    Arc::new(ResolvedBinding::explicit(declaration)?),
                    ErrorCode::Symbol,
                )?;
            }
            ArtifactFormat::ExplicitBindings
        }
        _ => return Err(err(ErrorCode::Record, "unknown participant module format")),
    };
    if string(&a[2])? != "physical" {
        return Err(err(
            ErrorCode::Stage,
            "production admission requires physical stage",
        ));
    }
    let mut decoder = Decoder {
        format,
        bindings,
        instructions: 0,
    };
    let (mut functions, mut participants, mut entries) =
        (BTreeMap::new(), BTreeMap::new(), BTreeMap::new());
    for v in list(&a[3], Limits::DEFINITIONS)? {
        let f = decoder.function(v)?;
        insert(
            &mut functions,
            f.name.clone(),
            Arc::new(f),
            ErrorCode::Symbol,
        )?;
    }
    for v in list(&a[4], Limits::DEFINITIONS)? {
        let p = decoder.participant(v)?;
        insert(
            &mut participants,
            p.symbol.clone(),
            Arc::new(p),
            ErrorCode::Symbol,
        )?;
    }
    for v in list(&a[5], Limits::DEFINITIONS)? {
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
        format,
        functions,
        participants,
        entries,
    })
}
