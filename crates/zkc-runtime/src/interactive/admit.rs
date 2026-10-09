use super::{PhysicalType, Representation, backend::Backend, decode, model::*};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

type Result<T> = std::result::Result<T, AdmissionError>;
fn err(code: ErrorCode, detail: impl Into<String>) -> AdmissionError {
    AdmissionError::new(code, detail)
}

/// Immutable custody of exactly the checked bytes and derived typed program.
#[derive(Clone, Debug)]
pub struct Admitted {
    pub(crate) program: Arc<Program>,
    bytes: Arc<[u8]>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntryRole {
    pub role: String,
    pub participant: String,
    pub instance: String,
    pub inputs: Vec<(String, PhysicalType)>,
    pub outputs: Vec<PhysicalType>,
    pub services: Vec<super::ServicePort>,
}
impl Admitted {
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn entry_names(&self) -> impl Iterator<Item = &str> {
        self.program.entries.keys().map(String::as_str)
    }
    pub fn entry(&self, name: &str) -> Option<Vec<EntryRole>> {
        self.program.entries.get(name).map(|roles| {
            roles
                .iter()
                .map(|(role, symbol)| {
                    let p = &self.program.participants[symbol];
                    EntryRole {
                        role: role.clone(),
                        participant: symbol.clone(),
                        instance: p.instance.clone(),
                        inputs: p.inputs.clone(),
                        outputs: p.outputs.clone(),
                        services: p.services.clone(),
                    }
                })
                .collect()
        })
    }

    /// Whether this artifact requires the native Boolean constructor, including
    /// retained unused definitions. This is separate from bound kernel names.
    pub fn requires_boolean_literals(&self) -> bool {
        requires_boolean_literals(&self.program)
    }
}

/// Admit an independently supplied native program by checking its executable
/// structure and installed contracts.
pub fn admit_supplied<B: Backend>(bytes: &[u8], backend: &B) -> Result<Admitted> {
    let program = decode::physical(bytes)?;
    validate(&program)?;
    installed(&program, backend)?;
    Ok(Admitted {
        program: Arc::new(program),
        bytes: Arc::from(bytes),
    })
}
fn requires_boolean_literals(p: &Program) -> bool {
    p.functions.values().any(|f| {
        LocalInstruction::walk(&f.body)
            .iter()
            .any(|op| matches!(op, LocalInstruction::BoolConstant { .. }))
    })
}
pub(crate) fn installed<B: Backend>(p: &Program, backend: &B) -> Result<()> {
    if requires_boolean_literals(p) && !backend.supports_boolean_literals() {
        return Err(err(ErrorCode::Backend, "native-boolean-unsupported"));
    }
    for participant in p.participants.values() {
        for port in &participant.services {
            let expected = port.contract.signature("draw").expect("installed method");
            if !backend
                .service_support(port.contract, "draw")
                .is_some_and(|support| {
                    support.signature == expected
                        && support.max_retained_bytes <= Limits::VALUE_BYTES
                })
            {
                return Err(err(
                    ErrorCode::Backend,
                    "installed service signature mismatch",
                ));
            }
        }
    }
    for f in p.functions.values() {
        for op in LocalInstruction::walk(&f.body) {
            if let LocalInstruction::Op { binding, .. } = op {
                let actual = backend.binding_signature(binding.declaration());
                if actual.as_ref() != Some(binding.signature()) {
                    return Err(err(
                        ErrorCode::Backend,
                        format!("installed signature mismatch: {}", binding.implementation()),
                    ));
                }
            }
        }
    }
    Ok(())
}
#[derive(Clone)]
struct Binding {
    ty: PhysicalType,
    available: bool,
}
type Env = BTreeMap<String, Binding>;
fn define(env: &mut Env, seen: &mut BTreeSet<String>, name: &str, ty: PhysicalType) -> Result<()> {
    if !seen.insert(name.to_owned()) {
        return Err(err(ErrorCode::Ssa, format!("duplicate SSA binding {name}")));
    }
    env.insert(
        name.to_owned(),
        Binding {
            ty,
            available: true,
        },
    );
    Ok(())
}
fn lookup(env: &Env, name: &str) -> Result<PhysicalType> {
    let b = env
        .get(name)
        .ok_or_else(|| err(ErrorCode::Ssa, format!("unavailable operand {name}")))?;
    if !b.available {
        return Err(err(
            ErrorCode::Ssa,
            format!("interactive-resource-reuse: consumed operand {name}"),
        ));
    }
    Ok(b.ty.clone())
}
fn operands(env: &mut Env, names: &[String], expected: &[PhysicalType]) -> Result<()> {
    if names.len() != expected.len() {
        return Err(err(ErrorCode::Signature, "operand arity"));
    }
    for (name, expected) in names.iter().zip(expected) {
        let ty = lookup(env, name)?;
        if ty != *expected {
            return Err(err(ErrorCode::Signature, format!("operand type {name}")));
        }
        if ty.is_affine() {
            env.get_mut(name).expect("looked up").available = false;
        }
    }
    Ok(())
}
fn results(
    env: &mut Env,
    seen: &mut BTreeSet<String>,
    names: &[String],
    expected: &[PhysicalType],
) -> Result<()> {
    if names.len() != expected.len() {
        return Err(err(ErrorCode::Signature, "result arity"));
    }
    for (name, ty) in names.iter().zip(expected) {
        define(env, seen, name, ty.clone())?;
    }
    Ok(())
}
fn environment(ports: &Ports) -> Result<(Env, BTreeSet<String>)> {
    let (mut env, mut seen) = (Env::new(), BTreeSet::new());
    for (name, ty) in ports {
        define(&mut env, &mut seen, name, ty.clone())?;
    }
    Ok((env, seen))
}
fn site(sites: &mut BTreeSet<String>, site: &str) -> Result<()> {
    if !sites.insert(site.to_owned()) {
        return Err(err(ErrorCode::Site, format!("duplicate site {site}")));
    }
    Ok(())
}
/// Operations whose natural attributes are vector sizes, positions or degrees.
const VECTOR_EXTENTS: [&str; 8] = [
    "vector.splat",
    "vector.powers",
    "vector.at",
    "vector.length_check",
    "poly.degree_check",
    "random.vector",
    "vector.gather",
    "vector.matvec",
];
fn natural_syntax(value: &str) -> Result<()> {
    if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
        return Err(err(ErrorCode::Attributes, "expected-natural"));
    }
    if !decode::canonical_decimal(value) {
        return Err(err(ErrorCode::Attributes, "noncanonical-natural"));
    }
    Ok(())
}
fn attributes(
    rule: AttributeRule,
    attrs: &[String],
    range_reason: &str,
    natural_limit: u64,
) -> Result<()> {
    // Arity first, then each natural's syntax and range in source order.
    // Do not let a later lexical fault hide an earlier range failure.
    let natural_arity = match rule {
        AttributeRule::Unsigned64 | AttributeRule::NaturalIndex => Some(attrs.len() == 1),
        AttributeRule::NaturalIndices => Some(true),
        AttributeRule::ScatterShape => Some(!attrs.is_empty()),
        AttributeRule::MatrixDimensions => Some(attrs.len() == 2),
        AttributeRule::MatrixShape => Some(attrs.len() == 3),
        _ => None,
    };
    if let Some(arity) = natural_arity {
        if !arity {
            return Err(err(ErrorCode::Attributes, range_reason));
        }
        let bound = if rule == AttributeRule::MatrixDimensions {
            natural_limit.min(65_536)
        } else {
            natural_limit
        };
        for value in attrs {
            natural_syntax(value)?;
            if !value.parse::<u64>().is_ok_and(|n| n <= bound) {
                return Err(err(ErrorCode::Attributes, range_reason));
            }
        }
        if rule == AttributeRule::MatrixShape && !matches!(attrs[2].as_str(), "0" | "1") {
            return Err(err(ErrorCode::Attributes, range_reason));
        }
        return Ok(());
    }
    match rule {
        AttributeRule::None if attrs.is_empty() => Ok(()),
        AttributeRule::Bn254Decimals
        | AttributeRule::FieldDecimals
        | AttributeRule::RistrettoDecimals
        | AttributeRule::KoalaBearDecimals => {
            let scalar = match rule {
                AttributeRule::Bn254Decimals => AttributeRule::Bn254Decimal,
                AttributeRule::RistrettoDecimals => AttributeRule::RistrettoDecimal,
                AttributeRule::KoalaBearDecimals => AttributeRule::KoalaBearDecimal,
                _ => AttributeRule::FieldDecimal,
            };
            for attr in attrs {
                attributes(
                    scalar,
                    std::slice::from_ref(attr),
                    range_reason,
                    natural_limit,
                )?;
            }
            Ok(())
        }
        AttributeRule::MatrixIdentity
            if attrs.len() == 1
                && attrs[0].len() == 64
                && attrs[0]
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) =>
        {
            Ok(())
        }
        AttributeRule::NativeMessageTemplate
            if crate::logical::native_origin_template(attrs, "message").is_ok() =>
        {
            Ok(())
        }
        AttributeRule::NativeChallengeTemplate
            if crate::logical::native_origin_template(attrs, "query").is_ok() =>
        {
            Ok(())
        }

        AttributeRule::Bn254Decimal
        | AttributeRule::FieldDecimal
        | AttributeRule::RistrettoDecimal
        | AttributeRule::KoalaBearDecimal
            if attrs.len() == 1 =>
        {
            natural_syntax(&attrs[0])?;
            // Exact installed field modulus; no modular reduction at admission.
            const MODULUS: &str =
                "52435875175126190479447740508185965837690552500527637822603658699938581184513";
            let modulus = if rule == AttributeRule::Bn254Decimal {
                "21888242871839275222246405745257275088548364400416034343698204186575808495617"
            } else if rule == AttributeRule::KoalaBearDecimal {
                "2130706433"
            } else if rule == AttributeRule::RistrettoDecimal {
                "7237005577332262213973186563042994240857116359379907606001950938285454250989"
            } else {
                MODULUS
            };
            let a = attrs[0].as_str();
            if decode::canonical_decimal(a)
                && (a.len() < modulus.len() || (a.len() == modulus.len() && a < modulus))
            {
                Ok(())
            } else {
                Err(err(
                    ErrorCode::Attributes,
                    "interactive-constant: out-of-field constant",
                ))
            }
        }
        _ => Err(err(
            ErrorCode::Attributes,
            format!("{range_reason}: exact kernel attributes required"),
        )),
    }
}
fn diagonal(ty: PhysicalType) -> bool {
    matches!(
        ty.representation(),
        Representation::FrDiagonal | Representation::RistrettoDiagonal
    )
}
fn local_boundary(inputs: &Ports, outputs: &[PhysicalType]) -> Result<()> {
    if inputs.iter().any(|(_, ty)| diagonal(ty.clone())) || outputs.iter().cloned().any(diagonal) {
        return Err(err(ErrorCode::Signature, "diagonal-escape"));
    }
    Ok(())
}
fn function(f: &Function) -> Result<()> {
    local_boundary(&f.inputs, &f.outputs)?;
    let (env, _) = environment(&f.inputs)?;
    let mut sites = BTreeSet::new();
    local_body(&f.body, env, &mut sites, false, Some(&f.outputs)).map(|_| ())
}
fn local_body(
    body: &[LocalInstruction],
    mut env: Env,
    sites: &mut BTreeSet<String>,
    nested: bool,
    expected: Option<&[PhysicalType]>,
) -> Result<Option<Vec<PhysicalType>>> {
    let mut seen = env.keys().cloned().collect();
    let mut views = BTreeMap::new();
    let mut returned = None;
    if body.is_empty() {
        return Err(err(ErrorCode::Terminal, "empty function"));
    }
    for (i, op) in body.iter().enumerate() {
        let terminal = matches!(
            op,
            LocalInstruction::Return(_)
                | LocalInstruction::Yield(_)
                | LocalInstruction::Stop { .. }
        );
        if terminal != (i + 1 == body.len()) {
            return Err(err(
                ErrorCode::Terminal,
                "local body must end at its sole terminator",
            ));
        }
        match op {
            LocalInstruction::BoolConstant {
                site: s, output, ..
            } => {
                site(sites, s)?;
                define(
                    &mut env,
                    &mut seen,
                    output,
                    PhysicalType::parse("bool@native.bool/1")?,
                )?;
            }
            LocalInstruction::Stop { site: s, .. } => {
                site(sites, s)?;
                returned = Some(None);
            }
            LocalInstruction::Variant {
                site: s,
                ty,
                alternative,
                payload,
                output,
            } => {
                site(sites, s)?;
                let logical = ty.logical();
                let descriptor = logical
                    .variant_descriptor()
                    .ok_or_else(|| err(ErrorCode::Type, "variant-constructor-type"))?;
                let arm = descriptor
                    .alternatives()
                    .iter()
                    .find(|a| a.label() == alternative)
                    .ok_or_else(|| err(ErrorCode::Signature, "variant-alternative"))?;
                let types = arm
                    .payload()
                    .iter()
                    .cloned()
                    .map(PhysicalType::default_for)
                    .collect::<Result<Vec<_>>>()?;
                operands(&mut env, payload, &types)?;
                define(&mut env, &mut seen, output, ty.clone())?;
            }
            LocalInstruction::Match {
                site: s,
                input,
                captures,
                arms,
                outputs,
            } => {
                site(sites, s)?;
                let ty = lookup(&env, input)?;
                let logical = ty.logical();
                let descriptor = logical
                    .variant_descriptor()
                    .ok_or_else(|| err(ErrorCode::Type, "match-scrutinee"))?;
                if arms.len() != descriptor.alternatives().len() {
                    return Err(err(ErrorCode::Signature, "match-exhaustive"));
                }
                operands(
                    &mut env,
                    std::slice::from_ref(input),
                    std::slice::from_ref(&ty),
                )?;
                let mut capture_ports = Vec::new();
                for name in captures {
                    let ty = lookup(&env, name)?;
                    if diagonal(ty.clone()) {
                        return Err(err(ErrorCode::Signature, "diagonal-escape"));
                    }
                    operands(
                        &mut env,
                        std::slice::from_ref(name),
                        std::slice::from_ref(&ty),
                    )?;
                    capture_ports.push((name.clone(), ty));
                }
                let mut joined = None;
                for (arm, declared) in arms.iter().zip(descriptor.alternatives()) {
                    // The contract decides this, not the attribute rule: the
                    // external duplex states are ordinary checked data and carry
                    // no origin attribute, yet they hold the same history.
                    if LocalInstruction::walk(&arm.body).iter().any(|op| matches!(op, LocalInstruction::Op { binding, .. } if binding.observes_history())) {
                        return Err(err(ErrorCode::Signature, "match-protocol-effect"));
                    }
                    if arm.alternative != declared.label()
                        || arm.payload.len() != declared.payload().len()
                    {
                        return Err(err(ErrorCode::Signature, "match-alternative"));
                    }
                    let mut ports = arm
                        .payload
                        .iter()
                        .cloned()
                        .zip(
                            declared
                                .payload()
                                .iter()
                                .cloned()
                                .map(PhysicalType::default_for)
                                .collect::<Result<Vec<_>>>()?,
                        )
                        .collect::<Ports>();
                    ports.extend(capture_ports.clone());
                    let (child, _) = environment(&ports)?;
                    if let Some(types) = local_body(&arm.body, child, sites, true, None)? {
                        if joined.as_ref().is_some_and(|previous| previous != &types) {
                            return Err(err(ErrorCode::Signature, "local-match-yield"));
                        }
                        joined = Some(types);
                    }
                }
                if joined.is_none() && !outputs.is_empty() {
                    return Err(err(ErrorCode::Signature, "local-terminal-outputs"));
                }
                results(&mut env, &mut seen, outputs, &joined.unwrap_or_default())?;
            }
            LocalInstruction::Conditional {
                site: s,
                condition,
                captures,
                then_body,
                else_body,
                outputs,
            } => {
                site(sites, s)?;
                if lookup(&env, condition)?.kind() != Type::Bool {
                    return Err(err(ErrorCode::Signature, "local condition must be bool"));
                }
                let mut child = Env::new();
                let mut child_seen = BTreeSet::new();
                for name in captures {
                    let ty = lookup(&env, name)?;
                    if diagonal(ty.clone()) {
                        return Err(err(ErrorCode::Signature, "diagonal-escape"));
                    }
                    define(&mut child, &mut child_seen, name, ty.clone())?;
                    operands(&mut env, std::slice::from_ref(name), &[ty])?;
                }
                let left = local_body(then_body, child.clone(), sites, true, None)?;
                let right = local_body(else_body, child, sites, true, None)?;
                if let (Some(left), Some(right)) = (&left, &right)
                    && left != right
                {
                    return Err(err(ErrorCode::Signature, "local-if-yield"));
                }
                let joined = left.or(right);
                if joined.is_none() && !outputs.is_empty() {
                    return Err(err(ErrorCode::Signature, "local-terminal-outputs"));
                }
                let types = joined.unwrap_or_default();
                results(&mut env, &mut seen, outputs, &types)?;
            }
            LocalInstruction::For {
                conditional,
                site: s,
                induction,
                lower,
                upper,
                carried,
                captures,
                body,
                outputs,
            } => {
                site(sites, s)?;
                for bound in [lower, upper] {
                    if lookup(&env, bound)?.kind() != Type::Index {
                        return Err(err(ErrorCode::Signature, "local bound must be index"));
                    }
                }
                let types = carried
                    .iter()
                    .map(|(_, n)| lookup(&env, n))
                    .collect::<Result<Vec<_>>>()?;
                if types.iter().cloned().any(diagonal) {
                    return Err(err(ErrorCode::Signature, "diagonal-escape"));
                }
                let mut ports = vec![(
                    induction.clone(),
                    PhysicalType::parse("index@native.index/1")?,
                )];
                ports.extend(
                    carried
                        .iter()
                        .zip(&types)
                        .map(|((n, _), ty)| (n.clone(), ty.clone())),
                );
                let (mut child, mut child_seen) = environment(&ports)?;
                operands(
                    &mut env,
                    &carried.iter().map(|p| p.1.clone()).collect::<Vec<_>>(),
                    &types,
                )?;
                for name in captures {
                    let ty = lookup(&env, name)?;
                    if !ty.is_duplicable() {
                        return Err(err(ErrorCode::Capture, "affine local loop capture"));
                    }
                    if diagonal(ty.clone()) {
                        return Err(err(ErrorCode::Signature, "diagonal-escape"));
                    }
                    define(&mut child, &mut child_seen, name, ty.clone())?;
                }
                let mut yielded = types.clone();
                if *conditional {
                    if !matches!(body.last(), Some(LocalInstruction::Yield(_))) {
                        return Err(err(ErrorCode::Record, "local-control-yield"));
                    }
                    yielded.insert(0, PhysicalType::parse("bool@native.bool/1")?);
                }
                local_body(body, child, sites, true, Some(&yielded))?;
                results(&mut env, &mut seen, outputs, &types)?;
            }
            LocalInstruction::Op {
                site: s,
                binding,
                attributes: a,
                inputs,
                outputs,
            } => {
                site(sites, s)?;
                let sig = binding.signature();
                let range_reason = if binding.declaration().contract == "curve.at" && a.len() == 1 {
                    "interactive-index"
                } else {
                    "interactive-kernel-parameters"
                };
                let contract = binding.declaration().contract.as_str();
                let natural_limit = if contract == "curve.at" || VECTOR_EXTENTS.contains(&contract)
                {
                    1_048_576
                } else {
                    u64::MAX
                };
                attributes(sig.attributes, a, range_reason, natural_limit)?;
                operands(&mut env, inputs, &sig.inputs).map_err(|error| {
                    if error.code == ErrorCode::Signature {
                        err(
                            error.code,
                            format!("binding-operation-signature: {}", error.detail),
                        )
                    } else {
                        error
                    }
                })?;
                for (index, name) in inputs.iter().enumerate() {
                    if let Some((consumer, used)) = views.get_mut(name) {
                        if index != 1 || binding.implementation() != *consumer {
                            return Err(err(ErrorCode::Signature, "diagonal-use"));
                        }
                        *used = true;
                    }
                }
                results(&mut env, &mut seen, outputs, &sig.outputs)?;
                for (name, ty) in outputs.iter().zip(&sig.outputs) {
                    let (producer, consumer) = match ty.representation() {
                        Representation::FrDiagonal => (
                            "arkworks-diagonal/vector.mul",
                            "arkworks-diagonal/vector.dot",
                        ),
                        Representation::RistrettoDiagonal => (
                            "dalek-diagonal/curve.scale_each",
                            "dalek-diagonal/curve.msm",
                        ),
                        _ => continue,
                    };
                    if binding.implementation() != producer
                        || sig.inputs.iter().cloned().any(diagonal)
                    {
                        return Err(err(ErrorCode::Signature, "diagonal-producer"));
                    }
                    views.insert(name.clone(), (consumer, false));
                }
                if i + 1 == body.len() {
                    return Err(err(ErrorCode::Terminal, "function missing return"));
                }
            }
            LocalInstruction::Release(names) => {
                if names.is_empty() {
                    return Err(err(ErrorCode::Record, "release-empty"));
                }
                for name in names {
                    let ty = lookup(&env, name)?;
                    // Internal immutable views have no wire codec, but retain
                    // ordinary storage. Resource exclusion is a logical-kind
                    // property, independently of the physical representation.
                    if !ty.is_discardable() {
                        return Err(err(ErrorCode::Type, "release-resource"));
                    }
                    env.get_mut(name).expect("looked up").available = false;
                }
                if i + 1 == body.len() {
                    return Err(err(ErrorCode::Terminal, "function missing return"));
                }
            }
            LocalInstruction::Return(names) | LocalInstruction::Yield(names) => {
                if matches!(op, LocalInstruction::Yield(_)) != nested {
                    return Err(err(
                        ErrorCode::Terminal,
                        "local-terminal-context: return/yield in wrong local region",
                    ));
                }
                let types = names
                    .iter()
                    .map(|n| lookup(&env, n))
                    .collect::<Result<Vec<_>>>()?;
                if types.iter().cloned().any(diagonal) {
                    return Err(err(ErrorCode::Signature, "diagonal-escape"));
                }
                operands(&mut env, names, expected.unwrap_or(&types)).map_err(|error| {
                    if error.code == ErrorCode::Signature {
                        let reason = if nested {
                            "local-yield-types"
                        } else {
                            "function-return-types"
                        };
                        err(error.code, format!("{reason}: {}", error.detail))
                    } else {
                        error
                    }
                })?;
                returned = Some(Some(types));
            }
        }
    }
    if views.values().any(|(_, used)| !used) {
        return Err(err(ErrorCode::Signature, "diagonal-unused"));
    }
    returned.ok_or_else(|| err(ErrorCode::Terminal, "missing local terminator"))
}
struct Check<'a> {
    program: &'a Program,
    role: &'a str,
    instance: &'a str,
    entry_outputs: &'a [PhysicalType],
    sites: BTreeSet<String>,
    services: &'a [super::ServicePort],
    seen: BTreeSet<String>,
    schemas: &'a mut BTreeMap<(String, String), PhysicalType>,
}
impl Check<'_> {
    fn message(&mut self, schema: &str, peer: &str, ty: PhysicalType) -> Result<()> {
        if peer == self.role {
            return Err(err(ErrorCode::Role, "self message"));
        }
        if !ty.is_message_type() {
            return Err(err(ErrorCode::Type, "nonserializable message type"));
        }
        if let Some(old) = self
            .schemas
            .insert((self.instance.to_owned(), schema.to_owned()), ty.clone())
            && old != ty
        {
            return Err(err(
                ErrorCode::Signature,
                "schema used with inconsistent types",
            ));
        }
        Ok(())
    }
    fn body(
        &mut self,
        body: &Body,
        mut env: Env,
        expected: &[PhysicalType],
        in_loop: bool,
    ) -> Result<()> {
        if body.is_empty() {
            return Err(err(ErrorCode::Terminal, "empty body"));
        }
        for (i, instruction) in body.iter().enumerate() {
            let terminal = matches!(instruction, Instruction::Return(_) | Instruction::Yield(_));
            if terminal != (i + 1 == body.len()) {
                return Err(err(
                    ErrorCode::Terminal,
                    "body must end at its sole terminator",
                ));
            }
            match instruction {
                Instruction::Query {
                    site: s,
                    port,
                    method,
                    inputs,
                    outputs,
                } => {
                    site(&mut self.sites, s)?;
                    let port = self
                        .services
                        .iter()
                        .find(|p| &p.name == port)
                        .ok_or_else(|| err(ErrorCode::Symbol, "unknown service port"))?;
                    let signature = port
                        .contract
                        .signature(method)
                        .ok_or_else(|| err(ErrorCode::Type, "unsupported service method"))?;
                    operands(&mut env, inputs, &signature.inputs)?;
                    results(&mut env, &mut self.seen, outputs, &signature.outputs)?;
                }
                Instruction::Local {
                    site: s,
                    function,
                    inputs,
                    outputs,
                } => {
                    site(&mut self.sites, s)?;
                    let f = self
                        .program
                        .functions
                        .get(function)
                        .ok_or_else(|| err(ErrorCode::Symbol, "unresolved local function"))?;
                    operands(
                        &mut env,
                        inputs,
                        &f.inputs.iter().map(|p| p.1.clone()).collect::<Vec<_>>(),
                    )?;
                    results(&mut env, &mut self.seen, outputs, &f.outputs)?;
                }
                Instruction::Send {
                    site: s,
                    schema,
                    peer,
                    input,
                } => {
                    site(&mut self.sites, s)?;
                    self.message(schema, peer, lookup(&env, input)?)?;
                }
                Instruction::Receive {
                    site: s,
                    schema,
                    peer,
                    output,
                    ty,
                } => {
                    site(&mut self.sites, s)?;
                    self.message(schema, peer, ty.clone())?;
                    define(&mut env, &mut self.seen, output, ty.clone())?;
                }
                Instruction::Loop {
                    site: s,
                    count,
                    carried,
                    captures,
                    body,
                    outputs,
                } => {
                    site(&mut self.sites, s)?;
                    if count.maximum > Limits::LOOP_COUNT {
                        return Err(err(ErrorCode::Record, "interactive-loop-count"));
                    }
                    let induction_type = lookup(&env, &count.value)?;
                    if induction_type != PhysicalType::parse("index@native.index/1")? {
                        return Err(err(ErrorCode::Type, "interactive-loop-count"));
                    }
                    let types = carried
                        .iter()
                        .map(|p| lookup(&env, &p.1))
                        .collect::<Result<Vec<_>>>()?;
                    operands(
                        &mut env,
                        &carried.iter().map(|p| p.1.clone()).collect::<Vec<_>>(),
                        &types,
                    )?;
                    let mut child = Env::new();
                    define(&mut child, &mut self.seen, &count.induction, induction_type)?;
                    for ((arg, _), ty) in carried.iter().zip(&types) {
                        define(&mut child, &mut self.seen, arg, ty.clone())?;
                    }
                    for capture in captures {
                        let ty = lookup(&env, capture)?;
                        if !ty.is_duplicable() {
                            return Err(err(
                                ErrorCode::Capture,
                                "affine values must be loop-carried, not invariant captures",
                            ));
                        }
                        if child
                            .insert(
                                capture.clone(),
                                Binding {
                                    ty,
                                    available: true,
                                },
                            )
                            .is_some()
                        {
                            return Err(err(ErrorCode::Capture, "duplicate/overlapping capture"));
                        }
                    }
                    self.body(body, child, &types, true)?;
                    results(&mut env, &mut self.seen, outputs, &types)?;
                }
                Instruction::ReturnIf {
                    site: s,
                    condition,
                    values,
                    continuations,
                } => {
                    site(&mut self.sites, s)?;
                    operands(
                        &mut env,
                        std::slice::from_ref(condition),
                        &[PhysicalType::parse("bool@native.bool/1")?],
                    )?;
                    operands(&mut env, values, self.entry_outputs)?;
                    let types: Vec<_> = self
                        .entry_outputs
                        .iter()
                        .filter(|ty| ty.is_affine())
                        .cloned()
                        .collect();
                    results(&mut env, &mut self.seen, continuations, &types)?;
                }
                Instruction::Return(names) if !in_loop => operands(&mut env, names, expected)?,
                Instruction::Yield(names) if in_loop => operands(&mut env, names, expected)?,
                _ => return Err(err(ErrorCode::Terminal, "return/yield in wrong region")),
            }
        }
        Ok(())
    }
}
fn validate(p: &Program) -> Result<()> {
    for f in p.functions.values() {
        function(f)?;
    }
    let mut identities = BTreeSet::new();
    let mut schemas = BTreeMap::new();
    for participant in p.participants.values() {
        local_boundary(&participant.inputs, &participant.outputs)?;
        if p.functions.contains_key(&participant.symbol)
            || p.entries.contains_key(&participant.symbol)
        {
            return Err(err(ErrorCode::Symbol, "symbol namespace collision"));
        }
        if !identities.insert((&participant.instance, &participant.role)) {
            return Err(err(ErrorCode::Symbol, "duplicate body for instance/role"));
        }
        if participant
            .inputs
            .iter()
            .map(|(_, ty)| ty)
            .chain(&participant.outputs)
            .any(|ty| !ty.logical().is_program_port())
        {
            return Err(err(ErrorCode::Type, "variant-participant-boundary"));
        }
        if participant.inputs.len() + participant.services.len() > Limits::PORTS {
            return Err(err(ErrorCode::Limit, "interactive-port-limit"));
        }
        let (env, mut seen) = environment(&participant.inputs)?;
        let mut indices = BTreeSet::new();
        for port in &participant.services {
            if !seen.insert(port.name.clone())
                || !indices.insert(port.input_index)
                || port.input_index >= participant.inputs.len() + participant.services.len()
            {
                return Err(err(ErrorCode::Type, "service-port-interface"));
            }
        }
        Check {
            program: p,
            role: &participant.role,
            instance: &participant.instance,
            entry_outputs: &participant.outputs,
            services: &participant.services,
            sites: BTreeSet::new(),
            seen,
            schemas: &mut schemas,
        }
        .body(&participant.body, env, &participant.outputs, false)?;
    }
    for (name, roles) in &p.entries {
        if p.functions.contains_key(name) {
            return Err(err(ErrorCode::Symbol, "entry/function namespace collision"));
        }
        let mut instance = None;
        for (role, symbol) in roles {
            let body = p
                .participants
                .get(symbol)
                .ok_or_else(|| err(ErrorCode::Symbol, "entry unresolved participant"))?;
            if &body.role != role {
                return Err(err(ErrorCode::Role, "entry role mismatch"));
            }
            if instance.is_some_and(|i| i != &body.instance) {
                return Err(err(
                    ErrorCode::Role,
                    "entry roles select different instances",
                ));
            }
            instance = Some(&body.instance);
        }
    }
    Ok(())
}
