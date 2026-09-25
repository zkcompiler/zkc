//! Native installation of authenticated row access. A root authenticates a
//! rectangular vector; polynomial meaning and query scheduling belong to PIR.
use crate::plonky3::oracle::{self as tree, Digest, Error, Shape};
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use std::sync::Arc;
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, Invocation, KernelSignature, LogicalType,
    OperationBinding, PhysicalType, Type,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Domain {
    Base,
    Extension,
}
impl Domain {
    pub fn identity(self) -> Identity {
        match self {
            Self::Base => Identity::MerkleKoalaBear,
            Self::Extension => Identity::MerkleKoalaBearExt8,
        }
    }
    fn from_identity(identity: Identity) -> Option<Self> {
        match identity {
            Identity::MerkleKoalaBear => Some(Self::Base),
            Identity::MerkleKoalaBearExt8 => Some(Self::Extension),
            _ => None,
        }
    }
    fn field(self) -> Identity {
        match self {
            Self::Base => Identity::KoalaBear,
            Self::Extension => Identity::KoalaBearExt8,
        }
    }
    fn physical(self, kind: Type) -> Option<PhysicalType> {
        let identity = match kind {
            Type::Index | Type::Bool => Identity::None,
            Type::Vector => self.field(),
            _ => self.identity(),
        };
        Some(PhysicalType::default_for(
            LogicalType::new(kind, identity).ok()?,
        ))
    }
}

#[derive(Clone, Debug)]
pub enum State {
    Base(Arc<tree::State<crate::KoalaBear>>),
    Extension(Arc<tree::State<crate::KoalaBearExt8>>),
}
impl State {
    pub fn domain(&self) -> Domain {
        match self {
            Self::Base(_) => Domain::Base,
            Self::Extension(_) => Domain::Extension,
        }
    }
    pub fn retained_bytes(&self) -> Result<usize> {
        match self {
            Self::Base(s) => s.shape().retained_bytes::<crate::KoalaBear>(),
            Self::Extension(s) => s.shape().retained_bytes::<crate::KoalaBearExt8>(),
        }
        .map_err(failure)
    }
}

fn failure(error: Error) -> zkc_runtime::interactive::BackendError {
    match error {
        Error::ElementLimit => exhausted("oracle-element-limit"),
        Error::ByteLimit => exhausted("oracle-byte-limit"),
        _ => refused(match error {
            Error::Shape => "oracle-shape",
            Error::ValueCount => "oracle-value-count",
            Error::Coordinate => "oracle-coordinate",
            Error::RowWidth => "oracle-row-width",
            Error::PathLength => "oracle-path-length",
            Error::Authentication => "oracle-authentication",
            _ => unreachable!(),
        }),
    }
}

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use Type::*;
    if binding.arguments.len() != 1
        || binding.implementation != format!("plonky3/{}", binding.contract)
    {
        return None;
    }
    let domain = Domain::from_identity(Identity::parse(&binding.arguments[0]).ok()?)?;
    // Independent native advertisement, not admission's operation-shape table.
    let (inputs, outputs): (&[Type], &[Type]) = match binding.contract.as_str() {
        "oracle.commit" => (&[Vector, Index], &[Commitment, OpeningState]),
        "oracle.open" => (&[OpeningState, Index], &[Vector, Proof]),
        "oracle.check" => (&[Commitment, Index, Index, Index, Vector, Proof], &[Bool]),
        "commitments.empty" => (&[], &[Commitments]),
        "commitments.append" => (&[Commitments, Commitment], &[Commitments]),
        "commitments.at" => (&[Commitments, Index], &[Commitment]),
        "commitments.length" => (&[Commitments], &[Index]),
        "opening_states.empty" => (&[], &[OpeningStates]),
        "opening_states.append" => (&[OpeningStates, OpeningState], &[OpeningStates]),
        "opening_states.at" => (&[OpeningStates, Index], &[OpeningState]),
        "opening_states.length" => (&[OpeningStates], &[Index]),
        _ => return None,
    };
    Some(KernelSignature {
        inputs: inputs
            .iter()
            .map(|t| domain.physical(*t))
            .collect::<Option<_>>()?,
        outputs: outputs
            .iter()
            .map(|t| domain.physical(*t))
            .collect::<Option<_>>()?,
        attributes: AttributeRule::None,
    })
}

fn index(v: &Value) -> Result<usize> {
    if let Value::Index(n) = v {
        usize::try_from(*n).map_err(|_| refused("oracle-coordinate"))
    } else {
        Err(refused("oracle-operands"))
    }
}
fn shape(width: usize, count: usize, policy: &Policy) -> Result<Shape> {
    if width == 0 || !count.is_multiple_of(width) {
        return Err(refused("oracle-shape"));
    }
    Shape::new(width, count / width, policy.max_table_elements.min(1 << 20)).map_err(failure)
}
fn check<E: tree::Element>(
    root: Digest,
    width: usize,
    height: usize,
    at: usize,
    row: &[E],
    path: &[Digest],
    policy: &Policy,
) -> Result<bool> {
    let shape =
        Shape::new(width, height, policy.max_table_elements.min(1 << 20)).map_err(failure)?;
    // Expected shape/coordinate errors are invalid verifier calls. A malformed or
    // false opening returns false, so the authored verifier must guard the result.
    if at >= height {
        return Err(refused("oracle-coordinate"));
    }
    Ok(tree::verify(root, shape, at, row, path).is_ok())
}

pub(crate) fn states_bytes(states: &[State]) -> Result<usize> {
    states.iter().try_fold(
        size(states.len(), std::mem::size_of::<State>())?,
        |sum, state| {
            sum.checked_add(state.retained_bytes()?)
                .ok_or_else(|| exhausted("size-overflow"))
        },
    )
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    invocation: &Invocation<'_>,
    policy: &Policy,
) -> Option<Result<Vec<Value>>> {
    if !name.starts_with("oracle.")
        && !name.starts_with("commitments.")
        && !name.starts_with("opening_states.")
    {
        return None;
    }
    Some((|| {
        let domain = invocation
            .binding
            .declaration()
            .arguments
            .first()
            .and_then(|s| Identity::parse(s).ok())
            .and_then(Domain::from_identity)
            .ok_or_else(|| refused("oracle-domain"))?;
        let available = invocation.max_output_bytes;
        let outputs = match (name, args) {
            ("oracle.commit", [Value::KoalaBearVector(values), width])
                if domain == Domain::Base =>
            {
                let s = shape(index(width)?, values.len(), policy)?;
                let bytes = s.retained_bytes::<crate::KoalaBear>().map_err(failure)?;
                policy.output(
                    bytes
                        .checked_add(512)
                        .ok_or_else(|| exhausted("size-overflow"))?,
                    available,
                )?;
                let (root, state) =
                    tree::commit(values.to_vec(), s, policy.max_value_bytes).map_err(failure)?;
                vec![
                    Value::OracleRoot(domain, root),
                    Value::OracleState(State::Base(Arc::new(state))),
                ]
            }
            ("oracle.commit", [Value::KoalaBearExt8Vector(values), width])
                if domain == Domain::Extension =>
            {
                let s = shape(index(width)?, values.len(), policy)?;
                let bytes = s
                    .retained_bytes::<crate::KoalaBearExt8>()
                    .map_err(failure)?;
                policy.output(
                    bytes
                        .checked_add(512)
                        .ok_or_else(|| exhausted("size-overflow"))?,
                    available,
                )?;
                let (root, state) =
                    tree::commit(values.to_vec(), s, policy.max_value_bytes).map_err(failure)?;
                vec![
                    Value::OracleRoot(domain, root),
                    Value::OracleState(State::Extension(Arc::new(state))),
                ]
            }
            ("oracle.open", [Value::OracleState(state), at]) if state.domain() == domain => {
                let at = index(at)?;
                match state {
                    State::Base(s) => {
                        policy.output(
                            size(s.shape().width(), 4)?
                                .checked_add(size(s.shape().depth(), 32)?)
                                .ok_or_else(|| exhausted("size-overflow"))?,
                            available,
                        )?;
                        let (row, path) = s.open(at).map_err(failure)?;
                        vec![
                            Value::KoalaBearVector(row.into()),
                            Value::OraclePath(domain, path.into()),
                        ]
                    }
                    State::Extension(s) => {
                        policy.output(
                            size(s.shape().width(), 32)?
                                .checked_add(size(s.shape().depth(), 32)?)
                                .ok_or_else(|| exhausted("size-overflow"))?,
                            available,
                        )?;
                        let (row, path) = s.open(at).map_err(failure)?;
                        vec![
                            Value::KoalaBearExt8Vector(row.into()),
                            Value::OraclePath(domain, path.into()),
                        ]
                    }
                }
            }
            (
                "oracle.check",
                [
                    Value::OracleRoot(d, root),
                    width,
                    height,
                    at,
                    row,
                    Value::OraclePath(p, path),
                ],
            ) if *d == domain && *p == domain => {
                policy.output(512, available)?;
                let (width, height, at) = (index(width)?, index(height)?, index(at)?);
                let valid = match row {
                    Value::KoalaBearVector(row) if domain == Domain::Base => {
                        check(*root, width, height, at, row, path, policy)?
                    }
                    Value::KoalaBearExt8Vector(row) if domain == Domain::Extension => {
                        check(*root, width, height, at, row, path, policy)?
                    }
                    _ => return Err(refused("oracle-operands")),
                };
                vec![Value::Bool(valid)]
            }
            ("commitments.empty", []) => {
                policy.output(256, available)?;
                vec![Value::OracleRoots(domain, Arc::from([]))]
            }
            ("opening_states.empty", []) => {
                policy.output(256, available)?;
                vec![Value::OracleStates(domain, Arc::from([]))]
            }
            ("commitments.append", [Value::OracleRoots(d, roots), Value::OracleRoot(r, root)])
                if *d == domain && *r == domain =>
            {
                let len = roots
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| exhausted("size-overflow"))?;
                policy.vector_width(len, 32)?;
                policy.output(size(len, 32)?, available)?;
                let mut result = crate::kernels::arithmetic::reserve(len)?;
                result.extend_from_slice(roots);
                result.push(*root);
                vec![Value::OracleRoots(domain, result.into())]
            }
            (
                "opening_states.append",
                [Value::OracleStates(d, states), Value::OracleState(state)],
            ) if *d == domain && state.domain() == domain => {
                let len = states
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| exhausted("size-overflow"))?;
                policy.vector_width(len, std::mem::size_of::<State>())?;
                let bytes = states_bytes(states)?
                    .checked_add(state.retained_bytes()?)
                    .and_then(|n| n.checked_add(std::mem::size_of::<State>()))
                    .ok_or_else(|| exhausted("size-overflow"))?;
                policy.output(bytes, available)?;
                let mut result = crate::kernels::arithmetic::reserve(len)?;
                result.extend_from_slice(states);
                result.push(state.clone());
                vec![Value::OracleStates(domain, result.into())]
            }
            ("commitments.at", [Value::OracleRoots(d, roots), at]) if *d == domain => {
                policy.output(512, available)?;
                vec![Value::OracleRoot(
                    domain,
                    *roots
                        .get(index(at)?)
                        .ok_or_else(|| refused("oracle-coordinate"))?,
                )]
            }
            ("opening_states.at", [Value::OracleStates(d, states), at]) if *d == domain => {
                let state = states
                    .get(index(at)?)
                    .ok_or_else(|| refused("oracle-coordinate"))?;
                policy.output(state.retained_bytes()?, available)?;
                vec![Value::OracleState(state.clone())]
            }
            ("commitments.length", [Value::OracleRoots(d, roots)]) if *d == domain => {
                vec![Value::Index(roots.len() as u64)]
            }
            ("opening_states.length", [Value::OracleStates(d, states)]) if *d == domain => {
                vec![Value::Index(states.len() as u64)]
            }
            _ => return Err(refused("oracle-operands")),
        };
        Ok(outputs)
    })())
}

fn tag(domain: Domain, kind: Type) -> Option<u8> {
    match (domain, kind) {
        (Domain::Base, Type::Commitment) => Some(33),
        (Domain::Base, Type::Proof) => Some(34),
        (Domain::Extension, Type::Commitment) => Some(35),
        (Domain::Extension, Type::Proof) => Some(36),
        (Domain::Base, Type::Commitments) => Some(37),
        (Domain::Extension, Type::Commitments) => Some(38),
        _ => None,
    }
}
pub(crate) fn encode(value: &Value, policy: &Policy) -> Option<Result<Vec<u8>>> {
    let (domain, kind, hashes): (_, _, &[Digest]) = match value {
        Value::OracleRoot(d, root) => (*d, Type::Commitment, std::slice::from_ref(root)),
        Value::OraclePath(d, path) => (*d, Type::Proof, path),
        Value::OracleRoots(d, roots) => (*d, Type::Commitments, roots),
        _ => return None,
    };
    Some((|| {
        limits(kind, hashes.len(), policy)?;
        let prefix = if kind == Type::Commitment { 6 } else { 10 };
        let bytes = hashes
            .len()
            .checked_mul(32)
            .and_then(|n| n.checked_add(prefix))
            .ok_or_else(|| exhausted("wire-bytes"))?;
        policy.wire(bytes)?;
        let mut out = crate::kernels::arithmetic::reserve(bytes)?;
        out.extend_from_slice(b"ZKCV\x01");
        out.push(tag(domain, kind).expect("public oracle kind"));
        if kind != Type::Commitment {
            out.extend((hashes.len() as u32).to_le_bytes());
        }
        for hash in hashes {
            out.extend_from_slice(hash);
        }
        Ok(out)
    })())
}
fn limits(kind: Type, count: usize, policy: &Policy) -> Result<()> {
    if kind == Type::Proof && count > 24 {
        return Err(refused("oracle-path-length"));
    }
    policy.vector_width(count, 32)
}
pub(crate) fn decode(ty: PhysicalType, bytes: &[u8], policy: &Policy) -> Option<Result<Value>> {
    let domain = Domain::from_identity(ty.logical().identity())?;
    Some((|| {
        let kind = ty.kind();
        let tag = tag(domain, kind).ok_or_else(|| refused("nonserializable"))?;
        policy.wire(bytes.len())?;
        if bytes.get(..5) != Some(b"ZKCV\x01") || bytes.get(5) != Some(&tag) {
            return Err(refused("wire-header"));
        }
        let (count, payload) = if kind == Type::Commitment {
            (1, &bytes[6..])
        } else {
            let count = u32::from_le_bytes(
                bytes
                    .get(6..10)
                    .ok_or_else(|| refused("wire-length"))?
                    .try_into()
                    .map_err(|_| refused("wire-length"))?,
            ) as usize;
            (count, &bytes[10..])
        };
        if count.checked_mul(32) != Some(payload.len()) {
            return Err(refused("wire-length"));
        }
        limits(kind, count, policy)?;
        if kind == Type::Commitment {
            return Ok(Value::OracleRoot(
                domain,
                payload.try_into().map_err(|_| refused("wire-length"))?,
            ));
        }
        let mut hashes = crate::kernels::arithmetic::reserve(count)?;
        hashes.extend(payload.as_chunks::<32>().0.iter().copied());
        Ok(if kind == Type::Proof {
            Value::OraclePath(domain, hashes.into())
        } else {
            Value::OracleRoots(domain, hashes.into())
        })
    })())
}
