//! Native installation of authenticated row access. A root authenticates a
//! rectangular vector; authored mathematical programs define polynomial meaning
//! and query scheduling.
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use std::sync::Arc;
use zkc_kernels::plonky3::{
    oracle as tree,
    oracle::{Digest, Error, Shape},
};
use zkc_runtime::vm::{
    AttributeRule, Backing, BoundSignature, Identity, Invocation, LogicalType, OperationBinding,
    OperationSignature, PhysicalType, Type,
};

// Each nominal Keccak carrier uses the same typed tree and resource policy.
macro_rules! domains {
    ($($domain:ident => ($identity:ident, $field:ident, $element:ty, $vector:ident, $root:literal, $path:literal)),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Domain { $($domain),+ }
        impl Domain {
            pub fn identity(self) -> Identity {
                match self { $(Self::$domain => Identity::$identity),+ }
            }
            pub(crate) fn from_identity(identity: Identity) -> Option<Self> {
                match identity { $(Identity::$identity => Some(Self::$domain),)+ _ => None }
            }
            fn field(self) -> Identity {
                match self { $(Self::$domain => Identity::$field),+ }
            }
            pub(crate) fn tag(self, kind: Type) -> Option<u8> {
                match (self, kind) {
                    $((Self::$domain, Type::Commitment) => Some($root),
                      (Self::$domain, Type::Proof) => Some($path),)+
                    _ => None,
                }
            }
        }
        #[derive(Clone, Debug)]
        pub enum State { $($domain(Arc<tree::State<$element>>)),+ }
        impl State {
            pub fn domain(&self) -> Domain {
                match self { $(Self::$domain(_) => Domain::$domain),+ }
            }
            pub fn retained_bytes(&self) -> Result<usize> {
                match self { $(Self::$domain(s) => s.shape().retained_bytes::<$element>()),+ }
                    .map_err(failure)
            }
            /// The committed table and tree, shared by every handle to this state.
            pub(crate) fn backing(&self) -> Result<Backing> {
                let bytes = self.retained_bytes()?;
                Ok(match self { $(Self::$domain(s) => Backing::of(s, bytes)),+ })
            }
            /// Bytes one opening reads: the selected row and its authentication path.
            pub(crate) fn opening_bytes(&self) -> Result<usize> {
                let (shape, element) = match self {
                    $(Self::$domain(s) => (s.shape(), std::mem::size_of::<$element>())),+
                };
                size(shape.width(), element)?
                    .checked_add(size(shape.depth(), 32)?)
                    .ok_or_else(|| exhausted("size-overflow"))
            }
        }
        fn commit_state(domain: Domain, values: &Value, width: usize, policy: &Policy, available: usize) -> Result<Vec<Value>> {
            match (domain, values) {
                $((Domain::$domain, Value::$vector(values)) => {
                    let shape = shape(width, values.len(), policy)?;
                    let bytes = shape.retained_bytes::<$element>().map_err(failure)?;
                    policy.output(bytes.checked_add(512).ok_or_else(|| exhausted("size-overflow"))?, available)?;
                    let (root, state) = tree::commit(values.to_vec(), shape, policy.max_value_bytes).map_err(failure)?;
                    Ok(vec![Value::OracleRoot(domain, root), Value::OracleState(State::$domain(Arc::new(state)))])
                },)+
                _ => Err(refused("oracle-operands")),
            }
        }
        fn open_state(state: &State, at: usize, policy: &Policy, available: usize) -> Result<Vec<Value>> {
            policy.output(state.opening_bytes()?, available)?;
            Ok(match state {
                $(State::$domain(s) => {
                    let (row, path) = s.open(at).map_err(failure)?;
                    vec![Value::$vector(row.into()), Value::OraclePath(state.domain(), path.into())]
                }),+
            })
        }
        #[allow(clippy::too_many_arguments)]
        fn check_row(domain: Domain, root: Digest, width: usize, height: usize, at: usize, row: &Value, path: &[Digest], policy: &Policy) -> Result<bool> {
            match (domain, row) {
                $((Domain::$domain, Value::$vector(row)) => check(root, width, height, at, row, path, policy),)+
                _ => Err(refused("oracle-operands")),
            }
        }
    };
}
domains! {
    Base => (MerkleKoalaBear, KoalaBear, crate::KoalaBear, KoalaBearVector, 33, 34),
    Extension => (MerkleKoalaBearExt8, KoalaBearExt8, crate::KoalaBearExt8, KoalaBearExt8Vector, 35, 36),
    Quartic => (MerkleKoalaBearExt4, KoalaBearExt4, crate::KoalaBearExt4, KoalaBearExt4Vector, 79, 80),
}
impl Domain {
    fn physical(self, kind: Type) -> Option<PhysicalType> {
        let identity = match kind {
            Type::Index | Type::Bool => Identity::None,
            Type::Vector => self.field(),
            _ => self.identity(),
        };
        PhysicalType::default_for(LogicalType::new(kind, identity).ok()?).ok()
    }
}

fn failure(error: Error) -> zkc_runtime::vm::BackendError {
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
    let identity = Identity::parse(&binding.arguments[0]).ok()?;
    // Digest-generic schemes share these contracts and own their carriers.
    if crate::merkle::Scheme::from_identity(identity).is_some() {
        return crate::merkle::signature(binding);
    }
    let domain = Domain::from_identity(identity)?;
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
    Some(OperationSignature {
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
/// The list's handle slots, which hold no table data.
pub(crate) fn states_list(states: &Arc<[State]>) -> Result<Backing> {
    Ok(Backing::of(
        states,
        size(states.len(), std::mem::size_of::<State>())?,
    ))
}
/// Report the list and, when it is newly retained, each distinct opening state.
pub(crate) fn states_parts(
    states: &Arc<[State]>,
    shared: &mut dyn FnMut(Backing) -> bool,
) -> Result<usize> {
    if shared(states_list(states)?) {
        for state in states.iter() {
            shared(state.backing()?);
        }
    }
    Ok(0)
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    invocation: &Invocation<'_>,
    policy: &Policy,
) -> Result<Vec<Value>> {
    if !name.starts_with("oracle.")
        && !name.starts_with("commitments.")
        && !name.starts_with("opening_states.")
    {
        return Err(refused("kernel-operands"));
    }
    let identity = invocation
        .binding
        .declaration()
        .arguments
        .first()
        .and_then(|s| Identity::parse(s).ok());
    if identity
        .and_then(crate::merkle::Scheme::from_identity)
        .is_some()
    {
        return crate::merkle::apply(name, args, invocation, policy);
    }
    let domain = identity
        .and_then(Domain::from_identity)
        .ok_or_else(|| refused("oracle-domain"))?;
    let available = invocation.max_output_bytes;
    let outputs = match (name, args) {
        ("oracle.commit", [values, width]) => {
            commit_state(domain, values, index(width)?, policy, available)?
        }
        ("oracle.open", [Value::OracleState(state), at]) if state.domain() == domain => {
            open_state(state, index(at)?, policy, available)?
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
            let valid = check_row(domain, *root, width, height, at, row, path, policy)?;
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
            let mut result = crate::operations::arithmetic::reserve(len)?;
            result.extend_from_slice(roots);
            result.push(*root);
            vec![Value::OracleRoots(domain, result.into())]
        }
        ("opening_states.append", [Value::OracleStates(d, states), Value::OracleState(state)])
            if *d == domain && state.domain() == domain =>
        {
            let len = states
                .len()
                .checked_add(1)
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.vector_width(len, std::mem::size_of::<State>())?;
            let bytes = states_bytes(states)?
                .checked_add(state.retained_bytes()?)
                .and_then(|n| n.checked_add(std::mem::size_of::<State>()))
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.output(bytes, usize::MAX)?;
            // Existing states are shared; only the new list of handles is allocated.
            policy.output(size(len, std::mem::size_of::<State>())?, available)?;
            let mut result = crate::operations::arithmetic::reserve(len)?;
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
            // The result shares the selected state; nothing new is allocated.
            policy.output(state.retained_bytes()?, usize::MAX)?;
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
}

pub(crate) fn encode(value: &Value, policy: &Policy) -> Option<Result<Vec<u8>>> {
    let (domain, kind, hashes): (_, _, &[Digest]) = match value {
        Value::OracleRoot(d, root) => (*d, Type::Commitment, std::slice::from_ref(root)),
        Value::OraclePath(d, path) => (*d, Type::Proof, path),
        _ => return None,
    };
    Some((|| {
        validate_hash_count(kind, hashes.len(), policy)?;
        let prefix = if kind == Type::Commitment { 6 } else { 10 };
        let bytes = hashes
            .len()
            .checked_mul(32)
            .and_then(|n| n.checked_add(prefix))
            .ok_or_else(|| exhausted("wire-bytes"))?;
        policy.wire(bytes)?;
        let mut out = crate::operations::arithmetic::reserve(bytes)?;
        out.extend_from_slice(b"ZKCV\x00");
        out.push(domain.tag(kind).expect("public oracle kind"));
        if kind != Type::Commitment {
            out.extend((hashes.len() as u32).to_le_bytes());
        }
        for hash in hashes {
            out.extend_from_slice(hash);
        }
        Ok(out)
    })())
}
pub(crate) fn validate_hash_count(kind: Type, count: usize, policy: &Policy) -> Result<()> {
    if kind == Type::Proof && count > 24 {
        return Err(refused("oracle-path-length"));
    }
    policy.vector_width(count, 32)
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("plonky3/oracle.commit", "oracle.commit"),
    ("plonky3/oracle.open", "oracle.open"),
    ("plonky3/oracle.check", "oracle.check"),
    ("plonky3/commitments.empty", "commitments.empty"),
    ("plonky3/commitments.append", "commitments.append"),
    ("plonky3/commitments.at", "commitments.at"),
    ("plonky3/commitments.length", "commitments.length"),
    ("plonky3/opening_states.empty", "opening_states.empty"),
    ("plonky3/opening_states.append", "opening_states.append"),
    ("plonky3/opening_states.at", "opening_states.at"),
    ("plonky3/opening_states.length", "opening_states.length"),
];
