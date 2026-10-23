//! Native admission and custody for generic Merkle row commitments.
//!
//! Schemes, VM values, resource preflight and operation policy live here; typed
//! trees, hash instances and canonical digest codecs belong to `zkc_kernels`.
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use std::sync::Arc;
use zkc_kernels::plonky3::{
    merkle::{Error, Instance, Tree, commit, open, poseidon2, retained_bytes, verify},
    oracle::Shape,
};
use zkc_runtime::vm::{
    AttributeRule, Backing, BoundSignature, Identity, Invocation, LogicalType, OperationBinding,
    OperationSignature, PhysicalType, Type,
};

// This native-only positive inventory associates nominal schemes with typed
// kernels and value carriers. Compiler and VM admission remain independent.
macro_rules! instances {
    ($($scheme:ident => ($identity:ident, $field:ident, $instance:ty, $vector:ident)),+ $(,)?) => {
        /// Installed instances, each a nominal row-commitment scheme.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub enum Scheme {
            $($scheme),+
        }
        impl Scheme {
            pub fn identity(self) -> Identity {
                match self { $(Self::$scheme => Identity::$identity),+ }
            }
            pub fn from_identity(identity: Identity) -> Option<Self> {
                match identity {
                    $(Identity::$identity => Some(Self::$scheme),)+
                    _ => None,
                }
            }
            /// The committed value field.
            pub fn field(self) -> Identity {
                match self { $(Self::$scheme => Identity::$field),+ }
            }
            pub fn digest_bytes(self) -> usize {
                match self { $(Self::$scheme => <$instance as Instance>::DIGEST_BYTES),+ }
            }
            fn element_bytes(self) -> usize {
                match self {
                    $(Self::$scheme => std::mem::size_of::<<$instance as Instance>::Element>()),+
                }
            }
            /// Whether the bytes are whole digests in this scheme's canonical encoding.
            pub fn valid_digests(self, bytes: &[u8]) -> bool {
                match self { $(Self::$scheme => <$instance as Instance>::valid_digests(bytes)),+ }
            }
        }

        #[derive(Clone, Debug)]
        pub enum State {
            $($scheme(Arc<Tree<$instance>>)),+
        }
        impl State {
            pub fn scheme(&self) -> Scheme {
                match self { $(Self::$scheme(_) => Scheme::$scheme),+ }
            }
            pub fn shape(&self) -> Shape {
                match self { $(Self::$scheme(tree) => tree.shape()),+ }
            }
            pub fn retained_bytes(&self) -> Result<usize> {
                match self {
                    $(Self::$scheme(tree) => retained_bytes::<$instance>(tree.shape())),+
                }
                .ok_or_else(|| exhausted("oracle-byte-limit"))
            }
            /// The committed table and tree, shared by every handle to this state.
            pub(crate) fn backing(&self) -> Result<Backing> {
                let bytes = self.retained_bytes()?;
                Ok(match self { $(Self::$scheme(tree) => Backing::of(tree, bytes)),+ })
            }
        }

        fn commit_state(
            scheme: Scheme,
            values: &Value,
            width: &Value,
            policy: &Policy,
            available: usize,
        ) -> Result<Vec<Value>> {
            match (scheme, values) {
                $((Scheme::$scheme, Value::$vector(values)) => {
                    let width = index(width)?;
                    if width == 0 || !values.len().is_multiple_of(width) {
                        return Err(refused("oracle-shape"));
                    }
                    let shape = table_shape(width, values.len() / width, policy)?;
                    let bytes = retained_bytes::<$instance>(shape)
                        .ok_or_else(|| exhausted("oracle-byte-limit"))?;
                    policy.output(
                        bytes
                            .checked_add(size(1, scheme.digest_bytes())?)
                            .ok_or_else(|| exhausted("size-overflow"))?,
                        available,
                    )?;
                    let (root, tree) =
                        commit::<$instance>(values.to_vec(), shape, policy.max_value_bytes)
                            .map_err(failure)?;
                    Ok(vec![
                        Value::MerkleDigest(scheme, root.into()),
                        Value::MerkleTree(State::$scheme(Arc::new(tree))),
                    ])
                },)+
                _ => Err(refused("oracle-operands")),
            }
        }

        fn open_state(
            state: &State,
            at: &[usize],
            policy: &Policy,
            available: usize,
        ) -> Result<Vec<Value>> {
            open_outputs(state, at.len(), policy, available)?;
            let scheme = state.scheme();
            Ok(match state {
                $(State::$scheme(tree) => {
                    let (rows, proof) = open(tree, at).map_err(failure)?;
                    vec![Value::$vector(rows.into()), Value::MerkleProof(scheme, proof.into())]
                }),+
            })
        }

        #[allow(clippy::too_many_arguments)]
        fn check_state(
            scheme: Scheme,
            root: &[u8],
            width: usize,
            height: usize,
            at: &[usize],
            rows: &Value,
            proof: &[u8],
            policy: &Policy,
        ) -> Result<bool> {
            let shape = table_shape(width, height, policy)?;
            let result = match (scheme, rows) {
                $((Scheme::$scheme, Value::$vector(rows)) =>
                    verify::<$instance>(root, shape, at, rows, proof),)+
                _ => return Err(refused("oracle-operands")),
            };
            result.map_err(failure)
        }
    };
}

instances! {
    Poseidon2KoalaBear => (MerklePoseidon2KoalaBear, KoalaBear, poseidon2::Base, KoalaBearVector),
    Poseidon2KoalaBearExt4 => (MerklePoseidon2KoalaBearExt4, KoalaBearExt4, poseidon2::Quartic, KoalaBearExt4Vector),
    Poseidon2BabyBear => (MerklePoseidon2BabyBear, BabyBear, poseidon2::baby_bear::Base, BabyBearVector),
    Poseidon2BabyBearExt4 => (MerklePoseidon2BabyBearExt4, BabyBearExt4, poseidon2::baby_bear::Quartic, BabyBearExt4Vector),
    Poseidon2Goldilocks => (MerklePoseidon2Goldilocks, Goldilocks, poseidon2::goldilocks::Base, GoldilocksVector),
    Poseidon2GoldilocksExt2 => (MerklePoseidon2GoldilocksExt2, GoldilocksExt2, poseidon2::goldilocks::Quadratic, GoldilocksExt2Vector),
}

impl Scheme {
    fn of_binding(binding: &OperationBinding) -> Option<Self> {
        match binding.arguments.as_slice() {
            [scheme] => Self::from_identity(Identity::parse(scheme).ok()?),
            _ => None,
        }
    }
    fn physical(self, kind: Type) -> Option<PhysicalType> {
        let identity = match kind {
            Type::Index | Type::Indices | Type::Bool => Identity::None,
            Type::Vector => self.field(),
            _ => self.identity(),
        };
        PhysicalType::default_for(LogicalType::new(kind, identity).ok()?).ok()
    }
}

impl State {
    /// Bytes `count` openings read: their rows and at most their full paths.
    pub(crate) fn opening_bytes(&self, count: usize) -> Result<usize> {
        let scheme = self.scheme();
        let shape = self.shape();
        let row = shape
            .width()
            .checked_mul(scheme.element_bytes())
            .and_then(|row| row.checked_add(shape.depth().checked_mul(scheme.digest_bytes())?))
            .ok_or_else(|| exhausted("size-overflow"))?;
        size(count, row)
    }
}

fn failure(error: Error) -> zkc_runtime::vm::BackendError {
    match error {
        Error::ByteLimit => exhausted("oracle-byte-limit"),
        Error::Allocation => exhausted("allocation"),
        Error::Positions => refused("oracle-positions"),
        Error::Coordinate => refused("oracle-coordinate"),
        Error::ValueCount => refused("oracle-value-count"),
    }
}

/// Independent native advertisement for the shared row-oracle contracts and
/// the multi-opening contracts, for this family's schemes only.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use Type::*;
    let scheme = Scheme::of_binding(binding)?;
    if binding.implementation != format!("plonky3/{}", binding.contract) {
        return None;
    }
    let (inputs, outputs): (&[Type], &[Type]) = match binding.contract.as_str() {
        "oracle.commit" => (&[Vector, Index], &[Commitment, OpeningState]),
        "oracle.open" => (&[OpeningState, Index], &[Vector, Proof]),
        "oracle.check" => (&[Commitment, Index, Index, Index, Vector, Proof], &[Bool]),
        "oracle.open_many" => (&[OpeningState, Indices], &[Vector, Proof]),
        "oracle.check_many" => (&[Commitment, Index, Index, Indices, Vector, Proof], &[Bool]),
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
            .map(|t| scheme.physical(*t))
            .collect::<Option<_>>()?,
        outputs: outputs
            .iter()
            .map(|t| scheme.physical(*t))
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
fn indices(v: &Value) -> Result<Vec<usize>> {
    let Value::Indices(values) = v else {
        return Err(refused("oracle-operands"));
    };
    values
        .iter()
        .map(|n| usize::try_from(*n).map_err(|_| refused("oracle-coordinate")))
        .collect()
}
fn table_shape(width: usize, height: usize, policy: &Policy) -> Result<Shape> {
    Shape::new(width, height, policy.max_table_elements.min(1 << 20)).map_err(|error| {
        use zkc_kernels::plonky3::oracle::Error as E;
        match error {
            E::ElementLimit => exhausted("oracle-element-limit"),
            _ => refused("oracle-shape"),
        }
    })
}
fn digest(scheme: Scheme, value: &Value) -> Option<Arc<[u8]>> {
    match value {
        Value::MerkleDigest(s, root) if *s == scheme => Some(root.clone()),
        _ => None,
    }
}

/// Opening several positions allocates their rows and at most one full path
/// per distinct position; the actual pruned proof is never larger.
fn open_outputs(state: &State, count: usize, policy: &Policy, available: usize) -> Result<()> {
    let scheme = state.scheme();
    let shape = state.shape();
    let elements = count
        .checked_mul(shape.width())
        .ok_or_else(|| exhausted("size-overflow"))?;
    policy.vector_width(elements, scheme.element_bytes())?;
    let proof = count
        .checked_mul(shape.depth())
        .ok_or_else(|| exhausted("size-overflow"))?;
    policy.vector_width(proof, scheme.digest_bytes())?;
    policy.output(
        size(elements, scheme.element_bytes())?
            .checked_add(size(proof, scheme.digest_bytes())?)
            .ok_or_else(|| exhausted("size-overflow"))?,
        available,
    )
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    invocation: &Invocation<'_>,
    policy: &Policy,
) -> Result<Vec<Value>> {
    let scheme = invocation
        .binding
        .declaration()
        .arguments
        .first()
        .and_then(|s| Identity::parse(s).ok())
        .and_then(Scheme::from_identity)
        .ok_or_else(|| refused("oracle-domain"))?;
    let available = invocation.max_output_bytes;
    let digest_bytes = scheme.digest_bytes();
    let outputs = match (name, args) {
        ("oracle.commit", [values, width]) => {
            commit_state(scheme, values, width, policy, available)?
        }
        ("oracle.open", [Value::MerkleTree(state), at]) if state.scheme() == scheme => {
            open_state(state, &[index(at)?], policy, available)?
        }
        ("oracle.open_many", [Value::MerkleTree(state), at]) if state.scheme() == scheme => {
            open_state(state, &indices(at)?, policy, available)?
        }
        (
            "oracle.check" | "oracle.check_many",
            [root, width, height, at, rows, Value::MerkleProof(p, proof)],
        ) if *p == scheme => {
            policy.output(512, available)?;
            let root = digest(scheme, root).ok_or_else(|| refused("oracle-operands"))?;
            let at = if name == "oracle.check" {
                vec![index(at)?]
            } else {
                indices(at)?
            };
            let (width, height) = (index(width)?, index(height)?);
            vec![Value::Bool(check_state(
                scheme, &root, width, height, &at, rows, proof, policy,
            )?)]
        }
        ("commitments.empty", []) => {
            policy.output(256, available)?;
            vec![Value::MerkleDigests(scheme, Arc::from([]))]
        }
        ("commitments.append", [Value::MerkleDigests(s, roots), Value::MerkleDigest(r, root)])
            if *s == scheme && *r == scheme =>
        {
            let length = roots
                .len()
                .checked_add(root.len())
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.vector_width(length / digest_bytes, digest_bytes)?;
            policy.output(size(length, 1)?, available)?;
            let mut result = crate::operations::arithmetic::reserve(length)?;
            result.extend_from_slice(roots);
            result.extend_from_slice(root);
            vec![Value::MerkleDigests(scheme, result.into())]
        }
        ("commitments.at", [Value::MerkleDigests(s, roots), at]) if *s == scheme => {
            policy.output(512, available)?;
            let at = index(at)?;
            let root = at
                .checked_mul(digest_bytes)
                .and_then(|start| roots.get(start..start.checked_add(digest_bytes)?))
                .ok_or_else(|| refused("oracle-coordinate"))?;
            vec![Value::MerkleDigest(scheme, root.into())]
        }
        ("commitments.length", [Value::MerkleDigests(s, roots)]) if *s == scheme => {
            vec![Value::Index((roots.len() / digest_bytes) as u64)]
        }
        ("opening_states.empty", []) => {
            policy.output(256, available)?;
            vec![Value::MerkleTrees(scheme, Arc::from([]))]
        }
        ("opening_states.append", [Value::MerkleTrees(s, states), Value::MerkleTree(state)])
            if *s == scheme && state.scheme() == scheme =>
        {
            let length = states
                .len()
                .checked_add(1)
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.vector_width(length, std::mem::size_of::<State>())?;
            let bytes = states_bytes(states)?
                .checked_add(state.retained_bytes()?)
                .and_then(|n| n.checked_add(std::mem::size_of::<State>()))
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.output(bytes, usize::MAX)?;
            // Existing trees are shared; only the new list of handles is allocated.
            policy.output(size(length, std::mem::size_of::<State>())?, available)?;
            let mut result = crate::operations::arithmetic::reserve(length)?;
            result.extend_from_slice(states);
            result.push(state.clone());
            vec![Value::MerkleTrees(scheme, result.into())]
        }
        ("opening_states.at", [Value::MerkleTrees(s, states), at]) if *s == scheme => {
            let state = states
                .get(index(at)?)
                .ok_or_else(|| refused("oracle-coordinate"))?;
            policy.output(state.retained_bytes()?, usize::MAX)?;
            vec![Value::MerkleTree(state.clone())]
        }
        ("opening_states.length", [Value::MerkleTrees(s, states)]) if *s == scheme => {
            vec![Value::Index(states.len() as u64)]
        }
        _ => return Err(refused("oracle-operands")),
    };
    Ok(outputs)
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
/// Report the list and, when it is newly retained, each distinct tree.
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

/// Digest bytes of a public value, or `None` when the value is not this
/// family's root or proof.
pub(crate) fn wire_digests(value: &Value) -> Option<(Scheme, &[u8])> {
    match value {
        Value::MerkleDigest(scheme, bytes) | Value::MerkleProof(scheme, bytes) => {
            Some((*scheme, bytes))
        }
        _ => None,
    }
}

/// The ZKCV frame of a root (`tag, digest`) or proof (`tag, count:u32,
/// digests`); the bulk codec checks limits and validates the complete frame.
pub(crate) fn encode(value: &Value, policy: &Policy) -> Option<Result<Vec<u8>>> {
    let (scheme, bytes) = wire_digests(value)?;
    let root = matches!(value, Value::MerkleDigest(..));
    Some((|| {
        validate(value, policy)?;
        let length = bytes
            .len()
            .checked_add(if root { 6 } else { 10 })
            .ok_or_else(|| exhausted("wire-bytes"))?;
        policy.wire(length)?;
        let mut out = crate::operations::arithmetic::reserve(length)?;
        out.extend_from_slice(b"ZKCV\x00");
        out.push(if root { 71 } else { 72 });
        if !root {
            let count = u32::try_from(bytes.len() / scheme.digest_bytes())
                .map_err(|_| exhausted("element-limit"))?;
            out.extend(count.to_le_bytes());
        }
        out.extend_from_slice(bytes);
        Ok(out)
    })())
}

/// Validate a carrier's digest bytes: whole canonical digests, and exactly one
/// for a root.
pub(crate) fn validate(value: &Value, policy: &Policy) -> Result<()> {
    let (scheme, bytes, root) = match value {
        Value::MerkleDigest(scheme, bytes) => (*scheme, bytes, true),
        Value::MerkleProof(scheme, bytes) | Value::MerkleDigests(scheme, bytes) => {
            (*scheme, bytes, false)
        }
        _ => return Ok(()),
    };
    let digest_bytes = scheme.digest_bytes();
    if !bytes.len().is_multiple_of(digest_bytes) || (root && bytes.len() != digest_bytes) {
        return Err(refused("oracle-digest"));
    }
    policy.vector_width(bytes.len() / digest_bytes, digest_bytes)?;
    if !scheme.valid_digests(bytes) {
        return Err(refused("oracle-digest"));
    }
    Ok(())
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("plonky3/oracle.open_many", "oracle.open_many"),
    ("plonky3/oracle.check_many", "oracle.check_many"),
];

#[cfg(test)]
mod tests {
    use super::*;

    fn decoding_exhaustion<I: Instance>(
        scheme: Scheme,
        values: Vec<I::Element>,
        value: impl FnOnce(Vec<I::Element>) -> Value,
    ) where
        <I::Mmcs as p3_commit::Mmcs<I::Element>>::Commitment: Send,
        <I::Mmcs as p3_commit::Mmcs<I::Element>>::ProverData<
            p3_matrix::dense::RowMajorMatrix<I::Element>,
        >: Send,
    {
        let shape = Shape::new(2, 8, 16).unwrap();
        let (root, tree) = commit::<I>(values, shape, 1 << 20).unwrap();
        let (rows, proof) = open(&tree, &[1]).unwrap();
        let rows = value(rows);
        let check = || check_state(scheme, &root, 2, 8, &[1], &rows, &proof, &Policy::default());
        for successful in [0, 1] {
            let guard = zkc_kernels::allocation::failure::after(successful);
            let error = check().unwrap_err();
            assert_eq!(error.code, "exhausted:allocation");
            assert_eq!(crate::classify_error(&error), crate::ErrorClass::Exhausted);
            drop(guard);
        }
        assert_eq!(check(), Ok(true));
    }

    #[test]
    fn merkle_decode_capacity_failures_propagate_as_native_exhaustion() {
        let values: Vec<_> = (1..=16).map(crate::KoalaBear::new).collect();
        decoding_exhaustion::<poseidon2::Base>(
            Scheme::Poseidon2KoalaBear,
            values.clone(),
            |values| Value::KoalaBearVector(values.into()),
        );
        decoding_exhaustion::<poseidon2::Quartic>(
            Scheme::Poseidon2KoalaBearExt4,
            values.into_iter().map(crate::KoalaBearExt4::from).collect(),
            |values| Value::KoalaBearExt4Vector(values.into()),
        );
        let baby: Vec<_> = (1..=16).map(crate::BabyBear::new).collect();
        decoding_exhaustion::<poseidon2::baby_bear::Base>(
            Scheme::Poseidon2BabyBear,
            baby.clone(),
            |values| Value::BabyBearVector(values.into()),
        );
        decoding_exhaustion::<poseidon2::baby_bear::Quartic>(
            Scheme::Poseidon2BabyBearExt4,
            baby.into_iter().map(crate::BabyBearExt4::from).collect(),
            |values| Value::BabyBearExt4Vector(values.into()),
        );
        let gold: Vec<_> = (1..=16).map(crate::Goldilocks::new).collect();
        decoding_exhaustion::<poseidon2::goldilocks::Base>(
            Scheme::Poseidon2Goldilocks,
            gold.clone(),
            |values| Value::GoldilocksVector(values.into()),
        );
        decoding_exhaustion::<poseidon2::goldilocks::Quadratic>(
            Scheme::Poseidon2GoldilocksExt2,
            gold.into_iter().map(crate::GoldilocksExt2::from).collect(),
            |values| Value::GoldilocksExt2Vector(values.into()),
        );
    }

    #[test]
    fn schemes_bind_exact_fields_and_widths() {
        for (scheme, identity, field, width) in [
            (
                Scheme::Poseidon2BabyBear,
                "rows.merkle-poseidon2-16.baby-bear/0",
                Identity::BabyBear,
                4,
            ),
            (
                Scheme::Poseidon2BabyBearExt4,
                "rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0",
                Identity::BabyBearExt4,
                16,
            ),
            (
                Scheme::Poseidon2Goldilocks,
                "rows.merkle-poseidon2-8.goldilocks/0",
                Identity::Goldilocks,
                8,
            ),
            (
                Scheme::Poseidon2GoldilocksExt2,
                "rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0",
                Identity::GoldilocksExt2,
                16,
            ),
        ] {
            assert_eq!(scheme.identity().name(), identity);
            assert_eq!(Scheme::from_identity(scheme.identity()), Some(scheme));
            assert_eq!(scheme.field(), field);
            assert_eq!(scheme.element_bytes(), width);
            assert_eq!(scheme.digest_bytes(), 32);
            assert_eq!(Scheme::from_identity(field), None);
        }
    }

    fn native_round_trip<I: Instance>(
        scheme: Scheme,
        values: Vec<I::Element>,
        wrap: impl Fn(Vec<I::Element>) -> Value,
    ) {
        let policy = Policy::default();
        let shape = Shape::new(2, 8, 16).unwrap();
        let retained = retained_bytes::<I>(shape).unwrap();
        let required = retained + size(1, scheme.digest_bytes()).unwrap();
        let value = wrap(values);
        assert_eq!(
            commit_state(scheme, &value, &Value::Index(2), &policy, required - 1)
                .unwrap_err()
                .code,
            "exhausted:output-bytes",
        );
        // Shape refusal precedes the output budget, as for the existing profiles.
        assert_eq!(
            commit_state(scheme, &value, &Value::Index(0), &policy, 0)
                .unwrap_err()
                .code,
            "refused:oracle-shape",
        );
        let outputs = commit_state(scheme, &value, &Value::Index(2), &policy, required).unwrap();
        let (Value::MerkleDigest(root_scheme, root), Value::MerkleTree(state)) =
            (&outputs[0], &outputs[1])
        else {
            panic!("wrong commit outputs")
        };
        assert_eq!(*root_scheme, scheme);
        assert_eq!(state.scheme(), scheme);
        assert_eq!(state.retained_bytes().unwrap(), retained);
        assert_eq!(
            state.opening_bytes(3).unwrap(),
            size(3, 2 * scheme.element_bytes() + shape.depth() * 32).unwrap()
        );
        let required =
            size(6, scheme.element_bytes()).unwrap() + size(3 * shape.depth(), 32).unwrap();
        assert_eq!(
            open_state(state, &[7, 1, 1], &policy, required - 1)
                .unwrap_err()
                .code,
            "exhausted:output-bytes"
        );
        for at in [&[1][..], &[7, 1, 1][..]] {
            let opened = open_state(state, at, &policy, required).unwrap();
            let Value::MerkleProof(proof_scheme, proof) = &opened[1] else {
                panic!("wrong proof output")
            };
            assert_eq!(*proof_scheme, scheme);
            assert_eq!(
                check_state(scheme, root, 2, 8, at, &opened[0], proof, &policy),
                Ok(true)
            );
            let wrong = Value::KoalaBearVector(Arc::from([]));
            assert_eq!(
                check_state(scheme, root, 2, 8, at, &wrong, proof, &policy)
                    .unwrap_err()
                    .code,
                "refused:oracle-operands"
            );
        }
        assert_eq!(
            commit_state(
                scheme,
                &Value::KoalaBearVector(Arc::from([])),
                &Value::Index(2),
                &policy,
                required
            )
            .unwrap_err()
            .code,
            "refused:oracle-operands"
        );
    }

    #[test]
    fn new_schemes_preserve_preflight_typed_openings_and_publication() {
        use p3_field::BasedVectorSpace;
        native_round_trip::<poseidon2::baby_bear::Base>(
            Scheme::Poseidon2BabyBear,
            (1..=16).map(crate::BabyBear::new).collect(),
            |values| Value::BabyBearVector(values.into()),
        );
        native_round_trip::<poseidon2::baby_bear::Quartic>(
            Scheme::Poseidon2BabyBearExt4,
            (1..=16)
                .map(|i| {
                    crate::BabyBearExt4::from_basis_coefficients_fn(|j| {
                        crate::BabyBear::new(i * 7 + j as u32)
                    })
                })
                .collect(),
            |values| Value::BabyBearExt4Vector(values.into()),
        );
        native_round_trip::<poseidon2::goldilocks::Base>(
            Scheme::Poseidon2Goldilocks,
            (1..=16)
                .map(|i| crate::Goldilocks::new((1 << 63) + i))
                .collect(),
            |values| Value::GoldilocksVector(values.into()),
        );
        native_round_trip::<poseidon2::goldilocks::Quadratic>(
            Scheme::Poseidon2GoldilocksExt2,
            (1..=16)
                .map(|i| {
                    crate::GoldilocksExt2::from_basis_coefficients_fn(|j| {
                        crate::Goldilocks::new((1 << 63) + i * 7 + j as u64)
                    })
                })
                .collect(),
            |values| Value::GoldilocksExt2Vector(values.into()),
        );
    }
}
