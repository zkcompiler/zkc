//! Shared entry, operand and result checks for every native kernel.
use super::EntryPolicy;
use crate::{Policy, Result, Value, exhausted, refused};
use crate::{SetupRegistry, resource::Resources};
use std::collections::HashSet;
use zkc_runtime::interactive::{
    Frame, FrameKind, Invocation, Retained, Type, Value as RuntimeValue,
};

pub(super) struct Core {
    pub(super) policy: Policy,
    pub(super) entry: EntryPolicy,
    pub(super) resources: Resources,
    pub(super) setups: SetupRegistry,
    pub(super) polynomial: crate::plonky3::polynomial::Kernels,
}
impl Core {
    pub(super) fn new(policy: Policy, entry: EntryPolicy, setups: SetupRegistry) -> Self {
        Self {
            policy,
            entry,
            resources: Resources::new(policy),
            setups,
            polynomial: Default::default(),
        }
    }
    pub(super) fn validate(&self, v: &Value) -> Result<()> {
        self.validate_retained(v, Retained::NONE)
    }
    pub(super) fn validate_retained(&self, v: &Value, retained: Retained<'_>) -> Result<()> {
        self.policy.output(v.retained_bytes(), usize::MAX)?;
        if let Some(t) = v.capability() {
            self.resources.validate(t, v.ty())?;
        }
        let metadata = match v {
            Value::Sequence(sequence) => {
                if sequence
                    .validation_backing()
                    .is_some_and(|b| retained.contains(b))
                {
                    return Ok(());
                }
                sequence.validate(&self.policy)?;
                sequence.validate_children(retained, &mut |element| {
                    self.validate_retained(element, retained)
                })?;
                return Ok(());
            }
            Value::Variant(variant) => {
                variant.validate()?;
                for payload in variant.payload() {
                    self.validate_retained(payload, retained)?;
                }
                return Ok(());
            }
            Value::FieldArray(value) => {
                value.validate()?;
                self.policy.vector(value.elements().len())?;
                None
            }
            Value::FixedVector(value) => {
                value.validate()?;
                self.policy.vector_width(value.elements().len(), 4)?;
                None
            }
            Value::Bn254Matrix(m) => {
                m.policy(&self.policy)?;
                None
            }
            Value::Bn254Vector(v) => {
                self.policy.vector(v.len())?;
                None
            }
            Value::Bn254Polynomial(v) => {
                self.policy.vector(v.len())?;
                if !crate::kernels::arithmetic::normalized(v) {
                    return Err(refused("polynomial-normalization"));
                }
                None
            }
            Value::Bn254G1Vector(v) => {
                self.policy.typed_groups::<crate::Bn254G1>(v.len())?;
                None
            }
            Value::Bn254G2Vector(v) => {
                self.policy.typed_groups::<crate::Bn254G2>(v.len())?;
                None
            }
            Value::Bls12381G2Vector(v) => {
                self.policy.typed_groups::<crate::Bls12381G2>(v.len())?;
                None
            }
            Value::Bytes(a) => {
                self.policy.bytes(a.len())?;
                None
            }
            Value::Indices(a) => {
                self.policy.vector_width(a.len(), 8)?;
                None
            }
            Value::Matrix(m) => {
                m.policy(&self.policy)?;
                None
            }
            Value::RistrettoMatrix(m) => {
                m.policy(&self.policy)?;
                None
            }
            Value::KoalaBearExt8Matrix(m) => {
                m.policy(&self.policy)?;
                None
            }
            Value::KoalaBearExt4Matrix(m) => {
                m.policy(&self.policy)?;
                None
            }
            Value::KoalaBearExt4Vector(a) => {
                self.policy.vector_width(a.len(), 16)?;
                None
            }
            Value::KoalaBearExt4Polynomial(a) => {
                self.policy.vector_width(a.len(), 16)?;
                if !crate::kernels::arithmetic::normalized(a) {
                    return Err(refused("polynomial-normalization"));
                }
                None
            }
            Value::Binary64Matrix(m) => {
                m.policy(&self.policy)?;
                None
            }
            Value::Binary64Vector(a) => {
                self.policy.vector_width(a.len(), 8)?;
                None
            }
            Value::Binary64Polynomial(a) => {
                self.policy.vector_width(a.len(), 8)?;
                if !crate::kernels::arithmetic::normalized(a) {
                    return Err(refused("polynomial-normalization"));
                }
                None
            }
            Value::Binary64Ext3Matrix(m) => {
                m.policy(&self.policy)?;
                None
            }
            Value::Binary64Ext3Vector(a) => {
                self.policy.vector_width(a.len(), 24)?;
                None
            }
            Value::Binary64Ext3Polynomial(a) => {
                self.policy.vector_width(a.len(), 24)?;
                if !crate::kernels::arithmetic::normalized(a) {
                    return Err(refused("polynomial-normalization"));
                }
                None
            }
            Value::KoalaBearExt8Vector(a) => {
                self.policy.vector_width(a.len(), 32)?;
                None
            }
            Value::KoalaBearExt8Polynomial(a) => {
                self.policy.vector_width(a.len(), 32)?;
                if !crate::kernels::arithmetic::normalized(a) {
                    return Err(refused("polynomial-normalization"));
                }
                None
            }
            Value::KoalaBearMatrix(m) => {
                m.policy(&self.policy)?;
                None
            }
            Value::KoalaBearVector(a) => {
                self.policy.vector_width(a.len(), 4)?;
                None
            }
            Value::KoalaBearPolynomial(a) => {
                self.policy.vector_width(a.len(), 4)?;
                if !crate::kernels::arithmetic::normalized(a) {
                    return Err(refused("polynomial-normalization"));
                }
                None
            }
            Value::Vector(a) => {
                self.policy.vector(a.len())?;
                None
            }
            Value::RistrettoVector(a) => {
                self.policy.vector(a.len())?;
                None
            }
            Value::Polynomial(a) => {
                self.policy.vector(a.len())?;
                if !crate::kernels::arithmetic::normalized(a) {
                    return Err(refused("polynomial-normalization"));
                }
                None
            }
            Value::RistrettoPolynomial(a) => {
                self.policy.vector(a.len())?;
                if !crate::kernels::arithmetic::normalized(a) {
                    return Err(refused("polynomial-normalization"));
                }
                None
            }
            Value::EdwardsGroups(a) => {
                self.policy.dalek_groups(a.len())?;
                None
            }
            Value::RistrettoGroups(a) => {
                self.policy.dalek_groups(a.len())?;
                None
            }
            Value::FrDiagonal(d) => {
                self.policy.vector(d.factors().len())?;
                None
            }
            Value::RistrettoDiagonal(d) => {
                self.policy.vector(d.factors().len())?;
                self.policy.dalek_groups(d.backing().len())?;
                None
            }
            Value::Table(t) => {
                self.policy.table_len(t.arity())?;
                None
            }
            Value::TableMsb(t) => {
                self.policy.table_len(t.arity())?;
                None
            }
            Value::Groups(p) => {
                self.policy.groups(p.len())?;
                None
            }
            Value::Point(p) => {
                self.policy.arity(p.len())?;
                None
            }
            Value::Commitment(c) => Some(c.metadata()),
            Value::OpeningState(s) => Some(s.commitment().metadata()),
            Value::Proof(p) => Some(p.metadata()),
            Value::ProverKey(k) => Some(k.metadata()),
            Value::VerifierKey(k) => Some(k.metadata()),
            Value::OracleRoots(_, roots) => {
                crate::oracle::validate_hash_count(Type::Commitments, roots.len(), &self.policy)?;
                None
            }
            Value::OraclePath(_, path) => {
                crate::oracle::validate_hash_count(Type::Proof, path.len(), &self.policy)?;
                None
            }
            Value::OracleStates(_, states) => {
                self.policy
                    .vector_width(states.len(), std::mem::size_of::<crate::oracle::State>())?;
                None
            }
            Value::MerkleDigest(..) | Value::MerkleProof(..) | Value::MerkleDigests(..) => {
                crate::merkle::validate(v, &self.policy)?;
                None
            }
            Value::MerkleTrees(_, trees) => {
                self.policy
                    .vector_width(trees.len(), std::mem::size_of::<crate::merkle::State>())?;
                None
            }
            Value::Shake128State(..)
            | Value::ResourceUnit(..)
            | Value::Bn254Field(..)
            | Value::Bn254Round(..)
            | Value::Bn254G1(..)
            | Value::Bn254Gt(..)
            | Value::Bn254G2(..)
            | Value::Bls12381G2(..)
            | Value::Bls12381Gt(..)
            | Value::OracleRoot(..)
            | Value::OracleState(..)
            | Value::MerkleTree(..)
            | Value::Index(..)
            | Value::KoalaBearExt8Field(..)
            | Value::KoalaBearExt8Round(..)
            | Value::KoalaBearExt4Field(..)
            | Value::KoalaBearExt4Round(..)
            | Value::Binary64Field(..)
            | Value::Binary64Round(..)
            | Value::Binary64Ext3Field(..)
            | Value::Binary64Ext3Round(..)
            | Value::KoalaBearField(..)
            | Value::KoalaBearRound(..)
            | Value::RistrettoField(..)
            | Value::RistrettoRound(..)
            | Value::RistrettoGroup(..)
            | Value::Field(..)
            | Value::Round(..)
            | Value::Bool(..)
            | Value::Rng(..)
            | Value::Nonce(..)
            | Value::Transcript(..)
            | Value::EdwardsGroup(..)
            | Value::Curve(..) => None,
        };
        if let Some(m) = metadata {
            self.policy.table_len(m.arity())?;
            self.setups.check(m)?;
        }
        Ok(())
    }
    /// Pure entry constraints; missing values are only pending resource roots.
    pub(super) fn check_entry_values<'a>(
        &self,
        inputs: impl Iterator<Item = &'a (String, zkc_runtime::interactive::PhysicalType)> + Clone,
        values: &[Option<&Value>],
    ) -> Result<()> {
        if inputs.clone().count() != values.len() {
            return Err(refused("frame-arguments"));
        }
        if let Some(n) = self.entry.arity {
            self.policy.arity(n)?;
        }
        for name in self.entry.ports.keys() {
            if !inputs.clone().any(|(n, _)| n == name) {
                return Err(refused("entry-constraint-port"));
            }
        }
        for ((port, ty), v) in inputs.zip(values) {
            if v.is_none() && !matches!(ty.kind(), Type::Rng | Type::Nonce | Type::Transcript) {
                return Err(refused("entry-preparation-value"));
            }
            let (arity, meta) = match v {
                Some(Value::Table(t)) => (Some(t.arity()), None),
                Some(Value::TableMsb(t)) => (Some(t.arity()), None),
                Some(Value::Point(point)) => (Some(point.len()), None),
                Some(Value::ProverKey(k)) => (Some(k.metadata().arity()), Some(k.metadata())),
                Some(Value::VerifierKey(k)) => (Some(k.metadata().arity()), Some(k.metadata())),
                Some(Value::Commitment(c)) => (Some(c.metadata().arity()), Some(c.metadata())),
                Some(Value::OpeningState(s)) => {
                    let meta = s.commitment().metadata();
                    (Some(meta.arity()), Some(meta))
                }
                Some(Value::Proof(p)) => (Some(p.metadata().arity()), Some(p.metadata())),
                _ => (None, None),
            };
            if let (Some(expected), Some(actual)) = (self.entry.arity, arity)
                && expected != actual
            {
                return Err(refused("entry-shape"));
            }
            if let Some(constraint) = self.entry.ports.get(port) {
                if constraint.arity.is_some() && constraint.arity != arity {
                    return Err(refused("entry-port-shape"));
                }
                if constraint.setup.is_some() && constraint.setup != meta {
                    return Err(refused("entry-port-setup"));
                }
            }
        }
        Ok(())
    }
    pub(super) fn enter(
        &mut self,
        frame: &Frame,
        args: &[Value],
        retained: Retained<'_>,
    ) -> Result<()> {
        for v in args {
            self.validate_retained(v, retained)?;
        }
        if matches!(frame.kind(), FrameKind::Entry) {
            if !self.entry.domain.matches(frame) {
                return Err(refused("entry-domain"));
            }
            self.check_entry_values(
                frame.inputs().iter(),
                &args.iter().map(Some).collect::<Vec<_>>(),
            )?;
        }
        self.resources.enter(frame, args)
    }
    pub(super) fn invoke(
        &self,
        i: &Invocation<'_>,
        args: &[Value],
        signature: &zkc_runtime::interactive::BoundSignature,
        call: Option<&mut Option<super::NativeCall>>,
    ) -> Result<()> {
        if i.binding.signature() != signature
            || i.binding.implementation() != i.kernel
            || args.len() != signature.inputs.len()
            || args
                .iter()
                .zip(&signature.inputs)
                .any(|(v, t)| !v.has_type(t))
        {
            return Err(refused("kernel-operands"));
        }
        if let Some(call) = call {
            super::NativeCall::prepare(call, signature.attributes, i.attributes)?;
        } else {
            super::NativeCall::check(signature.attributes, i.attributes)?;
        }
        for v in args {
            self.validate_retained(v, i.retained)?;
        }
        Ok(())
    }

    pub(super) fn outputs(
        &self,
        i: &Invocation<'_>,
        args: &[Value],
        values: Vec<Value>,
    ) -> Result<Vec<Value>> {
        if values.len() != i.binding.signature().outputs.len()
            || values
                .iter()
                .zip(&i.binding.signature().outputs)
                .any(|(v, t)| !v.has_type(t))
        {
            return Err(refused("kernel-output-type"));
        }
        let sum = values.iter().try_fold(0usize, |n, v| {
            n.checked_add(v.retained_bytes())
                .ok_or_else(|| exhausted("output-bytes"))
        })?;
        self.policy.output(sum, usize::MAX)?;
        // The invocation allowance bounds newly allocated storage. Include
        // nested operand backings so an accessor returning an existing child
        // does not need room for a second copy of that child.
        let mut held = HashSet::new();
        for argument in args {
            argument.retained_parts(&mut |backing| {
                !i.retained.contains(backing) && held.insert(backing)
            });
        }
        let mut fresh = 0u128;
        for value in &values {
            let owned = value.retained_parts(&mut |backing| {
                if i.retained.contains(backing) || !held.insert(backing) {
                    return false;
                }
                fresh += backing.bytes() as u128;
                true
            });
            fresh += owned as u128;
        }
        let fresh = usize::try_from(fresh).map_err(|_| exhausted("output-bytes"))?;
        self.policy.output(fresh, i.max_output_bytes)?;
        Ok(values)
    }
}
