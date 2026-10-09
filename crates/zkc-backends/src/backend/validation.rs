//! Shared entry, operand and result checks for every native kernel.
use super::EntryPolicy;
use crate::{Policy, Result, Value, ark, exhausted, refused};
use crate::{SetupRegistry, resource::Resources};
use zkc_runtime::interactive::{
    AttributeRule, Frame, FrameKind, Invocation, Type, Value as RuntimeValue,
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
        self.policy.output(v.retained_bytes(), usize::MAX)?;
        if let Some(t) = v.capability() {
            self.resources.validate(t, v.ty())?;
        }
        let metadata = match v {
            Value::Sequence(sequence) => {
                sequence.validate(&self.policy)?;
                for element in sequence.elements() {
                    self.validate(element)?;
                }
                return Ok(());
            }
            Value::Variant(variant) => {
                variant.validate()?;
                for payload in variant.payload() {
                    self.validate(payload)?;
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
                self.policy.bn254_groups::<crate::Bn254G1>(v.len())?;
                None
            }
            Value::Bn254G2Vector(v) => {
                self.policy.bn254_groups::<crate::Bn254G2>(v.len())?;
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
            Value::RistrettoGroups(a) => {
                self.policy.ristretto_groups(a.len())?;
                None
            }
            Value::FrDiagonal(d) => {
                self.policy.vector(d.factors().len())?;
                None
            }
            Value::RistrettoDiagonal(d) => {
                self.policy.vector(d.factors().len())?;
                self.policy.ristretto_groups(d.backing().len())?;
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
            Value::ResourceUnit(..)
            | Value::Bn254Field(..)
            | Value::Bn254Round(..)
            | Value::Bn254G1(..)
            | Value::Bn254Gt(..)
            | Value::Bn254G2(..)
            | Value::OracleRoot(..)
            | Value::OracleState(..)
            | Value::Index(..)
            | Value::KoalaBearExt8Field(..)
            | Value::KoalaBearExt8Round(..)
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
            | Value::Curve(..) => None,
        };
        if let Some(m) = metadata {
            self.policy.table_len(m.arity())?;
            self.setups.check(m)?;
        }
        Ok(())
    }
    /// Pure entry constraints; missing values are only pending resource roots.
    pub(super) fn check_entry_values(
        &self,
        inputs: &[(String, zkc_runtime::interactive::PhysicalType)],
        values: &[Option<&Value>],
    ) -> Result<()> {
        if inputs.len() != values.len() {
            return Err(refused("frame-arguments"));
        }
        if let Some(n) = self.entry.arity {
            self.policy.arity(n)?;
        }
        for name in self.entry.ports.keys() {
            if !inputs.iter().any(|(n, _)| n == name) {
                return Err(refused("entry-constraint-port"));
            }
        }
        for ((port, ty), v) in inputs.iter().zip(values) {
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
    pub(super) fn enter(&mut self, frame: &Frame, args: &[Value]) -> Result<()> {
        for v in args {
            self.validate(v)?;
        }
        if matches!(frame.kind(), FrameKind::Entry) {
            if !self.entry.domain.matches(frame) {
                return Err(refused("entry-domain"));
            }
            self.check_entry_values(frame.inputs(), &args.iter().map(Some).collect::<Vec<_>>())?;
        }
        self.resources.enter(frame, args)
    }
    pub(super) fn invoke(
        &self,
        i: &Invocation<'_>,
        args: &[Value],
        signature: &zkc_runtime::interactive::BoundSignature,
    ) -> Result<()> {
        if i.binding.signature() != signature
            || i.binding.implementation() != i.kernel
            || args.len() != signature.inputs.len()
            || args
                .iter()
                .zip(&signature.inputs)
                .any(|(v, t)| v.physical_type() != *t)
        {
            return Err(refused("kernel-operands"));
        }
        match signature.attributes {
            AttributeRule::None if i.attributes.is_empty() => (),
            AttributeRule::Unsigned64
                if i.attributes.len() == 1
                    && i.attributes[0]
                        .parse::<u64>()
                        .is_ok_and(|n| n.to_string() == i.attributes[0]) => {}
            AttributeRule::NaturalIndex if i.attributes.len() == 1 => {
                zkc_runtime::logical::natural_index(&i.attributes[0])
                    .map_err(|_| refused("kernel-attributes"))?;
            }
            AttributeRule::NaturalIndices
                if i.attributes
                    .iter()
                    .all(|a| zkc_runtime::logical::natural_index(a).is_ok()) => {}
            AttributeRule::ScatterShape
                if !i.attributes.is_empty()
                    && i.attributes
                        .iter()
                        .all(|a| zkc_runtime::logical::natural_index(a).is_ok()) => {}
            AttributeRule::Bn254Decimals => {
                for literal in i.attributes {
                    crate::parse_bn254_decimal(literal).map_err(ark)?;
                }
            }
            AttributeRule::Bn254Decimal if i.attributes.len() == 1 => {
                crate::parse_bn254_decimal(&i.attributes[0]).map_err(ark)?;
            }
            AttributeRule::FieldDecimals => {
                for literal in i.attributes {
                    zkc_arkworks::parse_decimal(literal).map_err(ark)?;
                }
            }
            AttributeRule::RistrettoDecimals => {
                for literal in i.attributes {
                    crate::parse_ristretto_decimal(literal)?;
                }
            }
            AttributeRule::KoalaBearDecimals => {
                for literal in i.attributes {
                    let _ = crate::plonky3::parse_decimal(literal)?;
                }
            }
            AttributeRule::MatrixIdentity
                if i.attributes.len() == 1
                    && i.attributes[0].len() == 64
                    && i.attributes[0]
                        .bytes()
                        .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) => {}
            AttributeRule::MatrixDimensions
                if i.attributes.len() == 2
                    && i.attributes.iter().all(|a| {
                        zkc_runtime::logical::natural_index(a).is_ok_and(|n| n <= 65536)
                    }) => {}
            AttributeRule::MatrixShape
                if i.attributes.len() == 3
                    && i.attributes
                        .iter()
                        .all(|a| zkc_runtime::logical::natural_index(a).is_ok())
                    && matches!(i.attributes[2].as_str(), "0" | "1") => {}
            AttributeRule::KoalaBearDecimal if i.attributes.len() == 1 => {
                let _ = crate::plonky3::parse_decimal(&i.attributes[0])?;
            }
            AttributeRule::RistrettoDecimal if i.attributes.len() == 1 => {
                crate::parse_ristretto_decimal(&i.attributes[0])?;
            }
            AttributeRule::NativeMessageTemplate | AttributeRule::NativeChallengeTemplate => {
                let kind = if signature.attributes == AttributeRule::NativeMessageTemplate {
                    "message"
                } else {
                    "query"
                };
                zkc_runtime::logical::native_origin_template(i.attributes, kind)
                    .map_err(|_| refused("kernel-attributes"))?;
            }

            AttributeRule::FieldDecimal if i.attributes.len() == 1 => {
                zkc_arkworks::parse_decimal(&i.attributes[0]).map_err(ark)?;
            }
            _ => return Err(refused("kernel-attributes")),
        }
        for v in args {
            self.validate(v)?;
        }
        Ok(())
    }

    pub(super) fn outputs(&self, i: &Invocation<'_>, values: Vec<Value>) -> Result<Vec<Value>> {
        if values.len() != i.binding.signature().outputs.len()
            || values
                .iter()
                .zip(&i.binding.signature().outputs)
                .any(|(v, t)| v.physical_type() != *t)
        {
            return Err(refused("kernel-output-type"));
        }
        let sum = values.iter().try_fold(0usize, |n, v| {
            n.checked_add(v.retained_bytes())
                .ok_or_else(|| exhausted("output-bytes"))
        })?;
        self.policy.output(sum, i.max_output_bytes)?;
        Ok(values)
    }
}
