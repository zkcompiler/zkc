//! Exact numerical consumers of the existing Ring DAG. Preparation belongs to
//! a reached NativeCall, never a process-wide cache or a Host Ring asset budget.
#![forbid(unsafe_code)]

use super::{Call, memory::payload_bytes};
use crate::kernels::field::Family;
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use std::mem::size_of;
use zkc_runtime::ring::{Expression, Node};
use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, Invocation, LogicalType, OperationBinding,
    OperationSignature, PhysicalType, Type,
};

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("arkworks/numerical.map", "numerical.map"),
    ("dalek/numerical.map", "numerical.map"),
    ("plonky3/numerical.map", "numerical.map"),
    ("arkworks/numerical.sum", "numerical.sum"),
    ("dalek/numerical.sum", "numerical.sum"),
    ("plonky3/numerical.sum", "numerical.sum"),
    ("arkworks/numerical.product", "numerical.product"),
    ("dalek/numerical.product", "numerical.product"),
    ("plonky3/numerical.product", "numerical.product"),
];

const BODY_BYTES: usize = 4096;
const INPUTS: usize = 1023;
const ROWS: u64 = 1_048_576;
/// Requested immutable metadata per installed call, including its copied key,
/// Ring inputs/nodes/facts/roots, typed constants, positional mask and node
/// schedules. Temporary classification flags are also conservatively included.
/// Parsing scratch is separately bounded by the 4096-byte carrier. This is not RSS.
const PREPARED_BYTES: usize = 1024 * 1024;

#[derive(Clone, Copy)]
enum Mode {
    Map,
    Sum,
    Product,
}
impl Mode {
    fn for_contract(contract: &str) -> Option<Self> {
        match contract {
            "numerical.map" => Some(Self::Map),
            "numerical.sum" => Some(Self::Sum),
            "numerical.product" => Some(Self::Product),
            _ => None,
        }
    }
}

/// Independently authored native advertisement. Do not call the runtime's
/// logical or physical operation resolvers from this owner.
pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    let mode = Mode::for_contract(&binding.contract)?;
    let [field, mask] = binding.arguments.as_slice() else {
        return None;
    };
    let field = Identity::parse(field).ok()?;
    let provider = match field {
        Identity::Bn254Fr | Identity::Bls12381Fr => "arkworks",
        Identity::Ristretto255Scalar => "dalek",
        Identity::KoalaBear
        | Identity::KoalaBearExt4
        | Identity::KoalaBearExt8
        | Identity::Binary64
        | Identity::Binary64Ext3 => "plonky3",
        _ => return None,
    };
    if binding.implementation != format!("{provider}/{}", binding.contract)
        || mask.len() > INPUTS
        || !mask.bytes().all(|bit| matches!(bit, b'0' | b'1'))
    {
        return None;
    }
    let port =
        |kind, identity| PhysicalType::default_for(LogicalType::new(kind, identity).ok()?).ok();
    let mut inputs = Vec::with_capacity(mask.len() + 1);
    inputs.push(port(Type::Index, Identity::None)?);
    for bit in mask.bytes() {
        inputs.push(port(
            if bit == b'0' {
                Type::Field
            } else {
                Type::Vector
            },
            field,
        )?);
    }
    Some(OperationSignature {
        inputs,
        outputs: vec![port(
            if matches!(mode, Mode::Map) {
                Type::Vector
            } else {
                Type::Field
            },
            field,
        )?],
        attributes: AttributeRule::NumericalExpression,
    })
}

pub(crate) enum Prepared {
    Bn254(Plan<crate::Bn254Scalar>),
    Bls12381(Plan<crate::Scalar>),
    Ristretto(Plan<crate::RistrettoScalar>),
    KoalaBear(Plan<crate::KoalaBear>),
    KoalaBearExt4(Plan<crate::KoalaBearExt4>),
    KoalaBearExt8(Plan<crate::KoalaBearExt8>),
    Binary64(Plan<crate::Binary64>),
    Binary64Ext3(Plan<crate::Binary64Ext3>),
}

pub(crate) struct Plan<S> {
    expression: Expression,
    constants: Box<[S]>,
    mask: Box<[u8]>,
    invariant_nodes: Box<[usize]>,
    varying_nodes: Box<[usize]>,
    mode: Mode,
    per_row: u64,
    setup: u64,
}

pub(crate) fn prepare(
    binding: &OperationBinding,
    ports: &BoundSignature,
    attributes: &[String],
) -> Result<Prepared> {
    if signature(binding).as_ref() != Some(ports) {
        return Err(refused("numerical-binding"));
    }
    let [body] = attributes else {
        return Err(refused("numerical-expression"));
    };
    if body.len() > BODY_BYTES {
        return Err(refused("numerical-expression-bytes"));
    }
    let expression = Expression::parse(body).map_err(|_| refused("numerical-expression"))?;
    let field = Identity::parse(&binding.arguments[0]).map_err(|_| refused("numerical-binding"))?;
    let mask = binding.arguments[1].as_bytes();
    if expression.canonical() != *body
        || expression.inputs().len() != mask.len()
        || expression.outputs().len() != 1
        || expression.inputs().iter().any(|f| *f != field)
        || expression.facts().iter().any(|f| f.field != field)
        || expression
            .nodes()
            .iter()
            .any(|node| matches!(node, Node::Embed(..)))
    {
        return Err(refused("numerical-expression"));
    }
    let mode = Mode::for_contract(&binding.contract).ok_or_else(|| refused("numerical-binding"))?;
    macro_rules! plan {
        ($scalar:ty, $variant:ident) => {
            Prepared::$variant(Plan::<$scalar>::new(
                expression,
                mask,
                mode,
                body.len(),
                binding,
            )?)
        };
    }
    Ok(match field {
        Identity::Bn254Fr => plan!(crate::Bn254Scalar, Bn254),
        Identity::Bls12381Fr => plan!(crate::Scalar, Bls12381),
        Identity::Ristretto255Scalar => plan!(crate::RistrettoScalar, Ristretto),
        Identity::KoalaBear => plan!(crate::KoalaBear, KoalaBear),
        Identity::KoalaBearExt4 => plan!(crate::KoalaBearExt4, KoalaBearExt4),
        Identity::KoalaBearExt8 => plan!(crate::KoalaBearExt8, KoalaBearExt8),
        Identity::Binary64 => plan!(crate::Binary64, Binary64),
        Identity::Binary64Ext3 => plan!(crate::Binary64Ext3, Binary64Ext3),
        _ => return Err(refused("numerical-binding")),
    })
}

/// Conservative evaluation-admission score W = 8B + 2I + 2N + 1 + R(3N + 3),
/// where B is the carrier byte length, I the slot count, N the node count and R
/// the row count. The fixed setup surcharge applies even on an empty domain and
/// is identical for cold and cached calls. Bounded parsing, canonicalization and
/// immutable preparation precede per-evaluation scope admission; this score does
/// not gate that preparation. Each row reserves three units per node and three
/// sink/copy units before managed scratch and result construction.
fn work_counts(bytes: usize, inputs: usize, nodes: usize) -> Result<(u64, u64)> {
    let count = |n| u64::try_from(n).map_err(|_| exhausted("numerical-work"));
    let setup = count(bytes)?
        .checked_mul(8)
        .and_then(|n| n.checked_add(count(inputs).ok()?.checked_mul(2)?))
        .and_then(|n| n.checked_add(count(nodes).ok()?.checked_mul(2)?))
        .and_then(|n| n.checked_add(1))
        .ok_or_else(|| exhausted("numerical-work"))?;
    let per_row = count(nodes)?
        .checked_mul(3)
        .and_then(|n| n.checked_add(3))
        .ok_or_else(|| exhausted("numerical-work"))?;
    Ok((per_row, setup))
}

impl<S: Family> Plan<S> {
    fn new(
        expression: Expression,
        mask: &[u8],
        mode: Mode,
        bytes: usize,
        binding: &OperationBinding,
    ) -> Result<Self> {
        let nodes = expression.nodes().len();
        // The key has only nominal, nonstructural types. Include their complete
        // owned descriptors, strings and carrier copies in this metadata bound.
        // Each node also has one schedule index and a temporary dependency flag.
        nodes
            .checked_mul(
                size_of::<Node>()
                    + size_of::<zkc_runtime::ring::Fact>()
                    + size_of::<S>()
                    + size_of::<usize>()
                    + size_of::<bool>(),
            )
            .and_then(|n| n.checked_add(mask.len().checked_mul(size_of::<Identity>() + 1)?))
            .and_then(|n| n.checked_add((mask.len() + 2).checked_mul(size_of::<PhysicalType>())?))
            .and_then(|n| n.checked_add(bytes.checked_mul(3)?))
            .and_then(|n| n.checked_add(binding.contract.len() + binding.implementation.len()))
            .and_then(|n| n.checked_add(binding.arguments.iter().map(String::len).sum::<usize>()))
            .and_then(|n| n.checked_add(size_of::<Self>() + 1024))
            .filter(|n| *n <= PREPARED_BYTES)
            .ok_or_else(|| exhausted("numerical-metadata"))?;
        let (per_row, setup) = work_counts(bytes, mask.len(), nodes)?;
        let mut constants = Vec::new();
        constants
            .try_reserve_exact(nodes)
            .map_err(|_| exhausted("allocation"))?;
        let mut row_dependent = Vec::new();
        row_dependent
            .try_reserve_exact(nodes)
            .map_err(|_| exhausted("allocation"))?;
        for node in expression.nodes() {
            // Ring admission guarantees that every dependency precedes its
            // consumer. Classification uses only the immutable positional mask.
            row_dependent.push(match *node {
                Node::Constant(..) => false,
                Node::Input(input) => mask[input] == b'1',
                Node::Add(a, b) | Node::Mul(a, b) => row_dependent[a] || row_dependent[b],
                Node::Neg(a) => row_dependent[a],
                Node::Embed(..) => return Err(refused("numerical-expression")),
            });
            constants.push(match node {
                Node::Constant(_, literal) => S::decimal(literal)?,
                _ => S::zero(),
            });
        }
        let varying_count = row_dependent.iter().filter(|varying| **varying).count();
        let mut invariant_nodes = Vec::new();
        invariant_nodes
            .try_reserve_exact(nodes - varying_count)
            .map_err(|_| exhausted("allocation"))?;
        let mut varying_nodes = Vec::new();
        varying_nodes
            .try_reserve_exact(varying_count)
            .map_err(|_| exhausted("allocation"))?;
        for (index, varying) in row_dependent.into_iter().enumerate() {
            if varying {
                varying_nodes.push(index);
            } else {
                invariant_nodes.push(index);
            }
        }
        Ok(Self {
            expression,
            constants: constants.into_boxed_slice(),
            mask: mask.into(),
            invariant_nodes: invariant_nodes.into_boxed_slice(),
            varying_nodes: varying_nodes.into_boxed_slice(),
            mode,
            per_row,
            setup,
        })
    }

    fn apply(&self, args: &[Value], i: &Invocation<'_>, policy: &Policy) -> Result<Vec<Value>> {
        let [Value::Index(rows), operands @ ..] = args else {
            return Err(refused("numerical-operands"));
        };
        if *rows > ROWS {
            return Err(refused("numerical-rows"));
        }
        let rows = usize::try_from(*rows).map_err(|_| exhausted("size-overflow"))?;
        if operands.len() != self.mask.len() {
            return Err(refused("numerical-operands"));
        }
        // Shape inspection does not allocate or extract typed operand views.
        // Every declared column must agree, including inputs absent from the DAG.
        for (operand, bit) in operands.iter().zip(self.mask.iter()) {
            if *bit == b'1' && vector_length(operand) != Some(rows) {
                return Err(refused("numerical-shape"));
            }
        }
        let map = matches!(self.mode, Mode::Map);
        let retained = if map {
            policy.vector_width(rows, size_of::<S>())?;
            size(rows, size_of::<S>())?
        } else {
            512
        };
        policy.output(retained, i.max_output_bytes)?;
        let call = Call::new(policy, i.max_output_bytes);
        call.work_items(rows, self.per_row, self.setup)?;
        let scratch_bytes = payload_bytes::<S>(self.expression.nodes().len())?
            .checked_add(payload_bytes::<Operand<'_, S>>(operands.len())?)
            .ok_or_else(|| exhausted("numerical-bytes"))?;
        let staging = if map { payload_bytes::<S>(rows)? } else { 0 };
        scratch_bytes
            .checked_add(staging)
            .and_then(|n| n.checked_add(retained))
            .filter(|n| *n <= policy.max_numerical_bytes)
            .ok_or_else(|| exhausted("numerical-bytes"))?;
        // All requested managed storage and work have passed preflight. Extract
        // exact scalar/column operands once; each lane uses only native elements.
        let mut inputs = call.scratch(operands.len(), Operand::Scalar(S::zero()))?;
        for ((destination, operand), bit) in inputs
            .as_mut()
            .iter_mut()
            .zip(operands)
            .zip(self.mask.iter())
        {
            *destination = if *bit == b'0' {
                Operand::Scalar(S::field(operand)?)
            } else {
                Operand::Column(S::vector(operand)?.as_ref())
            };
        }
        let mut scratch = call.scratch(self.expression.nodes().len(), S::zero())?;
        let value = if map {
            let mut output = call.output(rows, S::zero(), retained)?;
            for (row, destination) in output.as_mut_slice().iter_mut().enumerate() {
                *destination = self.row(row, inputs.as_ref(), scratch.as_mut())?;
            }
            output.finish(|values| Ok(S::vector_value(values.into())))?
        } else {
            let output = call.scalar(retained)?;
            let mut accumulator = if matches!(self.mode, Mode::Sum) {
                S::zero()
            } else {
                S::one()
            };
            for row in 0..rows {
                let term = self.row(row, inputs.as_ref(), scratch.as_mut())?;
                accumulator = if matches!(self.mode, Mode::Sum) {
                    accumulator + term
                } else {
                    accumulator * term
                };
            }
            output.finish(|| Ok(S::field_value(accumulator)))?
        };
        Ok(vec![value])
    }

    fn row(&self, row: usize, inputs: &[Operand<'_, S>], scratch: &mut [S]) -> Result<S> {
        // Initialize from this invocation's captures only when a row is reached,
        // after all preflight checks and destination reservations. An empty
        // domain never evaluates invariant arithmetic; no captures enter Plan.
        if row == 0 {
            self.evaluate_nodes(&self.invariant_nodes, row, inputs, scratch)?;
        }
        self.evaluate_nodes(&self.varying_nodes, row, inputs, scratch)?;
        Ok(scratch[self.expression.outputs()[0]])
    }

    fn evaluate_nodes(
        &self,
        nodes: &[usize],
        row: usize,
        inputs: &[Operand<'_, S>],
        scratch: &mut [S],
    ) -> Result<()> {
        for &index in nodes {
            scratch[index] = match self.expression.nodes()[index] {
                Node::Constant(..) => self.constants[index],
                Node::Input(input) => match inputs[input] {
                    Operand::Scalar(value) => value,
                    Operand::Column(values) => values[row],
                },
                Node::Add(a, b) => scratch[a] + scratch[b],
                Node::Mul(a, b) => scratch[a] * scratch[b],
                Node::Neg(a) => -scratch[a],
                Node::Embed(..) => return Err(refused("numerical-expression")),
            };
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum Operand<'a, S> {
    Scalar(S),
    Column(&'a [S]),
}

fn vector_length(value: &Value) -> Option<usize> {
    Some(match value {
        Value::Bn254Vector(values) => values.len(),
        Value::Vector(values) => values.len(),
        Value::RistrettoVector(values) => values.len(),
        Value::KoalaBearVector(values) => values.len(),
        Value::KoalaBearExt4Vector(values) => values.len(),
        Value::KoalaBearExt8Vector(values) => values.len(),
        Value::Binary64Vector(values) => values.len(),
        Value::Binary64Ext3Vector(values) => values.len(),
        _ => return None,
    })
}

impl Prepared {
    pub(crate) fn apply(
        &self,
        args: &[Value],
        i: &Invocation<'_>,
        policy: &Policy,
    ) -> Result<Vec<Value>> {
        match self {
            Self::Bn254(plan) => plan.apply(args, i, policy),
            Self::Bls12381(plan) => plan.apply(args, i, policy),
            Self::Ristretto(plan) => plan.apply(args, i, policy),
            Self::KoalaBear(plan) => plan.apply(args, i, policy),
            Self::KoalaBearExt4(plan) => plan.apply(args, i, policy),
            Self::KoalaBearExt8(plan) => plan.apply(args, i, policy),
            Self::Binary64(plan) => plan.apply(args, i, policy),
            Self::Binary64Ext3(plan) => plan.apply(args, i, policy),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn work_arithmetic_checks_overflow_before_use() {
        #[cfg(target_pointer_width = "64")]
        {
            assert_eq!(
                work_counts(usize::MAX, 0, 0).err(),
                Some(exhausted("numerical-work"))
            );
            assert_eq!(
                work_counts(0, usize::MAX, 0).err(),
                Some(exhausted("numerical-work"))
            );
            assert_eq!(
                work_counts(0, 0, usize::MAX).err(),
                Some(exhausted("numerical-work"))
            );
        }
        let call = Call::new(&Policy::default(), usize::MAX);
        assert_eq!(
            call.work_items(2, u64::MAX, 1),
            Err(exhausted("numerical-work"))
        );
        assert_eq!(
            call.work_items(1, 1, u64::MAX),
            Err(exhausted("numerical-work"))
        );
        assert_eq!(
            payload_bytes::<crate::Scalar>(usize::MAX),
            Err(exhausted("numerical-bytes"))
        );
    }
}
