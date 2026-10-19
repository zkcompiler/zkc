//! Exact numerical consumers of the existing Ring DAG. Preparation belongs to
//! a reached NativeCall, never a process-wide cache or a Host Ring asset budget.
#![forbid(unsafe_code)]

use super::{Call, memory::payload_bytes};
use crate::kernels::{field::Family, vector};
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

/// Bound the entire node workspace, rather than allocating whole intermediate
/// columns. This target is independent of protocols, fields and expression shape.
const WORKSPACE_BYTES: usize = 16 * 1024;
const CHUNK_ROWS: usize = 256;

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

    fn apply(
        &self,
        args: &[Value],
        max_output_bytes: usize,
        policy: &Policy,
    ) -> Result<Vec<Value>> {
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
        policy.output(retained, max_output_bytes)?;
        let call = Call::new(policy, max_output_bytes);
        call.work_items(rows, self.per_row, self.setup)?;
        let row_bytes = payload_bytes::<S>(self.expression.nodes().len())?;
        let input_bytes = payload_bytes::<Operand<'_, S>>(operands.len())?;
        let scratch_bytes = row_bytes
            .checked_add(input_bytes)
            .ok_or_else(|| exhausted("numerical-bytes"))?;
        let staging = if map { payload_bytes::<S>(rows)? } else { 0 };
        let minimum = scratch_bytes
            .checked_add(staging)
            .and_then(|n| n.checked_add(retained))
            .filter(|n| *n <= policy.max_numerical_bytes)
            .ok_or_else(|| exhausted("numerical-bytes"))?;
        // Preserve the scalar working-space admission boundary. Extra workspace
        // changes the chunk size, not the minimum policy allowance. Allocation
        // failure remains distinct from policy admission.
        let stride = if self.varying_nodes.is_empty() {
            1
        } else {
            rows.clamp(1, CHUNK_ROWS)
                .min((WORKSPACE_BYTES / row_bytes).max(1))
                .min(1 + (policy.max_numerical_bytes - minimum) / row_bytes)
        };
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
        let mut scratch = call.scratch(self.expression.nodes().len() * stride, S::zero())?;
        let value = if map {
            let mut output = call.output(rows, S::zero(), retained)?;
            for (chunk, destination) in output.as_mut_slice().chunks_mut(stride).enumerate() {
                let values = self.chunk(
                    chunk * stride,
                    destination.len(),
                    stride,
                    inputs.as_ref(),
                    scratch.as_mut(),
                )?;
                destination.copy_from_slice(values);
            }
            output.finish(|values| Ok(S::vector_value(values.into())))?
        } else {
            let output = call.scalar(retained)?;
            let mut accumulator = if matches!(self.mode, Mode::Sum) {
                S::zero()
            } else {
                S::one()
            };
            for row in (0..rows).step_by(stride) {
                let values = self.chunk(
                    row,
                    stride.min(rows - row),
                    stride,
                    inputs.as_ref(),
                    scratch.as_mut(),
                )?;
                accumulator = if matches!(self.mode, Mode::Sum) {
                    values.iter().fold(accumulator, |sum, value| sum + *value)
                } else {
                    values
                        .iter()
                        .fold(accumulator, |product, value| product * *value)
                };
            }
            output.finish(|| Ok(S::field_value(accumulator)))?
        };
        Ok(vec![value])
    }

    fn chunk<'a>(
        &self,
        row: usize,
        len: usize,
        stride: usize,
        inputs: &[Operand<'_, S>],
        scratch: &'a mut [S],
    ) -> Result<&'a [S]> {
        // Initialize from this invocation's captures only when a row is reached,
        // after all preflight checks and destination reservations. An empty
        // domain never evaluates invariant arithmetic; no captures enter Plan.
        if row == 0 {
            for &index in &self.invariant_nodes {
                let value = match self.expression.nodes()[index] {
                    Node::Constant(..) => self.constants[index],
                    Node::Input(input) => match inputs[input] {
                        Operand::Scalar(value) => value,
                        Operand::Column(_) => return Err(refused("numerical-expression")),
                    },
                    Node::Add(a, b) => scratch[a * stride] + scratch[b * stride],
                    Node::Mul(a, b) => scratch[a * stride] * scratch[b * stride],
                    Node::Neg(a) => -scratch[a * stride],
                    Node::Embed(..) => return Err(refused("numerical-expression")),
                };
                scratch[index * stride..(index + 1) * stride].fill(value);
            }
        }
        for &index in &self.varying_nodes {
            // Ring admission proves dependencies precede this node, so the
            // initialized destination cannot alias either immutable input slice.
            let (prefix, destination) = scratch.split_at_mut(index * stride);
            let destination = &mut destination[..len];
            let source = |node| &prefix[node * stride..node * stride + len];
            match self.expression.nodes()[index] {
                Node::Input(input) => match inputs[input] {
                    Operand::Scalar(value) => destination.fill(value),
                    Operand::Column(values) => destination.copy_from_slice(&values[row..row + len]),
                },
                Node::Add(a, b) => vector::add::<S>(source(a), source(b), destination),
                Node::Mul(a, b) => vector::mul::<S>(source(a), source(b), destination),
                Node::Neg(a) => vector::neg::<S>(source(a), destination),
                Node::Constant(..) => destination.fill(self.constants[index]),
                Node::Embed(..) => return Err(refused("numerical-expression")),
            }
        }
        let root = self.expression.outputs()[0] * stride;
        Ok(&scratch[root..root + len])
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
            Self::Bn254(plan) => plan.apply(args, i.max_output_bytes, policy),
            Self::Bls12381(plan) => plan.apply(args, i.max_output_bytes, policy),
            Self::Ristretto(plan) => plan.apply(args, i.max_output_bytes, policy),
            Self::KoalaBear(plan) => plan.apply(args, i.max_output_bytes, policy),
            Self::KoalaBearExt4(plan) => plan.apply(args, i.max_output_bytes, policy),
            Self::KoalaBearExt8(plan) => plan.apply(args, i.max_output_bytes, policy),
            Self::Binary64(plan) => plan.apply(args, i.max_output_bytes, policy),
            Self::Binary64Ext3(plan) => plan.apply(args, i.max_output_bytes, policy),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn captured_square<S: Family>(field: Identity, mode: Mode) -> Plan<S> {
        let binding = OperationBinding {
            contract: "numerical.map".into(),
            arguments: vec![field.name().into(), "10".into()],
            implementation: "test/numerical.map".into(),
        };
        let body = json!([
            "zkc.ring/0",
            [field.name(), field.name()],
            [["input", 0], ["input", 1], ["mul", 1, 1], ["add", 0, 2]],
            [3]
        ])
        .to_string();
        Plan::<S>::new(
            Expression::parse(&body).unwrap(),
            b"10",
            mode,
            body.len(),
            &binding,
        )
        .unwrap()
    }

    fn varying_memory_floor<S: Family>(field: Identity) {
        for mode in [Mode::Map, Mode::Sum, Mode::Product] {
            let plan = captured_square::<S>(field, mode);
            for rows in [0, 1, 513] {
                let map = matches!(mode, Mode::Map);
                let retained = if map {
                    size(rows, size_of::<S>()).unwrap()
                } else {
                    512
                };
                // Independent scalar-floor formula, including typed views and
                // staging/final overlap. Do not discover this value by probing.
                let minimum = 4 * size_of::<S>()
                    + 2 * size_of::<Operand<'_, S>>()
                    + if map { rows * size_of::<S>() } else { 0 }
                    + retained;
                let args = [
                    Value::Index(rows as u64),
                    S::vector_value(vec![S::one(); rows].into()),
                    S::field_value(S::one()),
                ];
                let policy = Policy {
                    max_numerical_bytes: minimum,
                    ..Policy::default()
                };
                assert!(plan.apply(&args, retained, &policy).is_ok());
                let below = Policy {
                    max_numerical_bytes: minimum - 1,
                    ..policy
                };
                assert_eq!(
                    plan.apply(&args, retained, &below).err(),
                    Some(exhausted("numerical-bytes"))
                );
            }
        }
    }

    #[test]
    fn distinct_rows_survive_packing_across_constrained_chunks() {
        use crate::KoalaBear as S;
        for mode in [Mode::Map, Mode::Sum, Mode::Product] {
            let plan = captured_square::<S>(Identity::KoalaBear, mode);
            for rows in [7, 8, 9, 31, 257, 513] {
                let inputs: Vec<_> = (0..rows).map(|i| S::new(i as u32 + 1)).collect();
                let map = matches!(mode, Mode::Map);
                let retained = if map {
                    size(rows, size_of::<S>()).unwrap()
                } else {
                    512
                };
                let row_bytes = 4 * size_of::<S>();
                let minimum = row_bytes
                    + 2 * size_of::<Operand<'_, S>>()
                    + if map { rows * size_of::<S>() } else { 0 }
                    + retained;
                // Widths on either side of native packs, including repeated
                // odd-sized chunks. Every row differs, exposing lane swaps.
                for width in [1, 7, 8, 9, 13, 17, 256] {
                    let policy = Policy {
                        max_numerical_bytes: minimum + (width - 1) * row_bytes,
                        ..Policy::default()
                    };
                    for capture in [3, 11] {
                        let expected: Vec<_> = inputs
                            .iter()
                            .map(|x| *x + S::new(capture * capture))
                            .collect();
                        let args = [
                            Value::Index(rows as u64),
                            S::vector_value(inputs.clone().into()),
                            S::field_value(S::new(capture)),
                        ];
                        let result = plan.apply(&args, retained, &policy).unwrap();
                        match mode {
                            Mode::Map => assert_eq!(
                                S::vector(&result[0]).unwrap().as_ref(),
                                expected.as_slice()
                            ),
                            Mode::Sum => assert_eq!(
                                S::field(&result[0]).unwrap(),
                                expected.iter().copied().sum::<S>()
                            ),
                            Mode::Product => assert_eq!(
                                S::field(&result[0]).unwrap(),
                                expected.iter().copied().product::<S>()
                            ),
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn varying_calls_keep_the_scalar_memory_floor_in_every_field() {
        varying_memory_floor::<crate::Bn254Scalar>(Identity::Bn254Fr);
        varying_memory_floor::<crate::Scalar>(Identity::Bls12381Fr);
        varying_memory_floor::<crate::RistrettoScalar>(Identity::Ristretto255Scalar);
        varying_memory_floor::<crate::KoalaBear>(Identity::KoalaBear);
        varying_memory_floor::<crate::KoalaBearExt4>(Identity::KoalaBearExt4);
        varying_memory_floor::<crate::KoalaBearExt8>(Identity::KoalaBearExt8);
        varying_memory_floor::<crate::Binary64>(Identity::Binary64);
        varying_memory_floor::<crate::Binary64Ext3>(Identity::Binary64Ext3);
    }

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
