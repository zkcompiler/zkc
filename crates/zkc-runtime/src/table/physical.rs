//! Checked physical scalar interpretation of the existing structured program.
//!
//! Preparation cells are immutable arena objects in the same storage owner as
//! their residual/point dependencies. Invoke decodes scalar operands, then uses
//! the existing table kernel/provider implementation and its persistent state.
use super::{
    Bound, ChallengeProvider, Domain, FieldKernel, Operation, SmallPrimeKernel, TableBindings,
    TableLibrary, TapeProvider, Type, Value,
    storage::{MAX_RANK, Object, ScalarCell, rank},
};
use crate::{
    AdmissionFailure, AdmittedProgram, Bindings, Budget, Checker, EndpointEntry, Error, Library,
    Outcome, PhaseEvidence, Realization, Resources, Sort, Stop,
    arena::Handle,
    buffer::{BufferStore, PackedBuffers, add},
    format,
};
use num_bigint::BigUint;
use serde_json::Value as Json;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Preparation {
    Lazy,
    Materialized,
}

#[derive(Clone, Debug)]
enum Kind {
    Invoke(Operation),
    Prepare(Preparation, Domain, BigUint),
}
/// Resolved operation and types. Private fields prevent inconsistent signatures.
#[derive(Clone, Debug)]
pub struct PhysicalOperation {
    kind: Kind,
    arguments: Vec<Type>,
    result: Type,
}
impl PhysicalOperation {
    fn logical(&self) -> Operation {
        match &self.kind {
            Kind::Invoke(op) => op.clone(),
            Kind::Prepare(_, d, n) => Operation::Evaluate(*d, n.clone()),
        }
    }
}
#[derive(Clone, Copy, Debug)]
pub struct PhysicalTableLibrary;
impl Library for PhysicalTableLibrary {
    type Operation = PhysicalOperation;
    fn condition_sort(&self) -> Sort {
        TableLibrary.condition_sort()
    }
    fn sort(&self, value: &Json) -> Result<Sort, Error> {
        TableLibrary.sort(value)
    }
    fn dependencies(&self) -> Json {
        TableLibrary.dependencies()
    }
    fn operation(&self, value: &Json) -> Result<PhysicalOperation, Error> {
        let kind = match format::list(value)? {
            [tag, op] if tag == "invoke" => Kind::Invoke(TableLibrary.operation(op)?),
            [tag, mode, domain, n] if tag == "prepare" => Kind::Prepare(
                match format::string(mode)? {
                    "lazy" => Preparation::Lazy,
                    "materialized" => Preparation::Materialized,
                    _ => return Err(Error("unsupported-preparation-mode")),
                },
                Domain::decode(domain)?,
                format::natural(n)?,
            ),
            _ => return Err(Error("unknown-physical-operation")),
        };
        let logical = match &kind {
            Kind::Invoke(op) => op.clone(),
            Kind::Prepare(_, d, n) => Operation::Evaluate(*d, n.clone()),
        };
        let (arguments, result) = TableLibrary.signature(&logical);
        Ok(PhysicalOperation {
            kind,
            arguments: arguments
                .iter()
                .map(|s| Type::decode(&s.0))
                .collect::<Result<_, _>>()?,
            result: Type::decode(&result.0)?,
        })
    }
    fn signature(&self, op: &PhysicalOperation) -> (Vec<Sort>, Sort) {
        (
            op.arguments.iter().map(Type::sort).collect(),
            op.result.sort(),
        )
    }
}
impl AdmittedProgram<PhysicalOperation> {
    /// The installed source interpretation is always table-protocol revision 1.
    /// The checker must establish the selected realization and all phase evidence.
    pub fn admit_physical(
        source: Vec<u8>,
        candidate: Vec<u8>,
        phase: Option<PhaseEvidence>,
        checker: &impl Checker,
    ) -> Result<Arc<Self>, Box<AdmissionFailure>> {
        Self::admit_interpreted(
            source,
            candidate,
            phase,
            Realization::TablePhysicalPlan,
            &TableLibrary,
            &PhysicalTableLibrary,
            checker,
        )
    }
}

#[derive(Clone, Debug)]
pub struct PhysicalBound {
    logical: Bound,
    // A possible deferred read, preserved through generic branch joins/loops.
    lazy_rank: Option<usize>,
}
fn read_resources(rank: Option<usize>) -> Result<Resources, Error> {
    let Some(n) = rank else {
        return Ok(Resources::default());
    };
    let cells = 1usize
        .checked_shl(n.try_into().map_err(|_| Error("capacity-overflow"))?)
        .ok_or(Error("capacity-overflow"))?;
    let work = add(
        n,
        (cells - 1)
            .checked_mul(3)
            .ok_or(Error("capacity-overflow"))?,
    )?;
    Ok(Resources {
        steps: work.try_into().map_err(|_| Error("capacity-overflow"))?,
        scratch: cells,
        ..Resources::default()
    })
}

pub struct PhysicalTableBindings<
    K = SmallPrimeKernel,
    P = TapeProvider,
    S: BufferStore<u8> = PackedBuffers<u8>,
> {
    logical: TableBindings<K, P, S>,
    evaluations: u64,
    scalar_cells: usize,
    // Resolved scalar arguments for one coarse invoke, reserved before execution.
    decoded: Vec<Value>,
}
impl<K: FieldKernel, P: ChallengeProvider, S: BufferStore<u8>> PhysicalTableBindings<K, P, S> {
    pub fn new(logical: TableBindings<K, P, S>) -> Result<Self, Error> {
        Ok(Self {
            logical,
            evaluations: 0,
            scalar_cells: 0,
            decoded: Vec::new(),
        })
    }
    pub fn state_json(&self) -> Json {
        self.logical.state_json()
    }
    pub fn endpoint_entry(&self) -> Option<EndpointEntry> {
        self.logical.endpoint_entry()
    }
    pub fn events(&self) -> &[Json] {
        self.logical.events()
    }
    pub fn table_evaluations(&self) -> u64 {
        self.evaluations
    }
    pub fn scalar_cells(&self) -> usize {
        self.scalar_cells
    }
    pub fn buffer_usage(&self) -> crate::buffer::BufferUsage {
        self.logical.buffer_usage()
    }
    /// Read while this completion owner is alive. Each explicit lazy read is
    /// counted; no implicit memoization changes the selected preparation mode.
    pub fn value_json(&mut self, value: &Value) -> Result<Json, Error> {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let value = self.decode(value)?;
            self.logical.value_json(&value)
        }))
        .unwrap_or(Err(Error("backend-panic")))
    }
    fn cell(&self, d: Domain, h: Handle) -> Result<&ScalarCell<S::Reference>, Error> {
        match self.logical.storage.arena.resolve(h)? {
            Object::Scalar { domain, cell } if *domain == d => Ok(cell),
            Object::Scalar { .. } => Err(Error("scalar-domain-mismatch")),
            _ => Err(Error("handle-kind-mismatch")),
        }
    }
    fn deferred_rank(&self, d: Domain, residual: Handle, point: Handle) -> Result<usize, Error> {
        let storage = &self.logical.storage;
        let (root, fixed) = storage.residual(&Value::Residual(residual))?;
        let root = storage.root(root)?;
        let (actual, tail) = storage.point(&Value::Point(point))?;
        if root.domain != d || actual != d {
            return Err(Error("scalar-domain-mismatch"));
        }
        if add(fixed.length, tail.length)? != root.rank {
            return Err(Error("invalid-scalar-reference"));
        }
        Ok(root.rank)
    }
    fn reference_rank(&self, d: Domain, h: Handle) -> Result<Option<usize>, Error> {
        match self.cell(d, h)? {
            ScalarCell::Materialized(buffer) => {
                let values = self.logical.storage.read_cells(buffer)?;
                if values.len() != 1 || values[0] >= d.modulus() {
                    return Err(Error("invalid-scalar-reference"));
                }
                Ok(None)
            }
            ScalarCell::Deferred { residual, point } => {
                Ok(Some(self.deferred_rank(d, *residual, *point)?))
            }
        }
    }
    fn validate_type(&self, ty: &Type, value: &Value) -> Result<(), Error> {
        if let (Type::Scalar(d), Value::ScalarReference(actual, h)) = (ty, value) {
            if d != actual {
                return Err(Error("scalar-domain-mismatch"));
            }
            self.reference_rank(*d, *h)?;
            Ok(())
        } else {
            self.logical.storage.validate(ty, value)
        }
    }
    fn evaluated(&mut self) -> Result<(), Error> {
        self.evaluations = self
            .evaluations
            .checked_add(1)
            .ok_or(Error("evaluation-bound-violation"))?;
        Ok(())
    }
    fn decode(&mut self, value: &Value) -> Result<Value, Error> {
        let Value::ScalarReference(d, h) = value else {
            return Ok(value.clone());
        };
        // Validate issuer, kind, domain, dependencies and shape before reading.
        self.reference_rank(*d, *h)?;
        let result = match self.cell(*d, *h)? {
            ScalarCell::Materialized(buffer) => self.logical.storage.read_cells(buffer)?[0],
            ScalarCell::Deferred { residual, point } => {
                let (residual, point) = (Value::Residual(*residual), Value::Point(*point));
                let x = self
                    .logical
                    .evaluate(*d, &residual, &point)?
                    .ok_or(Error("invalid-scalar-reference"))?;
                self.evaluated()?;
                x
            }
        };
        Ok(Value::Scalar(*d, result))
    }
    fn prepare(
        &mut self,
        mode: Preparation,
        d: Domain,
        args: &[Value],
    ) -> Result<Outcome<Value>, Error> {
        let (Value::Residual(residual), Value::Point(point)) = (&args[0], &args[1]) else {
            return Err(Error("value-kind-mismatch"));
        };
        // Shape guard occurs here even for an unused lazy preparation.
        let (root, fixed) = self.logical.storage.residual(&args[0])?;
        let (_, tail) = self.logical.storage.point(&args[1])?;
        if add(fixed.length, tail.length)? != self.logical.storage.root(root)?.rank {
            return Ok(Outcome::Stopped(Stop::Refused));
        }
        let cell = match mode {
            Preparation::Lazy => ScalarCell::Deferred {
                residual: *residual,
                point: *point,
            },
            Preparation::Materialized => {
                let x = self
                    .logical
                    .evaluate(d, &args[0], &args[1])?
                    .ok_or(Error("invalid-scalar-reference"))?;
                self.evaluated()?;
                ScalarCell::Materialized(self.logical.storage.publish_cells(&[x])?)
            }
        };
        let h = self
            .logical
            .storage
            .arena
            .publish(Object::Scalar { domain: d, cell })?;
        self.scalar_cells = add(self.scalar_cells, 1)?;
        Ok(Outcome::Returned(Value::ScalarReference(d, h)))
    }
}
impl<K, P, S: BufferStore<u8>> Library for PhysicalTableBindings<K, P, S> {
    type Operation = PhysicalOperation;
    fn condition_sort(&self) -> Sort {
        PhysicalTableLibrary.condition_sort()
    }
    fn sort(&self, value: &Json) -> Result<Sort, Error> {
        PhysicalTableLibrary.sort(value)
    }
    fn dependencies(&self) -> Json {
        PhysicalTableLibrary.dependencies()
    }
    fn operation(&self, value: &Json) -> Result<PhysicalOperation, Error> {
        PhysicalTableLibrary.operation(value)
    }
    fn signature(&self, op: &PhysicalOperation) -> (Vec<Sort>, Sort) {
        PhysicalTableLibrary.signature(op)
    }
}
impl<K: FieldKernel, P: ChallengeProvider, S: BufferStore<u8>> Bindings
    for PhysicalTableBindings<K, P, S>
{
    type Value = Value;
    type Bound = PhysicalBound;
    fn validate_entry(&self, role: &str, evidence: Option<&PhaseEvidence>) -> Result<(), Error> {
        self.logical.validate_entry(role, evidence)
    }
    fn input(&mut self, sort: &Sort, value: &Json) -> Result<Value, Error> {
        self.logical.input(sort, value)
    }
    fn validate(&self, sort: &Sort, value: &Value) -> Result<(), Error> {
        self.validate_type(&Type::decode(&sort.0)?, value)
    }
    fn validate_output(&self, op: &PhysicalOperation, value: &Value) -> Result<(), Error> {
        self.validate_type(&op.result, value)
    }
    fn validate_result(&self, _: &PhysicalOperation, _: &[Value], _: &Value) -> Result<(), Error> {
        // The selected table contract has no additional request-dependent shape.
        // Do not read scalars here: validation must not change demand accounting.
        Ok(())
    }
    fn condition(&self, value: &Value) -> Result<bool, Error> {
        self.logical.condition(value)
    }
    fn bound(&self, value: &Value) -> Result<PhysicalBound, Error> {
        if let Value::ScalarReference(d, h) = value {
            Ok(PhysicalBound {
                logical: Bound::for_type(Type::Scalar(*d), 0)?,
                lazy_rank: self.reference_rank(*d, *h)?,
            })
        } else {
            Ok(PhysicalBound {
                logical: self.logical.bound(value)?,
                lazy_rank: None,
            })
        }
    }
    fn top(&self, sort: &Sort, budget: &Budget) -> Result<PhysicalBound, Error> {
        let logical = self.logical.top(sort, budget)?;
        let lazy_rank = matches!(logical.ty, Type::Scalar(_)).then_some(MAX_RANK);
        Ok(PhysicalBound { logical, lazy_rank })
    }
    fn join(&self, a: &PhysicalBound, b: &PhysicalBound) -> PhysicalBound {
        PhysicalBound {
            logical: self.logical.join(&a.logical, &b.logical),
            lazy_rank: a.lazy_rank.max(b.lazy_rank),
        }
    }
    fn estimate(
        &self,
        op: &PhysicalOperation,
        args: &[PhysicalBound],
        budget: &Budget,
    ) -> Result<(PhysicalBound, Resources), Error> {
        let logical_args = args.iter().map(|b| b.logical.clone()).collect::<Vec<_>>();
        let (logical, mut cost) = self
            .logical
            .estimate(&op.logical(), &logical_args, budget)?;
        let lazy_rank = match &op.kind {
            Kind::Prepare(mode, _, n) => {
                let n = rank(n)?;
                if *mode == Preparation::Lazy {
                    // No kernel evaluation until demanded; publication still reserves an object.
                    cost.steps = 0;
                    cost.scratch = 0;
                    Some(n)
                } else {
                    None
                }
            }
            Kind::Invoke(_) => {
                for arg in args {
                    let read = read_resources(arg.lazy_rank)?;
                    cost.steps = cost
                        .steps
                        .checked_add(read.steps)
                        .ok_or(Error("capacity-overflow"))?;
                    cost.scratch = cost.scratch.max(read.scratch);
                }
                None
            }
        };
        Ok((PhysicalBound { logical, lazy_rank }, cost))
    }
    fn output_resources(&self, value: &PhysicalBound) -> Result<Resources, Error> {
        read_resources(value.lazy_rank)
    }
    fn reserve(&mut self, resources: Resources, budget: &Budget) -> Result<(), Error> {
        self.decoded
            .try_reserve_exact(resources.arguments.saturating_sub(self.decoded.len()))
            .map_err(|_| Error("reservation-failed"))?;
        let mut budget = *budget;
        budget.bytes = budget
            .bytes
            .checked_sub(crate::buffer::bytes::<Value>(self.decoded.capacity())?)
            .ok_or(Error("capacity-limit"))?;
        self.logical.reserve(resources, &budget)
    }
    fn begin_execution(&mut self) {
        self.logical.begin_execution();
        self.evaluations = 0;
        // Scalar cells are owned by these bindings and may survive invocations.
        // No store/provider reset; the counter is total live physical cells.
    }
    fn invoke(&mut self, op: &PhysicalOperation, args: &[Value]) -> Result<Outcome<Value>, Error> {
        if args.len() != op.arguments.len() {
            return Err(Error("backend-argument-count"));
        }
        for (ty, value) in op.arguments.iter().zip(args) {
            self.validate_type(ty, value)?;
        }
        match &op.kind {
            Kind::Prepare(mode, d, _) => self.prepare(*mode, *d, args),
            Kind::Invoke(logical_op) => {
                self.decoded.clear();
                if args.len() > self.decoded.capacity() {
                    return Err(Error("argument-bound-violation"));
                }
                for value in args {
                    let decoded = self.decode(value)?;
                    self.decoded.push(decoded);
                }
                let outcome = self.logical.invoke_table(logical_op, &self.decoded)?;
                if matches!(logical_op, Operation::Evaluate(..))
                    && matches!(outcome, Outcome::Returned(_))
                {
                    self.evaluated()?;
                }
                Ok(outcome)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn checked_read_capacity_never_wraps() {
        assert_eq!(
            read_resources(Some(usize::BITS as usize)).err(),
            Some(Error("capacity-overflow"))
        );
        assert_eq!(
            read_resources(Some(usize::MAX)).err(),
            Some(Error("capacity-overflow"))
        );
        assert_eq!(read_resources(Some(12)).unwrap().scratch, 4096);
    }
    #[test]
    fn malformed_scalar_cells_fail_before_kernel_use() {
        let (state, provider) = super::super::State::decode(&json!([0, 0, 0, [], []])).unwrap();
        let mut b = PhysicalTableBindings::new(
            TableBindings::new(SmallPrimeKernel, provider, state).unwrap(),
        )
        .unwrap();
        b.logical.storage.arena.reserve(4).unwrap();
        b.logical.storage.cells.reserve(4, 4).unwrap();
        for values in [&[][..], &[1, 2][..], &[7][..]] {
            let cell = ScalarCell::Materialized(b.logical.storage.publish_cells(values).unwrap());
            let h = b
                .logical
                .storage
                .arena
                .publish(Object::Scalar {
                    domain: Domain::Seven,
                    cell,
                })
                .unwrap();
            assert_eq!(
                b.value_json(&Value::ScalarReference(Domain::Seven, h)),
                Err(Error("invalid-scalar-reference"))
            );
        }
        let mut foreign = crate::arena::Arena::new().unwrap();
        foreign.reserve(1).unwrap();
        let h = foreign.publish(0).unwrap();
        let h = b
            .logical
            .storage
            .arena
            .publish(Object::Scalar {
                domain: Domain::Seven,
                cell: ScalarCell::Deferred {
                    residual: h,
                    point: h,
                },
            })
            .unwrap();
        assert_eq!(
            b.value_json(&Value::ScalarReference(Domain::Seven, h)),
            Err(Error("foreign-handle"))
        );
        assert_eq!(b.table_evaluations(), 0);
    }
}
