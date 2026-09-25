use super::{ChallengeProvider, FieldKernel, Operation, TableBindings, Type, Value};
use crate::buffer::BufferStore;
use crate::{Budget, Error, Resources};
use num_bigint::BigUint;

/// Shape and numeric bounds use the declared public capacity profile. Natural
/// inputs get a uniform bit limit, never a bound selected from secret digits.
#[derive(Clone, Debug)]
pub struct Bound {
    pub(super) ty: Type,
    pub(super) point_len: usize,
    pub(super) bits: usize,
}
pub(super) const INPUT_NATURAL_BITS: usize = 4096;
impl Bound {
    pub(super) fn for_type(ty: Type, bits: usize) -> Result<Self, Error> {
        let point_len = match &ty {
            Type::Table(_, n) | Type::Residual(_, n) => super::storage::rank(n)?,
            _ => 0,
        };
        Ok(Self {
            ty,
            point_len,
            bits,
        })
    }
}
impl<K: FieldKernel, P: ChallengeProvider, S: BufferStore<u8>> TableBindings<K, P, S> {
    pub(super) fn value_bound(&self, value: &Value) -> Result<Bound, Error> {
        use Type as T;
        let ty = match value {
            Value::Boolean(_) => T::Boolean,
            Value::Scalar(d, _) => T::Scalar(*d),
            Value::ScalarReference(..) => return Err(Error("value-type-mismatch")),
            Value::Digest(_) => T::Digest,
            Value::Summary(..) => T::Summary,
            Value::Table(h) => {
                let r = self.storage.root(*h)?;
                T::Table(r.domain, BigUint::from(r.rank))
            }
            Value::Residual(_) => {
                let (h, _) = self.storage.residual(value)?;
                let r = self.storage.root(h)?;
                T::Residual(r.domain, BigUint::from(r.rank))
            }
            Value::Point(_) => {
                let (d, c) = self.storage.point(value)?;
                return Ok(Bound {
                    ty: T::Point(d),
                    point_len: c.length,
                    bits: 0,
                });
            }
        };
        Bound::for_type(ty, INPUT_NATURAL_BITS)
    }
    pub(super) fn operation_bound(
        &self,
        op: &Operation,
        args: &[Bound],
        budget: &Budget,
    ) -> Result<(Bound, Resources), Error> {
        use crate::Library;
        use Operation::*;
        let (_, sort) = self.signature(op);
        let mut bound = Bound::for_type(Type::decode(&sort.0)?, 0)?;
        let mut cost = Resources {
            values: 1,
            bytes: 128,
            ..Resources::default()
        };
        match op {
            View(_, n) | Restrict(_, n) => {
                let n = super::storage::rank(n)?;
                cost.bytes += n;
            }
            Evaluate(_, n) => {
                let n = super::storage::rank(n)?;
                cost.scratch = 1usize << n;
                cost.steps = (n + 3 * ((1usize << n) - 1)) as u64;
            }
            Record(_) | AbortWrite(_) | Send | Draw => {
                cost.events = 1;
                cost.bytes += 64;
            }
            OrderedPair | Parent(_) => {
                bound.bits = args[0]
                    .bits
                    .max(args[1].bits)
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(2))
                    .ok_or(Error("capacity-overflow"))?;
                if bound.bits > budget.natural_bits {
                    return Err(Error("natural-capacity-limit"));
                }
                cost.bytes = cost
                    .bytes
                    .checked_add(
                        bound
                            .bits
                            .div_ceil(8)
                            .checked_mul(4)
                            .ok_or(Error("capacity-overflow"))?,
                    )
                    .ok_or(Error("capacity-overflow"))?;
            }
            Pack => bound.bits = args[2].bits,
            Point | EndpointPoint(_) => {
                bound.point_len = 1;
                cost.bytes += 1;
            }
            Add(_) | Linear | Equal | DigestEqual => {}
        }
        // Check every resolved domain/rank even if a branch will never execute.
        for b in args {
            match &b.ty {
                Type::Table(_, n) | Type::Residual(_, n) => {
                    super::storage::rank(n)?;
                }
                _ => {}
            }
        }
        Ok((bound, cost))
    }
}
