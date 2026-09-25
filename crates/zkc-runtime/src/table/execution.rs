use super::endpoint::Call;
use super::{
    ChallengeProvider, Domain, Event, FieldKernel, Operation, TableBindings, Value, storage::Object,
};
use crate::buffer::BufferStore;
use crate::{Error, Outcome, Stop};
use num_bigint::BigUint;
use std::sync::Arc;
fn scalar(value: &Value) -> Result<u8, Error> {
    match value {
        Value::Scalar(_, x) => Ok(*x),
        _ => Err(Error("value-kind-mismatch")),
    }
}
fn digest(value: &Value) -> Result<&BigUint, Error> {
    match value {
        Value::Digest(n) => Ok(n),
        _ => Err(Error("value-kind-mismatch")),
    }
}
fn checked(d: Domain, x: u8) -> Result<u8, Error> {
    if x < d.modulus() {
        Ok(x)
    } else {
        Err(Error("field-contract-violation"))
    }
}
fn pair(a: &BigUint, b: &BigUint) -> BigUint {
    if a < b { b * b + a } else { a * a + a + b }
}
impl<K: FieldKernel, P: ChallengeProvider, S: BufferStore<u8>> TableBindings<K, P, S> {
    // Shared eager/deferred kernel. Scratch belongs to the retained bindings.
    pub(super) fn evaluate(
        &mut self,
        d: Domain,
        view: &Value,
        point: &Value,
    ) -> Result<Option<u8>, Error> {
        let (h, fixed) = self.storage.residual(view)?;
        let (_, tail) = self.storage.point(point)?;
        let root = self.storage.root(h)?;
        if fixed.length + tail.length != root.rank {
            return Ok(None);
        }
        let fixed = self.storage.read_cells(fixed)?;
        let tail = self.storage.read_cells(tail)?;
        let cells = self.storage.read_cells(&root.cells)?;
        if cells.len() > self.scratch.capacity() {
            return Err(Error("scratch-bound-violation"));
        }
        self.scratch.clear();
        self.scratch.extend_from_slice(cells);
        let mut live = self.scratch.len();
        for r in fixed.iter().chain(tail) {
            let complement = checked(d, self.kernel.sub(d, 1, *r))?;
            let half = live / 2;
            for j in 0..half {
                let left = checked(d, self.kernel.mul(d, complement, self.scratch[j]))?;
                let right = checked(d, self.kernel.mul(d, *r, self.scratch[half + j]))?;
                self.scratch[j] = checked(d, self.kernel.add(d, left, right))?;
            }
            live = half;
        }
        Ok(Some(self.scratch[0]))
    }
    pub(super) fn invoke_table(
        &mut self,
        op: &Operation,
        args: &[Value],
    ) -> Result<Outcome<Value>, Error> {
        use Operation::*;
        let value = match op {
            View(_, _) => {
                let Value::Table(root) = args[0] else {
                    return Err(Error("value-kind-mismatch"));
                };
                self.storage.view(root)?
            }
            Restrict(_, _) => {
                let Some(value) = self.storage.restrict(&args[0], scalar(&args[1])?)? else {
                    return Ok(Outcome::Stopped(Stop::Refused));
                };
                value
            }
            Evaluate(d, _) => {
                let Some(value) = self.evaluate(*d, &args[0], &args[1])? else {
                    return Ok(Outcome::Stopped(Stop::Refused));
                };
                Value::Scalar(*d, value)
            }
            Add(d) => Value::Scalar(
                *d,
                checked(
                    *d,
                    self.kernel.add(*d, scalar(&args[0])?, scalar(&args[1])?),
                )?,
            ),
            Record(d) | AbortWrite(d) => {
                let before = self.begin_call(Call::Write)?;
                let x = scalar(&args[0])?;
                self.event(Event::Write(*d, x))?;
                match d {
                    Domain::Two => self.state.two = x,
                    Domain::Seven => self.state.seven = x,
                };
                self.additional_writes = self
                    .additional_writes
                    .checked_add(1)
                    .ok_or(Error("write-bound-violation"))?;
                if matches!(op, AbortWrite(_)) {
                    self.complete_call(before, false);
                    return Ok(Outcome::Stopped(Stop::Abort));
                }
                self.complete_call(before, true);
                Value::Boolean(x != 0)
            }
            OrderedPair | Parent(_) => {
                let a = digest(&args[0])?;
                let b = digest(&args[1])?;
                Value::Digest(Arc::new(if matches!(op, Parent(true)) {
                    pair(b, a)
                } else {
                    pair(a, b)
                }))
            }
            Pack => Value::Summary(
                scalar(&args[0])?,
                scalar(&args[1])?,
                Arc::new(digest(&args[2])?.clone()),
            ),
            Send => {
                let before = self.begin_call(Call::Send)?;
                let a = scalar(&args[0])?;
                let b = scalar(&args[1])?;
                self.event(Event::Sent(a, b))?;
                self.state.sent.push((a, b));
                self.complete_call(before, true);
                Value::Boolean(true)
            }
            Draw => {
                let before = self.begin_call(Call::Draw)?;
                match self.provider.draw()? {
                    Outcome::Stopped(reason) => {
                        self.complete_call(before, false);
                        return Ok(Outcome::Stopped(reason));
                    }
                    Outcome::Returned(r) => {
                        checked(Domain::Seven, r)?;
                        self.event(Event::Drawn(r))?;
                        self.complete_call(before, true);
                        Value::Scalar(Domain::Seven, r)
                    }
                }
            }
            Linear => {
                let d = Domain::Seven;
                let a = scalar(&args[0])?;
                let b = scalar(&args[1])?;
                let r = scalar(&args[2])?;
                let complement = checked(d, self.kernel.sub(d, 1, r))?;
                let left = checked(d, self.kernel.mul(d, complement, a))?;
                let right = checked(d, self.kernel.mul(d, r, b))?;
                Value::Scalar(d, checked(d, self.kernel.add(d, left, right))?)
            }
            Point | EndpointPoint(_) => {
                let x = if let EndpointPoint(one) = op {
                    u8::from(*one)
                } else {
                    scalar(&args[0])?
                };
                let coordinates = self.storage.publish_cells(&[x])?;
                Value::Point(self.storage.arena.publish(Object::Point {
                    domain: Domain::Seven,
                    coordinates,
                })?)
            }
            Equal => Value::Boolean(scalar(&args[0])? == scalar(&args[1])?),
            DigestEqual => Value::Boolean(digest(&args[0])? == digest(&args[1])?),
        };
        Ok(Outcome::Returned(value))
    }
}
