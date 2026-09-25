//! An independently installed library, outside the runtime's built-in table profile.
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use serde_json::{Value, json};
use std::collections::VecDeque;
use zkc_runtime::{Bindings, Budget, Error, Library, Outcome, Resources, Sort, Stop, format};

const VECTOR_LIMIT: usize = 1024;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    Request,
    Send,
    RequestAndSend,
    Sum,
}
// Interface requests are distinct from source operations: an operation can
// issue multiple requests. Only call() exposes a reply to its interpreter.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Request {
    Vector,
    Send,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Datum {
    Count(BigUint),
    Vector(Vec<u8>),
    Predicate(bool),
}
impl Datum {
    pub fn json(&self) -> Value {
        match self {
            Self::Count(n) => format::number(n),
            Self::Vector(xs) => json!(xs),
            Self::Predicate(b) => json!(b),
        }
    }
}
#[derive(Clone)]
pub enum Bound {
    Count(usize), // Maximum bit width, not a value or a semantic source sort.
    Vector(usize),
    Predicate,
}
impl Bound {
    fn bytes(&self) -> usize {
        match self {
            Self::Count(bits) => bits.div_ceil(8),
            Self::Vector(n) => *n,
            Self::Predicate => 1,
        }
    }
}
pub struct Service {
    calls: BigUint,
    tape: VecDeque<u8>,
    events: Vec<(Request, BigUint)>,
    // Fault injection belongs to the test host, never to a protocol artifact.
    fault: Option<(String, usize)>,
}
fn sort(name: &str) -> Sort {
    Sort(json!([name]))
}
fn scalars(value: &Value) -> Result<Vec<u8>, Error> {
    format::list(value)?
        .iter()
        .map(|v| {
            format::natural(v)?
                .to_u8()
                .filter(|n| *n < 7)
                .ok_or(Error("noncanonical-scalar"))
        })
        .collect()
}
impl Service {
    pub fn new(state: &Value, fault: Option<(String, usize)>) -> Result<Self, Error> {
        let state = format::array(state, 2)?;
        Ok(Self {
            calls: format::natural(&state[0])?,
            tape: scalars(&state[1])?.into(),
            events: Vec::new(),
            fault,
        })
    }
    pub fn state(&self) -> Value {
        json!([format::number(&self.calls), self.tape])
    }
    pub fn events(&self) -> Value {
        json!(
            self.events
                .iter()
                .map(|(op, n)| json!([
                    if *op == Request::Vector {
                        "request"
                    } else {
                        "send"
                    },
                    format::number(n)
                ]))
                .collect::<Vec<_>>()
        )
    }
}
impl Library for Service {
    type Operation = Operation;
    fn dependencies(&self) -> Value {
        json!([["vector-service", "1"]])
    }
    fn condition_sort(&self) -> Sort {
        sort("predicate")
    }
    fn sort(&self, v: &Value) -> Result<Sort, Error> {
        match format::array(v, 1)?[0].as_str() {
            Some("count" | "vector" | "predicate") => Ok(Sort(v.clone())),
            _ => Err(Error("unknown-type")),
        }
    }
    fn operation(&self, v: &Value) -> Result<Operation, Error> {
        match format::array(v, 1)?[0].as_str() {
            Some("request") => Ok(Operation::Request),
            Some("send") => Ok(Operation::Send),
            Some("request_and_send") => Ok(Operation::RequestAndSend),
            Some("sum") => Ok(Operation::Sum),
            _ => Err(Error("unknown-operation")),
        }
    }
    fn signature(&self, op: &Operation) -> (Vec<Sort>, Sort) {
        match op {
            Operation::Request => (vec![sort("count")], sort("vector")),
            Operation::Send | Operation::RequestAndSend => (vec![sort("count")], sort("predicate")),
            Operation::Sum => (vec![sort("vector")], sort("count")),
        }
    }
}
impl Bindings for Service {
    type Value = Datum;
    type Bound = Bound;
    fn input(&mut self, ty: &Sort, v: &Value) -> Result<Datum, Error> {
        match ty.0[0].as_str() {
            Some("count") => Ok(Datum::Count(format::natural(v)?)),
            Some("vector") => Ok(Datum::Vector(scalars(v)?)),
            Some("predicate") => Ok(Datum::Predicate(v.as_bool().ok_or(Error("invalid-value"))?)),
            _ => Err(Error("unknown-type")),
        }
    }
    fn validate(&self, ty: &Sort, value: &Datum) -> Result<(), Error> {
        match (ty.0[0].as_str(), value) {
            (Some("count"), Datum::Count(_)) | (Some("predicate"), Datum::Predicate(_)) => Ok(()),
            (Some("vector"), Datum::Vector(xs)) => {
                if xs.iter().any(|n| *n >= 7) {
                    Err(Error("noncanonical-scalar"))
                } else {
                    Ok(())
                }
            }
            _ => Err(Error("invalid-value")),
        }
    }
    fn validate_result(&self, op: &Operation, args: &[Datum], reply: &Datum) -> Result<(), Error> {
        match (op, args) {
            (Operation::Request, [Datum::Count(n)]) => check_reply(Request::Vector, n, reply),
            (Operation::Send, [Datum::Count(n)]) => check_reply(Request::Send, n, reply),
            (Operation::RequestAndSend, [Datum::Count(_)])
            | (Operation::Sum, [Datum::Vector(_)]) => Ok(()),
            _ => Err(Error("invalid-value")),
        }
    }
    fn condition(&self, value: &Datum) -> Result<bool, Error> {
        if let Datum::Predicate(b) = value {
            Ok(*b)
        } else {
            Err(Error("invalid-value"))
        }
    }
    fn bound(&self, value: &Datum) -> Result<Bound, Error> {
        Ok(match value {
            Datum::Count(n) => {
                Bound::Count(n.bits().try_into().map_err(|_| Error("capacity-limit"))?)
            }
            Datum::Vector(xs) => Bound::Vector(xs.len()),
            Datum::Predicate(_) => Bound::Predicate,
        })
    }
    fn top(&self, ty: &Sort, budget: &Budget) -> Result<Bound, Error> {
        match ty.0[0].as_str() {
            Some("count") => Ok(Bound::Count(budget.natural_bits)),
            // Top is relative to the admitted byte budget, not the request policy.
            Some("vector") => Ok(Bound::Vector(budget.bytes)),
            Some("predicate") => Ok(Bound::Predicate),
            _ => Err(Error("unknown-type")),
        }
    }
    fn join(&self, a: &Bound, b: &Bound) -> Bound {
        match (a, b) {
            (Bound::Count(a), Bound::Count(b)) => Bound::Count((*a).max(*b)),
            (Bound::Vector(a), Bound::Vector(b)) => Bound::Vector((*a).max(*b)),
            _ => Bound::Predicate,
        }
    }
    fn estimate(
        &self,
        op: &Operation,
        args: &[Bound],
        budget: &Budget,
    ) -> Result<(Bound, Resources), Error> {
        let [arg] = args else {
            return Err(Error("invalid-value"));
        };
        let result = match (op, arg) {
            (Operation::Request, Bound::Count(bits)) if *bits <= budget.natural_bits => {
                Bound::Vector(VECTOR_LIMIT)
            }
            (Operation::Send | Operation::RequestAndSend, Bound::Count(bits))
                if *bits <= budget.natural_bits =>
            {
                Bound::Predicate
            }
            (Operation::Sum, Bound::Vector(n)) if *n <= VECTOR_LIMIT => Bound::Count(64),
            _ => return Err(Error("capacity-limit")),
        };
        let ordered = *op != Operation::Sum;
        // Conservative admission accounting: a retained result, three carrier
        // copies for arguments/dispatch/provider records, and object overhead.
        // The composite also owns an intermediate vector and a second call.
        // This estimates payloads, not an allocator-level peak-memory theorem;
        // reply allocation is separately fallible and retains the call prefix.
        let bytes = result
            .bytes()
            .checked_add(
                arg.bytes()
                    .checked_mul(3)
                    .ok_or(Error("capacity-overflow"))?,
            )
            .and_then(|n| n.checked_add(128))
            .and_then(|n| {
                n.checked_add(if *op == Operation::RequestAndSend {
                    VECTOR_LIMIT + 128
                } else {
                    0
                })
            })
            .ok_or(Error("capacity-overflow"))?;
        Ok((
            result,
            Resources {
                bytes,
                events: if *op == Operation::RequestAndSend {
                    2
                } else {
                    usize::from(ordered)
                },
                values: 1,
                ..Resources::default()
            },
        ))
    }
    fn reserve(&mut self, resources: Resources, budget: &Budget) -> Result<(), Error> {
        if resources.bytes > budget.bytes {
            return Err(Error("capacity-limit"));
        }
        self.events
            .try_reserve_exact(resources.events)
            .map_err(|_| Error("reservation-failed"))
    }
    fn begin_execution(&mut self) {
        self.events.clear();
    }
    fn invoke(&mut self, op: &Operation, args: &[Datum]) -> Result<Outcome<Datum>, Error> {
        if let (Operation::Sum, [Datum::Vector(xs)]) = (op, args) {
            return Ok(Outcome::Returned(Datum::Count(sum(xs))));
        }
        let [Datum::Count(n)] = args else {
            return Err(Error("invalid-value"));
        };
        if matches!(op, Operation::Request | Operation::RequestAndSend)
            && n > &BigUint::from(VECTOR_LIMIT)
        {
            return Ok(Outcome::Stopped(Stop::Refused));
        }
        match op {
            Operation::Request => self.call(Request::Vector, n),
            Operation::Send => self.call(Request::Send, n),
            Operation::RequestAndSend => {
                // call() has already checked this intermediate reply. The
                // generic dispatcher will only see the final predicate.
                match self.call(Request::Vector, n)? {
                    Outcome::Stopped(why) => Ok(Outcome::Stopped(why)),
                    Outcome::Returned(Datum::Vector(xs)) => self.call(Request::Send, &sum(&xs)),
                    Outcome::Returned(_) => Err(Error("invalid-value")),
                }
            }
            Operation::Sum => Err(Error("invalid-value")),
        }
    }
}
fn sum(xs: &[u8]) -> BigUint {
    xs.iter().map(|n| BigUint::from(*n)).sum()
}
// Static reply shape and request-dependent legality at the interface boundary.
// Provider value laws and transition correspondence are separate obligations.
fn check_reply(request: Request, n: &BigUint, reply: &Datum) -> Result<(), Error> {
    match (request, reply) {
        (Request::Vector, Datum::Vector(xs)) => {
            if xs.iter().any(|v| *v >= 7) {
                return Err(Error("noncanonical-scalar"));
            }
            if *n != BigUint::from(xs.len()) {
                return Err(Error("invalid-dependent-reply"));
            }
            Ok(())
        }
        (Request::Send, Datum::Predicate(b)) => {
            if *b != (n == &BigUint::default()) {
                return Err(Error("invalid-dependent-reply"));
            }
            Ok(())
        }
        _ => Err(Error("invalid-value")),
    }
}
impl Service {
    fn call(&mut self, request: Request, n: &BigUint) -> Result<Outcome<Datum>, Error> {
        self.calls += 1u8;
        self.events.push((request, n.clone()));
        let Some(seed) = self.tape.pop_front() else {
            return Ok(Outcome::Stopped(Stop::Exhausted));
        };
        let mut reply = match request {
            Request::Vector => {
                let count = n.to_usize().ok_or(Error("capacity-limit"))?;
                let mut values = Vec::new();
                values
                    .try_reserve_exact(count)
                    .map_err(|_| Error("reservation-failed"))?;
                values.resize(count, seed);
                Datum::Vector(values)
            }
            Request::Send => Datum::Predicate(n == &BigUint::default()),
        };
        if let Some((fault, at)) = &self.fault
            && *at == self.events.len()
        {
            match (fault.as_str(), &mut reply) {
                ("wrong-content", Datum::Vector(xs)) if !xs.is_empty() => {
                    xs[0] = (xs[0] + 1) % 7;
                }
                ("wrong-length", Datum::Vector(xs)) => {
                    if xs.is_empty() {
                        xs.push(0);
                    } else {
                        xs.pop();
                    }
                }
                ("noncanonical", Datum::Vector(xs)) => {
                    if xs.is_empty() {
                        xs.push(7);
                    } else {
                        xs[0] = 7;
                    }
                }
                ("wrong-flag", Datum::Predicate(b)) => *b = !*b,
                ("wrong-type", _) => reply = Datum::Count(BigUint::default()),
                _ => return Err(Error("inapplicable-fault")),
            }
        }
        check_reply(request, n, &reply)?;
        Ok(Outcome::Returned(reply))
    }
}
