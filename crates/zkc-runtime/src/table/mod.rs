//! Finite field/table interpretation used to exercise the generic runtime.
//! Its handler is a deterministic trace, not a cryptographic challenger.
use crate::buffer::{BufferStore, BufferUsage, PackedBuffers};
mod bounds;
mod endpoint;
mod execution;
pub use endpoint::{ENDPOINT_PROFILE, Phase};
mod kernel;
mod language;
mod physical;
mod provider;
pub use physical::{
    PhysicalBound, PhysicalOperation, PhysicalTableBindings, PhysicalTableLibrary, Preparation,
};
mod storage;
use crate::{Bindings, Budget, Error, Library, Outcome, Resources, Sort, format};
pub use bounds::Bound;
pub use kernel::{FieldKernel, SmallPrimeKernel};
pub use language::{Domain, Operation, TableLibrary, Type};
use num_bigint::BigUint;
pub use provider::{ChallengeProvider, TapeProvider};
use serde_json::{Value as Json, json};
use std::sync::OnceLock;
pub use storage::Value;

#[derive(Clone, Copy)]
enum Event {
    Write(Domain, u8),
    Sent(u8, u8),
    Drawn(u8),
}
impl Event {
    fn json(self) -> Json {
        match self {
            Self::Write(d, x) => json!(["write", d.name(), x]),
            Self::Sent(a, b) => json!(["sent", a, b]),
            Self::Drawn(x) => json!(["drawn", x]),
        }
    }
}

#[derive(Debug)]
pub struct State {
    pub two: u8,
    pub seven: u8,
    pub writes: BigUint,
    pub sent: Vec<(u8, u8)>,
}
impl State {
    pub fn decode(value: &Json) -> Result<(Self, TapeProvider), Error> {
        let a = format::array(value, 5)?;
        let sent = format::list(&a[3])?
            .iter()
            .map(|pair| {
                let p = format::array(pair, 2)?;
                Ok((
                    storage::scalar(Domain::Seven, &p[0])?,
                    storage::scalar(Domain::Seven, &p[1])?,
                ))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        let tape = format::list(&a[4])?
            .iter()
            .map(|v| storage::scalar(Domain::Seven, v))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((
            Self {
                two: storage::scalar(Domain::Two, &a[0])?,
                seven: storage::scalar(Domain::Seven, &a[1])?,
                writes: format::natural(&a[2])?,
                sent,
            },
            TapeProvider::new(tape)?,
        ))
    }
}
pub struct TableBindings<
    K = SmallPrimeKernel,
    P = TapeProvider,
    S: BufferStore<u8> = PackedBuffers<u8>,
> {
    storage: storage::Storage<S>,
    kernel: K,
    provider: P,
    state: State,
    events: Vec<Event>,
    event_json: OnceLock<Vec<Json>>,
    // Count writes without reallocating an arbitrary-precision integer during
    // execution. The logical count is state.writes + additional_writes.
    additional_writes: u64,
    scratch: Vec<u8>,
    event_limit: usize,
    endpoint: Option<endpoint::Endpoint>,
}
impl<K: FieldKernel, P: ChallengeProvider> TableBindings<K, P> {
    pub fn new(kernel: K, provider: P, state: State) -> Result<Self, Error> {
        Self::with_storage(kernel, provider, state, PackedBuffers::new()?)
    }
}
impl<K: FieldKernel, P: ChallengeProvider, S: BufferStore<u8>> TableBindings<K, P, S> {
    pub fn with_storage(kernel: K, provider: P, state: State, cells: S) -> Result<Self, Error> {
        if state.two >= 2
            || state.seven >= 7
            || state.sent.iter().any(|(a, b)| *a >= 7 || *b >= 7)
            || state.writes.bits() > bounds::INPUT_NATURAL_BITS as u64
        {
            return Err(Error("invalid-state"));
        }
        Ok(Self {
            storage: storage::Storage::new(cells)?,
            kernel,
            provider,
            state,
            events: Vec::new(),
            event_json: OnceLock::new(),
            additional_writes: 0,
            scratch: Vec::new(),
            event_limit: 0,
            endpoint: None,
        })
    }
    pub fn buffer_usage(&self) -> BufferUsage {
        self.storage.cells.usage()
    }
    pub fn value_json(&self, value: &Value) -> Result<Json, Error> {
        self.storage.json(value)
    }
    pub fn state_json(&self) -> Json {
        let state = json!([
            self.state.two,
            self.state.seven,
            format::number(&(&self.state.writes + self.additional_writes)),
            self.state.sent,
            self.provider.remaining()
        ]);
        match &self.endpoint {
            Some(endpoint) => json!([endpoint.role, endpoint.phase.name(), state]),
            None => state,
        }
    }
    pub fn events(&self) -> &[Json] {
        // Encoding belongs to host reporting, after the modeled operation.
        self.event_json
            .get_or_init(|| self.events.iter().map(|e| e.json()).collect())
    }
    fn reserved_bytes(&self, r: Resources) -> Result<usize, Error> {
        use crate::buffer::{add, bytes};
        let objects = self
            .storage
            .arena
            .capacity()
            .max(add(self.storage.arena.len(), r.values)?);
        let messages = self
            .state
            .sent
            .capacity()
            .max(add(self.state.sent.len(), r.events)?);
        let events = self.events.capacity().max(r.events);
        let scratch = self.scratch.capacity().max(r.scratch);
        let metadata = add(
            bytes::<storage::Object<S::Reference>>(objects)?,
            bytes::<Event>(events)?,
        )?;
        let state = add(
            bytes::<(u8, u8)>(messages)?,
            self.provider.remaining().len(),
        )?;
        add(
            add(
                add(
                    self.storage.cells.required_bytes(r.bytes, r.values)?,
                    metadata,
                )?,
                state,
            )?,
            scratch,
        )
    }
    fn event(&mut self, event: Event) -> Result<(), Error> {
        if self.events.len() >= self.event_limit {
            return Err(Error("event-bound-violation"));
        }
        self.events.push(event);
        self.event_json.take();
        Ok(())
    }
}
impl<K, P, S: BufferStore<u8>> Library for TableBindings<K, P, S> {
    type Operation = Operation;
    fn condition_sort(&self) -> Sort {
        TableLibrary.condition_sort()
    }
    fn sort(&self, v: &Json) -> Result<Sort, Error> {
        TableLibrary.sort(v)
    }
    fn operation(&self, v: &Json) -> Result<Operation, Error> {
        TableLibrary.operation(v)
    }
    fn signature(&self, op: &Operation) -> (Vec<Sort>, Sort) {
        TableLibrary.signature(op)
    }
    fn dependencies(&self) -> Json {
        TableLibrary.dependencies()
    }
}
impl<K: FieldKernel, P: ChallengeProvider, S: BufferStore<u8>> Bindings for TableBindings<K, P, S> {
    type Value = Value;
    type Bound = Bound;
    fn validate_entry(
        &self,
        role: &str,
        evidence: Option<&crate::PhaseEvidence>,
    ) -> Result<(), Error> {
        self.check_entry(role, evidence)
    }
    fn validate_result(&self, _: &Operation, _: &[Value], _: &Value) -> Result<(), Error> {
        // This profile has no request-dependent reply shape. Static value
        // validation already enforces its domain and storage invariants.
        Ok(())
    }
    fn input(&mut self, sort: &Sort, json: &Json) -> Result<Value, Error> {
        let ty = Type::decode(&sort.0)?;
        let value = self.storage.input(&ty, json)?;
        let numbers = match &value {
            Value::Digest(n) | Value::Summary(_, _, n) => Some(n.as_ref()),
            _ => None,
        };
        if numbers.is_some_and(|n| n.bits() > bounds::INPUT_NATURAL_BITS as u64) {
            return Err(Error("input-natural-limit"));
        }
        Ok(value)
    }
    fn validate(&self, sort: &Sort, value: &Value) -> Result<(), Error> {
        self.storage.validate(&Type::decode(&sort.0)?, value)
    }
    fn condition(&self, value: &Value) -> Result<bool, Error> {
        match value {
            Value::Boolean(x) => Ok(*x),
            _ => Err(Error("expected-boolean")),
        }
    }
    fn bound(&self, value: &Value) -> Result<Bound, Error> {
        self.value_bound(value)
    }
    fn top(&self, sort: &Sort, budget: &Budget) -> Result<Bound, Error> {
        Bound::for_type(Type::decode(&sort.0)?, budget.natural_bits)
    }
    fn join(&self, a: &Bound, b: &Bound) -> Bound {
        Bound {
            ty: a.ty.clone(),
            point_len: a.point_len.max(b.point_len),
            bits: a.bits.max(b.bits),
        }
    }
    fn estimate(
        &self,
        op: &Operation,
        args: &[Bound],
        budget: &Budget,
    ) -> Result<(Bound, Resources), Error> {
        self.operation_bound(op, args, budget)
    }
    fn reserve(&mut self, r: Resources, budget: &Budget) -> Result<(), Error> {
        self.additional_writes
            .checked_add(
                r.events
                    .try_into()
                    .map_err(|_| Error("capacity-overflow"))?,
            )
            .ok_or(Error("capacity-overflow"))?;
        if self.reserved_bytes(r)? > budget.bytes {
            return Err(Error("capacity-limit"));
        }
        if bounds::INPUT_NATURAL_BITS + 64 > budget.natural_bits {
            return Err(Error("natural-capacity-limit"));
        }
        self.storage.arena.reserve(r.values)?;
        self.storage.cells.reserve(r.bytes, r.values)?;
        self.scratch
            .try_reserve_exact(r.scratch.saturating_sub(self.scratch.len()))
            .map_err(|_| Error("reservation-failed"))?;
        self.events
            .try_reserve_exact(r.events.saturating_sub(self.events.len()))
            .map_err(|_| Error("reservation-failed"))?;
        self.state
            .sent
            .try_reserve_exact(r.events)
            .map_err(|_| Error("reservation-failed"))?;
        // Vec and third-party stores may reserve more than their requested
        // minimum. Observe actual retained capacity before modeled execution.
        if self.reserved_bytes(Resources::default())? > budget.bytes {
            return Err(Error("capacity-limit"));
        }
        self.event_limit = r.events;
        Ok(())
    }
    fn begin_execution(&mut self) {
        self.events.clear();
        self.event_json.take();
    }
    fn invoke(&mut self, op: &Operation, args: &[Value]) -> Result<Outcome<Value>, Error> {
        let (sorts, _) = self.signature(op);
        if args.len() != sorts.len() {
            return Err(Error("backend-argument-count"));
        }
        for (sort, value) in sorts.iter().zip(args) {
            self.validate(sort, value)?;
        }
        self.invoke_table(op, args)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn repeated_reservation_reuses_existing_scratch() {
        let mut bindings = TableBindings::new(
            SmallPrimeKernel,
            TapeProvider::new(vec![]).unwrap(),
            State {
                two: 0,
                seven: 0,
                writes: 0u8.into(),
                sent: vec![],
            },
        )
        .unwrap();
        bindings.scratch = vec![0; 4096];
        let before = bindings.scratch.capacity();
        bindings
            .reserve(
                Resources {
                    scratch: 4096,
                    ..Resources::default()
                },
                &Budget::default(),
            )
            .unwrap();
        assert_eq!(bindings.scratch.capacity(), before);
    }
}
