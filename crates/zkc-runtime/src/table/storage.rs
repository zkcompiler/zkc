use super::{Domain, Type};
use crate::{
    Error,
    arena::{Arena, Handle},
    buffer::BufferStore,
    format::{array, list, natural, number},
};
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use serde_json::{Value as Json, json};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub enum Value {
    Boolean(bool),
    Scalar(Domain, u8),
    /// Internal physical scalar reference. Never accepted by the logical input codec.
    ScalarReference(Domain, Handle),
    Digest(Arc<BigUint>),
    Summary(u8, u8, Arc<BigUint>),
    Table(Handle),
    Residual(Handle),
    Point(Handle),
}
pub(super) const MAX_RANK: usize = 12;

pub(super) struct Buffer<R> {
    reference: R,
    pub length: usize,
}
pub(super) struct Root<R> {
    pub domain: Domain,
    pub rank: usize,
    pub origin: BigUint,
    pub cells: Buffer<R>,
}
pub(super) enum Object<R> {
    Root(Root<R>),
    Residual {
        root: Handle,
        coordinates: Buffer<R>,
    },
    Point {
        domain: Domain,
        coordinates: Buffer<R>,
    },
    Scalar {
        domain: Domain,
        cell: ScalarCell<R>,
    },
}
pub(super) enum ScalarCell<R> {
    Materialized(Buffer<R>),
    Deferred { residual: Handle, point: Handle },
}
pub(super) struct Storage<S: BufferStore<u8>> {
    pub arena: Arena<Object<S::Reference>>,
    pub cells: S,
}
pub(super) fn rank(n: &BigUint) -> Result<usize, Error> {
    n.to_usize()
        .filter(|n| *n <= MAX_RANK)
        .ok_or(Error("input-rank-limit"))
}
pub(super) fn scalar(d: Domain, json: &Json) -> Result<u8, Error> {
    natural(json)?
        .to_u8()
        .filter(|n| *n < d.modulus())
        .ok_or(Error("noncanonical-scalar"))
}
impl<S: BufferStore<u8>> Storage<S> {
    pub fn new(cells: S) -> Result<Self, Error> {
        Ok(Self {
            arena: Arena::new()?,
            cells,
        })
    }
    fn input_cells(&mut self, d: Domain, json: &Json) -> Result<Buffer<S::Reference>, Error> {
        let values = list(json)?;
        if self
            .cells
            .usage()
            .elements
            .checked_add(values.len())
            .ok_or(Error("input-capacity"))?
            > 1024 * 1024
        {
            return Err(Error("input-capacity"));
        }
        let cells = values
            .iter()
            .map(|v| scalar(d, v))
            .collect::<Result<Vec<_>, _>>()?;
        self.cells.reserve(cells.len(), 1)?;
        self.publish_cells(&cells)
    }
    pub fn publish_cells(&mut self, cells: &[u8]) -> Result<Buffer<S::Reference>, Error> {
        Ok(Buffer {
            reference: self.cells.publish(cells)?,
            length: cells.len(),
        })
    }
    pub fn read_cells(&self, buffer: &Buffer<S::Reference>) -> Result<&[u8], Error> {
        let cells = self.cells.read(&buffer.reference)?;
        if cells.len() != buffer.length {
            return Err(Error("buffer-contract-violation"));
        }
        Ok(cells)
    }
    pub fn input(&mut self, ty: &Type, json: &Json) -> Result<Value, Error> {
        use Type as T;
        self.arena.reserve(2)?;
        Ok(match ty {
            T::Boolean => Value::Boolean(json.as_bool().ok_or(Error("expected-boolean"))?),
            T::Scalar(d) => Value::Scalar(*d, scalar(*d, json)?),
            T::Digest => Value::Digest(Arc::new(natural(json)?)),
            T::Summary => {
                let a = array(json, 3)?;
                Value::Summary(
                    scalar(Domain::Two, &a[0])?,
                    scalar(Domain::Seven, &a[1])?,
                    Arc::new(natural(&a[2])?),
                )
            }
            T::Point(d) => {
                let coordinates = self.input_cells(*d, json)?;
                Value::Point(self.arena.publish(Object::Point {
                    domain: *d,
                    coordinates,
                })?)
            }
            T::Table(d, n) | T::Residual(d, n) => {
                let rank = rank(n)?;
                let residual = matches!(ty, T::Residual(..));
                let a = array(json, if residual { 3 } else { 2 })?;
                let origin = natural(&a[0])?;
                if list(&a[1])?.len() != 1usize << rank {
                    return Err(Error("invalid-table-shape"));
                }
                let cells = self.input_cells(*d, &a[1])?;
                let root = self.arena.publish(Object::Root(Root {
                    domain: *d,
                    rank,
                    origin,
                    cells,
                }))?;
                if residual {
                    if list(&a[2])?.len() > rank {
                        return Err(Error("invalid-residual-shape"));
                    }
                    let coordinates = self.input_cells(*d, &a[2])?;
                    Value::Residual(self.arena.publish(Object::Residual { root, coordinates })?)
                } else {
                    Value::Table(root)
                }
            }
        })
    }
    pub fn view(&mut self, root: Handle) -> Result<Value, Error> {
        self.root(root)?;
        let coordinates = self.publish_cells(&[])?;
        Ok(Value::Residual(
            self.arena.publish(Object::Residual { root, coordinates })?,
        ))
    }
    pub fn restrict(&mut self, value: &Value, coordinate: u8) -> Result<Option<Value>, Error> {
        let (root, coordinates) = self.residual(value)?;
        let n = self.root(root)?.rank;
        if coordinates.length >= n {
            return Ok(None);
        }
        // This finite profile admits ranks at most 12. Copy only the ordered
        // prefix; do not copy or overwrite original cells or earlier views.
        let mut extended = [0; MAX_RANK];
        let size = coordinates.length;
        let coordinates = self.read_cells(coordinates)?;
        extended[..size].copy_from_slice(coordinates);
        extended[size] = coordinate;
        let coordinates = self.publish_cells(&extended[..size + 1])?;
        Ok(Some(Value::Residual(
            self.arena.publish(Object::Residual { root, coordinates })?,
        )))
    }
    pub fn root(&self, handle: Handle) -> Result<&Root<S::Reference>, Error> {
        match self.arena.resolve(handle)? {
            Object::Root(root) => Ok(root),
            _ => Err(Error("handle-kind-mismatch")),
        }
    }
    pub fn residual(&self, value: &Value) -> Result<(Handle, &Buffer<S::Reference>), Error> {
        let Value::Residual(handle) = value else {
            return Err(Error("value-kind-mismatch"));
        };
        match self.arena.resolve(*handle)? {
            Object::Residual { root, coordinates } => Ok((*root, coordinates)),
            _ => Err(Error("handle-kind-mismatch")),
        }
    }
    pub fn point(&self, value: &Value) -> Result<(Domain, &Buffer<S::Reference>), Error> {
        let Value::Point(handle) = value else {
            return Err(Error("value-kind-mismatch"));
        };
        match self.arena.resolve(*handle)? {
            Object::Point {
                domain,
                coordinates,
            } => Ok((*domain, coordinates)),
            _ => Err(Error("handle-kind-mismatch")),
        }
    }
    pub fn validate(&self, ty: &Type, value: &Value) -> Result<(), Error> {
        use Type as T;
        let valid = match (ty, value) {
            (T::Boolean, Value::Boolean(_)) => true,
            (T::Scalar(d), Value::Scalar(actual, x)) => d == actual && *x < d.modulus(),
            (T::Digest, Value::Digest(_)) => true,
            (T::Summary, Value::Summary(a, b, _)) => *a < 2 && *b < 7,
            (T::Table(d, n), Value::Table(h)) => {
                let r = self.root(*h)?;
                r.domain == *d && n.to_usize() == Some(r.rank)
            }
            (T::Residual(d, n), Value::Residual(_)) => {
                let (h, c) = self.residual(value)?;
                let r = self.root(h)?;
                r.domain == *d && n.to_usize() == Some(r.rank) && c.length <= r.rank
            }
            (T::Point(d), Value::Point(_)) => self.point(value)?.0 == *d,
            _ => false,
        };
        if valid {
            Ok(())
        } else {
            Err(Error("value-type-mismatch"))
        }
    }
    pub fn json(&self, value: &Value) -> Result<Json, Error> {
        Ok(match value {
            Value::Boolean(x) => json!(x),
            Value::Scalar(_, x) => json!(x),
            Value::ScalarReference(..) => return Err(Error("physical-reference-needs-owner-read")),
            Value::Digest(n) => number(n),
            Value::Summary(a, b, n) => json!([a, b, number(n)]),
            Value::Point(_) => {
                let (_, c) = self.point(value)?;
                json!(self.read_cells(c)?)
            }
            Value::Table(h) => {
                let r = self.root(*h)?;
                json!([number(&r.origin), self.read_cells(&r.cells)?])
            }
            Value::Residual(_) => {
                let (h, c) = self.residual(value)?;
                let r = self.root(h)?;
                json!([
                    number(&r.origin),
                    self.read_cells(&r.cells)?,
                    self.read_cells(c)?
                ])
            }
        })
    }
}
