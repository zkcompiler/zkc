//! Monotone invocation storage. Handles are internal references, not serialized
//! credentials. A completion keeps the arena alive behind every returned borrow.
use crate::Error;
use std::sync::atomic::{AtomicU64, Ordering};
static NEXT_SESSION: AtomicU64 = AtomicU64::new(1);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Handle {
    session: u64,
    slot: usize,
    generation: u64,
}
#[derive(Debug)]
pub struct Arena<T> {
    session: u64,
    values: Vec<T>,
}
impl<T> Arena<T> {
    pub fn new() -> Result<Self, Error> {
        let session = NEXT_SESSION
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
            .map_err(|_| Error("session-identity-exhausted"))?;
        Ok(Self {
            session,
            values: Vec::new(),
        })
    }
    pub fn len(&self) -> usize {
        self.values.len()
    }
    pub fn capacity(&self) -> usize {
        self.values.capacity()
    }
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
    pub fn reserve(&mut self, additional: usize) -> Result<(), Error> {
        self.values
            .try_reserve_exact(additional)
            .map_err(|_| Error("reservation-failed"))
    }
    pub fn publish(&mut self, value: T) -> Result<Handle, Error> {
        if self.values.len() == self.values.capacity() {
            return Err(Error("arena-capacity-violation"));
        }
        let handle = Handle {
            session: self.session,
            slot: self.values.len(),
            generation: 0,
        };
        self.values.push(value);
        Ok(handle)
    }
    pub fn resolve(&self, handle: Handle) -> Result<&T, Error> {
        if handle.session != self.session {
            return Err(Error("foreign-handle"));
        }
        if handle.generation != 0 {
            return Err(Error("stale-handle"));
        }
        self.values.get(handle.slot).ok_or(Error("invalid-handle"))
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn handles_resolve_and_foreign_stale_and_out_of_range_handles_are_refused() {
        let mut a = Arena::new().unwrap();
        a.reserve(3).unwrap();
        let first = a.publish(7).unwrap();
        let second = a.publish(9).unwrap();
        assert_eq!(*a.resolve(first).unwrap(), 7);
        assert_eq!(*a.resolve(second).unwrap(), 9);
        let b: Arena<u8> = Arena::new().unwrap();
        assert_eq!(b.resolve(first), Err(Error("foreign-handle")));
        assert_eq!(
            a.resolve(Handle {
                generation: 1,
                ..first
            }),
            Err(Error("stale-handle"))
        );
        assert_eq!(
            a.resolve(Handle {
                slot: a.len(),
                ..first
            }),
            Err(Error("invalid-handle"))
        );
    }
}
