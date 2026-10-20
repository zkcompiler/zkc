use crate::{Result, exhausted};
use std::{cell::Cell, mem::size_of};

/// A stack guard; no registry or shared ownership is needed for a borrowed call.
pub(super) struct Reservation<'a> {
    counter: &'a Cell<usize>,
    bytes: usize,
}

impl<'a> Reservation<'a> {
    pub(super) fn new(
        counter: &'a Cell<usize>,
        bytes: usize,
        limit: usize,
        reason: &str,
    ) -> Result<Self> {
        let next = counter
            .get()
            .checked_add(bytes)
            .filter(|next| *next <= limit)
            .ok_or_else(|| exhausted(reason))?;
        counter.set(next);
        Ok(Self { counter, bytes })
    }

    /// Leave a finished result charged until the enclosing Call itself is dropped.
    pub(super) fn keep(mut self) {
        self.bytes = 0;
    }
}

impl Drop for Reservation<'_> {
    fn drop(&mut self) {
        self.counter.set(
            self.counter
                .get()
                .checked_sub(self.bytes)
                .expect("live numerical reservation"),
        );
    }
}

pub(super) fn payload_bytes<T>(len: usize) -> Result<usize> {
    len.checked_mul(size_of::<T>())
        .filter(|bytes| *bytes <= isize::MAX as usize)
        .ok_or_else(|| exhausted("numerical-bytes"))
}

/// Data precedes its guard so abandoned storage is freed before its charge.
pub(super) struct Buffer<'a, T> {
    pub(super) data: Vec<T>,
    pub(super) reservation: Reservation<'a>,
}

impl<'a, T: Clone> Buffer<'a, T> {
    pub(super) fn new(len: usize, initial: T, reservation: Reservation<'a>) -> Result<Self> {
        let mut data = crate::allocation::reserve(len).map_err(|_| exhausted("allocation"))?;
        data.resize(len, initial);
        Ok(Self { data, reservation })
    }
}
