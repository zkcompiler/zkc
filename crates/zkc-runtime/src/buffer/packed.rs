use super::{BufferStore, BufferUsage, add, bytes};
use crate::{
    Error,
    arena::{Arena, Handle},
};
use std::ops::Range;

/// One append-only payload vector. References remain valid if reservation
/// relocates the vector; only checked offsets, not pointers, are retained.
pub struct PackedBuffers<T> {
    data: Vec<T>,
    references: Arena<Range<usize>>,
}
impl<T> PackedBuffers<T> {
    pub fn new() -> Result<Self, Error> {
        Ok(Self {
            data: Vec::new(),
            references: Arena::new()?,
        })
    }
}
impl<T: Copy> BufferStore<T> for PackedBuffers<T> {
    type Reference = Handle;
    fn required_bytes(&self, elements: usize, buffers: usize) -> Result<usize, Error> {
        let elements = self.data.capacity().max(add(self.data.len(), elements)?);
        let buffers = self
            .references
            .capacity()
            .max(add(self.references.len(), buffers)?);
        add(bytes::<T>(elements)?, bytes::<Range<usize>>(buffers)?)
    }
    fn reserve(&mut self, elements: usize, buffers: usize) -> Result<(), Error> {
        self.required_bytes(elements, buffers)?;
        self.data
            .try_reserve_exact(elements)
            .map_err(|_| Error("reservation-failed"))?;
        self.references.reserve(buffers)
    }
    fn publish(&mut self, values: &[T]) -> Result<Handle, Error> {
        let start = self.data.len();
        let end = add(start, values.len())?;
        if end > self.data.capacity() || self.references.len() == self.references.capacity() {
            return Err(Error("buffer-capacity-violation"));
        }
        self.data.extend_from_slice(values);
        self.references.publish(start..end)
    }
    fn read(&self, reference: &Handle) -> Result<&[T], Error> {
        let range = self.references.resolve(*reference)?;
        self.data
            .get(range.clone())
            .ok_or(Error("invalid-buffer-range"))
    }
    fn usage(&self) -> BufferUsage {
        BufferUsage {
            elements: self.data.len(),
            buffers: self.references.len(),
            reserved_bytes: self
                .required_bytes(0, 0)
                .expect("allocated capacity fits usize"),
        }
    }
}
