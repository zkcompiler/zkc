use super::{BufferStore, BufferUsage, add, bytes};
use crate::{
    Error,
    arena::{Arena, Handle},
};
use std::ops::Range;

struct Span {
    segment: Option<usize>,
    range: Range<usize>,
}
/// Retained reservation segments. Growing capacity never relocates old payload
/// allocations. Unused capacity in earlier segments remains accounted for.
pub struct SegmentedBuffers<T> {
    segments: Vec<Vec<T>>,
    references: Arena<Span>,
    elements: usize,
}
impl<T> SegmentedBuffers<T> {
    pub fn new() -> Result<Self, Error> {
        Ok(Self {
            segments: Vec::new(),
            references: Arena::new()?,
            elements: 0,
        })
    }
    fn needs_segment(&self, additional: usize) -> bool {
        additional > self.segments.last().map_or(0, |s| s.capacity() - s.len())
    }
}
impl<T: Copy> BufferStore<T> for SegmentedBuffers<T> {
    type Reference = Handle;
    fn required_bytes(&self, elements: usize, buffers: usize) -> Result<usize, Error> {
        add(self.elements, elements)?;
        let mut capacity = self
            .segments
            .iter()
            .try_fold(0, |total, s| add(total, s.capacity()))?;
        let extra = usize::from(self.needs_segment(elements));
        if extra != 0 {
            capacity = add(capacity, elements)?;
        }
        let segments = self
            .segments
            .capacity()
            .max(add(self.segments.len(), extra)?);
        let buffers = self
            .references
            .capacity()
            .max(add(self.references.len(), buffers)?);
        add(
            add(bytes::<T>(capacity)?, bytes::<Vec<T>>(segments)?)?,
            bytes::<Span>(buffers)?,
        )
    }
    fn reserve(&mut self, elements: usize, buffers: usize) -> Result<(), Error> {
        self.required_bytes(elements, buffers)?;
        self.references.reserve(buffers)?;
        if self.needs_segment(elements) {
            self.segments
                .try_reserve_exact(1)
                .map_err(|_| Error("reservation-failed"))?;
            let mut segment = Vec::new();
            segment
                .try_reserve_exact(elements)
                .map_err(|_| Error("reservation-failed"))?;
            self.segments.push(segment);
        }
        Ok(())
    }
    fn publish(&mut self, values: &[T]) -> Result<Handle, Error> {
        if self.needs_segment(values.len()) || self.references.len() == self.references.capacity() {
            return Err(Error("buffer-capacity-violation"));
        }
        let elements = add(self.elements, values.len())?;
        let span = if values.is_empty() {
            Span {
                segment: None,
                range: 0..0,
            }
        } else {
            let index = self.segments.len() - 1;
            let segment = &mut self.segments[index];
            let start = segment.len();
            segment.extend_from_slice(values);
            Span {
                segment: Some(index),
                range: start..segment.len(),
            }
        };
        let reference = self.references.publish(span)?;
        self.elements = elements;
        Ok(reference)
    }
    fn read(&self, reference: &Handle) -> Result<&[T], Error> {
        let span = self.references.resolve(*reference)?;
        match span.segment {
            None => Ok(&[]),
            Some(index) => self
                .segments
                .get(index)
                .and_then(|s| s.get(span.range.clone()))
                .ok_or(Error("invalid-buffer-range")),
        }
    }
    fn usage(&self) -> BufferUsage {
        BufferUsage {
            elements: self.elements,
            buffers: self.references.len(),
            reserved_bytes: self
                .required_bytes(0, 0)
                .expect("allocated capacity fits usize"),
        }
    }
}
