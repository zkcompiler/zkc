//! Immutable shared dense storage that adopts its initialized allocation.
use std::{ops::Deref, sync::Arc};
use zkc_runtime::vm::Backing;

/// Read-only shared elements. Construction consumes a vector without moving its
/// elements or shrinking its allocation. Clones share the complete allocation.
/// The container exposes no mutable element or allocation access.
///
/// Native resource accounting includes retained capacity, including spare slots.
/// Construct with an exactly reserved vector when a tight bound is required.
#[derive(Debug, PartialEq, Eq)]
pub struct Buffer<T>(Arc<Vec<T>>);

impl<T> Buffer<T> {
    /// Number of element slots retained by this allocation.
    pub fn storage_capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Whether two buffers share the same immutable owner, including empty ones.
    pub fn ptr_eq(left: &Self, right: &Self) -> bool {
        Arc::ptr_eq(&left.0, &right.0)
    }

    pub(crate) fn backing(&self, bytes: usize) -> Backing {
        Backing::of(&self.0, bytes)
    }
}

impl<T> Clone for Buffer<T> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<T> Deref for Buffer<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        self.0.as_slice()
    }
}

impl<T> AsRef<[T]> for Buffer<T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> From<Vec<T>> for Buffer<T> {
    fn from(values: Vec<T>) -> Self {
        Self(Arc::new(values))
    }
}

impl<T, const N: usize> From<[T; N]> for Buffer<T> {
    fn from(values: [T; N]) -> Self {
        Vec::from(values).into()
    }
}

impl<T: Clone> From<&[T]> for Buffer<T> {
    fn from(values: &[T]) -> Self {
        values.to_vec().into()
    }
}

impl<T> Default for Buffer<T> {
    fn default() -> Self {
        Vec::new().into()
    }
}

impl<T> FromIterator<T> for Buffer<T> {
    fn from_iter<I: IntoIterator<Item = T>>(values: I) -> Self {
        Vec::from_iter(values).into()
    }
}

impl<'a, T> IntoIterator for &'a Buffer<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn publication_adopts_spare_capacity_and_clones_without_element_cloning() {
        #[derive(Debug)]
        struct Element(u64);
        let mut values = Vec::with_capacity(31);
        values.extend([Element(7), Element(11)]);
        let pointer = values.as_ptr();
        let capacity = values.capacity();
        let buffer = Buffer::from(values);
        let alias = buffer.clone();
        assert_eq!(buffer.as_ptr(), pointer);
        assert_eq!(buffer.storage_capacity(), capacity);
        assert!(Buffer::ptr_eq(&buffer, &alias));
        assert_eq!(alias.iter().map(|v| v.0).collect::<Vec<_>>(), [7, 11]);
    }

    #[test]
    fn independent_empty_and_equal_allocations_have_distinct_owners() {
        for original in [Buffer::<u64>::default(), [7, 11].into()] {
            let alias = original.clone();
            let independent = Buffer::from(original.to_vec());
            assert_eq!(original, independent);
            assert_eq!(original.backing(512), alias.backing(512));
            assert_ne!(original.backing(512), independent.backing(512));
        }
    }
}
