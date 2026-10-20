//! Fallible reservations for adapter-owned vectors; provider internals are separate.
use std::collections::TryReserveError;

pub(crate) fn reserve<T>(capacity: usize) -> Result<Vec<T>, TryReserveError> {
    #[cfg(test)]
    if failure::reached() {
        // Produce the standard capacity error without asking the allocator for memory.
        return Err(Vec::<u8>::new().try_reserve_exact(usize::MAX).unwrap_err());
    }
    let mut values = Vec::new();
    values.try_reserve_exact(capacity)?;
    Ok(values)
}

#[cfg(test)]
pub(crate) mod failure {
    use std::cell::Cell;

    thread_local! {
        static REMAINING: Cell<Option<usize>> = const { Cell::new(None) };
    }

    pub(crate) struct Guard(Option<usize>);

    /// Fail one adapter reservation after `successful` reservations on this thread.
    pub(crate) fn after(successful: usize) -> Guard {
        Guard(REMAINING.replace(Some(successful)))
    }

    pub(super) fn reached() -> bool {
        REMAINING.with(|remaining| match remaining.get() {
            Some(0) => {
                remaining.set(None);
                true
            }
            Some(n) => {
                remaining.set(Some(n - 1));
                false
            }
            None => false,
        })
    }

    impl Drop for Guard {
        fn drop(&mut self) {
            REMAINING.set(self.0);
        }
    }
}
