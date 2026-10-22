use super::Error;

pub(crate) fn allocation_size<T>(len: usize) -> Result<usize, Error> {
    let bytes = len
        .checked_mul(std::mem::size_of::<T>())
        .ok_or(Error::CapacityOverflow)?;
    if bytes > isize::MAX as usize {
        return Err(Error::CapacityOverflow);
    }
    Ok(bytes)
}

pub(crate) fn vector<T>(len: usize) -> Result<Vec<T>, Error> {
    #[cfg(test)]
    {
        VECTOR_REQUESTS.with(|count| count.set(count.get() + 1));
        let fail = VECTOR_FAILURE.with(|remaining| match remaining.get() {
            Some(0) => {
                remaining.set(None);
                true
            }
            Some(n) => {
                remaining.set(Some(n - 1));
                false
            }
            None => false,
        });
        if fail {
            return Err(Error::Allocation);
        }
    }
    allocation_size::<T>(len)?;
    crate::allocation::reserve(len).map_err(|_| Error::Allocation)
}

#[cfg(test)]
std::thread_local! {
    // Count wrapper allocation attempts, including failures, on this test's
    // thread. This does not instrument Arc or upstream infallible allocations.
    pub(crate) static VECTOR_REQUESTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    pub(crate) static VECTOR_FAILURE: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}
