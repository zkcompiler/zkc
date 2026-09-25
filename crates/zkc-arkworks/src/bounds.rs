use crate::Error;

/// Explicit finite admission policy; there is no implicit permanent arity cap.
///
/// Limits are per operation/object, not a reservation or total session budget.
/// Zero limits are useful to deny a class of ingress. Host representability
/// checks apply even when the policy limits are larger.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    max_arity: usize,
    max_table_elements: usize,
    max_artifact_bytes: usize,
    max_setup_cells: usize,
}

impl Bounds {
    /// Select arity, table-element, wire-byte, and `n * 2^n` setup-work limits.
    /// `max_setup_cells` bounds an upstream setup work measure, **not** its
    /// peak byte allocation. The PCS allocates additional field/group scratch.
    pub const fn new(
        max_arity: usize,
        max_table_elements: usize,
        max_artifact_bytes: usize,
        max_setup_cells: usize,
    ) -> Self {
        Self {
            max_arity,
            max_table_elements,
            max_artifact_bytes,
            max_setup_cells,
        }
    }

    pub(crate) fn arity(&self, n: usize) -> Result<(), Error> {
        if n > self.max_arity {
            return Err(Error::ArityLimit);
        }
        Ok(())
    }

    pub(crate) fn table(&self, n: usize) -> Result<usize, Error> {
        self.arity(n)?;
        let shift = u32::try_from(n).map_err(|_| Error::CapacityOverflow)?;
        let len = 1usize.checked_shl(shift).ok_or(Error::CapacityOverflow)?;
        if len > self.max_table_elements {
            return Err(Error::ElementLimit);
        }
        allocation_size::<crate::Scalar>(len)?;
        Ok(len)
    }

    pub(crate) fn table_length(&self, len: usize) -> Result<usize, Error> {
        if !len.is_power_of_two() {
            return Err(Error::InvalidTableLength);
        }
        let n = len.trailing_zeros() as usize;
        self.table(n)?;
        Ok(n)
    }

    pub(crate) fn bytes(&self, bytes: usize) -> Result<(), Error> {
        if bytes > self.max_artifact_bytes {
            return Err(Error::ByteLimit);
        }
        allocation_size::<u8>(bytes)?;
        Ok(())
    }

    pub(crate) fn pcs_arity(&self, n: usize) -> Result<(), Error> {
        if n == 0 {
            return Err(Error::PositiveArityRequired);
        }
        self.table(n)?;
        Ok(())
    }

    pub(crate) fn setup(&self, n: usize) -> Result<(), Error> {
        self.pcs_arity(n)?;
        let len = self.table(n)?;
        let cells = n.checked_mul(len).ok_or(Error::CapacityOverflow)?;
        if cells > self.max_setup_cells {
            return Err(Error::SetupLimit);
        }
        allocation_size::<crate::Scalar>(cells)?;
        let bases = len
            .checked_mul(2)
            .and_then(|v| v.checked_sub(2))
            .ok_or(Error::CapacityOverflow)?;
        allocation_size::<ark_bls12_381::G1Affine>(bases)?;
        allocation_size::<ark_bls12_381::G2Affine>(bases)?;
        Ok(())
    }
}

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
    VECTOR_REQUESTS.with(|count| count.set(count.get() + 1));
    allocation_size::<T>(len)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(len)
        .map_err(|_| Error::Allocation)?;
    Ok(values)
}

#[cfg(test)]
std::thread_local! {
    // Count wrapper allocation attempts, including failures, on this test's
    // thread. This does not instrument Arc or upstream infallible allocations.
    pub(crate) static VECTOR_REQUESTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
