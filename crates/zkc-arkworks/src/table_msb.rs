use crate::{Bounds, Error, Scalar, Table, bounds::vector, error::same_arity};
use ark_ff::{AdditiveGroup, Field};
use std::sync::Arc;

/// Immutable multilinear evaluations in logical MSB-first storage order.
/// Arithmetic uses Arkworks scalars; this is a table representation and kernel
/// implementation, not a separate field or commitment implementation.
#[derive(Clone, Debug)]
pub struct MsbTable {
    values: Arc<Vec<Scalar>>,
    arity: usize,
}

impl MsbTable {
    /// Check shape and bounds, then copy evaluations into immutable storage.
    pub fn from_logical(values: &[Scalar], bounds: &Bounds) -> Result<Self, Error> {
        bounds.table_length(values.len())?;
        let mut owned = vector(values.len())?;
        owned.extend_from_slice(values);
        Self::from_logical_vec(owned, bounds)
    }

    /// The caller accounts for the input allocation. Shape/policy rejection
    /// drops that input; it cannot change any previously published table.
    pub fn from_logical_vec(values: Vec<Scalar>, bounds: &Bounds) -> Result<Self, Error> {
        let arity = bounds.table_length(values.len())?;
        Ok(Self {
            values: Arc::new(values),
            arity,
        })
    }

    /// Number of logical coordinates.
    pub fn arity(&self) -> usize {
        self.arity
    }
    /// Number of stored evaluations, including one for a constant table.
    pub fn len(&self) -> usize {
        self.values.len()
    }
    /// Admitted tables always contain at least one evaluation.
    pub fn is_empty(&self) -> bool {
        false
    }
    /// Allocated scalar slots, used for conservative retained-byte accounting.
    pub fn storage_capacity(&self) -> usize {
        self.values.capacity()
    }
    /// Borrow logical evaluations without copying or exposing mutable storage.
    pub fn logical_values(&self) -> &[Scalar] {
        &self.values
    }

    /// Allocate and permute the source into a genuinely different storage.
    /// Bounds are checked before the allocation; the source remains immutable.
    pub fn from_lsb(table: &Table, bounds: &Bounds) -> Result<Self, Error> {
        bounds.table(table.arity())?;
        Self::from_logical_vec(table.logical_values()?, bounds)
    }

    /// Copy and permute once into the Arkworks commitment-compatible layout.
    pub fn to_lsb(&self, bounds: &Bounds) -> Result<Table, Error> {
        // Table::from_logical copies once and permutes that destination in place.
        Table::from_logical(&self.values, bounds)
    }

    /// Fix the first logical coordinate, producing fresh immutable storage.
    pub fn restrict_first(&self, r: Scalar) -> Result<Self, Error> {
        if self.arity == 0 {
            return Err(Error::PositiveArityRequired);
        }
        let half = self.len() / 2;
        let mut values = vector(half)?;
        for (a, b) in self.values[..half].iter().zip(&self.values[half..]) {
            values.push(*a + r * (*b - a));
        }
        Ok(Self {
            values: Arc::new(values),
            arity: self.arity - 1,
        })
    }

    /// Sum the product on the Boolean cube, without allocating a new table.
    pub fn product_boolean_sum(&self, other: &Self) -> Result<Scalar, Error> {
        same_arity(self.arity, other.arity)?;
        Ok(self
            .values
            .iter()
            .zip(other.values.iter())
            .map(|(a, b)| *a * b)
            .sum())
    }

    /// Product-round coefficients, computed directly from the two storage halves.
    /// No interpolation divisions or hidden LSB conversion are used.
    pub fn round_product(&self, other: &Self) -> Result<[Scalar; 3], Error> {
        same_arity(self.arity, other.arity)?;
        if self.arity == 0 {
            return Err(Error::PositiveArityRequired);
        }
        let half = self.len() / 2;
        let mut q = [Scalar::ZERO; 3];
        for i in 0..half {
            let a = self.values[i];
            let b = other.values[i];
            let da = self.values[i + half] - a;
            let db = other.values[i + half] - b;
            q[0] += a * b;
            q[1] += da * b + a * db;
            q[2] += da * db;
        }
        Ok(q)
    }

    /// Evaluate directly by the tensor-product formula, without table allocation.
    pub fn evaluate(&self, point: &[Scalar]) -> Result<Scalar, Error> {
        same_arity(self.arity, point.len())?;
        Ok(self
            .values
            .iter()
            .enumerate()
            .map(|(i, value)| {
                point.iter().enumerate().fold(*value, |v, (bit, r)| {
                    v * if i >> (self.arity - 1 - bit) & 1 == 1 {
                        *r
                    } else {
                        Scalar::ONE - r
                    }
                })
            })
            .sum())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn asymmetric_coordinates_and_immutable_conversion() {
        let bounds = Bounds::new(4, 16, 4096, 64);
        let values = [0u64, 1, 4, 9].map(Scalar::from);
        let lsb = Table::from_logical(&values, &bounds).unwrap();
        let msb = MsbTable::from_lsb(&lsb, &bounds).unwrap();
        let alias = msb.clone();
        let folded = msb.restrict_first(Scalar::from(2)).unwrap();
        assert_eq!(folded.logical_values(), &[8u64, 17].map(Scalar::from));
        assert_eq!(
            folded.to_lsb(&bounds).unwrap().logical_values().unwrap(),
            folded.logical_values()
        );
        assert_eq!(alias.logical_values(), values);
        assert_eq!(lsb.logical_values().unwrap(), values);
        let tiny = Bounds::new(1, 2, 4096, 2);
        assert!(msb.to_lsb(&tiny).is_err());
        assert!(MsbTable::from_lsb(&lsb, &tiny).is_err());
        assert_eq!(alias.logical_values(), values);
        assert!(MsbTable::from_logical(&[], &bounds).is_err());
        assert!(MsbTable::from_logical(&values[..3], &bounds).is_err());
        let scalar = MsbTable::from_logical(&values[..1], &bounds).unwrap();
        assert_eq!(scalar.evaluate(&[]).unwrap(), Scalar::ZERO);
        assert_eq!(
            scalar.restrict_first(Scalar::ONE).unwrap_err(),
            Error::PositiveArityRequired
        );
        assert!(scalar.round_product(&scalar).is_err());
        assert!(scalar.product_boolean_sum(&msb).is_err());
        assert!(msb.evaluate(&[]).is_err());
    }

    #[test]
    fn independent_layouts_agree_across_ranks() {
        let bounds = Bounds::new(8, 256, 16384, 1024);
        let mut state = 17u64;
        let mut draw = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            Scalar::from(state)
        };
        for rank in 0..=8 {
            let a: Vec<_> = (0..1 << rank).map(|_| draw()).collect();
            let b: Vec<_> = (0..1 << rank).map(|_| draw()).collect();
            let point: Vec<_> = (0..rank).map(|_| draw()).collect();
            let (mut la, lb) = (
                Table::from_logical(&a, &bounds).unwrap(),
                Table::from_logical(&b, &bounds).unwrap(),
            );
            let (mut ma, mb) = (
                MsbTable::from_logical(&a, &bounds).unwrap(),
                MsbTable::from_logical(&b, &bounds).unwrap(),
            );
            assert_eq!(
                ma.product_boolean_sum(&mb).unwrap(),
                la.product_boolean_sum(&lb).unwrap()
            );
            assert_eq!(ma.evaluate(&point).unwrap(), la.evaluate(&point).unwrap());
            if rank > 0 {
                assert_eq!(
                    ma.round_product(&mb).unwrap(),
                    la.round_product(&lb).unwrap()
                );
            }
            for r in point {
                la = la.restrict_first(r).unwrap();
                ma = ma.restrict_first(r).unwrap();
                assert_eq!(ma.logical_values(), la.logical_values().unwrap());
            }
        }
    }
}
