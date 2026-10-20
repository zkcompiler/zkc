//! Provider-neutral geometry and admission for a sum of opening quotients.
use crate::{Policy, Result, exhausted, refused, value::size};

#[derive(Clone, Copy)]
pub(crate) struct OpeningQuotientSumShape {
    pub(crate) width: usize,
    pub(crate) height: usize,
    input_len: usize,
    descriptors: usize,
}

impl OpeningQuotientSumShape {
    pub(crate) fn new(
        input_len: usize,
        width: usize,
        height: usize,
        descriptors: usize,
        descriptor_lengths: [usize; 3],
        initial_len: usize,
    ) -> Result<Self> {
        let expected = width
            .checked_mul(height)
            .ok_or_else(|| exhausted("size-overflow"))?;
        if input_len != expected {
            return Err(refused("coset-batch-shape"));
        }
        if descriptor_lengths != [descriptors; 3] || initial_len != height {
            return Err(refused("coset-opening-shape"));
        }
        Ok(Self {
            width,
            height,
            input_len,
            descriptors,
        })
    }

    /// Bound the complete input vectors before the descriptor membership scan.
    /// Equal descriptor lengths share a per-value check, not a combined ceiling.
    pub(crate) fn admit_inputs(self, policy: &Policy, element_bytes: usize) -> Result<()> {
        policy.vector_width(self.input_len, element_bytes)?;
        policy.vector_width(self.height, element_bytes)?;
        policy.vector_width(self.descriptors, element_bytes)?;
        policy.vector_width(self.descriptors, std::mem::size_of::<u64>())
    }

    /// Admit every input vector, result, and the complete live managed storage
    /// before allocating. Call still owns the actual output/scratch reservations.
    /// The final Value overlaps result staging; nonempty calls also own two
    /// height-sized arrays, reused for every descriptor without column copies.
    pub(crate) fn admit(
        self,
        policy: &Policy,
        element_bytes: usize,
        available: usize,
    ) -> Result<usize> {
        self.admit_inputs(policy, element_bytes)?;
        let retained = size(self.height, element_bytes)?;
        policy.output(retained, available)?;
        if self.managed_bytes(element_bytes)? > policy.max_numerical_bytes {
            return Err(exhausted("numerical-bytes"));
        }
        Ok(retained)
    }

    pub(crate) fn managed_bytes(self, element_bytes: usize) -> Result<usize> {
        let retained = size(self.height, element_bytes)?;
        let scratch_and_staging = if self.descriptors == 0 { 1 } else { 3 };
        self.height
            .checked_mul(element_bytes)
            .and_then(|payload| payload.checked_mul(scratch_and_staging))
            .and_then(|bytes| bytes.checked_add(retained))
            .ok_or_else(|| exhausted("size-overflow"))
    }

    /// Conservative native-field operations and bounded scalar-loop steps,
    /// matching the unit of the single-opening operation. This is neither a
    /// base-coordinate expansion nor elapsed time. Thirty-two units per row
    /// cover initialized/copied storage; per descriptor they cover denominator
    /// generation, prefix/reverse products and weighted accumulation. The fixed
    /// allowance covers domain/membership powers and the installed bounded
    /// degree-1/4/8 and BN254 inversion routines. Empty calls copy initial only.
    pub(crate) fn work(self) -> Result<u64> {
        let checked = || {
            let copied_initial = self.height.checked_mul(32)?.checked_add(1)?;
            if self.descriptors == 0 {
                return Some(copied_initial);
            }
            let per_descriptor = self.height.checked_mul(32)?.checked_add(8192)?;
            copied_initial.checked_add(self.descriptors.checked_mul(per_descriptor)?)
        };
        checked()
            .and_then(|units| u64::try_from(units).ok())
            .ok_or_else(|| exhausted("size-overflow"))
    }
}

pub(crate) fn column_index(column: u64, width: usize) -> Option<usize> {
    usize::try_from(column)
        .ok()
        .filter(|column| *column < width)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_shapes_and_checked_sizes() {
        for (input, width, height, count, lengths, initial, expected) in [
            (3, 2, 2, 0, [0; 3], 2, "refused:coset-batch-shape"),
            (5, 2, 2, 0, [0; 3], 2, "refused:coset-batch-shape"),
            (4, 2, 2, 2, [1, 2, 2], 2, "refused:coset-opening-shape"),
            (4, 2, 2, 2, [2, 1, 2], 2, "refused:coset-opening-shape"),
            (4, 2, 2, 2, [2, 2, 1], 2, "refused:coset-opening-shape"),
            (4, 2, 2, 0, [0; 3], 1, "refused:coset-opening-shape"),
            (0, usize::MAX, 2, 0, [0; 3], 2, "exhausted:size-overflow"),
        ] {
            assert_eq!(
                OpeningQuotientSumShape::new(input, width, height, count, lengths, initial)
                    .err()
                    .unwrap()
                    .code,
                expected
            );
        }
        let large = OpeningQuotientSumShape::new(0, 0, usize::MAX, 0, [0; 3], usize::MAX).unwrap();
        assert_eq!(
            large.managed_bytes(32).unwrap_err().code,
            "exhausted:size-overflow"
        );
        assert_eq!(large.work().unwrap_err().code, "exhausted:size-overflow");
        let descriptors =
            OpeningQuotientSumShape::new(1, 1, 1, usize::MAX, [usize::MAX; 3], 1).unwrap();
        assert_eq!(
            descriptors.work().unwrap_err().code,
            "exhausted:size-overflow"
        );
        assert_eq!(column_index(u64::MAX, 4), None);
        assert_eq!(column_index(4, 4), None);
        assert_eq!(column_index(3, 4), Some(3));
    }

    #[test]
    fn admission_checks_each_vector_and_exact_storage() {
        let shape = OpeningQuotientSumShape::new(8, 2, 4, 3, [3; 3], 4).unwrap();
        let retained = size(4, 32).unwrap();
        let managed = 256 + 4 * 4 * 32;
        // Pin the published worst-case floors independently of provider reuse.
        assert_eq!(retained, 384);
        assert_eq!(shape.work().unwrap(), 25_089);
        assert_eq!(shape.managed_bytes(32).unwrap(), managed);
        let exact = Policy {
            max_numerical_bytes: managed,
            ..Policy::default()
        };
        assert_eq!(shape.admit(&exact, 32, retained).unwrap(), retained);
        assert_eq!(
            shape.admit(&exact, 32, retained - 1).unwrap_err().code,
            "exhausted:output-bytes"
        );
        assert_eq!(
            shape
                .admit(
                    &Policy {
                        max_numerical_bytes: managed - 1,
                        ..exact
                    },
                    32,
                    retained
                )
                .unwrap_err()
                .code,
            "exhausted:numerical-bytes"
        );
        for (input, width, height, count, limit) in
            [(8, 2, 4, 3, 7), (0, 0, 4, 0, 3), (1, 1, 1, 4, 3)]
        {
            let shape =
                OpeningQuotientSumShape::new(input, width, height, count, [count; 3], height)
                    .unwrap();
            let policy = Policy {
                max_table_elements: limit,
                ..Policy::default()
            };
            assert_eq!(
                shape.admit(&policy, 4, usize::MAX).unwrap_err().code,
                "exhausted:element-limit"
            );
        }
        // Indices need eight bytes per element even for four-byte field values.
        let shape = OpeningQuotientSumShape::new(1, 1, 1, 40, [40; 3], 1).unwrap();
        assert_eq!(
            shape
                .admit(
                    &Policy {
                        max_value_bytes: size(40, 4).unwrap(),
                        ..Policy::default()
                    },
                    4,
                    usize::MAX
                )
                .unwrap_err()
                .code,
            "exhausted:output-bytes"
        );
        let empty = OpeningQuotientSumShape::new(0, 0, 3, 0, [0; 3], 3).unwrap();
        assert_eq!(empty.managed_bytes(32).unwrap(), 256 + 2 * 3 * 32);
        assert_eq!(empty.work().unwrap(), 3 * 32 + 1);
    }

    #[test]
    fn ordinary_opening_batches_fit_the_current_work_policy() {
        for (height, descriptors) in [(4096, 8), (16384, 32), (16384, 64)] {
            let shape = OpeningQuotientSumShape::new(
                4 * height,
                4,
                height,
                descriptors,
                [descriptors; 3],
                height,
            )
            .unwrap();
            assert!(shape.work().unwrap() <= Policy::default().max_numerical_work);
        }
    }
}
