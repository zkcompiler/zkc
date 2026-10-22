//! Full scalar negacyclic transforms with explicit natural-order coordinates.
//!
//! Forward: E[k] = sum_j a[j] r^((2k+1)j). Inverse takes the inverse-root
//! attribute r^-1 and returns canonical coefficients. This profile matches the
//! admitted HEIR boundary; it does not cover ML-KEM's quadratic decomposition.
use super::{Error, Polynomial, Ring};

#[derive(Clone, Copy, Debug)]
pub struct Transform {
    ring: Ring,
    root: u64,
}

fn power(mut value: u64, mut exponent: u64, q: u64) -> u64 {
    let mut result = 1;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = result * value % q;
        }
        value = value * value % q;
        exponent >>= 1;
    }
    result
}

impl Transform {
    /// All parameter checks precede destination mutation. The prime test is
    /// bounded by the admitted 31-bit modulus, independent of coefficient data.
    pub fn new(ring: Ring, root: u64) -> Result<Self, Error> {
        let q = ring.modulus();
        let n = ring.degree();
        if !(3..(1u64 << 31)).contains(&q)
            || q.is_multiple_of(2)
            || !(2..=65536).contains(&n)
            || !n.is_power_of_two()
            || !(q - 1).is_multiple_of(2 * n as u64)
        {
            return Err(Error::TransformProfile);
        }
        let mut divisor = 3;
        while divisor * divisor <= q {
            if q.is_multiple_of(divisor) {
                return Err(Error::TransformProfile);
            }
            divisor += 2;
        }
        if root >= q || power(root, n as u64, q) != q - 1 {
            return Err(Error::TransformRoot);
        }
        Ok(Self { ring, root })
    }

    pub const fn ring(self) -> Ring {
        self.ring
    }
    pub const fn root(self) -> u64 {
        self.root
    }

    pub fn forward_into(self, input: Polynomial<'_>, output: &mut [u64]) -> Result<(), Error> {
        self.apply(input, output, false)
    }

    pub fn inverse_into(self, input: Polynomial<'_>, output: &mut [u64]) -> Result<(), Error> {
        self.apply(input, output, true)
    }

    fn apply(self, input: Polynomial<'_>, output: &mut [u64], inverse: bool) -> Result<(), Error> {
        if input.ring() != self.ring {
            return Err(Error::RingMismatch);
        }
        let n = self.ring.degree();
        let q = self.ring.modulus();
        if output.len() != n {
            return Err(Error::Destination);
        }
        let mut twist = 1;
        for (out, &coefficient) in output.iter_mut().zip(input.coefficients()) {
            *out = coefficient * twist % q;
            if !inverse {
                twist = twist * self.root % q;
            }
        }
        // Iterative radix-two DIT: bit-reverse the input so output coordinates
        // are natural. Scratch is exactly the caller-owned destination.
        let shift = usize::BITS - n.trailing_zeros();
        for index in 0..n {
            let reversed = index.reverse_bits() >> shift;
            if index < reversed {
                output.swap(index, reversed);
            }
        }
        let mut width = 2;
        while width <= n {
            let step = power(self.root, (2 * n / width) as u64, q);
            for block in output.chunks_exact_mut(width) {
                let (left, right) = block.split_at_mut(width / 2);
                let mut twiddle = 1;
                for (a, b) in left.iter_mut().zip(right) {
                    let upper = *a;
                    let lower = *b * twiddle % q;
                    *a = (upper + lower) % q;
                    *b = (upper + q - lower) % q;
                    twiddle = twiddle * step % q;
                }
            }
            width *= 2;
        }
        if inverse {
            let scale = power(n as u64, q - 2, q);
            let mut twist = scale;
            for coefficient in output {
                *coefficient = *coefficient * twist % q;
                twist = twist * self.root % q;
            }
        }
        Ok(())
    }
}

/// Admission score includes parameter checks and exponentiation; not timing.
pub fn work(degree: usize) -> Option<u64> {
    if !(2..=65536).contains(&degree) || !degree.is_power_of_two() {
        return None;
    }
    let n = degree as u64;
    n.checked_mul(u64::from(degree.trailing_zeros()))?
        .checked_mul(8)?
        .checked_add(n.checked_mul(16)?)?
        .checked_add(65536)
}

#[cfg(test)]
mod tests;
