//! Canonical coefficients in `(Z/qZ)[X]/(X^n + 1)`.
//!
//! These rings need not be fields. In particular, their elements do not implement
//! `field::Coefficient`. Coefficients are in ascending degree order, including
//! exactly `n` entries even when the leading coefficients are zero. No transform
//! coordinates, Montgomery representation, or implicit reduction are accepted.

/// Invalid mathematical operands or caller-owned destination.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Modulus,
    Degree,
    Shape,
    Residue,
    RingMismatch,
    Destination,
}
impl Error {
    pub const fn code(self) -> &'static str {
        match self {
            Self::Modulus => "quotient-modulus",
            Self::Degree => "quotient-degree",
            Self::Shape => "quotient-shape",
            Self::Residue => "quotient-residue",
            Self::RingMismatch => "quotient-ring-mismatch",
            Self::Destination => "quotient-destination",
        }
    }
}

/// An exact quotient-ring identity. Composite moduli and non-two-adic degrees
/// are supported; only `q >= 2` and `n > 0` are required.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ring {
    modulus: u64,
    degree: usize,
}
impl Ring {
    pub fn new(modulus: u64, degree: usize) -> Result<Self, Error> {
        if modulus < 2 {
            return Err(Error::Modulus);
        }
        if degree == 0 {
            return Err(Error::Degree);
        }
        Ok(Self { modulus, degree })
    }
    pub const fn modulus(self) -> u64 {
        self.modulus
    }
    pub const fn degree(self) -> usize {
        self.degree
    }
    /// Validate the complete immutable input before any arithmetic or allocation.
    pub fn polynomial(self, coefficients: &[u64]) -> Result<Polynomial<'_>, Error> {
        if coefficients.len() != self.degree {
            return Err(Error::Shape);
        }
        if coefficients.iter().any(|&c| c >= self.modulus) {
            return Err(Error::Residue);
        }
        Ok(Polynomial {
            ring: self,
            coefficients,
        })
    }
}

/// A borrowed canonical representative, inseparable from its ring identity.
#[derive(Clone, Copy, Debug)]
pub struct Polynomial<'a> {
    ring: Ring,
    coefficients: &'a [u64],
}
impl<'a> Polynomial<'a> {
    pub const fn ring(self) -> Ring {
        self.ring
    }
    pub const fn coefficients(self) -> &'a [u64] {
        self.coefficients
    }
    /// Exact integer representatives in `[-floor(q/2), ceil(q/2))`.
    /// An even modulus's midpoint is negative. This is not modular arithmetic.
    pub fn centered(self) -> impl ExactSizeIterator<Item = i128> + 'a {
        let q = self.ring.modulus;
        let split = q / 2 + q % 2;
        self.coefficients.iter().map(move |&c| {
            if c < split {
                i128::from(c)
            } else {
                i128::from(c) - i128::from(q)
            }
        })
    }
}

/// Two admitted operands in the same ring. Operations allocate no memory.
#[derive(Clone, Copy, Debug)]
pub struct Operands<'a> {
    left: Polynomial<'a>,
    right: Polynomial<'a>,
}
impl<'a> Operands<'a> {
    pub fn new(left: Polynomial<'a>, right: Polynomial<'a>) -> Result<Self, Error> {
        if left.ring != right.ring {
            return Err(Error::RingMismatch);
        }
        Ok(Self { left, right })
    }
    pub const fn ring(self) -> Ring {
        self.left.ring
    }
    fn destination(self, output: &[u64]) -> Result<(), Error> {
        if output.len() != self.ring().degree {
            return Err(Error::Destination);
        }
        Ok(())
    }
    /// Refuse a wrong extent before writing any coefficient.
    pub fn add_into(self, output: &mut [u64]) -> Result<(), Error> {
        self.destination(output)?;
        let q = u128::from(self.ring().modulus);
        for ((out, &a), &b) in output
            .iter_mut()
            .zip(self.left.coefficients)
            .zip(self.right.coefficients)
        {
            *out = ((u128::from(a) + u128::from(b)) % q) as u64;
        }
        Ok(())
    }
    pub fn subtract_into(self, output: &mut [u64]) -> Result<(), Error> {
        self.destination(output)?;
        let q = self.ring().modulus;
        for ((out, &a), &b) in output
            .iter_mut()
            .zip(self.left.coefficients)
            .zip(self.right.coefficients)
        {
            *out = if a >= b { a - b } else { q - (b - a) };
        }
        Ok(())
    }
    /// Schoolbook negacyclic convolution. Each product fits in `u128`; reduction
    /// after each term prevents accumulation overflow even for `q = u64::MAX`.
    pub fn multiply_into(self, output: &mut [u64]) -> Result<(), Error> {
        self.destination(output)?;
        let n = self.ring().degree;
        let q = u128::from(self.ring().modulus);
        for (i, out) in output.iter_mut().enumerate() {
            let mut sum = 0;
            for (j, &a) in self.left.coefficients.iter().enumerate() {
                // Avoid computing i+n, which could overflow a host index.
                let (k, wrapped) = if j > i {
                    (n - (j - i), true)
                } else {
                    (i - j, false)
                };
                let term = u128::from(a) * u128::from(self.right.coefficients[k]) % q;
                sum = if wrapped {
                    (sum + q - term) % q
                } else {
                    (sum + term) % q
                };
            }
            *out = sum as u64;
        }
        Ok(())
    }
    /// Whether the sum of both centered squared norms is at most `bound`.
    /// A decreasing integer budget avoids overflow of the total norm. Every
    /// coefficient is visited even after the predicate becomes false. This is
    /// not a constant-time guarantee for the compiler or enclosing application.
    pub fn norm_within(self, bound: u64) -> bool {
        let mut remaining = u128::from(bound);
        let mut within = true;
        for coefficient in self.left.centered().chain(self.right.centered()) {
            let magnitude = coefficient.unsigned_abs();
            let square = magnitude * magnitude;
            within &= square <= remaining;
            remaining = remaining.saturating_sub(square);
        }
        within
    }
}

/// Conservative native work admission, including two coefficient scans.
pub fn linear_work(degree: usize) -> Option<u64> {
    u64::try_from(degree).ok()?.checked_mul(8)?.checked_add(1)
}
/// Conservative schoolbook work admission, not a timing estimate.
pub fn product_work(degree: usize) -> Option<u64> {
    let n = u64::try_from(degree).ok()?;
    n.checked_mul(n)?
        .checked_mul(8)?
        .checked_add(n.checked_mul(2)?)?
        .checked_add(1)
}

#[cfg(test)]
mod tests;
