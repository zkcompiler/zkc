//! Exact signed-digit matrix products using bounded centered CRT lifts.
//!
//! The protocol modulus is independent of the compute primes. Each chunk's
//! integer coefficient has magnitude at most `columns * n * A * B`; centered
//! reconstruction is valid only when twice that bound is below their product.
//! Matrix transforms have private, immutable ownership. Kernels allocate no
//! memory: callers supply charged storage and scratch before preparation.
use super::{Error, Ring, transform::Transform};

const PRIMES: [u64; 3] = [2_013_265_921, 1_811_939_329, 469_762_049];
const GENERATORS: [u64; 3] = [31, 13, 3];

fn power(mut a: u64, mut e: u64, p: u64) -> u64 {
    let mut result = 1;
    while e != 0 {
        if e & 1 != 0 {
            result = result * a % p;
        }
        a = a * a % p;
        e >>= 1;
    }
    result
}

fn centered(a: u64, q: u64) -> i128 {
    if a < q / 2 + q % 2 {
        a as i128
    } else {
        a as i128 - q as i128
    }
}

fn residue(a: i128, q: u64) -> u64 {
    a.rem_euclid(q as i128) as u64
}

// For positive factors, successive floor divisions equal division by their
// product. This computes the strict lift capacity without overflowing a
// denominator even when protocol coefficients occupy the full u64 range.
fn capacity(product: u128, degree: usize, a: u64, b: u64) -> usize {
    if a == 0 || b == 0 {
        return usize::MAX;
    }
    usize::try_from((product - 1) / 2 / degree as u128 / a as u128 / b as u128)
        .unwrap_or(usize::MAX)
}

/// Parameter plan bound to the fully checked original coefficients.
pub struct Matrix<'a> {
    coefficients: &'a [u64],
    plan: Plan,
}

#[derive(Debug)]
struct Plan {
    ring: Ring,
    rows: usize,
    columns: usize,
    bound: u64,
    limbs: usize,
    chunk: usize,
    product: u128,
    forward: [Transform; 3],
    // Inverse of the preceding prime product modulo this limb.
    garner: [u64; 3],
    elements: usize,
}

impl<'a> Matrix<'a> {
    /// Conservative score for the complete coefficient scan and at most three
    /// compute-basis admissions. Charge before calling `new`, including refusal.
    pub fn admission_work(elements: usize) -> Option<u64> {
        u64::try_from(elements)
            .ok()?
            .checked_mul(8)?
            .checked_add(3 * 65_536)
    }

    pub fn new(
        coefficients: &'a [u64],
        q: u64,
        n: usize,
        rows: usize,
        columns: usize,
        bound: u64,
    ) -> Result<Self, Error> {
        let ring = Ring::new(q, n)?;
        if rows == 0 || columns == 0 {
            return Err(Error::Shape);
        }
        let elements = rows
            .checked_mul(columns)
            .and_then(|v| v.checked_mul(n))
            .ok_or(Error::Shape)?;
        if coefficients.len() != elements {
            return Err(Error::Shape);
        }
        if !(2..=65536).contains(&n) || !n.is_power_of_two() {
            return Err(Error::TransformProfile);
        }
        let mut a = 0;
        for &value in coefficients {
            if value >= q {
                return Err(Error::Residue);
            }
            a = a.max(centered(value, q).unsigned_abs() as u64);
        }
        let transform = |i: usize| {
            let p = PRIMES[i];
            let root = power(GENERATORS[i], (p - 1) / (2 * n as u64), p);
            Transform::new(Ring::new(p, n)?, root)
        };
        let mut product = 1u128;
        let mut limbs = 0;
        let mut chunk = 0;
        let mut garner = [1; 3];
        for (i, &p) in PRIMES.iter().enumerate() {
            garner[i] = power((product % p as u128) as u64, p - 2, p);
            product *= p as u128;
            limbs = i + 1;
            // Canonical protocol coefficients already have magnitude at most
            // floor(q/2), including the negative midpoint for even q. This
            // tighter planning fact does not change the declared input bound.
            chunk = capacity(product, n, a, bound.min(q / 2)).min(columns);
            if chunk == columns {
                break;
            }
        }
        if chunk == 0 {
            return Err(Error::RnsCapacity);
        }
        elements.checked_mul(limbs).ok_or(Error::Shape)?;
        // Validate exactly the selected basis. Rechecking unused primes and
        // roots adds substantial preparation cost for one-limb matrices.
        // The fixed arrays avoid hidden allocation; unused slots are copies
        // of an admitted transform and are never read by the active prefix.
        let mut forward = [transform(0)?; 3];
        for i in 1..limbs {
            forward[i] = transform(i)?;
        }
        Ok(Self {
            coefficients,
            plan: Plan {
                ring,
                rows,
                columns,
                bound,
                limbs,
                chunk,
                product,
                forward,
                garner,
                elements,
            },
        })
    }
    pub fn storage_elements(&self) -> usize {
        self.plan.elements * self.plan.limbs
    }
    pub fn scratch_elements(&self) -> usize {
        self.plan.ring.degree()
    }
    /// Conservative transform preparation score, after charged matrix admission.
    /// The native caller owns when this score is charged and reserves storage.
    pub fn work(&self) -> Option<u64> {
        let p = &self.plan;
        let transforms = p.rows.checked_mul(p.columns)?.checked_mul(p.limbs)?;
        (transforms as u64)
            .checked_mul(super::transform::work(p.ring.degree())?)?
            .checked_add((p.elements as u64).checked_mul(8)?)
    }
    /// The only constructor of a prepared matrix performs the actual transforms.
    /// A caller cannot relabel arbitrary coordinates as prepared matrix data.
    pub fn prepare(
        self,
        mut storage: Vec<u64>,
        scratch: &mut [u64],
    ) -> Result<PreparedMatrix, Error> {
        if storage.len() != self.storage_elements() || scratch.len() != self.scratch_elements() {
            return Err(Error::Destination);
        }
        let p = &self.plan;
        let n = p.ring.degree();
        for limb in 0..p.limbs {
            let transform = p.forward[limb];
            let target = &mut storage[limb * p.elements..(limb + 1) * p.elements];
            for (input, output) in self
                .coefficients
                .chunks_exact(n)
                .zip(target.chunks_exact_mut(n))
            {
                for (out, &value) in scratch.iter_mut().zip(input) {
                    *out = residue(centered(value, p.ring.modulus()), PRIMES[limb]);
                }
                transform.forward_into(transform.ring().polynomial(scratch)?, output)?;
            }
        }
        Ok(PreparedMatrix {
            plan: self.plan,
            storage,
        })
    }
}

/// Immutable local value with no unchecked constructor or wire representation.
#[derive(Debug)]
pub struct PreparedMatrix {
    plan: Plan,
    storage: Vec<u64>,
}

impl PreparedMatrix {
    /// The complete owned coordinate allocation, including spare capacity.
    /// Native publication adds its own metadata and allocation accounting.
    pub fn storage_elements(&self) -> usize {
        self.storage.len()
    }
    pub fn storage_capacity(&self) -> usize {
        self.storage.capacity()
    }
    pub const fn ring(&self) -> Ring {
        self.plan.ring
    }
    pub const fn rows(&self) -> usize {
        self.plan.rows
    }
    pub const fn columns(&self) -> usize {
        self.plan.columns
    }
    pub const fn digit_bound(&self) -> u64 {
        self.plan.bound
    }
    pub fn output_elements(&self) -> usize {
        self.plan.rows * self.plan.ring.degree()
    }
    pub fn input_elements(&self) -> usize {
        self.plan.columns * self.plan.ring.degree()
    }
    pub fn limbs(&self) -> usize {
        self.plan.limbs
    }
    pub fn chunk_columns(&self) -> usize {
        self.plan.chunk
    }
    pub fn scratch_elements(&self) -> Option<usize> {
        self.input_elements()
            .checked_mul(self.plan.limbs)?
            .checked_add(self.plan.ring.degree().checked_mul(self.plan.limbs + 1)?)
    }
    pub fn work(&self) -> Option<u64> {
        let p = &self.plan;
        let chunks = p.columns.div_ceil(p.chunk);
        let transforms = p
            .rows
            .checked_mul(chunks)?
            .checked_add(p.columns)?
            .checked_mul(p.limbs)?;
        (transforms as u64)
            .checked_mul(super::transform::work(p.ring.degree())?)?
            .checked_add(
                (p.elements as u64)
                    .checked_mul(p.limbs as u64)?
                    .checked_mul(8)?,
            )?
            .checked_add(
                (self.output_elements() as u64)
                    .checked_mul(chunks as u64)?
                    .checked_mul(64)?,
            )
    }
    /// Check the complete digit input before any destination is modified.
    pub fn digits<'a>(&'a self, digits: &'a [u64]) -> Result<Product<'a>, Error> {
        if digits.len() != self.input_elements() {
            return Err(Error::Shape);
        }
        let q = self.plan.ring.modulus();
        for &value in digits {
            if value >= q {
                return Err(Error::Residue);
            }
            if centered(value, q).unsigned_abs() > self.plan.bound as u128 {
                return Err(Error::DigitBound);
            }
        }
        Ok(Product {
            matrix: self,
            digits,
        })
    }
}

/// Validated bounded input tied to the exact live immutable matrix and digits.
/// All destinations are supplied by the caller. Validation cannot survive a
/// mutation of the checked input.
///
/// ```compile_fail,E0506
/// use zkc_kernels::polynomial::quotient::rns::PreparedMatrix;
/// fn reuse(matrix: &PreparedMatrix, input: &mut [u64], output: &mut [u64], scratch: &mut [u64]) {
///     let checked = matrix.digits(input).unwrap();
///     input[0] = 0;
///     checked.evaluate(output, scratch).unwrap();
/// }
/// ```
pub struct Product<'a> {
    matrix: &'a PreparedMatrix,
    digits: &'a [u64],
}
impl Product<'_> {
    pub fn evaluate(self, output: &mut [u64], scratch: &mut [u64]) -> Result<(), Error> {
        let m = self.matrix;
        if output.len() != m.output_elements() || Some(scratch.len()) != m.scratch_elements() {
            return Err(Error::Destination);
        }
        let p = &m.plan;
        let n = p.ring.degree();
        let q = p.ring.modulus();
        let (vector, rest) = scratch.split_at_mut(p.limbs * m.input_elements());
        let (accumulator, temporary) = rest.split_at_mut(p.limbs * n);
        for (limb, &prime) in PRIMES.iter().enumerate().take(p.limbs) {
            let transform = p.forward[limb];
            for column in 0..p.columns {
                for (out, &value) in temporary
                    .iter_mut()
                    .zip(&self.digits[column * n..(column + 1) * n])
                {
                    *out = residue(centered(value, q), prime);
                }
                let start = (limb * p.columns + column) * n;
                transform.forward_into(
                    transform.ring().polynomial(temporary)?,
                    &mut vector[start..start + n],
                )?;
            }
        }
        output.fill(0);
        for row in 0..p.rows {
            for start in (0..p.columns).step_by(p.chunk) {
                let end = start.saturating_add(p.chunk).min(p.columns);
                accumulator.fill(0);
                for limb in 0..p.limbs {
                    let prime = PRIMES[limb];
                    let accum = &mut accumulator[limb * n..(limb + 1) * n];
                    for column in start..end {
                        let offset = (row * p.columns + column) * n;
                        let matrix =
                            &m.storage[limb * p.elements + offset..limb * p.elements + offset + n];
                        let offset = (limb * p.columns + column) * n;
                        for ((out, &a), &b) in accum
                            .iter_mut()
                            .zip(matrix)
                            .zip(&vector[offset..offset + n])
                        {
                            *out = (*out + a * b % prime) % prime;
                        }
                    }
                    // Inversion consumes coordinates in the same forward
                    // basis; Transform derives its reciprocal internally.
                    let basis = p.forward[limb];
                    basis.inverse_into(basis.evaluations(accum)?, temporary)?;
                    accum.copy_from_slice(temporary);
                }
                for i in 0..n {
                    let mut integer = accumulator[i] as u128;
                    let mut prefix = PRIMES[0] as u128;
                    for limb in 1..p.limbs {
                        let prime = PRIMES[limb];
                        let difference = (accumulator[limb * n + i] + prime
                            - (integer % prime as u128) as u64)
                            % prime;
                        let digit = difference * p.garner[limb] % prime;
                        integer += prefix * digit as u128;
                        prefix *= prime as u128;
                    }
                    let lifted = if integer > p.product / 2 {
                        integer as i128 - p.product as i128
                    } else {
                        integer as i128
                    };
                    let out = &mut output[row * n + i];
                    *out = ((*out as u128 + residue(lifted, q) as u128) % q as u128) as u64;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
