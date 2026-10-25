//! Per-call preparation, one Miller product, one final exponentiation.
use super::{
    Error, G1, G1Element, G1Vector, G2, G2Vector, pairing_work, pairing_workspace_bytes, vector,
};
use halo2curves_axiom::{
    bn256::{G2Prepared, Gt, multi_miller_loop},
    pairing::MillerLoopResult,
};

/// Product of validated subgroup pairings equals one. Empty products are true;
/// a mismatched shape is an error, not a false equation.
pub fn pairing_check(left: &[G1], right: &[G2]) -> Result<bool, Error> {
    if left.len() != right.len() {
        return Err(Error::LengthMismatch);
    }
    product(left.len(), |i| left[i], |i| right[i])
}

pub fn pairing_check_bulk(left: &G1Vector, right: &G2Vector) -> Result<bool, Error> {
    if left.len() != right.len() {
        return Err(Error::LengthMismatch);
    }
    product(
        left.len(),
        |i| left.get(i).expect("checked length"),
        |i| right.get(i).expect("checked length"),
    )
}

fn product(
    len: usize,
    left_at: impl Fn(usize) -> G1 + Send + Sync,
    right_at: impl Fn(usize) -> G2 + Send + Sync,
) -> Result<bool, Error> {
    pairing_workspace_bytes(len)?;
    pairing_work(len)?;
    if len == 0 {
        return Ok(true);
    }
    // Reserve every adapter buffer before entering numerical work. Upstream
    // preparation and Miller iterator Vecs still allocate privately/infallibly;
    // the public bound admits them without claiming allocator recovery.
    let mut left = vector::<G1Element>(len)?;
    let prepared = vector::<G2Prepared>(len)?;
    let terms = vector::<(&G1Element, &G2Prepared)>(len)?;
    left.extend((0..len).map(|i| left_at(i).0));
    Ok(crate::cpu::install(move || {
        let mut prepared = prepared;
        let mut terms = terms;
        for index in 0..len {
            prepared.push(G2Prepared::from_affine(right_at(index).0));
        }
        terms.extend(left.iter().zip(&prepared));
        // Gt::default() is extension-field zero, not the target identity.
        // Upstream wraps an unfinalized Miller value in Gt as well: only the
        // result after this single final exponentiation is compared.
        multi_miller_loop(&terms).final_exponentiation() == Gt::identity()
    }))
}
