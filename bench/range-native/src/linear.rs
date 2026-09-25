//! Checked contractions. A diagonal view can be materialized on group elements
//! or pulled into scalar weights; neither route may silently truncate operands.
use crate::{Error, Result};
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar, traits::MultiscalarMul};

pub(crate) fn dot(a: &[Scalar], b: &[Scalar]) -> Result<Scalar> {
    if a.len() != b.len() {
        return Err(Error::Shape);
    }
    Ok(a.iter().zip(b).map(|(x, y)| x * y).sum())
}
pub(crate) fn msm(w: &[Scalar], bases: &[RistrettoPoint]) -> Result<RistrettoPoint> {
    if w.len() != bases.len() {
        return Err(Error::Shape);
    }
    Ok(RistrettoPoint::multiscalar_mul(w, bases))
}
pub(crate) fn diagonal_msm(
    w: &[Scalar],
    factors: &[Scalar],
    bases: &[RistrettoPoint],
) -> Result<RistrettoPoint> {
    if w.len() != bases.len() || factors.len() != bases.len() {
        return Err(Error::Shape);
    }
    Ok(RistrettoPoint::multiscalar_mul(
        w.iter().zip(factors).map(|(w, f)| w * f),
        bases,
    ))
}
pub(crate) fn powers(x: Scalar, n: usize) -> Vec<Scalar> {
    let mut p = Scalar::ONE;
    (0..n)
        .map(|_| {
            let out = p;
            p *= x;
            out
        })
        .collect()
}
