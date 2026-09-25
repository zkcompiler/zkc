//! Depth-one physical views. Private fields prevent malformed lengths or nested
//! views; factors and values retain their complete immutable Arc slices.
use crate::{Result, exhausted, refused, value::size};
use std::sync::Arc;
#[derive(Clone, Debug)]
pub struct Diagonal<S, B> {
    factors: Arc<[S]>,
    backing: Arc<[B]>,
}
impl<S, B> Diagonal<S, B> {
    pub(crate) fn new(factors: Arc<[S]>, backing: Arc<[B]>) -> Result<Self> {
        if factors.len() != backing.len() {
            return Err(refused("length-mismatch"));
        }
        Ok(Self { factors, backing })
    }
    pub fn factors(&self) -> &[S] {
        &self.factors
    }
    pub fn backing(&self) -> &[B] {
        &self.backing
    }
    pub(crate) fn retained_bytes(&self) -> Result<usize> {
        size(self.factors.len(), std::mem::size_of::<S>())?
            .checked_add(size(self.backing.len(), std::mem::size_of::<B>())?)
            .and_then(|n| n.checked_add(256))
            .ok_or_else(|| exhausted("size-overflow"))
    }
}

pub(crate) fn apply(
    i: &zkc_runtime::interactive::Invocation<'_>,
    args: &[crate::Value],
    p: &crate::Policy,
) -> Option<Result<Vec<crate::Value>>> {
    use crate::Value::*;
    use crate::kernels::arithmetic::equal_len;
    use curve25519_dalek::traits::MultiscalarMul;
    if !i.kernel.starts_with("arkworks-diagonal/") && !i.kernel.starts_with("dalek-diagonal/") {
        return None;
    }
    Some((|| {
        let result = match (i.kernel, args) {
            ("arkworks-diagonal/vector.mul", [Vector(f), Vector(b)]) => {
                equal_len(f.len(), b.len())?;
                let d = Diagonal::new(f.clone(), b.clone())?;
                p.output(d.retained_bytes()?, i.max_output_bytes)?;
                FrDiagonal(Arc::new(d))
            }
            ("arkworks-diagonal/vector.dot", [Vector(w), FrDiagonal(d)]) => {
                equal_len(w.len(), d.backing.len())?;
                p.output(512, i.max_output_bytes)?;
                Field(
                    w.iter()
                        .zip(d.factors.iter())
                        .zip(d.backing.iter())
                        .fold(crate::Scalar::from(0), |s, ((w, f), b)| s + *w * (*f * *b)),
                )
            }
            ("dalek-diagonal/curve.scale_each", [RistrettoVector(f), RistrettoGroups(b)]) => {
                equal_len(f.len(), b.len())?;
                let d = Diagonal::new(f.clone(), b.clone())?;
                p.output(d.retained_bytes()?, i.max_output_bytes)?;
                RistrettoDiagonal(Arc::new(d))
            }
            ("dalek-diagonal/curve.msm", [RistrettoVector(w), RistrettoDiagonal(d)]) => {
                equal_len(w.len(), d.backing.len())?;
                p.output(512, i.max_output_bytes)?;
                // Iterator carries exact checked length. No variable-time scalar API.
                RistrettoGroup(crate::RistrettoPoint::multiscalar_mul(
                    w.iter().zip(d.factors.iter()).map(|(w, f)| w * f),
                    d.backing.iter(),
                ))
            }
            _ => return Err(refused("kernel-operands")),
        };
        Ok(vec![result])
    })())
}
