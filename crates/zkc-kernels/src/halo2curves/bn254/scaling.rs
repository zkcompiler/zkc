//! Bounded affine-base multiplication and upstream batch normalization.
//!
//! One projective buffer and one private affine buffer are reused across all
//! chunks. Upstream uses the affine destination for prefixes without allocating.
//! No projective coordinates are copied or interpreted by this adapter.
use super::{Error, ScalarElement, payload, vector};
use halo2curves_axiom::{
    CurveAffine,
    group::{Curve, Group},
};

pub const CHUNK_CAP: usize = 256;

pub(super) fn workspace_bytes<C: CurveAffine>(len: usize) -> Option<usize> {
    if len > CHUNK_CAP {
        return None;
    }
    len.checked_mul(size_of::<C::CurveExt>().checked_add(size_of::<C>())?)
        .filter(|bytes| *bytes <= isize::MAX as usize)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Algorithm {
    Direct,
    Batched { chunk_len: usize },
}

/// Optional allocation may select Direct during preparation. Execution never
/// reallocates scratch or changes the prepared choice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Selection {
    Fixed(Algorithm),
    Automatic { max_workspace: usize },
}

enum Execution<C: CurveAffine> {
    Direct,
    Batched {
        projectives: Vec<C::CurveExt>,
        affines: Vec<C>,
    },
}

/// Prepared shape-bound scratch. Caller-owned output is reserved separately.
/// All recoverable failures precede numerical writes. Contents are not zeroized.
pub struct Plan<C: CurveAffine<ScalarExt = ScalarElement>> {
    len: usize,
    execution: Execution<C>,
}

impl<C: CurveAffine<ScalarExt = ScalarElement>> Plan<C> {
    pub fn workspace_bound(len: usize, max_workspace: usize) -> usize {
        let width = size_of::<C::CurveExt>() + size_of::<C>();
        let chunk_len = len.min(CHUNK_CAP).min(max_workspace / width);
        if chunk_len >= 2 { chunk_len * width } else { 0 }
    }

    pub fn new(len: usize, selection: Selection) -> Result<Self, Error> {
        payload::<C>(len)?;
        let (algorithm, optional) = match selection {
            Selection::Fixed(algorithm) => (algorithm, false),
            Selection::Automatic { max_workspace } => {
                let bytes = Self::workspace_bound(len, max_workspace);
                (
                    if bytes == 0 {
                        Algorithm::Direct
                    } else {
                        Algorithm::Batched {
                            chunk_len: bytes / (size_of::<C::CurveExt>() + size_of::<C>()),
                        }
                    },
                    true,
                )
            }
        };
        let execution = match algorithm {
            Algorithm::Direct => Execution::Direct,
            Algorithm::Batched { chunk_len } => {
                if !(2..=CHUNK_CAP).contains(&chunk_len) || chunk_len > len {
                    return Err(Error::InvalidPlan);
                }
                let scratch = || -> Result<Execution<C>, Error> {
                    let mut projectives = vector(chunk_len)?;
                    let mut affines = vector(chunk_len)?;
                    projectives.resize(chunk_len, C::CurveExt::identity());
                    affines.resize(chunk_len, C::identity());
                    Ok(Execution::Batched {
                        projectives,
                        affines,
                    })
                };
                match scratch() {
                    Ok(scratch) => scratch,
                    Err(Error::Allocation) if optional => Execution::Direct,
                    Err(error) => return Err(error),
                }
            }
        };
        Ok(Self { len, execution })
    }

    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    pub fn algorithm(&self) -> Algorithm {
        match &self.execution {
            Execution::Direct => Algorithm::Direct,
            Execution::Batched { projectives, .. } => Algorithm::Batched {
                chunk_len: projectives.len(),
            },
        }
    }
    pub fn output_bytes(&self) -> usize {
        self.len * size_of::<C>()
    }
    /// Reserved payload, including spare vector capacity.
    pub fn workspace_bytes(&self) -> usize {
        match &self.execution {
            Execution::Direct => 0,
            Execution::Batched {
                projectives,
                affines,
            } => {
                projectives.capacity() * size_of::<C::CurveExt>()
                    + affines.capacity() * size_of::<C>()
            }
        }
    }

    pub(super) fn scale_into<W: Copy + Send + Sync>(
        &mut self,
        points: &[W],
        destination: &mut [W],
        scalar_at: impl Fn(usize) -> ScalarElement + Send + Sync,
        affine: impl Fn(W) -> C + Send + Sync,
        wrap: impl Fn(C) -> W + Send + Sync,
    ) -> Result<(), Error> {
        if points.len() != self.len || destination.len() != self.len {
            return Err(Error::LengthMismatch);
        }
        match &mut self.execution {
            Execution::Direct => {
                crate::cpu::chunks_mut(destination, 32, |offset, chunk| {
                    for (index, out) in chunk.iter_mut().enumerate() {
                        let index = offset + index;
                        *out = wrap((affine(points[index]) * scalar_at(index)).to_affine());
                    }
                });
            }
            Execution::Batched {
                projectives,
                affines,
            } => {
                let chunk_len = projectives.len();
                crate::cpu::phase(chunk_len.min(self.len), 32, || {
                    for (chunk_index, (inputs, outputs)) in points
                        .chunks(chunk_len)
                        .zip(destination.chunks_mut(chunk_len))
                        .enumerate()
                    {
                        let len = inputs.len();
                        // Workers write disjoint slices of the same admitted
                        // buffer. There is no hidden per-worker heap scratch.
                        crate::cpu::chunks_mut(&mut projectives[..len], 32, |offset, chunk| {
                            for (index, out) in chunk.iter_mut().enumerate() {
                                let index = offset + index;
                                *out = affine(inputs[index])
                                    * scalar_at(chunk_index * chunk_len + index);
                            }
                        });
                        // This pinned upstream leaf is serial and allocates no
                        // scratch. Its temporary invalid affine prefixes remain
                        // private until normalization has completed.
                        C::CurveExt::batch_normalize(&projectives[..len], &mut affines[..len]);
                        for (out, point) in outputs.iter_mut().zip(&affines[..len]) {
                            *out = wrap(*point);
                        }
                    }
                });
            }
        }
        Ok(())
    }
}
