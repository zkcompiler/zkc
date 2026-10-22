//! Bounded affine-base multiplication followed by serial batch normalization.
//!
//! Normalization and zero-tolerant inversion are adapted from ark-ec 0.6.0
//! `models/short_weierstrass/group.rs::normalize_batch` and ark-ff 0.6.0
//! `fields/mod.rs::serial_batch_inversion_and_mul`. The prefix buffer is
//! fallible and reused here instead of allocating inside each provider call.
use crate::arkworks::Error;
use ark_ec::{
    AffineRepr, CurveGroup,
    short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::{Field, One, PrimeField, Zero};

/// Bound temporary payload independently of the complete input length.
pub const CHUNK_CAP: usize = 256;

pub(crate) fn workspace_bytes<P: SWCurveConfig>(len: usize) -> Option<usize> {
    if len > CHUNK_CAP {
        return None;
    }
    let width = size_of::<P::BaseField>()
        .checked_mul(2)?
        .checked_add(size_of::<Projective<P>>())?;
    len.checked_mul(width)
        .filter(|bytes| *bytes <= isize::MAX as usize)
}

struct Scratch<P: SWCurveConfig> {
    projectives: Vec<Projective<P>>,
    zs: Vec<P::BaseField>,
    prefixes: Vec<P::BaseField>,
}

impl<P: SWCurveConfig> Scratch<P> {
    fn new(len: usize) -> Result<Self, Error> {
        Ok(Self {
            projectives: crate::arkworks::allocation::vector(len)?,
            zs: crate::arkworks::allocation::vector(len)?,
            prefixes: crate::arkworks::allocation::vector(len)?,
        })
    }

    fn normalize<W>(&mut self, destination: &mut [W], wrap: impl Fn(Affine<P>) -> W) {
        self.zs.clear();
        self.zs.extend(self.projectives.iter().map(|point| point.z));
        self.prefixes.clear();
        let mut product = P::BaseField::one();
        for z in self.zs.iter().filter(|z| !z.is_zero()) {
            product *= z;
            self.prefixes.push(product);
        }
        // A product of nonzero field elements (including the empty product).
        let mut inverse = product.inverse().expect("nonzero normalization product");
        for (z, prefix) in self.zs.iter_mut().rev().filter(|z| !z.is_zero()).zip(
            self.prefixes
                .iter()
                .rev()
                .skip(1)
                .copied()
                .chain(Some(P::BaseField::one())),
        ) {
            let next = inverse * *z;
            *z = inverse * prefix;
            inverse = next;
        }
        for ((point, z), output) in self.projectives.iter().zip(&self.zs).zip(destination) {
            *output = wrap(if point.is_zero() {
                Affine::identity()
            } else {
                let z2 = z.square();
                // Only subgroup-preserving multiplication results reach here.
                Affine::new_unchecked(point.x * z2, point.y * z2 * z)
            });
        }
    }
}

/// Arithmetic choices within the same checked affine representation. Both
/// retain Arkworks' variable-time behavior; neither grants timing permission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Algorithm {
    Direct,
    Batched { chunk_len: usize },
}

/// A fixed choice refuses unavailable workspace. Automatic preparation may use
/// the direct algorithm when optional scratch cannot be allocated, before any
/// destination write. Execution never changes the prepared choice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Selection {
    Fixed(Algorithm),
    Automatic { max_workspace: usize },
}

/// Per-call prepared scaling with owned, bounded, unpublished scratch. The
/// curve type and exact length bind applicability. Reuse changes
/// neither the selected algorithm nor the resource requirement. Scratch is not
/// zeroized; callers retain their normal custody obligations for private data.
pub struct Plan<P: SWCurveConfig> {
    len: usize,
    execution: Execution<P>,
}

enum Execution<P: SWCurveConfig> {
    Direct,
    Batched {
        chunk_len: usize,
        scratch: Scratch<P>,
    },
}

impl<P: SWCurveConfig> Plan<P> {
    /// Maximum optional managed scratch for this public shape and allowance.
    /// Output, allocator metadata and provider-private allocations are excluded.
    pub fn workspace_bound(len: usize, max_workspace: usize) -> usize {
        let width = workspace_bytes::<P>(1).expect("one curve workspace element fits");
        let chunk = len.min(CHUNK_CAP).min(max_workspace / width);
        if chunk >= 2 {
            workspace_bytes::<P>(chunk).expect("bounded workspace")
        } else {
            0
        }
    }

    pub fn new(len: usize, selection: Selection) -> Result<Self, Error> {
        len.checked_mul(size_of::<Affine<P>>())
            .filter(|bytes| *bytes <= isize::MAX as usize)
            .ok_or(Error::CapacityOverflow)?;
        let (algorithm, optional) = match selection {
            Selection::Fixed(algorithm) => (algorithm, false),
            Selection::Automatic { max_workspace } => {
                let bytes = Self::workspace_bound(len, max_workspace);
                let width = workspace_bytes::<P>(1).expect("one curve workspace element fits");
                (
                    if bytes == 0 {
                        Algorithm::Direct
                    } else {
                        Algorithm::Batched {
                            chunk_len: bytes / width,
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
                    return Err(Error::InvalidEncoding);
                }
                match Scratch::new(chunk_len) {
                    Ok(scratch) => Execution::Batched { chunk_len, scratch },
                    Err(Error::Allocation) if optional => Execution::Direct,
                    Err(error) => return Err(error),
                }
            }
        };
        Ok(Self { len, execution })
    }
    pub fn algorithm(&self) -> Algorithm {
        match &self.execution {
            Execution::Direct => Algorithm::Direct,
            Execution::Batched { chunk_len, .. } => Algorithm::Batched {
                chunk_len: *chunk_len,
            },
        }
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    pub fn workspace_bytes(&self) -> usize {
        match self.algorithm() {
            Algorithm::Direct => 0,
            Algorithm::Batched { chunk_len } => {
                workspace_bytes::<P>(chunk_len).expect("prepared workspace")
            }
        }
    }
    pub fn output_bytes(&self) -> usize {
        self.len * size_of::<Affine<P>>()
    }

    pub(crate) fn scale_into<W: Copy>(
        &mut self,
        points: &[W],
        destination: &mut [W],
        scalar_at: impl Fn(usize) -> <P::ScalarField as PrimeField>::BigInt,
        affine: impl Fn(W) -> Affine<P>,
        wrap: impl Fn(Affine<P>) -> W,
    ) -> Result<(), Error> {
        if points.len() != self.len || destination.len() != self.len {
            return Err(Error::InvalidEncoding);
        }
        match &mut self.execution {
            Execution::Batched { chunk_len, scratch } => {
                for (chunk_index, (inputs, outputs)) in points
                    .chunks(*chunk_len)
                    .zip(destination.chunks_mut(*chunk_len))
                    .enumerate()
                {
                    scratch.projectives.clear();
                    scratch
                        .projectives
                        .extend(inputs.iter().enumerate().map(|(index, point)| {
                            // Preserve affine mul_bigint dispatch, including the provider's GLV choice.
                            affine(*point).mul_bigint(scalar_at(chunk_index * *chunk_len + index))
                        }));
                    scratch.normalize(outputs, &wrap);
                }
            }
            Execution::Direct => {
                for (index, (point, output)) in points.iter().zip(destination).enumerate() {
                    *output = wrap(affine(*point).mul_bigint(scalar_at(index)).into_affine());
                }
            }
        }
        Ok(())
    }
}

macro_rules! impl_scaling {
    ($wrapper:ty, $config:ty) => {
        impl $wrapper {
            /// Projective, Z and prefix payload for a batch, excluding output.
            /// Returns None above the conservative batch cap or on overflow.
            pub fn scaling_workspace_bytes(chunk_len: usize) -> Option<usize> {
                $crate::arkworks::scaling::workspace_bytes::<$config>(chunk_len)
            }
            /// Optional workspace bound for this public length and allowance.
            pub fn scaling_workspace_bound(len: usize, max_workspace: usize) -> usize {
                $crate::arkworks::scaling::Plan::<$config>::workspace_bound(len, max_workspace)
            }
            /// Freeze the algorithm and prepare all optional scratch before writes.
            pub fn scaling_plan(
                len: usize,
                selection: $crate::arkworks::scaling::Selection,
            ) -> Result<$crate::arkworks::scaling::Plan<$config>, $crate::arkworks::Error> {
                $crate::arkworks::scaling::Plan::new(len, selection)
            }
            /// Exact checked affine destinations. The caller accounts for and
            /// retains plan.workspace_bytes() until the prepared plan is dropped.
            pub fn scale_many_into(
                points: &[Self],
                scalar: <$config as ark_ec::CurveConfig>::ScalarField,
                destination: &mut [Self],
                plan: &mut $crate::arkworks::scaling::Plan<$config>,
            ) -> Result<(), $crate::arkworks::Error> {
                use ark_ff::PrimeField;
                let scalar = scalar.into_bigint();
                plan.scale_into(points, destination, |_| scalar, |point| point.0, Self)
            }
            /// Corresponding per-point scalars, with every shape check before writes.
            pub fn scale_each_into(
                scalars: &[<$config as ark_ec::CurveConfig>::ScalarField],
                points: &[Self],
                destination: &mut [Self],
                plan: &mut $crate::arkworks::scaling::Plan<$config>,
            ) -> Result<(), $crate::arkworks::Error> {
                use ark_ff::PrimeField;
                if scalars.len() != points.len() {
                    return Err($crate::arkworks::Error::InvalidEncoding);
                }
                plan.scale_into(
                    points,
                    destination,
                    |index| scalars[index].into_bigint(),
                    |point| point.0,
                    Self,
                )
            }
        }
    };
}
pub(crate) use impl_scaling;

#[cfg(test)]
mod tests {
    use super::*;

    fn normalization<P: SWCurveConfig>(lambda: P::BaseField) {
        let generator = Affine::<P>::generator();
        let twice = (generator + generator).into_affine();
        let expected = [Affine::identity(), generator, -generator, twice, generator];
        let mut scratch = Scratch::<P>::new(expected.len()).unwrap();
        for (index, point) in expected.iter().enumerate() {
            let mut projective = point.into_group();
            if index != 1 {
                projective.x *= lambda.square();
                projective.y *= lambda.square() * lambda;
                projective.z *= lambda;
            }
            scratch.projectives.push(projective);
        }
        let mut actual = [generator; 5];
        scratch.normalize(&mut actual, |point| point);
        for (actual, expected) in actual.iter().zip(expected) {
            assert_eq!(*actual, expected);
            assert_eq!(actual.x, expected.x);
            assert_eq!(actual.y, expected.y);
        }
        // Reuse the same buffers for an all-zero product and a shorter batch.
        scratch.projectives.clear();
        scratch.projectives.push(Projective::zero());
        scratch.normalize(&mut actual[..1], |point| point);
        assert!(actual[0].is_zero());
        assert_eq!(actual[0].x, P::BaseField::zero());
        assert_eq!(actual[0].y, P::BaseField::zero());
    }

    #[test]
    fn each_optional_allocation_failure_falls_back_before_writing() {
        use crate::arkworks::bls12_381::G1;
        let g = G1::generator();
        let choices = [g, G1::identity(), g.neg(), g.add(&g)];
        let points: Vec<_> = (0..513).map(|i| choices[i % choices.len()]).collect();
        let saved = points.clone();
        let scalars: Vec<_> = (0..points.len())
            .map(|i| crate::arkworks::bls12_381::Scalar::from((i % 5) as u64))
            .collect();
        for common in [false, true] {
            let expected: Vec<_> = points
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    p.scale(if common {
                        crate::arkworks::bls12_381::Scalar::from(3)
                    } else {
                        scalars[i]
                    })
                })
                .collect();
            for failure in 0..3 {
                let mut output = vec![G1::identity(); points.len()];
                crate::arkworks::allocation::VECTOR_REQUESTS.with(|count| count.set(0));
                crate::arkworks::allocation::VECTOR_FAILURE.with(|count| count.set(Some(failure)));
                let mut plan = G1::scaling_plan(
                    points.len(),
                    Selection::Automatic {
                        max_workspace: G1::scaling_workspace_bytes(256).unwrap(),
                    },
                )
                .unwrap();
                assert_eq!(plan.algorithm(), Algorithm::Direct);
                assert_eq!(plan.workspace_bytes(), 0);
                let result = if common {
                    G1::scale_many_into(
                        &points,
                        crate::arkworks::bls12_381::Scalar::from(3),
                        &mut output,
                        &mut plan,
                    )
                } else {
                    G1::scale_each_into(&scalars, &points, &mut output, &mut plan)
                };
                assert!(
                    crate::arkworks::allocation::VECTOR_FAILURE
                        .with(|count| count.get())
                        .is_none()
                );
                assert_eq!(
                    crate::arkworks::allocation::VECTOR_REQUESTS.with(|count| count.get()),
                    failure + 1
                );
                result.unwrap();
                assert_eq!(output, expected);
                assert_eq!(points, saved);
            }
        }
    }

    #[test]
    fn fixed_preparation_refuses_allocation_and_execution_never_reselects() {
        use crate::arkworks::bls12_381::{G1, Scalar};
        for failure in 0..3 {
            crate::arkworks::allocation::VECTOR_FAILURE.with(|value| value.set(Some(failure)));
            assert!(matches!(
                G1::scaling_plan(17, Selection::Fixed(Algorithm::Batched { chunk_len: 7 })),
                Err(Error::Allocation)
            ));
        }
        let mut plan =
            G1::scaling_plan(17, Selection::Fixed(Algorithm::Batched { chunk_len: 7 })).unwrap();
        let points = vec![G1::generator(); 17];
        let mut out = points.clone();
        crate::arkworks::allocation::VECTOR_REQUESTS.with(|value| value.set(0));
        crate::arkworks::allocation::VECTOR_FAILURE.with(|value| value.set(Some(0)));
        G1::scale_many_into(&points, Scalar::from(3), &mut out, &mut plan).unwrap();
        assert_eq!(plan.algorithm(), Algorithm::Batched { chunk_len: 7 });
        assert_eq!(
            crate::arkworks::allocation::VECTOR_REQUESTS.with(|value| value.get()),
            0
        );
        assert_eq!(
            crate::arkworks::allocation::VECTOR_FAILURE.with(|value| value.replace(None)),
            Some(0)
        );
        assert!(
            out.iter()
                .all(|point| *point == G1::generator().scale(Scalar::from(3)))
        );
    }

    #[test]
    fn serial_normalization_handles_scaled_jacobians_and_extension_coordinates() {
        normalization::<ark_bls12_381::g1::Config>(ark_bls12_381::Fq::from(7));
        normalization::<ark_bls12_381::g2::Config>(ark_bls12_381::Fq2::new(
            ark_bls12_381::Fq::from(7),
            ark_bls12_381::Fq::from(11),
        ));
        normalization::<ark_bn254::g1::Config>(ark_bn254::Fq::from(7));
        normalization::<ark_bn254::g2::Config>(ark_bn254::Fq2::new(
            ark_bn254::Fq::from(7),
            ark_bn254::Fq::from(11),
        ));
    }
}
