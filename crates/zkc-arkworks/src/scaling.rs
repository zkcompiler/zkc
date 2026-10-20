//! Bounded affine-base multiplication followed by serial batch normalization.
//!
//! Normalization and zero-tolerant inversion are adapted from ark-ec 0.6.0
//! `models/short_weierstrass/group.rs::normalize_batch` and ark-ff 0.6.0
//! `fields/mod.rs::serial_batch_inversion_and_mul`. The prefix buffer is
//! fallible and reused here instead of allocating inside each provider call.
use crate::Error;
use ark_ec::{
    AffineRepr, CurveGroup,
    short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::{Field, One, PrimeField, Zero};

/// Bound temporary payload independently of the complete input length.
pub const SCALING_CHUNK_CAP: usize = 256;

pub(crate) fn workspace_bytes<P: SWCurveConfig>(len: usize) -> Option<usize> {
    if len > SCALING_CHUNK_CAP {
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
            projectives: crate::bounds::vector(len)?,
            zs: crate::bounds::vector(len)?,
            prefixes: crate::bounds::vector(len)?,
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

pub(crate) fn scale_into<P: SWCurveConfig, W: Copy>(
    points: &[W],
    destination: &mut [W],
    chunk_len: usize,
    scalar_at: impl Fn(usize) -> <P::ScalarField as PrimeField>::BigInt,
    affine: impl Fn(W) -> Affine<P>,
    wrap: impl Fn(Affine<P>) -> W,
) -> Result<(), Error> {
    if points.len() != destination.len() {
        return Err(Error::InvalidEncoding);
    }
    let chunk_len = chunk_len.min(points.len()).min(SCALING_CHUNK_CAP);
    // Optional workspace failure must not add an allocation refusal to a call
    // that previously needed only its output allocation. Allocate before writes.
    let scratch = if chunk_len >= 2 {
        Scratch::<P>::new(chunk_len).ok()
    } else {
        None
    };
    if let Some(mut scratch) = scratch {
        for (chunk_index, (inputs, outputs)) in points
            .chunks(chunk_len)
            .zip(destination.chunks_mut(chunk_len))
            .enumerate()
        {
            scratch.projectives.clear();
            scratch
                .projectives
                .extend(inputs.iter().enumerate().map(|(index, point)| {
                    // Preserve affine mul_bigint dispatch; projective GLV is separate.
                    affine(*point).mul_bigint(scalar_at(chunk_index * chunk_len + index))
                }));
            scratch.normalize(outputs, &wrap);
        }
    } else {
        for (index, (point, output)) in points.iter().zip(destination).enumerate() {
            *output = wrap(affine(*point).mul_bigint(scalar_at(index)).into_affine());
        }
    }
    Ok(())
}

macro_rules! impl_scaling {
    ($wrapper:ty, $config:ty) => {
        impl $wrapper {
            /// Requested projective, Z and prefix payload for this batch length.
            /// Returns None above the conservative batch cap or on size overflow.
            /// Output storage and hidden provider/allocator overhead are excluded.
            pub fn scaling_workspace_bytes(chunk_len: usize) -> Option<usize> {
                $crate::scaling::workspace_bytes::<$config>(chunk_len)
            }

            /// Scale checked bases into an equally sized initialized private slice.
            /// The caller accounts for scaling_workspace_bytes(chunk_len) while
            /// this runs. A chunk below two or failed scratch allocation uses the
            /// scalar loop. All length checks precede destination writes.
            pub fn scale_many_into(
                points: &[Self],
                scalar: <$config as ark_ec::CurveConfig>::ScalarField,
                destination: &mut [Self],
                chunk_len: usize,
            ) -> Result<(), $crate::Error> {
                use ark_ff::PrimeField;
                let scalar = scalar.into_bigint();
                $crate::scaling::scale_into::<$config, Self>(
                    points,
                    destination,
                    chunk_len,
                    |_| scalar,
                    |point| point.0,
                    Self,
                )
            }

            /// Scale each checked base by its corresponding scalar into an
            /// equally sized initialized private slice. Workspace and fallback
            /// follow scale_many_into; all lengths are checked before writes.
            pub fn scale_each_into(
                scalars: &[<$config as ark_ec::CurveConfig>::ScalarField],
                points: &[Self],
                destination: &mut [Self],
                chunk_len: usize,
            ) -> Result<(), $crate::Error> {
                use ark_ff::PrimeField;
                if scalars.len() != points.len() {
                    return Err($crate::Error::InvalidEncoding);
                }
                $crate::scaling::scale_into::<$config, Self>(
                    points,
                    destination,
                    chunk_len,
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
        use crate::GroupPoint;
        let g = GroupPoint::generator();
        let choices = [g, GroupPoint::identity(), g.neg(), g.add(&g)];
        let points: Vec<_> = (0..513).map(|i| choices[i % choices.len()]).collect();
        let saved = points.clone();
        let scalars: Vec<_> = (0..points.len())
            .map(|i| crate::Scalar::from((i % 5) as u64))
            .collect();
        for common in [false, true] {
            let expected: Vec<_> = points
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    p.scale(if common {
                        crate::Scalar::from(3)
                    } else {
                        scalars[i]
                    })
                })
                .collect();
            for failure in 0..3 {
                let mut output = vec![GroupPoint::identity(); points.len()];
                crate::bounds::VECTOR_REQUESTS.with(|count| count.set(0));
                crate::bounds::VECTOR_FAILURE.with(|count| count.set(Some(failure)));
                let result = if common {
                    GroupPoint::scale_many_into(&points, crate::Scalar::from(3), &mut output, 256)
                } else {
                    GroupPoint::scale_each_into(&scalars, &points, &mut output, 256)
                };
                assert!(
                    crate::bounds::VECTOR_FAILURE
                        .with(|count| count.get())
                        .is_none()
                );
                assert_eq!(
                    crate::bounds::VECTOR_REQUESTS.with(|count| count.get()),
                    failure + 1
                );
                result.unwrap();
                assert_eq!(output, expected);
                assert_eq!(points, saved);
            }
        }
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
