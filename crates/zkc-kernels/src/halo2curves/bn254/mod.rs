//! BN254 prime-subgroup arithmetic using halo2curves-axiom 0.7.3.
//!
//! Scalars and affine points have private coordinates. External bytes use the
//! same mathematical encoding as the Arkworks provider, not upstream's point
//! encoding. No operation grants an operand-independent timing guarantee. MSM
//! is explicitly variable-time; its caller owns timing permission and admission.
//! Bounds cover payload, not allocator overhead or recoverable upstream OOM.
use halo2curves_axiom::{
    CurveAffine,
    group::{Curve, cofactor::CofactorGroup, prime::PrimeCurveAffine},
};

/// Upstream types for typed family adapters. Point ingress is checked even
/// through `from_element`; projective coordinates never cross this boundary.
pub use halo2curves_axiom::bn256::{
    Fr as ScalarElement, G1Affine as G1Element, G2Affine as G2Element,
};

mod scalar;
pub use scalar::{MODULUS, Scalar, decode_scalar, encode_scalar, parse_decimal};
mod bulk;
mod codec;
pub use bulk::{G1Vector, G2Vector, ScalarVector};
mod bounds;
pub use bounds::{msm_work, msm_workspace_bytes, pairing_work, pairing_workspace_bytes};
mod pairing;
pub use pairing::{pairing_check, pairing_check_bulk};
pub mod scaling;

/// Kernel refusals are separate from a valid but false pairing equation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidEncoding,
    LengthMismatch,
    CapacityOverflow,
    Allocation,
    InvalidPlan,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::InvalidEncoding => "invalid-encoding",
            Self::LengthMismatch => "length-mismatch",
            Self::CapacityOverflow => "capacity-overflow",
            Self::Allocation => "allocation-failed",
            Self::InvalidPlan => "invalid-plan",
        })
    }
}
impl std::error::Error for Error {}

fn payload<T>(len: usize) -> Result<usize, Error> {
    len.checked_mul(size_of::<T>())
        .filter(|bytes| *bytes <= isize::MAX as usize)
        .ok_or(Error::CapacityOverflow)
}

fn vector<T>(len: usize) -> Result<Vec<T>, Error> {
    payload::<T>(len)?;
    if len == 0 {
        return Ok(Vec::new());
    }
    crate::allocation::reserve(len).map_err(|_| Error::Allocation)
}

macro_rules! source_group {
    ($name:ident, $bulk:ident, $affine:ty, $bytes:expr, $validate:path, $decode:path, $encode:path) => {
        /// Validated affine prime-subgroup point, including identity.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $name($affine);
        impl $name {
            pub const BYTES: usize = $bytes;
            pub fn generator() -> Self {
                Self(<$affine>::generator())
            }
            pub fn identity() -> Self {
                Self(<$affine>::identity())
            }
            /// Validate curve membership and the prime subgroup. This accepts
            /// typed affine coordinates, not Montgomery or projective bytes.
            pub fn from_element(element: $affine) -> Result<Self, Error> {
                $validate(element).map(Self)
            }
            pub fn from_affine(element: $affine) -> Result<Self, Error> {
                Self::from_element(element)
            }
            pub fn into_element(self) -> $affine {
                self.0
            }
            pub fn add(&self, rhs: &Self) -> Self {
                Self((self.0 + rhs.0).to_affine())
            }
            pub fn neg(&self) -> Self {
                Self(-self.0)
            }
            pub fn equal(&self, rhs: &Self) -> bool {
                self == rhs
            }
            pub fn is_identity(&self) -> bool {
                bool::from(self.0.is_identity())
            }
            pub fn scale(&self, scalar: Scalar) -> Self {
                Self((self.0 * scalar.0).to_affine())
            }
            /// Arkworks-compatible compressed bytes with unique infinity.
            pub fn to_bytes(&self) -> [u8; Self::BYTES] {
                $encode(self.0)
            }
            pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
                $decode(bytes).map(Self)
            }
            /// Explicitly variable-time MSM, with no timing authorization
            /// implied by this method. Empty/all-zero inputs give identity.
            /// This convenience adapter stages scalars and bases; resident
            /// callers use the owned buffer's MSM without those copies.
            pub fn msm(scalars: &[Scalar], points: &[Self]) -> Result<Self, Error> {
                if scalars.len() != points.len() {
                    return Err(Error::LengthMismatch);
                }
                msm_workspace_bytes(points.len())?;
                msm_work(points.len())?;
                let points = $bulk::from_slice(points)?;
                let scalars = ScalarVector::from_slice(scalars)?;
                points.msm(&scalars)
            }
            /// Maximum projective and affine normalization scratch for a batch.
            pub fn scaling_workspace_bytes(chunk_len: usize) -> Option<usize> {
                scaling::workspace_bytes::<$affine>(chunk_len)
            }
            pub fn scaling_workspace_bound(len: usize, max_workspace: usize) -> usize {
                scaling::Plan::<$affine>::workspace_bound(len, max_workspace)
            }
            pub fn scaling_plan(
                len: usize,
                selection: scaling::Selection,
            ) -> Result<scaling::Plan<$affine>, Error> {
                scaling::Plan::new(len, selection)
            }
            /// All shape checks precede writes; plan scratch is already owned.
            pub fn scale_many_into(
                points: &[Self],
                scalar: Scalar,
                destination: &mut [Self],
                plan: &mut scaling::Plan<$affine>,
            ) -> Result<(), Error> {
                plan.scale_into(points, destination, |_| scalar.0, |p| p.0, Self)
            }
            pub fn scale_each_into(
                scalars: &[Scalar],
                points: &[Self],
                destination: &mut [Self],
                plan: &mut scaling::Plan<$affine>,
            ) -> Result<(), Error> {
                if scalars.len() != points.len() {
                    return Err(Error::LengthMismatch);
                }
                plan.scale_into(points, destination, |i| scalars[i].0, |p| p.0, Self)
            }
        }
    };
}

fn validate_g1(point: G1Element) -> Result<G1Element, Error> {
    // Upstream's cofactor-one is_torsion_free is unconditional: curve
    // validation is still essential at every typed ingress.
    if !bool::from(point.is_on_curve()) {
        return Err(Error::InvalidEncoding);
    }
    Ok(if bool::from(point.is_identity()) {
        G1Element::identity()
    } else {
        point
    })
}

fn validate_g2(point: G2Element) -> Result<G2Element, Error> {
    // Never call G2::into_subgroup: it is unimplemented in the pinned source.
    if !bool::from(point.is_on_curve()) || !bool::from(point.to_curve().is_torsion_free()) {
        return Err(Error::InvalidEncoding);
    }
    Ok(if bool::from(point.is_identity()) {
        G2Element::identity()
    } else {
        point
    })
}

source_group!(
    G1,
    G1Vector,
    G1Element,
    32,
    validate_g1,
    codec::decode_g1,
    codec::encode_g1
);
source_group!(
    G2,
    G2Vector,
    G2Element,
    64,
    validate_g2,
    codec::decode_g2,
    codec::encode_g2
);

pub mod arkworks {
    //! Explicit checked mathematical-byte transitions. No coordinate or limb
    //! copying between providers, whose projective conventions differ.
    use super::{Error, G1, G2, Scalar, decode_scalar};
    use crate::arkworks::bn254 as ark;

    pub fn import_scalar(scalar: ark::Scalar) -> Result<Scalar, Error> {
        decode_scalar(&ark::encode_scalar(&scalar).map_err(|_| Error::InvalidEncoding)?)
    }
    pub fn export_scalar(scalar: Scalar) -> Result<ark::Scalar, Error> {
        ark::decode_scalar(&scalar.to_bytes_le()).map_err(|_| Error::InvalidEncoding)
    }
    macro_rules! bridge {
        ($point:ident, $import:ident, $export:ident) => {
            pub fn $import(point: ark::$point) -> Result<$point, Error> {
                $point::from_bytes(&point.to_bytes().map_err(|_| Error::InvalidEncoding)?)
            }
            pub fn $export(point: $point) -> Result<ark::$point, Error> {
                ark::$point::from_bytes(&point.to_bytes()).map_err(|_| Error::InvalidEncoding)
            }
        };
    }
    bridge!(G1, import_g1, export_g1);
    bridge!(G2, import_g2, export_g2);
}
