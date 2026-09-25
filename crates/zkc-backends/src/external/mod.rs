//! Exact external construction primitives, without zkc artifact/domain prefixes.
//!
//! These providers know no proof schedule. Protocol authors choose transition
//! grouping and wire mappings; the runtime owns admission, caps and attempts.
//! See [`replay`] and the adjacent README for the finite conformance boundary.
pub mod grinding;
pub mod monero;
pub mod openvm;
pub mod replay;
pub mod wire;

/// Stable errors at the primitive/mapping boundary. No error means proof validity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    NonCanonicalField,
    InvalidBitWidth,
    SizeOverflow,
    MalformedReplay,
    UnknownMember,
    DuplicateIdentity,
    MissingItem,
    WrongItemType,
    UnmappedItem,
    ConflictingMapping,
    MissingGuard,
    ExpectationMismatch,
    ResourceLimit,
}
impl Error {
    pub fn code(self) -> &'static str {
        match self {
            Self::NonCanonicalField => "external:noncanonical-field",
            Self::InvalidBitWidth => "external:invalid-bit-width",
            Self::SizeOverflow => "external:size-overflow",
            Self::MalformedReplay => "external:malformed-replay",
            Self::UnknownMember => "external:unknown-member",
            Self::DuplicateIdentity => "external:duplicate-identity",
            Self::MissingItem => "external:missing-item",
            Self::WrongItemType => "external:wrong-item-type",
            Self::UnmappedItem => "external:unmapped-item",
            Self::ConflictingMapping => "external:conflicting-mapping",
            Self::MissingGuard => "external:missing-guard",
            Self::ExpectationMismatch => "external:expectation-mismatch",
            Self::ResourceLimit => "external:resource-limit",
        }
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;

/// Logical primitive work, not time, allocation accounting, or a security estimate.
/// Query work before a call to charge runtime caps without mutating transcript state.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    pub hash_calls: u64,
    pub hash_bytes: u64,
    pub permutations: u64,
    pub observes: u64,
    pub samples: u64,
}
impl Work {
    /// The deployment metric used by native external kernels and grinding.
    /// Each primitive count and hashed byte costs one unit; this is not a
    /// cryptographic cost model or a wall-clock prediction.
    pub fn units(self) -> Result<u64> {
        [
            self.hash_calls,
            self.hash_bytes,
            self.permutations,
            self.observes,
            self.samples,
        ]
        .into_iter()
        .try_fold(0u64, |a, b| a.checked_add(b).ok_or(Error::SizeOverflow))
    }

    pub fn checked_add(self, rhs: Self) -> Result<Self> {
        let add = |a: u64, b: u64| a.checked_add(b).ok_or(Error::SizeOverflow);
        Ok(Self {
            hash_calls: add(self.hash_calls, rhs.hash_calls)?,
            hash_bytes: add(self.hash_bytes, rhs.hash_bytes)?,
            permutations: add(self.permutations, rhs.permutations)?,
            observes: add(self.observes, rhs.observes)?,
            samples: add(self.samples, rhs.samples)?,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Transition<T> {
    pub value: T,
    pub work: Work,
}
