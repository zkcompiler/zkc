use std::fmt;

/// Admission/host errors are distinct from a well-shaped failed PCS check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// A table must contain a positive power-of-two number of scalars.
    InvalidTableLength,
    /// The selected profile excludes this arity.
    ArityLimit,
    /// The selected profile excludes this table size.
    ElementLimit,
    /// The selected profile excludes this byte length.
    ByteLimit,
    /// The selected profile excludes this setup work size.
    SetupLimit,
    /// A size calculation cannot be represented on this host.
    CapacityOverflow,
    /// A fallible allocation failed; published values remain unchanged.
    Allocation,
    /// A table, point or artifact has the wrong number of variables.
    ArityMismatch {
        /// Required arity.
        expected: usize,
        /// Supplied arity.
        actual: usize,
    },
    /// PCS keys and round polynomials require at least one variable.
    PositiveArityRequired,
    /// Extracting a scalar requires a fully restricted table.
    ZeroArityRequired,
    /// Invalid scalar/point bytes, subgroup, exact length or decimal syntax.
    InvalidEncoding,
    /// Decoding succeeded but canonical re-encoding differs.
    NonCanonicalEncoding,
    /// Wrong wire version, profile marker or artifact kind.
    InvalidHeader,
    /// Setup/key metadata, material fingerprint or shared generators do not
    /// match the independently selected material.
    KeyMismatch,
    /// Invalid key shape or a zero setup generator.
    InvalidKey,
    /// OS entropy could not seed the random source.
    EntropyUnavailable,
}

impl Error {
    /// Stable machine-readable error code. Message prose is not a wire format.
    pub const fn code(&self) -> &'static str {
        match self {
            Self::InvalidTableLength => "invalid-table-length",
            Self::ArityLimit => "arity-limit",
            Self::ElementLimit => "element-limit",
            Self::ByteLimit => "byte-limit",
            Self::SetupLimit => "setup-limit",
            Self::CapacityOverflow => "capacity-overflow",
            Self::Allocation => "allocation-failed",
            Self::ArityMismatch { .. } => "arity-mismatch",
            Self::PositiveArityRequired => "positive-arity-required",
            Self::ZeroArityRequired => "zero-arity-required",
            Self::InvalidEncoding => "invalid-encoding",
            Self::NonCanonicalEncoding => "noncanonical-encoding",
            Self::InvalidHeader => "invalid-header",
            Self::KeyMismatch => "key-mismatch",
            Self::InvalidKey => "invalid-key",
            Self::EntropyUnavailable => "entropy-unavailable",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.code())?;
        if let Self::ArityMismatch { expected, actual } = self {
            write!(f, ": expected {expected}, got {actual}")?;
        }
        Ok(())
    }
}

impl std::error::Error for Error {}

pub(crate) fn same_arity(expected: usize, actual: usize) -> Result<(), Error> {
    if expected == actual {
        Ok(())
    } else {
        Err(Error::ArityMismatch { expected, actual })
    }
}
