//! Representation boundaries for pinned Edwards arithmetic and ordered MLEs.
//!
//! Raw bytes are observations; decoding and cofactor clearing are distinct maps.
//! The Edwards adapter uses curve25519-dalek 4.1.3, with canonical round-trip
//! admission matching Monero 4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5's
//! `ge_frombytes_vartime` canonical-y and zero-x-sign checks. This is not a
//! complete proof-decoder or hash-to-point implementation.
use curve25519_dalek::{
    edwards::{CompressedEdwardsY, EdwardsPoint},
    scalar::Scalar,
};
use p3_field_043::{ExtensionField, Field};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RepresentationError {
    InvalidPoint,
    NonCanonicalPoint,
    NotPrimeSubgroup,
    RawPointModule,
    DuplicateAxis,
    DimensionOverflow,
    ShapeMismatch,
    DuplicateNode,
    UnsupportedDomain,
    AxisMismatch,
    InvalidPermutation,
    IndexOutOfBounds,
}
impl RepresentationError {
    pub const fn code(self) -> &'static str {
        match self {
            Self::InvalidPoint => "representation.invalid-point",
            Self::NonCanonicalPoint => "representation.noncanonical-point",
            Self::NotPrimeSubgroup => "representation.not-prime-subgroup",
            Self::RawPointModule => "representation.raw-point-module",
            Self::DuplicateAxis => "representation.duplicate-axis",
            Self::DimensionOverflow => "representation.dimension-overflow",
            Self::ShapeMismatch => "representation.shape-mismatch",
            Self::DuplicateNode => "representation.duplicate-node",
            Self::UnsupportedDomain => "representation.unsupported-domain",
            Self::AxisMismatch => "representation.axis-mismatch",
            Self::InvalidPermutation => "representation.invalid-permutation",
            Self::IndexOutOfBounds => "representation.index-out-of-bounds",
        }
    }
}
impl std::fmt::Display for RepresentationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}
impl std::error::Error for RepresentationError {}
type Result<T> = std::result::Result<T, RepresentationError>;

/// Uninterpreted 32 bytes, including possibly invalid point encodings.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RawEncodedEdwards([u8; 32]);
impl RawEncodedEdwards {
    pub const fn new(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }
    pub const fn transcript_bytes(&self) -> &[u8; 32] {
        &self.0
    }
    pub fn decode(self) -> Result<DecodedEdwards> {
        let point = CompressedEdwardsY(self.0)
            .decompress()
            .ok_or(RepresentationError::InvalidPoint)?;
        if point.compress().to_bytes() != self.0 {
            return Err(RepresentationError::NonCanonicalPoint);
        }
        Ok(DecodedEdwards { raw: self, point })
    }
}

/// A valid canonical Edwards representative, which may carry torsion.
#[derive(Clone, Debug)]
pub struct DecodedEdwards {
    raw: RawEncodedEdwards,
    point: EdwardsPoint,
}
impl DecodedEdwards {
    pub const fn raw(&self) -> &RawEncodedEdwards {
        &self.raw
    }
    /// Mathematical integer multiplication [8]P, not scalar-field reassociation.
    pub fn clear_cofactor(&self) -> SubgroupEdwards {
        SubgroupEdwards(self.point.mul_by_cofactor())
    }
    /// No clearing: establish subgroup membership of this exact decoded value.
    pub fn check_subgroup(&self) -> Result<SubgroupEdwards> {
        if self.point.is_torsion_free() {
            Ok(SubgroupEdwards(self.point))
        } else {
            Err(RepresentationError::NotPrimeSubgroup)
        }
    }
}

/// Invariant: the inner Edwards point is in the prime-order subgroup.
/// Identity is allowed. No Ristretto encoding or quotient is used.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubgroupEdwards(EdwardsPoint);
impl SubgroupEdwards {
    pub fn encoding(&self) -> RawEncodedEdwards {
        RawEncodedEdwards(self.0.compress().to_bytes())
    }
    pub fn scale(&self, scalar: Scalar) -> Self {
        Self(self.0 * scalar)
    }
    pub fn add(&self, other: &Self) -> Self {
        Self(self.0 + other.0)
    }
    /// Lawful on this carrier: (a/8)P = a((1/8)P).
    pub fn inverse_eight(&self) -> Self {
        self.scale(Scalar::from(8u64).invert())
    }
}

/// Admission carries a reference to the actual arithmetic value. Raw/decoded
/// representations never receive a scalar-module witness implicitly, even when
/// their bytes happen to encode a subgroup point; call check_subgroup explicitly.
pub enum EdwardsValue<'a> {
    Raw(&'a RawEncodedEdwards),
    Decoded(&'a DecodedEdwards),
    Subgroup(&'a SubgroupEdwards),
}
pub fn admit_scalar_module(value: EdwardsValue<'_>) -> Result<&SubgroupEdwards> {
    match value {
        EdwardsValue::Subgroup(point) => Ok(point),
        EdwardsValue::Raw(_) | EdwardsValue::Decoded(_) => Err(RepresentationError::RawPointModule),
    }
}

/// Axis identities in increasing index-bit significance (LSB first). These are
/// logical coordinates, not a promise of physical row/column-major layout.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderedAxes(Vec<u32>);
impl OrderedAxes {
    pub fn new(axes: Vec<u32>) -> Result<Self> {
        if axes.len() >= usize::BITS as usize {
            return Err(RepresentationError::DimensionOverflow);
        }
        for (i, axis) in axes.iter().enumerate() {
            if axes[..i].contains(axis) {
                return Err(RepresentationError::DuplicateAxis);
            }
        }
        Ok(Self(axes))
    }
    pub fn axes(&self) -> &[u32] {
        &self.0
    }
    pub fn cardinality(&self) -> usize {
        1usize << self.0.len()
    }
    pub fn permutation_to(&self, target: &Self) -> Result<AxisPermutation> {
        if self.0.len() != target.0.len() || target.0.iter().any(|axis| !self.0.contains(axis)) {
            return Err(RepresentationError::InvalidPermutation);
        }
        Ok(AxisPermutation {
            source: self.clone(),
            target: target.clone(),
        })
    }
}

/// A checked bijection, with its full source and target domains retained.
#[derive(Clone, Debug)]
pub struct AxisPermutation {
    source: OrderedAxes,
    target: OrderedAxes,
}
impl AxisPermutation {
    pub fn source(&self) -> &OrderedAxes {
        &self.source
    }
    pub fn target(&self) -> &OrderedAxes {
        &self.target
    }
    /// Output row j reads this input row. Computed without a dense map.
    pub fn source_index(&self, j: usize) -> Result<usize> {
        if j >= self.target.cardinality() {
            return Err(RepresentationError::IndexOutOfBounds);
        }
        let mut result = 0;
        for (target_bit, axis) in self.target.0.iter().enumerate() {
            let source_bit = self
                .source
                .0
                .iter()
                .position(|a| a == axis)
                .expect("checked permutation");
            result |= ((j >> target_bit) & 1) << source_bit;
        }
        Ok(result)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FoldConvention {
    Adjacent,
    HalfFirst,
}

/// Actual interpolation data. Unsupported domains retain their nodes and values
/// but receive no Boolean-MLE fold law. No protocol-name dispatch is involved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvaluationDomain<F> {
    Boolean(OrderedAxes),
    Univariate(Vec<F>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvaluationTable<F> {
    domain: EvaluationDomain<F>,
    values: Vec<F>,
}
impl<F: Field> EvaluationTable<F> {
    pub fn new(domain: EvaluationDomain<F>, values: Vec<F>) -> Result<Self> {
        let cardinality = match &domain {
            EvaluationDomain::Boolean(axes) => axes.cardinality(),
            EvaluationDomain::Univariate(nodes) => {
                if nodes.is_empty() {
                    return Err(RepresentationError::ShapeMismatch);
                }
                for (i, node) in nodes.iter().enumerate() {
                    if nodes[..i].contains(node) {
                        return Err(RepresentationError::DuplicateNode);
                    }
                }
                nodes.len()
            }
        };
        if values.len() != cardinality {
            return Err(RepresentationError::ShapeMismatch);
        }
        Ok(Self { domain, values })
    }
    pub fn domain(&self) -> &EvaluationDomain<F> {
        &self.domain
    }
    pub fn values(&self) -> &[F] {
        &self.values
    }
    /// Successful admission returns the actual ordered domain of this table.
    pub fn admit_boolean_mle(&self) -> Result<&OrderedAxes> {
        match &self.domain {
            EvaluationDomain::Boolean(axes) => Ok(axes),
            EvaluationDomain::Univariate(_) => Err(RepresentationError::UnsupportedDomain),
        }
    }
    pub fn fold(&self, axis: u32, convention: FoldConvention, r: F) -> Result<Self> {
        let axes = self.admit_boolean_mle()?;
        let position = match convention {
            FoldConvention::Adjacent => 0,
            FoldConvention::HalfFirst => axes
                .0
                .len()
                .checked_sub(1)
                .ok_or(RepresentationError::AxisMismatch)?,
        };
        if axes.0.get(position) != Some(&axis) {
            return Err(RepresentationError::AxisMismatch);
        }
        let n = self.values.len() / 2;
        let values = (0..n)
            .map(|i| {
                let (lo, hi) = match convention {
                    FoldConvention::Adjacent => (2 * i, 2 * i + 1),
                    FoldConvention::HalfFirst => (i, i + n),
                };
                self.values[lo] + r * (self.values[hi] - self.values[lo])
            })
            .collect();
        let mut remaining = axes.0.clone();
        remaining.remove(position);
        Self::new(
            EvaluationDomain::Boolean(OrderedAxes::new(remaining)?),
            values,
        )
    }
    /// Challenges are identified by axis; duplicate/missing/out-of-order axes
    /// refuse, rather than silently interpreting an incorrectly ordered point.
    pub fn evaluate(&self, point_lsb_first: &[(u32, F)]) -> Result<F> {
        let axes = self.admit_boolean_mle()?;
        if point_lsb_first.len() != axes.0.len() {
            return Err(RepresentationError::ShapeMismatch);
        }
        let mut table = self.clone();
        for &(axis, r) in point_lsb_first {
            table = table.fold(axis, FoldConvention::Adjacent, r)?;
        }
        Ok(table.values[0])
    }
    pub fn permute_axes(&self, map: &AxisPermutation) -> Result<Self> {
        if self.admit_boolean_mle()? != map.source() {
            return Err(RepresentationError::AxisMismatch);
        }
        let values = (0..self.values.len())
            .map(|i| self.values[map.source_index(i).expect("bounded index")])
            .collect();
        Self::new(EvaluationDomain::Boolean(map.target.clone()), values)
    }
    /// Cyclic row view output[i] = input[(i + shift) mod n]. This grants no
    /// coordinate substitution law for evaluating the rotated polynomial.
    pub fn rotate_rows(&self, shift: usize) -> Result<Self> {
        self.admit_boolean_mle()?;
        let n = self.values.len();
        let shift = shift % n;
        let values = (0..n)
            .map(|i| {
                let j = if i >= n - shift {
                    i - (n - shift)
                } else {
                    i + shift
                };
                self.values[j]
            })
            .collect();
        Self::new(self.domain.clone(), values)
    }
    /// The library's ExtensionField relation supplies the base-field embedding;
    /// arbitrary caller functions cannot claim an embedding law.
    pub fn embed<E: ExtensionField<F>>(&self) -> EvaluationTable<E> {
        let domain = match &self.domain {
            EvaluationDomain::Boolean(axes) => EvaluationDomain::Boolean(axes.clone()),
            EvaluationDomain::Univariate(nodes) => {
                EvaluationDomain::Univariate(nodes.iter().copied().map(E::from).collect())
            }
        };
        EvaluationTable {
            domain,
            values: self.values.iter().copied().map(E::from).collect(),
        }
    }
}
