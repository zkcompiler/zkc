//! Native library installations, independent of admission's nominal catalogue.
use zkc_runtime::interactive::{Identity, LogicalType, PhysicalType, Representation, Type};

#[derive(Clone, Copy, Debug)]
pub struct NativeDomain {
    pub field: Identity,
    pub group: Option<Identity>,
    pub provider: &'static str,
}
pub const BN254_G1: NativeDomain = NativeDomain {
    field: Identity::Bn254Fr,
    group: Some(Identity::Bn254G1),
    provider: "arkworks",
};
pub const BN254_G2: NativeDomain = NativeDomain {
    field: Identity::Bn254Fr,
    group: Some(Identity::Bn254G2),
    provider: "arkworks",
};
pub const BN254_GT: NativeDomain = NativeDomain {
    field: Identity::Bn254Fr,
    group: Some(Identity::Bn254Gt),
    provider: "arkworks",
};
pub const BLS: NativeDomain = NativeDomain {
    field: Identity::Bls12381Fr,
    group: Some(Identity::Bls12381G1),
    provider: "arkworks",
};
pub const BLS_G2: NativeDomain = NativeDomain {
    field: Identity::Bls12381Fr,
    group: Some(Identity::Bls12381G2),
    provider: "arkworks",
};
pub const BLS_GT: NativeDomain = NativeDomain {
    field: Identity::Bls12381Fr,
    group: Some(Identity::Bls12381Gt),
    provider: "arkworks",
};
pub const EDWARDS: NativeDomain = NativeDomain {
    field: Identity::Ristretto255Scalar,
    group: Some(Identity::Edwards25519Prime),
    provider: "dalek",
};
pub const RISTRETTO: NativeDomain = NativeDomain {
    field: Identity::Ristretto255Scalar,
    group: Some(Identity::Ristretto255Group),
    provider: "dalek",
};
pub const KOALA_BEAR: NativeDomain = NativeDomain {
    field: Identity::KoalaBear,
    group: None,
    provider: "plonky3",
};
pub const KOALA_BEAR_EXT8: NativeDomain = NativeDomain {
    field: Identity::KoalaBearExt8,
    group: None,
    provider: "plonky3",
};
pub const KOALA_BEAR_EXT4: NativeDomain = NativeDomain {
    field: Identity::KoalaBearExt4,
    group: None,
    provider: "plonky3",
};
/// Characteristic-two fields from Plonky3 0.8.0's `p3-binary-field`.
pub const BINARY64: NativeDomain = NativeDomain {
    field: Identity::Binary64,
    group: None,
    provider: "plonky3",
};
pub const BINARY64_EXT3: NativeDomain = NativeDomain {
    field: Identity::Binary64Ext3,
    group: None,
    provider: "plonky3",
};
pub const INSTALLED: &[NativeDomain] = &[
    BLS,
    RISTRETTO,
    EDWARDS,
    KOALA_BEAR,
    KOALA_BEAR_EXT8,
    KOALA_BEAR_EXT4,
    BINARY64,
    BINARY64_EXT3,
    BN254_G1,
    BN254_G2,
    BN254_GT,
    BLS_G2,
    BLS_GT,
];
impl NativeDomain {
    pub fn physical(self, kind: Type) -> Option<PhysicalType> {
        use Representation as R;
        use Type::*;
        if matches!(kind, Group | Groups) {
            let group = self.group?;
            if group.scalar_field()? != self.field {
                return None;
            }
            let representation = match (group, kind) {
                (Identity::Bls12381G1, Group) => R::G1,
                (Identity::Bls12381G1, Groups) => R::Groups,
                (Identity::Bn254G1, Group) => R::Bn254G1,
                (Identity::Bn254G1, Groups) => R::Bn254G1Vector,
                (Identity::Bn254G2, Group) => R::Bn254G2,
                (Identity::Bn254G2, Groups) => R::Bn254G2Vector,
                (Identity::Bn254Gt, Group) => R::Bn254Gt,
                (Identity::Bls12381G2, Group) => R::Bls12381G2,
                (Identity::Bls12381G2, Groups) => R::Bls12381G2Vector,
                (Identity::Bls12381Gt, Group) => R::Bls12381Gt,
                (Identity::Ristretto255Group, Group) => R::Ristretto,
                (Identity::Ristretto255Group, Groups) => R::RistrettoVector,
                (Identity::Edwards25519Prime, Group) => R::EdwardsPrime,
                (Identity::Edwards25519Prime, Groups) => R::EdwardsPrimeVector,
                _ => return None,
            };
            return PhysicalType::new(LogicalType::new(kind, group).ok()?, representation).ok();
        }
        let (identity, representation) = match (self.field, kind) {
            (Identity::Bn254Fr, Field) => (self.field, R::Bn254Fr),
            (Identity::Bn254Fr, Vector) => (self.field, R::Bn254FrVector),
            (Identity::Bn254Fr, Polynomial) => (self.field, R::Bn254Polynomial),
            (Identity::Bn254Fr, Round) => (self.field, R::Bn254Round),
            (Identity::Bn254Fr, Matrix) => (self.field, R::Bn254SparseCoo),
            (Identity::Bn254Fr, Rng) => (self.field, R::Resource),
            (_, Bool) => (Identity::None, R::Bool),
            (_, Index) => (Identity::None, R::Index),
            (_, Indices) => (Identity::None, R::Indices),
            (_, Bytes) => (Identity::None, R::Bytes),
            (_, Shake128State) => (Identity::None, R::Shake128State),
            (Identity::Bls12381Fr, Matrix) => (self.field, R::FrSparseCoo),
            (Identity::Ristretto255Scalar, Matrix) => (self.field, R::DalekSparseCoo),
            (Identity::KoalaBear, Matrix) => (self.field, R::KoalaBearSparseCoo),
            (Identity::KoalaBearExt8, Field) => (self.field, R::KoalaBearExt8),
            (Identity::KoalaBearExt8, Vector) => (self.field, R::KoalaBearExt8Vector),
            (Identity::KoalaBearExt8, Polynomial) => (self.field, R::KoalaBearExt8Polynomial),
            (Identity::KoalaBearExt8, Round) => (self.field, R::KoalaBearExt8Round),
            (Identity::KoalaBearExt8, Matrix) => (self.field, R::KoalaBearExt8SparseCoo),
            (Identity::KoalaBearExt4, Field) => (self.field, R::KoalaBearExt4),
            (Identity::KoalaBearExt4, Vector) => (self.field, R::KoalaBearExt4Vector),
            (Identity::KoalaBearExt4, Polynomial) => (self.field, R::KoalaBearExt4Polynomial),
            (Identity::KoalaBearExt4, Round) => (self.field, R::KoalaBearExt4Round),
            (Identity::KoalaBearExt4, Matrix) => (self.field, R::KoalaBearExt4SparseCoo),
            (Identity::Binary64, Field) => (self.field, R::Binary64),
            (Identity::Binary64, Vector) => (self.field, R::Binary64Vector),
            (Identity::Binary64, Polynomial) => (self.field, R::Binary64Polynomial),
            (Identity::Binary64, Round) => (self.field, R::Binary64Round),
            (Identity::Binary64, Matrix) => (self.field, R::Binary64SparseCoo),
            (Identity::Binary64Ext3, Field) => (self.field, R::Binary64Ext3),
            (Identity::Binary64Ext3, Vector) => (self.field, R::Binary64Ext3Vector),
            (Identity::Binary64Ext3, Polynomial) => (self.field, R::Binary64Ext3Polynomial),
            (Identity::Binary64Ext3, Round) => (self.field, R::Binary64Ext3Round),
            (Identity::Binary64Ext3, Matrix) => (self.field, R::Binary64Ext3SparseCoo),
            (Identity::KoalaBear, Field) => (self.field, R::KoalaBear),
            (Identity::KoalaBear, Vector) => (self.field, R::KoalaBearVector),
            (Identity::KoalaBear, Polynomial) => (self.field, R::KoalaBearPolynomial),
            (Identity::KoalaBear, Round) => (self.field, R::KoalaBearRound),
            (Identity::Ristretto255Scalar, Field) => (self.field, R::DalekScalar),
            (Identity::Ristretto255Scalar, Vector) => (self.field, R::DalekVector),
            (Identity::Ristretto255Scalar, Polynomial) => (self.field, R::DalekPolynomial),
            (Identity::Ristretto255Scalar, Round) => (self.field, R::DalekRound),
            (Identity::Bls12381Fr, Field) => (self.field, R::Fr),
            (Identity::Bls12381Fr, Vector) => (self.field, R::FrVector),
            (Identity::Bls12381Fr, Polynomial) => (self.field, R::Polynomial),
            (Identity::Bls12381Fr, Round) => (self.field, R::Round),
            (Identity::Bls12381Fr, Table) => (self.field, R::TableLsb),
            (Identity::Bls12381Fr, Point) => (self.field, R::Point),
            (Identity::Bls12381Fr, Commitment | Proof | ProverKey | VerifierKey | OpeningState) => {
                (Identity::MultilinearKzgBls12381, R::Pcs)
            }
            (Identity::KoalaBearExt8, Rng) => (self.field, R::Resource),
            (Identity::Bls12381Fr | Identity::Ristretto255Scalar, Rng | Nonce) => {
                (self.field, R::Resource)
            }
            _ => return None,
        };
        PhysicalType::new(LogicalType::new(kind, identity).ok()?, representation).ok()
    }
    pub fn codec(self, kind: Type) -> Option<String> {
        let ty = self.physical(kind)?;
        if !ty.is_serializable() {
            return None;
        }
        let suffix = match kind {
            Type::Bool => String::new(),
            Type::Group | Type::Groups => format!(".{}", self.group?.name()),
            Type::Commitment | Type::Proof => ".multilinear-kzg.bls12-381".into(),
            _ => format!(".{}", self.field.name()),
        };
        Some(format!("zkcv.{}{suffix}/0", kind.name()))
    }
}
pub fn for_identity(identity: Identity) -> Option<NativeDomain> {
    INSTALLED.iter().copied().find(|d| {
        (identity == d.field || d.group == Some(identity))
            || (d.field == BLS.field && identity == Identity::MultilinearKzgBls12381)
    })
}

/// Construction implementation facts, independent of arithmetic installations.
#[derive(Clone, Copy, Debug)]
pub struct NativeTranscript {
    pub suite: Identity,
    pub domain: NativeDomain,
    pub provider: &'static str,
}
pub const TRANSCRIPTS: &[NativeTranscript] = &[
    NativeTranscript {
        suite: Identity::Merlin3KoalaBearExt8,
        domain: KOALA_BEAR_EXT8,
        provider: "plonky3",
    },
    NativeTranscript {
        suite: Identity::Merlin3Fr64Be,
        domain: BLS,
        provider: "arkworks",
    },
    NativeTranscript {
        suite: Identity::Merlin3Ristretto64Le,
        domain: RISTRETTO,
        provider: "dalek",
    },
    NativeTranscript {
        suite: Identity::Spongefish080KeccakFr64Be,
        domain: BLS,
        provider: "spongefish",
    },
    NativeTranscript {
        suite: Identity::HashChainKeccak256Fr64Be,
        domain: BLS,
        provider: "arkworks",
    },
    NativeTranscript {
        suite: Identity::HashChainKeccak256KoalaBearExt8,
        domain: KOALA_BEAR_EXT8,
        provider: "plonky3",
    },
];
