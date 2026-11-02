//! The native library domains that the CPU backend implements. A row names an
//! implemented field and group; the provider, the field-group association and
//! the codecs come from the catalog and installation.
use zkc_runtime::vm::{Identity, LogicalType, PhysicalType, Type};

#[derive(Clone, Copy, Debug)]
pub struct NativeDomain {
    pub field: Identity,
    pub group: Option<Identity>,
}
pub const BN254_G1: NativeDomain = NativeDomain {
    field: Identity::Bn254Fr,
    group: Some(Identity::Bn254G1),
};
pub const BN254_G2: NativeDomain = NativeDomain {
    field: Identity::Bn254Fr,
    group: Some(Identity::Bn254G2),
};
pub const BN254_GT: NativeDomain = NativeDomain {
    field: Identity::Bn254Fr,
    group: Some(Identity::Bn254Gt),
};
pub const BLS: NativeDomain = NativeDomain {
    field: Identity::Bls12381Fr,
    group: Some(Identity::Bls12381G1),
};
pub const BLS_G2: NativeDomain = NativeDomain {
    field: Identity::Bls12381Fr,
    group: Some(Identity::Bls12381G2),
};
pub const BLS_GT: NativeDomain = NativeDomain {
    field: Identity::Bls12381Fr,
    group: Some(Identity::Bls12381Gt),
};
pub const EDWARDS: NativeDomain = NativeDomain {
    field: Identity::Ristretto255Scalar,
    group: Some(Identity::Edwards25519Prime),
};
pub const RISTRETTO: NativeDomain = NativeDomain {
    field: Identity::Ristretto255Scalar,
    group: Some(Identity::Ristretto255Group),
};
pub const KOALA_BEAR: NativeDomain = NativeDomain {
    field: Identity::KoalaBear,
    group: None,
};
pub const KOALA_BEAR_EXT8: NativeDomain = NativeDomain {
    field: Identity::KoalaBearExt8,
    group: None,
};
pub const KOALA_BEAR_EXT4: NativeDomain = NativeDomain {
    field: Identity::KoalaBearExt4,
    group: None,
};
pub const BABY_BEAR: NativeDomain = NativeDomain {
    field: Identity::BabyBear,
    group: None,
};
pub const BABY_BEAR_EXT4: NativeDomain = NativeDomain {
    field: Identity::BabyBearExt4,
    group: None,
};
pub const GOLDILOCKS: NativeDomain = NativeDomain {
    field: Identity::Goldilocks,
    group: None,
};
pub const GOLDILOCKS_EXT2: NativeDomain = NativeDomain {
    field: Identity::GoldilocksExt2,
    group: None,
};
/// Characteristic-two fields from Plonky3 0.8.0's `p3-binary-field`.
pub const BINARY64: NativeDomain = NativeDomain {
    field: Identity::Binary64,
    group: None,
};
pub const BINARY64_EXT3: NativeDomain = NativeDomain {
    field: Identity::Binary64Ext3,
    group: None,
};
pub const INSTALLED: &[NativeDomain] = &[
    BLS,
    RISTRETTO,
    EDWARDS,
    KOALA_BEAR,
    KOALA_BEAR_EXT8,
    KOALA_BEAR_EXT4,
    BABY_BEAR,
    BABY_BEAR_EXT4,
    GOLDILOCKS,
    GOLDILOCKS_EXT2,
    BINARY64,
    BINARY64_EXT3,
    BN254_G1,
    BN254_G2,
    BN254_GT,
    BLS_G2,
    BLS_GT,
];
impl NativeDomain {
    /// The installation's default representation of this domain's instance of
    /// `kind`: its group for group kinds, the multilinear commitment scheme
    /// over its field for commitment kinds, no identity for parameterless
    /// kinds, and its field otherwise.
    pub fn physical(self, kind: Type) -> Option<PhysicalType> {
        use Type::*;
        let identity = match kind {
            Group | Groups => {
                let group = self.group?;
                if group.scalar_field()? != self.field {
                    return None;
                }
                group
            }
            Commitment | Proof | ProverKey | VerifierKey | OpeningState => {
                multilinear_scheme(self.field)?
            }
            kind if zkc_runtime::catalog::constructor(kind.name())
                .is_some_and(|row| row.parameters.is_empty()) =>
            {
                Identity::None
            }
            _ => self.field,
        };
        PhysicalType::default_for(LogicalType::new(kind, identity).ok()?).ok()
    }
    /// The installed codec of this domain's instance of `kind`.
    pub fn codec(self, kind: Type) -> Option<String> {
        self.physical(kind)?.logical().codec()
    }
    /// The installation's default provider of the domain.
    pub fn provider(self) -> &'static str {
        self.group
            .unwrap_or(self.field)
            .provider()
            .expect("an implemented domain has an installed provider")
    }
}
/// The installed multilinear opening scheme whose value field is `field`.
fn multilinear_scheme(field: Identity) -> Option<Identity> {
    zkc_runtime::catalog::CATALOG
        .domains
        .iter()
        .map(|row| Identity::from_catalog(row.identity))
        .find(|scheme| {
            scheme.sort() == Some("Commitment")
                && scheme.holds("MultilinearOpening")
                && scheme.member("ValueField") == Some(field)
        })
}
/// The implemented domain of a field, a group, or a multilinear scheme over
/// an implemented field.
pub fn for_identity(identity: Identity) -> Option<NativeDomain> {
    INSTALLED.iter().copied().find(|d| {
        (identity == d.field || d.group == Some(identity))
            || multilinear_scheme(d.field) == Some(identity)
    })
}

/// A transcript suite the backend implements. The challenge field and the
/// provider come from the catalog and installation.
#[derive(Clone, Copy, Debug)]
pub struct NativeTranscript {
    pub suite: Identity,
}
impl NativeTranscript {
    /// The implemented domain of the suite's installed challenge field.
    pub fn domain(self) -> NativeDomain {
        self.suite
            .member("ChallengeField")
            .and_then(for_identity)
            .expect("an implemented suite has an implemented challenge field")
    }
    /// The installation's default provider of the suite.
    pub fn provider(self) -> &'static str {
        self.suite
            .provider()
            .expect("an implemented suite has an installed provider")
    }
}
pub const TRANSCRIPTS: &[NativeTranscript] = &[
    NativeTranscript {
        suite: Identity::HashChainKeccak256KoalaBearExt4,
    },
    NativeTranscript {
        suite: Identity::Merlin3BabyBearExt4,
    },
    NativeTranscript {
        suite: Identity::Merlin3GoldilocksExt2,
    },
    NativeTranscript {
        suite: Identity::Merlin3KoalaBearExt8,
    },
    NativeTranscript {
        suite: Identity::Merlin3Fr64Be,
    },
    NativeTranscript {
        suite: Identity::Merlin3Ristretto64Le,
    },
    NativeTranscript {
        suite: Identity::Spongefish080KeccakFr64Be,
    },
    NativeTranscript {
        suite: Identity::HashChainKeccak256Fr64Be,
    },
    NativeTranscript {
        suite: Identity::HashChainKeccak256KoalaBearExt8,
    },
];
