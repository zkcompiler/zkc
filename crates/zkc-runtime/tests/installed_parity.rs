//! The runtime's presentation names against the generated installed-instance
//! and installation tables. Identities, constructor heads, representations
//! and random services are Rust names bound to catalog rows; their facts are
//! read from the rows. These checks keep each binding a bijection, and keep
//! program admission's origin codecs equal to the declared codecs.
use serde_json::json;
use std::collections::BTreeSet;
use zkc_catalog::{CATALOG, DomainIdentity, INSTALLATION};
use zkc_runtime::vm::{
    Contracts, ExecutionPolicy, Identity, LogicalType, PhysicalType, Program, Representation,
    ServiceContract, Type,
};

/// Every runtime identity; the match makes a new variant a compile error here.
fn runtime_identities() -> Vec<Identity> {
    use Identity::*;
    let all = vec![
        Bn254Fr,
        Bn254G1,
        Bn254G2,
        Bn254Gt,
        Bls12381Fr,
        Bls12381G1,
        MultilinearKzgBls12381,
        MerkleKoalaBear,
        MerkleKoalaBearExt8,
        MerkleKoalaBearExt4,
        MerklePoseidon2KoalaBear,
        MerklePoseidon2KoalaBearExt4,
        MerklePoseidon2BabyBear,
        MerklePoseidon2BabyBearExt4,
        MerklePoseidon2Goldilocks,
        MerklePoseidon2GoldilocksExt2,
        Merlin3KoalaBearExt8,
        Merlin3Fr64Be,
        Spongefish080KeccakFr64Be,
        Ristretto255Scalar,
        KoalaBear,
        KoalaBearExt8,
        KoalaBearExt4,
        BabyBear,
        BabyBearExt4,
        Goldilocks,
        GoldilocksExt2,
        Merlin3BabyBearExt4,
        Merlin3GoldilocksExt2,
        Ristretto255Group,
        Edwards25519Prime,
        Merlin3Ristretto64Le,
        Bls12381G2,
        Bls12381Gt,
        HashChainKeccak256Fr64Be,
        HashChainKeccak256KoalaBearExt8,
        HashChainKeccak256KoalaBearExt4,
        Binary64,
        Binary64Ext3,
    ];
    for identity in &all {
        match identity {
            None
            | Bn254Fr
            | Bn254G1
            | Bn254G2
            | Bn254Gt
            | Bls12381Fr
            | Bls12381G1
            | MultilinearKzgBls12381
            | MerkleKoalaBear
            | MerkleKoalaBearExt8
            | MerkleKoalaBearExt4
            | MerklePoseidon2KoalaBear
            | MerklePoseidon2KoalaBearExt4
            | MerklePoseidon2BabyBear
            | MerklePoseidon2BabyBearExt4
            | MerklePoseidon2Goldilocks
            | MerklePoseidon2GoldilocksExt2
            | Merlin3KoalaBearExt8
            | Merlin3Fr64Be
            | Spongefish080KeccakFr64Be
            | Ristretto255Scalar
            | KoalaBear
            | KoalaBearExt8
            | KoalaBearExt4
            | BabyBear
            | BabyBearExt4
            | Goldilocks
            | GoldilocksExt2
            | Merlin3BabyBearExt4
            | Merlin3GoldilocksExt2
            | Ristretto255Group
            | Edwards25519Prime
            | Merlin3Ristretto64Le
            | Bls12381G2
            | Bls12381Gt
            | HashChainKeccak256Fr64Be
            | HashChainKeccak256KoalaBearExt8
            | HashChainKeccak256KoalaBearExt4
            | Binary64
            | Binary64Ext3 => {}
        }
    }
    all
}

/// Every runtime constructor head; the match makes a new one a compile error.
fn runtime_types() -> Vec<Type> {
    use Type::*;
    let all = vec![
        Sequence,
        FieldArray,
        FixedVector,
        Variant,
        ResourceUnit,
        Index,
        Indices,
        Bytes,
        Shake128State,
        QuotientMatrix,
        Matrix,
        Vector,
        Polynomial,
        Field,
        Table,
        Point,
        Round,
        Bool,
        Rng,
        Commitment,
        Commitments,
        OpeningStates,
        Proof,
        ProverKey,
        VerifierKey,
        OpeningState,
        Group,
        Nonce,
        Transcript,
        Groups,
    ];
    for ty in &all {
        match ty {
            Sequence | FieldArray | FixedVector | Variant | ResourceUnit | Index | Indices
            | Bytes | Shake128State | QuotientMatrix | Matrix | Vector | Polynomial | Field
            | Table | Point | Round | Bool | Rng | Commitment | Commitments | OpeningStates
            | Proof | ProverKey | VerifierKey | OpeningState | Group | Nonce | Transcript
            | Groups => {}
        }
    }
    all
}

/// The listed differences must be exactly the found ones.
fn agree(comparison: &str, found: BTreeSet<String>, expected: &[(&str, &str)]) {
    let listed = expected
        .iter()
        .map(|(subject, _)| subject.to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        listed.len(),
        expected.len(),
        "{comparison}: duplicate listed difference"
    );
    let unexpected = found.difference(&listed).collect::<Vec<_>>();
    let resolved = listed.difference(&found).collect::<Vec<_>>();
    assert!(
        unexpected.is_empty() && resolved.is_empty(),
        "{comparison}: unexpected {unexpected:?}; no longer differs {resolved:?}"
    );
}

fn runtime(identity: DomainIdentity) -> Identity {
    Identity::parse(identity.name()).unwrap_or_else(|_| panic!("{}", identity.name()))
}
#[test]
fn identities_are_the_installed_domains() {
    let generated = DomainIdentity::ALL
        .iter()
        .map(|identity| identity.name().to_owned())
        .collect::<BTreeSet<_>>();
    let hand = runtime_identities()
        .into_iter()
        .map(|identity| identity.name().to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(generated.len(), DomainIdentity::ALL.len());
    agree(
        "identities",
        generated.symmetric_difference(&hand).cloned().collect(),
        &[],
    );
    for identity in DomainIdentity::ALL {
        assert_eq!(runtime(*identity).name(), identity.name());
    }
}

#[test]
fn every_logical_type_has_its_default_representation() {
    let mut found = BTreeSet::new();
    for row in CATALOG.logical_types {
        let ty = runtime_types()
            .into_iter()
            .find(|ty| ty.name() == row.kind)
            .unwrap_or_else(|| panic!("{}", row.kind));
        let identity = row.domain.map_or(Identity::None, runtime);
        let subject = format!("{} {}", row.kind, identity.name());
        let Ok(logical) = LogicalType::new(ty, identity) else {
            found.insert(format!("logical type {subject}"));
            continue;
        };
        let default = INSTALLATION
            .representations
            .iter()
            .find(|r| r.kind == row.kind && r.domain == row.domain && r.default)
            .map(|r| r.identity);
        let physical = PhysicalType::default_for(logical).ok();
        if physical.map(|p| p.representation().name()) != default {
            found.insert(format!("default representation {subject}"));
        }
    }
    agree("logical types", found, &[]);
}

#[test]
fn constructor_heads_follow_the_declared_types() {
    let mut found = BTreeSet::new();
    // `variant` has its own formation and no constructor row.
    let heads = runtime_types()
        .into_iter()
        .filter(|ty| *ty != Type::Variant)
        .collect::<Vec<_>>();
    for row in CATALOG.types {
        if !heads.iter().any(|ty| ty.name() == row.name) {
            found.insert(format!("constructor {}", row.name));
        }
    }
    for ty in heads {
        if zkc_catalog::constructor(ty.name()).is_none() {
            found.insert(format!("constructor {}", ty.name()));
        }
    }
    agree("constructor heads", found, &[]);
}

#[test]
fn random_services_are_the_installed_services() {
    let mut found = BTreeSet::new();
    let generated = CATALOG
        .random_services
        .iter()
        .map(|row| (row.contract.to_owned(), row.field.name().to_owned()))
        .collect::<BTreeSet<_>>();
    let named = ServiceContract::ALL
        .iter()
        .map(|contract| {
            (
                contract.name().to_owned(),
                contract.field().name().to_owned(),
            )
        })
        .collect::<BTreeSet<_>>();
    for (contract, field) in generated.symmetric_difference(&named) {
        found.insert(format!("service {contract} {field}"));
    }
    for contract in ServiceContract::ALL {
        assert_eq!(
            ServiceContract::parse(contract.name()).ok(),
            Some(*contract)
        );
        assert_eq!(
            ServiceContract::for_field(contract.field()),
            Some(*contract)
        );
    }
    agree("random services", found, &[]);
}

/// Whether program admission accepts `spelling` as a function origin's static
/// argument.
fn origin_argument(spelling: &str) -> bool {
    let program = json!([
        "zkc.program/0",
        [],
        [[
            "function",
            "f",
            [],
            [],
            [["return", []]],
            ["f", [["X", spelling]]]
        ]],
        [],
        []
    ]);
    match Program::decode(
        &serde_json::to_vec(&program).unwrap(),
        &Contracts::standard(ExecutionPolicy::general_purpose()),
    ) {
        Ok(_) => true,
        Err(error) => {
            let text = format!("{error:?}");
            assert!(
                text.contains("logical origin static identity"),
                "{spelling}: {text}"
            );
            false
        }
    }
}

#[test]
fn origin_codec_arguments() {
    let declared = CATALOG
        .codecs
        .iter()
        .map(|row| row.identity.to_owned())
        .collect::<BTreeSet<_>>();
    let mut candidates = declared.clone();
    for row in CATALOG.logical_types {
        candidates.insert(match row.domain {
            None => format!("zkcv.{}/0", row.kind),
            Some(domain) => format!("zkcv.{}.{}/0", row.kind, domain.name()),
        });
    }
    let mut found = BTreeSet::new();
    for spelling in &candidates {
        if origin_argument(spelling) != declared.contains(spelling) {
            found.insert(spelling.clone());
        }
    }
    // Program admission admits exactly the declared codec identities; other
    // codec-like spellings, such as those of parameterless constructors
    // without a codec, refuse.
    agree("origin codec arguments", found, &[]);
    for uninstalled in ["zkcv.shake128_state/0", "zkcv.quotient_matrix/0"] {
        assert!(!origin_argument(uninstalled), "{uninstalled}");
    }
    assert!(origin_argument("zkcv.bool/0"));
}

#[test]
fn built_in_representations_are_installation_rows() {
    // Every default installation row names a built-in representation of its
    // logical type.
    let mut found = BTreeSet::new();
    let identities = INSTALLATION
        .representations
        .iter()
        .map(|row| row.identity)
        .chain(
            INSTALLATION
                .applied_representations
                .iter()
                .map(|row| row.identity),
        )
        .collect::<BTreeSet<_>>();
    for row in INSTALLATION
        .representations
        .iter()
        .filter(|row| row.default)
    {
        let spelling = format!(
            "{}@{}",
            match row.domain {
                None => row.kind.to_owned(),
                Some(domain) => format!("{}:{}", row.kind, domain.name()),
            },
            row.identity
        );
        if PhysicalType::parse(&spelling).is_err() {
            found.insert(format!("default {spelling}"));
        }
    }
    // Every built-in representation is an installation row.
    for representation in Representation::BUILT_IN {
        if !identities.contains(representation.name()) {
            found.insert(format!("built-in {}", representation.name()));
        }
    }
    assert!(identities.len() > 100);
    agree("representations", found, &[]);
}
