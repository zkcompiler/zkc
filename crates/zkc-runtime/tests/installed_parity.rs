//! The generated installed-instance and installation tables against the
//! runtime's hand-written tables. Every known difference is listed with its
//! reason: the consumer step that derives the runtime table from the catalog
//! removes the entry. Any other difference, or a listed one that no longer
//! occurs, fails.
use serde_json::json;
use std::collections::BTreeSet;
use zkc_catalog::{
    CATALOG, CommitmentFacts, DomainFacts, DomainIdentity, ExtensionBase, FieldStructure,
    INSTALLATION, InstalledDomain, installed_domain,
};
use zkc_runtime::vm::{
    Contracts, ExecutionPolicy, Identity, LogicalType, PhysicalType, Program, ServiceContract, Type,
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
fn member(row: &InstalledDomain, name: &str) -> Option<DomainIdentity> {
    row.members
        .iter()
        .find(|(member, _)| *member == name)
        .map(|(_, identity)| *identity)
}
fn holds(row: &InstalledDomain, capability: &str) -> bool {
    row.capabilities.contains(&capability)
}
/// Field elements as GF(2) coordinates; `None` for other characteristics.
fn binary_width(identity: DomainIdentity) -> Option<u32> {
    let row = installed_domain(identity);
    let DomainFacts::Field(facts) = row.facts else {
        return None;
    };
    if facts.characteristic != "2" {
        return None;
    }
    match facts.structure {
        FieldStructure::Prime => Some(1),
        FieldStructure::Extension {
            over: ExtensionBase::PrimeSubfield,
            degree,
            ..
        } => Some(degree as u32),
        FieldStructure::Extension { degree, .. } => {
            Some(degree as u32 * binary_width(member(row, "BaseField")?)?)
        }
    }
}
/// The last row along BaseField extensions, when it is prime.
fn prime_base(identity: DomainIdentity) -> Option<DomainIdentity> {
    let row = installed_domain(identity);
    match row.facts {
        DomainFacts::Field(facts) => match facts.structure {
            FieldStructure::Prime => Some(identity),
            FieldStructure::Extension {
                over: ExtensionBase::BaseField,
                ..
            } => prime_base(member(row, "BaseField")?),
            FieldStructure::Extension { .. } => None,
        },
        _ => None,
    }
}
fn logical_type(kind: &str, domain: Option<DomainIdentity>) -> bool {
    CATALOG
        .logical_types
        .iter()
        .any(|row| row.kind == kind && row.domain == domain)
}
fn codec(kind: &str, domain: Option<DomainIdentity>) -> Option<&'static zkc_catalog::Codec> {
    CATALOG
        .codecs
        .iter()
        .find(|row| row.kind == kind && row.domain == domain)
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
fn identity_facts_follow_the_installed_rows() {
    let mut found = BTreeSet::new();
    let forms = |identity: DomainIdentity| {
        INSTALLATION
            .field_forms
            .iter()
            .find(|row| row.field == identity)
    };
    for row in CATALOG.domains {
        let identity = runtime(row.identity);
        let name = row.identity.name();
        let mut check = |fact: &str, hand: bool, generated: bool| {
            if hand != generated {
                found.insert(format!("{fact} {name}"));
            }
        };
        check("prime", identity.is_prime_field(), holds(row, "PrimeField"));
        check(
            "characteristic not two",
            identity.has_characteristic_not_two(),
            holds(row, "CharacteristicNotTwo"),
        );
        check(
            "multi-opening",
            identity.has_multi_opening(),
            holds(row, "MultiOpening"),
        );
        check(
            "row commitment",
            identity.is_row_commitment(),
            matches!(
                row.facts,
                DomainFacts::Commitment(
                    CommitmentFacts::Keccak256Rows { .. } | CommitmentFacts::Poseidon2Rows { .. }
                )
            ),
        );
        check(
            "transcript",
            identity.transcript() == Some(identity),
            row.sort == "Transcript",
        );
        check(
            "index transcript",
            identity.has_index_transcript(),
            holds(row, "IndexTranscript"),
        );
        check(
            "index block transcript",
            identity.has_index_block_transcript(),
            holds(row, "IndexBlockTranscript"),
        );
        check(
            "base field",
            identity.base_field().map(Identity::name)
                == member(row, "BaseField").map(DomainIdentity::name),
            true,
        );
        let scalar = match row.sort {
            "Field" => Some(row.identity),
            "Group" => member(row, "Scalar"),
            "Transcript" => member(row, "ChallengeField"),
            _ => member(row, "ValueField"),
        };
        check(
            "scalar field",
            identity.scalar_field().map(Identity::name) == scalar.map(DomainIdentity::name),
            true,
        );
        check(
            "bit-pattern width",
            identity.bit_pattern_width() == binary_width(row.identity),
            true,
        );
        check(
            "residue coordinates",
            identity.has_residue_coordinates(),
            prime_base(row.identity).is_some(),
        );
        let form = forms(row.identity);
        check(
            "residue arithmetic",
            identity.is_plonky3_residue(),
            form.is_some_and(|form| form.arithmetic.is_some()),
        );
        check(
            "Montgomery words",
            identity.has_montgomery_words(),
            form.is_some_and(|form| form.montgomery.is_some_and(|m| m.radix_bits == 32)),
        );
        let provider = INSTALLATION
            .providers
            .iter()
            .find(|preference| preference.domain == row.identity)
            .map(|preference| preference.default.name());
        check("default provider", identity.provider() == provider, true);
    }
    agree("identity facts", found, &[]);
}

#[test]
fn logical_types_codecs_and_default_representations() {
    let mut found = BTreeSet::new();
    let mut admitted = 0;
    for ty in runtime_types() {
        // Structural constructors have their own formation.
        if matches!(
            ty,
            Type::Variant
                | Type::ResourceUnit
                | Type::Sequence
                | Type::FieldArray
                | Type::FixedVector
        ) {
            continue;
        }
        let Some(declared) = zkc_catalog::constructor(ty.name()) else {
            found.insert(format!("constructor {}", ty.name()));
            continue;
        };
        let domains = if declared.parameters.is_empty() {
            vec![None]
        } else {
            DomainIdentity::ALL.iter().copied().map(Some).collect()
        };
        for domain in domains {
            let identity = domain.map_or(Identity::None, runtime);
            let subject = format!("{} {}", ty.name(), domain.map_or("", DomainIdentity::name));
            let hand = LogicalType::new(ty, identity).ok();
            if hand.is_some() != logical_type(ty.name(), domain) {
                found.insert(format!("logical type {subject}"));
            }
            let Some(logical) = hand else {
                continue;
            };
            admitted += 1;
            let generated = codec(ty.name(), domain);
            if logical.codec().as_deref() != generated.map(|row| row.identity) {
                found.insert(format!("codec {subject}"));
            }
            let message = declared.message && generated.is_some_and(|row| row.frame.is_some());
            if logical.is_native_message_data() != message {
                found.insert(format!("message {subject}"));
            }
            let default = INSTALLATION
                .representations
                .iter()
                .find(|row| row.kind == ty.name() && row.domain == domain && row.default);
            let physical = PhysicalType::default_for(logical).ok();
            if physical.map(|p| p.representation().name()) != default.map(|row| row.identity) {
                found.insert(format!("default representation {subject}"));
            }
        }
    }
    assert_eq!(admitted, CATALOG.logical_types.len());
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
        // Copy and drop permissions already read the constructor rows.
        let encodes = format!("Encodes.{}", ty.name());
        if ty.is_serializable() != CATALOG.capabilities.iter().any(|c| c.name == encodes) {
            found.insert(format!("serializable {}", ty.name()));
        }
    }
    agree("constructor heads", found, &[]);
}

#[test]
fn random_services_and_their_gates() {
    use ServiceContract::*;
    let hand = [
        RandomBls12381Field,
        RandomBn254Field,
        RandomRistrettoField,
        RandomExtensionField,
        RandomKoalaBearExt4,
        RandomBabyBearExt4,
        RandomGoldilocksExt2,
    ];
    let mut found = BTreeSet::new();
    let generated = CATALOG
        .random_services
        .iter()
        .map(|row| (row.contract.to_owned(), row.field.name().to_owned()))
        .collect::<BTreeSet<_>>();
    let written = hand
        .iter()
        .map(|contract| {
            (
                contract.name().to_owned(),
                contract.field().name().to_owned(),
            )
        })
        .collect::<BTreeSet<_>>();
    for (contract, field) in generated.symmetric_difference(&written) {
        found.insert(format!("service {contract} {field}"));
    }
    for service in CATALOG.random_services {
        let Ok(contract) = ServiceContract::parse(service.contract) else {
            continue;
        };
        let field = installed_domain(service.field);
        for method in CATALOG.service_methods {
            let gated = method.capability.is_empty() || holds(field, method.capability);
            if contract.signature(method.name).is_some() != gated {
                found.insert(format!("method {} {}", service.contract, method.name));
            }
        }
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
    // Program admission parses a codec-like spelling as a type and so admits
    // identities that no codec row declares; the consumer step that reads
    // codec identities from the catalog removes these entries.
    const PHANTOM: &str = "admitted as an origin codec but not a declared codec";
    agree(
        "origin codec arguments",
        found,
        &[
            ("zkcv.shake128_state/0", PHANTOM),
            ("zkcv.quotient_matrix/0", PHANTOM),
            ("zkcv.commitment.multilinear.kzg.bls12-381/0/0", PHANTOM),
            ("zkcv.proof.multilinear.kzg.bls12-381/0/0", PHANTOM),
            (
                "zkcv.commitment.rows.merkle-keccak256.koala-bear/0/0",
                PHANTOM,
            ),
            ("zkcv.proof.rows.merkle-keccak256.koala-bear/0/0", PHANTOM),
            (
                "zkcv.commitments.rows.merkle-keccak256.koala-bear/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitment.rows.merkle-keccak256.koala-bear.ext8-binomial3/0/0",
                PHANTOM,
            ),
            (
                "zkcv.proof.rows.merkle-keccak256.koala-bear.ext8-binomial3/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitments.rows.merkle-keccak256.koala-bear.ext8-binomial3/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitment.rows.merkle-keccak256.koala-bear.ext4-binomial3/0/0",
                PHANTOM,
            ),
            (
                "zkcv.proof.rows.merkle-keccak256.koala-bear.ext4-binomial3/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitments.rows.merkle-keccak256.koala-bear.ext4-binomial3/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitment.rows.merkle-poseidon2-16.koala-bear/0/0",
                PHANTOM,
            ),
            (
                "zkcv.proof.rows.merkle-poseidon2-16.koala-bear/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitments.rows.merkle-poseidon2-16.koala-bear/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitment.rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0/0",
                PHANTOM,
            ),
            (
                "zkcv.proof.rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitments.rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitment.rows.merkle-poseidon2-16.baby-bear/0/0",
                PHANTOM,
            ),
            ("zkcv.proof.rows.merkle-poseidon2-16.baby-bear/0/0", PHANTOM),
            (
                "zkcv.commitments.rows.merkle-poseidon2-16.baby-bear/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitment.rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0/0",
                PHANTOM,
            ),
            (
                "zkcv.proof.rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitments.rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitment.rows.merkle-poseidon2-8.goldilocks/0/0",
                PHANTOM,
            ),
            ("zkcv.proof.rows.merkle-poseidon2-8.goldilocks/0/0", PHANTOM),
            (
                "zkcv.commitments.rows.merkle-poseidon2-8.goldilocks/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitment.rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0/0",
                PHANTOM,
            ),
            (
                "zkcv.proof.rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0/0",
                PHANTOM,
            ),
            (
                "zkcv.commitments.rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0/0",
                PHANTOM,
            ),
        ],
    );
}
