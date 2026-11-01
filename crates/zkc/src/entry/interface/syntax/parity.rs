//! Interoperability oracle against native admission. This is test-only: the
//! production metadata checker must not acquire a VM or CPU dependency.
use super::*;
use zkc_runtime::vm::{Identity, LogicalType, Type};

fn native_constructible(ty: &LogicalType) -> bool {
    if let Some(element) = ty.sequence_element() {
        return native_constructible(element);
    }
    if let Some((element, _)) = ty.fixed_vector_parts() {
        return native_constructible(element);
    }
    if let Some(variant) = ty.variant_descriptor() {
        return variant
            .alternatives()
            .iter()
            .flat_map(|a| a.payload())
            .all(native_constructible);
    }
    matches!(
        ty.kind(),
        Type::Bool
            | Type::Index
            | Type::Field
            | Type::Group
            | Type::FieldArray
            | Type::Vector
            | Type::Matrix
            | Type::Groups
            | Type::Indices
            | Type::Bytes
            | Type::Polynomial
            | Type::Table
            | Type::Point
            | Type::Round
            | Type::Commitment
            | Type::Commitments
            | Type::Proof
    )
}
fn check(spelling: &str) {
    let native = LogicalType::parse(spelling).unwrap();
    let portable = Leaf::parse(spelling, &mut 1_000_000).unwrap();
    assert_eq!(portable.copy, native.is_duplicable(), "copy: {spelling}");
    assert_eq!(portable.drop, native.is_discardable(), "drop: {spelling}");
    assert_eq!(
        portable.constructible,
        native_constructible(&native),
        "constructible: {spelling}"
    );
    if let Some(variant) = native.variant_descriptor() {
        let nominal = variant.nominal_identity().unwrap();
        let expected = nominal
            .as_array()
            .filter(|a| a.len() == 2 && a[0] == "zkc.language")
            .and_then(|a| crate::source_names::decode_nominal_identity(a[1].as_str()?, 256 * 1024))
            .map(|name| crate::io::bytes::hex(&Sha256::digest(name.as_bytes())));
        assert_eq!(portable.source_identity, expected);
        for (actual, expected) in portable.alternatives.iter().zip(variant.alternatives()) {
            assert_eq!(actual.0, expected.label());
            assert_eq!(
                actual.1,
                expected
                    .payload()
                    .iter()
                    .map(LogicalType::spelling)
                    .collect::<Vec<_>>()
            );
        }
    }
}

#[test]
fn portable_permissions_match_native_atomic_and_aggregate_admission() {
    // Identity values originate in the independent native owner. Try its exact
    // declared combinations, retaining the combinations it actually admits.
    let identities = [
        Identity::Bn254Fr,
        Identity::Bn254G1,
        Identity::Bn254G2,
        Identity::Bn254Gt,
        Identity::Bls12381Fr,
        Identity::Bls12381G1,
        Identity::Bls12381G2,
        Identity::Bls12381Gt,
        Identity::Ristretto255Scalar,
        Identity::Ristretto255Group,
        Identity::Edwards25519Prime,
        Identity::KoalaBear,
        Identity::KoalaBearExt4,
        Identity::KoalaBearExt8,
        Identity::BabyBear,
        Identity::BabyBearExt4,
        Identity::Goldilocks,
        Identity::GoldilocksExt2,
        Identity::Binary64,
        Identity::Binary64Ext3,
        Identity::MultilinearKzgBls12381,
        Identity::MerkleKoalaBear,
        Identity::MerkleKoalaBearExt4,
        Identity::MerkleKoalaBearExt8,
        Identity::MerklePoseidon2KoalaBear,
        Identity::MerklePoseidon2KoalaBearExt4,
        Identity::MerklePoseidon2BabyBear,
        Identity::MerklePoseidon2BabyBearExt4,
        Identity::MerklePoseidon2Goldilocks,
        Identity::MerklePoseidon2GoldilocksExt2,
        Identity::Merlin3Fr64Be,
        Identity::Merlin3Ristretto64Le,
        Identity::Merlin3KoalaBearExt8,
        Identity::Merlin3BabyBearExt4,
        Identity::Merlin3GoldilocksExt2,
        Identity::Spongefish080KeccakFr64Be,
        Identity::HashChainKeccak256Fr64Be,
        Identity::HashChainKeccak256KoalaBearExt4,
        Identity::HashChainKeccak256KoalaBearExt8,
    ];
    for identity in &identities {
        assert_eq!(
            block_transcript(identity.name()),
            identity.has_index_block_transcript(),
            "block metadata differs for {}",
            identity.name()
        );
    }
    let mut admitted = 0;
    for row in zkc_catalog::CATALOG.types {
        let spellings = match row.parameters {
            [] => vec![row.name.to_owned()],
            [Kind::Domain(_)] => identities
                .iter()
                .map(|id| format!("{}:{}", row.name, id.name()))
                .collect(),
            _ => continue,
        };
        for spelling in spellings {
            if LogicalType::parse(&spelling).is_err() {
                continue;
            }
            admitted += 1;
            check(&spelling);
            let native = LogicalType::parse(&spelling).unwrap();
            if native.is_duplicable() && native.is_discardable() {
                check(&format!("sequence<{spelling}>"));
            }
            check(&format!("fixed_vector<{spelling},0>"));
            check(&format!("fixed_vector<{spelling},3>"));
        }
    }
    assert!(
        admitted >= 120,
        "native fixture coverage shrank: {admitted}"
    );
    for spelling in [
        "resource_unit:Slot",
        "field_array<bls12-381.fr,4>",
        "field_array<koala-bear.ext4-binomial3,0>",
        "sequence<sequence<field:bn254.fr>>",
    ] {
        check(spelling);
    }
}

#[test]
fn dormant_variant_payloads_and_nominal_identity_match_native_admission() {
    use serde_json::json;
    let inner = json!(["inner", [["_Empty", []], ["Data", ["bool"]]]]);
    for dormant in [
        "bool",
        "verifier_key:multilinear.kzg.bls12-381/0",
        "resource_unit:Slot",
        "transcript:hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0",
    ] {
        let tree = json!([
            [
                "zkc.language",
                crate::source_names::encode_nominal_identity("例::Choice")
            ],
            [["c0", [inner]], ["c1", [dormant]]]
        ]);
        check(&zkc_format::types::variant_spelling(&tree).unwrap());
    }
    for tree in [
        json!(["name", [["1bad", []]]]),
        json!(["name", [["ok", ["field:unknown"]]]]),
        json!(["name", [["ok", []], ["ok", []]]]),
    ] {
        let spelling = zkc_format::types::variant_spelling(&tree).unwrap();
        assert!(LogicalType::parse(&spelling).is_err());
        assert!(Leaf::parse(&spelling, &mut 1_000_000).is_err());
    }
    for spelling in [
        "bool:",
        "field:bn254.g1",
        "sequence<rng:bls12-381.fr>",
        "fixed_vector<bool,01>",
        "field_array<bn254.g1,2>",
        "sequence<bool>@native",
    ] {
        assert!(LogicalType::parse(spelling).is_err(), "{spelling}");
        assert!(Leaf::parse(spelling, &mut 1_000_000).is_err(), "{spelling}");
    }
}
