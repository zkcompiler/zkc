//! Native preparation controls; fixture keys deliberately contain identity
//! points. They exercise codecs/bindings and establish no setup soundness.
use ark_bn254::{Fq, Fr};
use ark_ff::{BigInteger, Field, PrimeField};
use serde_json::json;
use zkc_arkworks::{Bounds, Keys, Scalar};
use zkc_tools::{
    groth16::{Statement, VerifyingKey},
    ingress::*,
    snarkjs::{Limits, Witness},
};

fn relation(c: &str) -> Vec<u8> {
    serde_json::to_vec(&json!([
        "zkc.relation.r1cs/1",
        "bn254.fr",
        "3",
        "0",
        "1",
        [[[["1", "1"]], [["2", "1"]], [["0", c]]]]
    ]))
    .unwrap()
}
fn vk() -> VerifyingKey {
    VerifyingKey::from_json(
        &serde_json::to_vec(&json!({
            "protocol":"groth16", "curve":"bn128", "nPublic":1,
            "vk_alpha_1":["0","1","0"],
            "vk_beta_2":[["0","0"],["1","0"],["0","0"]],
            "vk_gamma_2":[["0","0"],["1","0"],["0","0"]],
            "vk_delta_2":[["0","0"],["1","0"],["0","0"]],
            "IC":[["0","1","0"],["0","1","0"]]
        }))
        .unwrap(),
    )
    .unwrap()
}
fn contract(c: &str) -> Groth16Contract {
    Groth16Contract::new(
        RelationSubject::from_normalized(&relation(c)).unwrap(),
        vk(),
        GROTH16_PREMISES,
    )
    .unwrap()
}
fn container(magic: &[u8; 4], version: u32, sections: Vec<(u32, Vec<u8>)>) -> Vec<u8> {
    let mut out = magic.to_vec();
    out.extend(version.to_le_bytes());
    out.extend((sections.len() as u32).to_le_bytes());
    for (id, bytes) in sections {
        out.extend(id.to_le_bytes());
        out.extend((bytes.len() as u64).to_le_bytes());
        out.extend(bytes);
    }
    out
}
fn zkey(a: u64, b: u64, public: u32) -> Vec<u8> {
    let mut h = 32u32.to_le_bytes().to_vec();
    h.extend(Fq::MODULUS.to_bytes_le());
    h.extend(32u32.to_le_bytes());
    h.extend(Fr::MODULUS.to_bytes_le());
    for n in [3u32, public, 4] {
        h.extend(n.to_le_bytes());
    }
    h.extend([0u8; 576]);
    let mut coeff = 4u32.to_le_bytes().to_vec();
    for (m, r, c, v) in [
        (0u32, 0u32, 1u32, a),
        (0, 1, 0, 1),
        (0, 2, 1, 1),
        (1, 0, 2, b),
    ] {
        for n in [m, r, c] {
            coeff.extend(n.to_le_bytes());
        }
        coeff.extend(
            (Fr::from(v) * Fr::from(2).pow([512]))
                .into_bigint()
                .to_bytes_le(),
        );
    }
    container(
        b"zkey",
        1,
        vec![
            (1, 1u32.to_le_bytes().to_vec()),
            (2, h),
            (3, vec![0; 64 * (public as usize + 1)]),
            (4, coeff),
            (5, vec![0; 192]),
            (6, vec![0; 192]),
            (7, vec![0; 384]),
            (8, vec![0; 64 * (2 - public as usize)]),
            (9, vec![0; 256]),
        ],
    )
}
fn wtns(values: &[u64]) -> Vec<u8> {
    let mut h = 32u32.to_le_bytes().to_vec();
    h.extend(Fr::MODULUS.to_bytes_le());
    h.extend((values.len() as u32).to_le_bytes());
    container(
        b"wtns",
        2,
        vec![
            (1, h),
            (
                2,
                values
                    .iter()
                    .flat_map(|v| Fr::from(*v).into_bigint().to_bytes_le())
                    .collect(),
            ),
        ],
    )
}
fn error<T: std::fmt::Debug>(result: Result<T>, kind: FailureKind, code: &str) {
    let e = result.unwrap_err();
    assert_eq!((e.kind, e.code), (kind, code));
}
#[test]
fn actual_groth16_decoders_bind_exact_relation_layout_matrices_and_key() {
    let expected = contract("6");
    let mut captured = zkey(1, 1, 1);
    let checked = expected
        .check_key(&relation("6"), &captured, &Limits::default())
        .unwrap();
    let frozen = captured.clone();
    captured.fill(0);
    assert_eq!(checked.captured_zkey(), frozen);
    checked.check_applicability(&expected).unwrap();
    for (a, b) in [(2, 1), (1, 2)] {
        error(
            expected.check_key(&relation("6"), &zkey(a, b, 1), &Limits::default()),
            FailureKind::Mismatch,
            "groth16-relation-key-coefficients",
        );
    }
    error(
        expected.check_key(&relation("6"), &zkey(1, 1, 0), &Limits::default()),
        FailureKind::Mismatch,
        "groth16-relation-key-header",
    );
    error(
        expected.check_key(&relation("7"), &frozen, &Limits::default()),
        FailureKind::Mismatch,
        "ingress-relation-mismatch",
    );
    error(
        checked.check_applicability(&contract("7")),
        FailureKind::Mismatch,
        "ingress-key-subject",
    );
    // C is not in zkey: independent expectation catches changed subject; if
    // explicitly configured for it, C derivation remains unavailable.
    let changed_c = contract("7")
        .check_key(&relation("7"), &frozen, &Limits::default())
        .unwrap();
    assert!(
        changed_c
            .evidence()
            .contains(&EvidenceStatus::MissingProof(Premise::Groth16CDerivation))
    );
    for p in GROTH16_PREMISES {
        assert!(
            checked
                .evidence()
                .contains(&EvidenceStatus::MissingProof(p))
        );
    }
    let mut key_json: serde_json::Value = serde_json::from_slice(&vk().to_json().unwrap()).unwrap();
    key_json["vk_alpha_1"] = json!(["1", "2", "1"]);
    let other_vk = VerifyingKey::from_json(&serde_json::to_vec(&key_json).unwrap()).unwrap();
    let other = Groth16Contract::new(expected.relation().clone(), other_vk, []).unwrap();
    error(
        other.check_key(&relation("6"), &frozen, &Limits::default()),
        FailureKind::Mismatch,
        "groth16-key-mismatch",
    );
}
#[test]
fn assignment_facts_bind_exact_public_statement_and_retained_witness() {
    let c = contract("6");
    let statement = Statement(vec![Fr::from(2)].into());
    let mut input = wtns(&[1, 2, 3]);
    let bound = c
        .check_assignment(&statement, &input, &Limits::default())
        .unwrap();
    input.fill(0);
    assert_eq!(
        bound.witness().0.as_ref(),
        &[Fr::from(1), Fr::from(2), Fr::from(3)]
    );
    bound.check_applicability(c.relation(), &statement).unwrap();
    error(
        bound.check_applicability(contract("7").relation(), &statement),
        FailureKind::Mismatch,
        "ingress-assignment-subject",
    );
    error(
        bound.check_applicability(c.relation(), &Statement(vec![Fr::from(3)].into())),
        FailureKind::Mismatch,
        "ingress-assignment-subject",
    );
    error(
        c.check_assignment(&statement, &wtns(&[1, 3, 2]), &Limits::default()),
        FailureKind::Mismatch,
        "ingress-statement-mismatch",
    );
    error(
        c.check_assignment(&statement, &wtns(&[1, 2]), &Limits::default()),
        FailureKind::Mismatch,
        "ingress-assignment-layout",
    );
    error(
        c.bind_assignment(&statement, Witness(vec![Fr::from(0); 3].into())),
        FailureKind::Mismatch,
        "ingress-assignment-layout",
    );
    error(
        c.bind_assignment(&Statement(vec![].into()), bound.witness().clone()),
        FailureKind::Mismatch,
        "ingress-public-layout",
    );
    // Unsatisfied assignments can bind: no ingress satisfaction fact is issued.
    let unsatisfied = c
        .check_assignment(&statement, &wtns(&[1, 2, 4]), &Limits::default())
        .unwrap();
    assert_eq!(
        unsatisfied.evidence(),
        EvidenceStatus::Checked(Predicate::AssignmentLayoutAndPublicPrefix)
    );
}
#[test]
fn malformed_and_resource_failures_do_not_become_negative_crypto_evidence() {
    let c = contract("6");
    let bytes = zkey(1, 1, 1);
    error(
        c.check_key(&relation("6"), &bytes[..5], &Limits::default()),
        FailureKind::Malformed,
        "import-truncated",
    );
    for (limits, code) in [
        (
            Limits {
                max_file_bytes: 1,
                ..Limits::default()
            },
            "import-file-limit",
        ),
        (
            Limits {
                max_domain_size: 2,
                ..Limits::default()
            },
            "import-domain-limit",
        ),
        (
            Limits {
                max_decoded_bytes: 1,
                ..Limits::default()
            },
            "import-decoded-limit",
        ),
    ] {
        error(
            c.check_key(&relation("6"), &bytes, &limits),
            FailureKind::Resource,
            code,
        );
    }
    let mut bad: serde_json::Value = serde_json::from_slice(&relation("6")).unwrap();
    bad[2] = json!("32769");
    error(
        RelationSubject::from_normalized(&serde_json::to_vec(&bad).unwrap()),
        FailureKind::Resource,
        "groth16-relation-resource",
    );
    for spelling in [
        "01",
        "-1",
        "+1",
        " 1",
        "0",
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    ] {
        assert_eq!(
            RelationSubject::from_normalized(&relation(spelling))
                .unwrap_err()
                .kind,
            FailureKind::Malformed
        );
    }
    let original = RelationSubject::from_normalized(&relation("6")).unwrap();
    let spaced = serde_json::to_vec_pretty(
        &serde_json::from_slice::<serde_json::Value>(&relation("6")).unwrap(),
    )
    .unwrap();
    assert_eq!(original, RelationSubject::from_normalized(&spaced).unwrap());
    let mut partition: serde_json::Value = serde_json::from_slice(&relation("6")).unwrap();
    partition[3] = json!("1");
    partition[4] = json!("0");
    assert_ne!(
        original,
        RelationSubject::from_normalized(&serde_json::to_vec(&partition).unwrap()).unwrap()
    );
}
fn setup() -> (ExpectedSetup, CheckedSetup) {
    let bounds = Bounds::new(4, 16, 1 << 20, 64);
    let keys = Keys::setup_for_development(2, &bounds).unwrap();
    let expected = ExpectedSetup::from_keys(&keys, &bounds).unwrap();
    let checked = expected
        .check(expected.verifier_bytes(), expected.prover_bytes(), &bounds)
        .unwrap();
    (expected, checked)
}
#[test]
fn one_real_setup_serves_two_indices_but_index_evidence_cannot_be_retagged() {
    let (_, s) = setup();
    let r = contract("6").relation().clone();
    let other = contract("7").relation().clone();
    assert_eq!(s.capacity(), 4);
    let first = CoefficientIndex::encode(&r, 2, IndexLimits::default()).unwrap();
    assert_eq!(first.coefficients[0], [0u64, 1, 0, 0].map(Scalar::from));
    assert_eq!(first.coefficients[1], [0u64, 0, 1, 0].map(Scalar::from));
    assert_eq!(first.coefficients[2], [6u64, 0, 0, 0].map(Scalar::from));
    let index = s.check_index(&r, &first, IndexLimits::default()).unwrap();
    let second = CoefficientIndex::encode(&other, 2, IndexLimits::default()).unwrap();
    let second = s
        .check_index(&other, &second, IndexLimits::default())
        .unwrap();
    error(
        s.check_index(&other, &first, IndexLimits::default()),
        FailureKind::Mismatch,
        "ingress-index-mismatch",
    );
    error(
        s.commit_index(&other, &index, &AcceptedPremises::new(PCS_PREMISES)),
        FailureKind::Mismatch,
        "ingress-index-subject",
    );
    let point = [Scalar::from(2), Scalar::from(3)];
    for (relation, index, expected_values) in
        [(&r, &index, [3, 2, 6]), (&other, &second, [3, 2, 7])]
    {
        let committed = s
            .commit_index(relation, index, &AcceptedPremises::new(PCS_PREMISES))
            .unwrap();
        for (table, value) in committed.tables().iter().zip(expected_values) {
            let (actual, proof) = table.open(&point).unwrap();
            assert_eq!(actual, Scalar::from(value));
            assert!(
                s.verifier()
                    .check(table.commitment(), &point, actual, &proof)
                    .unwrap()
            );
        }
    }
    let (_, different_setup) = setup();
    error(
        different_setup.commit_index(&r, &index, &AcceptedPremises::new(PCS_PREMISES)),
        FailureKind::Mismatch,
        "ingress-index-subject",
    );
}
#[test]
fn index_recomputation_checks_each_matrix_encoding_dimensions_and_padding() {
    let (expected, s) = setup();
    let r = contract("6").relation().clone();
    let good = CoefficientIndex::encode(&r, 2, IndexLimits::default()).unwrap();
    for change in 0..8 {
        let mut bad = good.clone();
        match change {
            0..=2 => bad.coefficients[change][0] += Scalar::from(1),
            3 => bad.rows += 1,
            4 => bad.columns += 1,
            5 => bad.arity += 1,
            6 => {
                bad.coefficients[0].pop();
            }
            _ => bad.encoding.push('x'),
        }
        error(
            s.check_index(&r, &bad, IndexLimits::default()),
            FailureKind::Mismatch,
            "ingress-index-mismatch",
        );
    }
    error(
        s.check_index(
            &r,
            &good,
            IndexLimits {
                max_coefficients: 11,
            },
        ),
        FailureKind::Resource,
        "ingress-index-budget",
    );
    error(
        CoefficientIndex::encode(&r, 1, IndexLimits::default()),
        FailureKind::Mismatch,
        "ingress-setup-capacity",
    );
    error(
        CoefficientIndex::encode(&r, usize::MAX, IndexLimits::default()),
        FailureKind::Resource,
        "ingress-index-capacity-overflow",
    );
    let tiny = Bounds::new(1, 2, 1 << 20, 64);
    assert_eq!(
        expected
            .check(expected.verifier_bytes(), expected.prover_bytes(), &tiny)
            .unwrap_err()
            .kind,
        FailureKind::Resource
    );
    let (other, _) = setup();
    assert_eq!(
        expected
            .check(
                other.verifier_bytes(),
                other.prover_bytes(),
                &Bounds::new(4, 16, 1 << 20, 64)
            )
            .unwrap_err()
            .kind,
        FailureKind::Mismatch
    );
}

#[test]
fn required_premises_refuse_without_conflating_acceptance_and_checked_facts() {
    let c = contract("6");
    error(
        c.authorize(&AcceptedPremises::default()),
        FailureKind::UnapprovedPremise,
        "ingress-required-premise",
    );
    for missing in GROTH16_PREMISES {
        let accepted =
            AcceptedPremises::new(GROTH16_PREMISES.into_iter().filter(|p| *p != missing));
        error(
            c.authorize(&accepted),
            FailureKind::UnapprovedPremise,
            "ingress-required-premise",
        );
    }
    let accepted = AcceptedPremises::new(GROTH16_PREMISES);
    assert!(
        c.authorize(&accepted)
            .unwrap()
            .iter()
            .all(|e| matches!(e, EvidenceStatus::AcceptedPremise(_)))
    );
    let optional = Groth16Contract::new(c.relation().clone(), vk(), []).unwrap();
    assert!(
        optional
            .authorize(&AcceptedPremises::default())
            .unwrap()
            .iter()
            .all(|e| matches!(e, EvidenceStatus::UnacceptedPremise(_)))
    );
    error(
        Groth16Contract::new(c.relation().clone(), vk(), [Premise::PcsBasisConsistency]),
        FailureKind::Unavailable,
        "ingress-groth16-premise",
    );
    let malformed = wtns(&[]);
    error(
        c.check_assignment(
            &Statement(vec![Fr::from(2)].into()),
            &malformed,
            &Limits::default(),
        ),
        FailureKind::Malformed,
        "import-variable-count",
    );
}

#[test]
fn coefficient_integer_encoding_preserves_large_bn254_values_without_reduction() {
    // This is an encoding of integers, not arithmetic in the source field.
    let max = (Fr::from(0) - Fr::from(1)).into_bigint().to_string();
    let relation = RelationSubject::from_normalized(&relation(&max)).unwrap();
    let index = CoefficientIndex::encode(&relation, 2, IndexLimits::default()).unwrap();
    assert_eq!(index.coefficients[2][0].into_bigint().to_string(), max);
    assert_ne!(index.coefficients[2][0] + Scalar::from(1), Scalar::from(0));
}

#[test]
fn configured_setup_pair_and_exact_padded_polynomial_semantics() {
    let bounds = Bounds::new(4, 16, 1 << 20, 64);
    let keys = Keys::setup_for_development(3, &bounds).unwrap();
    let foreign = Keys::setup_for_development(3, &bounds).unwrap();
    error(
        ExpectedSetup::from_configured_keys(keys.prover_key(), foreign.verifier_key(), &bounds),
        FailureKind::Mismatch,
        "ingress-setup-pair",
    );
    let expected = ExpectedSetup::from_keys(&keys, &bounds).unwrap();
    let setup = expected
        .check(expected.verifier_bytes(), expected.prover_bytes(), &bounds)
        .unwrap();
    let relation = RelationSubject::from_normalized(
        &serde_json::to_vec(&json!([
            "zkc.relation.r1cs/1",
            "bn254.fr",
            "3",
            "0",
            "1",
            [
                [[["0", "1"], ["1", "2"], ["2", "3"]], [], []],
                [[["0", "4"], ["1", "5"], ["2", "6"]], [], []]
            ]
        ]))
        .unwrap(),
    )
    .unwrap();
    let candidate = CoefficientIndex::encode(&relation, 3, IndexLimits::default()).unwrap();
    assert_eq!(
        candidate.coefficients[0],
        [1u64, 2, 3, 4, 5, 6, 0, 0].map(Scalar::from)
    );
    let checked = setup
        .check_index(&relation, &candidate, IndexLimits::default())
        .unwrap();
    let commitments = setup
        .commit_index(&relation, &checked, &AcceptedPremises::new(PCS_PREMISES))
        .unwrap();
    let point = [2u64, 3, 5].map(Scalar::from);
    // c0 + c1*z + c2*y + c3*y*z + c4*x + c5*x*z;
    // the absent padding coefficients of x*y and x*y*z stay exactly zero.
    let expected_value = Scalar::from(1 + 2 * 5 + 3 * 3 + 4 * 3 * 5 + 5 * 2 + 6 * 2 * 5);
    let (value, proof) = commitments.tables()[0].open(&point).unwrap();
    assert_eq!(value, expected_value);
    assert!(
        setup
            .verifier()
            .check(commitments.tables()[0].commitment(), &point, value, &proof)
            .unwrap()
    );
}

#[test]
fn equal_tables_of_different_shapes_differ_in_the_subject_binding() {
    // One constraint over four columns and two over two columns place their
    // A, B and C cells at the same row-major positions 3, 2 and 1.
    let wide = RelationSubject::from_normalized(
        &serde_json::to_vec(&json!([
            "zkc.relation.r1cs/1",
            "bn254.fr",
            "4",
            "0",
            "1",
            [[[["3", "1"]], [["2", "1"]], [["1", "1"]]]]
        ]))
        .unwrap(),
    )
    .unwrap();
    let square = RelationSubject::from_normalized(
        &serde_json::to_vec(&json!([
            "zkc.relation.r1cs/1",
            "bn254.fr",
            "2",
            "0",
            "1",
            [[[], [], [["1", "1"]]], [[["1", "1"]], [["0", "1"]], []]]
        ]))
        .unwrap(),
    )
    .unwrap();
    let first = CoefficientIndex::encode(&wide, 2, IndexLimits::default()).unwrap();
    let second = CoefficientIndex::encode(&square, 2, IndexLimits::default()).unwrap();
    assert_eq!(first.coefficients, second.coefficients);
    let (_, setup) = setup();
    let first = setup
        .check_index(&wide, &first, IndexLimits::default())
        .unwrap();
    let second = setup
        .check_index(&square, &second, IndexLimits::default())
        .unwrap();
    assert_eq!(first.subject().dimensions(), (1, 4));
    assert_eq!(second.subject().dimensions(), (2, 2));
    assert_ne!(first.subject().binding(), second.subject().binding());
}

#[test]
fn commitment_subjects_preserve_public_layout_and_pcs_premises_are_required() {
    let (expected, setup) = setup();
    let original = RelationSubject::from_normalized(&relation("6")).unwrap();
    let mut alternate: serde_json::Value = serde_json::from_slice(&relation("6")).unwrap();
    alternate[3] = json!("1");
    alternate[4] = json!("0");
    let alternate =
        RelationSubject::from_normalized(&serde_json::to_vec(&alternate).unwrap()).unwrap();
    let first = CoefficientIndex::encode(
        &original,
        2,
        IndexLimits {
            max_coefficients: 12,
        },
    )
    .unwrap();
    let second = CoefficientIndex::encode(&alternate, 2, IndexLimits::default()).unwrap();
    assert_eq!(first.coefficients, second.coefficients);
    assert_ne!(first.relation_descriptor, second.relation_descriptor);
    error(
        setup.check_index(&original, &second, IndexLimits::default()),
        FailureKind::Mismatch,
        "ingress-index-mismatch",
    );
    let index = setup
        .check_index(&original, &first, IndexLimits::default())
        .unwrap();
    for missing in PCS_PREMISES {
        let accepted = AcceptedPremises::new(PCS_PREMISES.into_iter().filter(|p| *p != missing));
        error(
            setup.commit_index(&original, &index, &accepted),
            FailureKind::UnapprovedPremise,
            "ingress-required-premise",
        );
    }
    let committed = setup
        .commit_index(&original, &index, &AcceptedPremises::new(PCS_PREMISES))
        .unwrap();
    assert_eq!(committed.subject(), index.subject());
    committed.check_applicability(&setup, &original).unwrap();
    error(
        committed.check_applicability(&setup, &alternate),
        FailureKind::Mismatch,
        "ingress-commitment-subject",
    );
    // Swapped key material fails at the verifier key's own header, whose kind
    // byte names a prover key. The later exact-material comparison is not
    // reached: bytes that pass both pinned decoders are the expected bytes.
    error(
        expected.check(
            expected.prover_bytes(),
            expected.verifier_bytes(),
            &Bounds::new(4, 16, 1 << 20, 64),
        ),
        FailureKind::Malformed,
        "invalid-header",
    );
}

#[test]
fn relation_subject_refuses_noncanonical_sparse_columns() {
    for entries in [
        json!([["2", "1"], ["1", "1"]]),
        json!([["1", "1"], ["1", "2"]]),
        json!([["3", "1"]]),
    ] {
        let mut candidate: serde_json::Value = serde_json::from_slice(&relation("6")).unwrap();
        candidate[5][0][0] = entries;
        assert_eq!(
            RelationSubject::from_normalized(&serde_json::to_vec(&candidate).unwrap())
                .unwrap_err()
                .kind,
            FailureKind::Malformed
        );
    }
    let relation = RelationSubject::from_normalized(&relation("6")).unwrap();
    assert_eq!(
        RelationSubject::from_prepared(relation.relation()),
        relation
    );
}

#[test]
fn expected_relation_and_verification_key_public_counts_must_agree() {
    let mut encoded: serde_json::Value = serde_json::from_slice(&vk().to_json().unwrap()).unwrap();
    encoded["nPublic"] = json!(2);
    encoded["IC"]
        .as_array_mut()
        .unwrap()
        .push(json!(["0", "1", "0"]));
    let wrong = VerifyingKey::from_json(&serde_json::to_vec(&encoded).unwrap()).unwrap();
    error(
        Groth16Contract::new(
            RelationSubject::from_normalized(&relation("6")).unwrap(),
            wrong,
            GROTH16_PREMISES,
        ),
        FailureKind::Mismatch,
        "ingress-public-layout",
    );
}
