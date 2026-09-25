use crate::codec::*;
use serde_json::json;
use zkc_arkworks::{GroupPoint, Scalar};

#[test]
fn independent_logical_wire_goldens_and_utf8() {
    // Literal byte oracle, independent of the encoder's recursive implementation.
    assert_eq!(
        hex(&logical(&json!(["é", []])).unwrap()),
        "010200000000000000000200000000000000c3a9010000000000000000"
    );
    assert_ne!(
        logical(&json!("é")).unwrap(),
        logical(&json!("e\u{301}")).unwrap()
    );
    assert_eq!(
        hex(&scalar(Scalar::from(1u64)).unwrap()),
        "5a4b435601010100000000000000000000000000000000000000000000000000000000000000"
    );
}

#[test]
fn logical_encoding_refuses_wrong_kinds_and_depth_width_and_byte_limits() {
    for value in [json!(null), json!(1), json!(false), json!({"a":"b"})] {
        assert!(logical(&value).is_err());
    }
    let mut nested = json!("leaf");
    for _ in 0..64 {
        nested = json!([nested]);
    }
    assert!(logical(&nested).is_ok());
    assert!(logical(&json!([nested])).is_err());
    assert!(logical(&json!(vec![""; 32769])).is_err());
    // 8 arrays below the per-array limit exceed the independent node budget.
    assert!(logical(&json!(vec![vec![""; 25000]; 8])).is_err());
    assert!(logical(&json!("x".repeat(LIMIT))).is_err()); // nine-byte overhead counts
}

#[test]
fn public_ingress_is_canonical_exact_and_domain_specific() {
    let mut f = scalar(Scalar::from(3u64)).unwrap();
    f.push(0);
    assert!(field(&f).is_err());
    assert!(field(&wire(1, &[255; 32])).is_err());
    assert!(point(&scalar(Scalar::from(3u64)).unwrap()).is_err());
    let g = group(GroupPoint::generator()).unwrap();
    assert!(field(&g).is_err());
    let mut trailing = g.clone();
    trailing.push(0);
    assert!(point(&trailing).is_err());
    assert_eq!(point(&g).unwrap(), GroupPoint::generator());
    assert!(unhex("AA").is_err());
    assert!(unhex("0").is_err());
}

#[test]
fn proof_reader_checks_header_lengths_and_exhaustion() {
    use crate::transcript::Session;
    let root = json!(["test"]);
    let s = Session::new(&root, None).unwrap();
    let header = s.proof;
    let mut trailing = header.clone();
    trailing.push(0);
    assert!(Session::new(&root, Some(&header)).unwrap().finish().is_ok());
    assert!(
        Session::new(&root, Some(&trailing))
            .unwrap()
            .finish()
            .is_err()
    );
    let mut huge = header.clone();
    huge.extend(u64::MAX.to_le_bytes());
    assert!(Session::new(&root, Some(&huge)).unwrap().receive().is_err());
    assert!(Session::new(&json!(["other"]), Some(&header)).is_err());
}

fn pinned_case(
    name: &str,
    directory: &std::path::Path,
) -> (std::path::PathBuf, std::path::PathBuf) {
    let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/artifact");
    let source_path = directory.join("source.json");
    let descriptor_path = directory.join("descriptor.json");
    let mut source = json_file(&fixtures.join(format!("{name}.json"))).unwrap();
    if name == "committed-two-factor" {
        source[4][0][3][0][1] = json!("1");
        source[4][2][3][0][1] = json!("1");
    }
    write_json(&source_path, &source).unwrap();
    std::fs::copy(
        fixtures.join(format!("{name}.construction.json")),
        &descriptor_path,
    )
    .unwrap();
    (source_path, descriptor_path)
}

#[test]
fn pinned_explicit_algorithms_roundtrip_and_reject_changed_statements() {
    use crate::{fixture, input::Input, source::Source, transcript::Session};
    for name in ["dleq", "committed-two-factor"] {
        // One directory per case: they generate a fixture tree under the same
        // name, and the second would meet the first one's.
        let dir = zkc_test_support::evidence(module_path!()).nested(name);
        let (source_path, descriptor_path) = pinned_case(name, dir.path());
        let source = Source::load(&source_path, &descriptor_path).unwrap();
        let fixtures = dir.path().join("fixture");
        fixture::generate(&source, &source_path, &descriptor_path, &fixtures).unwrap();
        let execute = |input: &Input, session: &mut Session<'_>| {
            if let Some(n) = source.n {
                crate::two_factor::execute(input, n, session)
            } else {
                crate::dleq::execute(input, session)
            }
        };
        let producer = Input::load(&source, &fixtures.join("producer/inputs.json"), true).unwrap();
        let validator_path = fixtures.join("validator/inputs.json");
        let validator = Input::load(&source, &validator_path, false).unwrap();
        assert_eq!(producer.root, validator.root);
        assert_eq!(producer.root[0], "zkc.artifact-binding/1");
        let mut produced = Session::new(&producer.root, None).unwrap();
        execute(&producer, &mut produced).unwrap();
        let mut checked = Session::new(&validator.root, Some(&produced.proof)).unwrap();
        execute(&validator, &mut checked).unwrap();
        assert_eq!(checked.messages, if source.n.is_some() { 7 } else { 6 });
        assert_eq!(checked.draws, if source.n.is_some() { 1 } else { 2 });
        let mut trailing = produced.proof.clone();
        trailing.push(0);
        assert!(
            execute(
                &validator,
                &mut Session::new(&validator.root, Some(&trailing)).unwrap()
            )
            .is_err()
        );
        let mut changed = json_file(&validator_path).unwrap();
        changed[1] = json!("00");
        write_json(&validator_path, &changed).unwrap();
        let changed_input = Input::load(&source, &validator_path, false).unwrap();
        assert!(Session::new(&changed_input.root, Some(&produced.proof)).is_err());
        if source.n.is_some() {
            changed[4][3][0][3] = json!("unselected");
            write_json(&validator_path, &changed).unwrap();
            assert!(Input::load(&source, &validator_path, false).is_err());
        }
        let mut changed = source.source.clone();
        changed[1][0][3] = json!("reference/group.public");
        write_json(&source_path, &changed).unwrap();
        assert!(Source::load(&source_path, &descriptor_path).is_err());
        changed[0] = json!("zkc.protocol/2");
        write_json(&source_path, &changed).unwrap();
        assert!(Source::load(&source_path, &descriptor_path).is_err());
    }
}
