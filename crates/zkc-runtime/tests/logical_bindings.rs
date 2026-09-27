//! Logical formation, explicit selection, and the production admission boundary.
use serde_json::json;
use zkc_runtime::interactive::{
    AttributeRule, Backend, BackendError, ErrorCode, Frame, FrameExit, Invocation, KernelSignature,
    LogicalType, OperationBinding, PhysicalType, Representation, Value, admit_supplied,
};
use zkc_test_support::variants::logical as variant;

fn binding(contract: &str, arguments: &[&str], implementation: &str) -> OperationBinding {
    OperationBinding {
        contract: contract.into(),
        arguments: arguments.iter().map(|s| (*s).into()).collect(),
        implementation: implementation.into(),
    }
}

fn assert_ports(signature: &KernelSignature<LogicalType>, inputs: &[&str], outputs: &[&str]) {
    assert_eq!(
        signature
            .inputs
            .iter()
            .map(LogicalType::spelling)
            .collect::<Vec<_>>(),
        inputs
    );
    assert_eq!(
        signature
            .outputs
            .iter()
            .map(LogicalType::spelling)
            .collect::<Vec<_>>(),
        outputs
    );
}

#[test]
fn open_legacy_bindings_have_exact_logical_ports() {
    type SignatureCase<'a> = (
        &'a str,
        &'a [&'a str],
        &'a [&'a str],
        &'a [&'a str],
        AttributeRule,
    );
    let cases: &[SignatureCase<'_>] = &[
        (
            "bool.and",
            &[],
            &["bool", "bool"],
            &["bool"],
            AttributeRule::None,
        ),
        ("control.require", &[], &["bool"], &[], AttributeRule::None),
        (
            "index.constant",
            &[],
            &[],
            &["index"],
            AttributeRule::Unsigned64,
        ),
        (
            "indices.append",
            &[],
            &["indices", "index"],
            &["indices"],
            AttributeRule::None,
        ),
        (
            "external.openvm.sample",
            &[],
            &["indices"],
            &["indices", "index"],
            AttributeRule::None,
        ),
        (
            "field.add",
            &["bls12-381.fr"],
            &["field:bls12-381.fr", "field:bls12-381.fr"],
            &["field:bls12-381.fr"],
            AttributeRule::None,
        ),
        (
            "field.embed",
            &["koala-bear.ext8-binomial3"],
            &["field:koala-bear"],
            &["field:koala-bear.ext8-binomial3"],
            AttributeRule::None,
        ),
        (
            "vector.embed",
            &["koala-bear.ext8-binomial3"],
            &["vector:koala-bear"],
            &["vector:koala-bear.ext8-binomial3"],
            AttributeRule::None,
        ),
        (
            "curve.msm",
            &["ristretto255.group"],
            &["vector:ristretto255.scalar", "groups:ristretto255.group"],
            &["group:ristretto255.group"],
            AttributeRule::None,
        ),
        (
            "pairing.check",
            &["bn254.fr"],
            &["groups:bn254.g1", "groups:bn254.g2"],
            &["bool"],
            AttributeRule::None,
        ),
        (
            "poly.domain_root",
            &["koala-bear"],
            &["index"],
            &["field:koala-bear"],
            AttributeRule::None,
        ),
        (
            "oracle.commit",
            &["rows.merkle-keccak256.koala-bear/1"],
            &["vector:koala-bear", "index"],
            &[
                "commitment:rows.merkle-keccak256.koala-bear/1",
                "opening_state:rows.merkle-keccak256.koala-bear/1",
            ],
            AttributeRule::None,
        ),
        (
            "opening_states.empty",
            &["rows.merkle-keccak256.koala-bear/1"],
            &[],
            &["opening_states:rows.merkle-keccak256.koala-bear/1"],
            AttributeRule::None,
        ),
        (
            "commitments.length",
            &["rows.merkle-keccak256.koala-bear/1"],
            &["commitments:rows.merkle-keccak256.koala-bear/1"],
            &["index"],
            AttributeRule::None,
        ),
        (
            "transcript.observe.bool",
            &["merlin3.bls12-381.fr64be/1", "zkcv.bool/1"],
            &["transcript:merlin3.bls12-381.fr64be/1", "bool"],
            &["transcript:merlin3.bls12-381.fr64be/1"],
            AttributeRule::MessageOrigin,
        ),
        (
            "resource_unit.create",
            &["Slot.A"],
            &[],
            &["resource_unit:Slot.A"],
            AttributeRule::None,
        ),
        (
            "resource_unit.pass",
            &["Slot.A"],
            &["resource_unit:Slot.A"],
            &["resource_unit:Slot.A"],
            AttributeRule::None,
        ),
        (
            "resource_unit.consume",
            &["Slot.A"],
            &["resource_unit:Slot.A"],
            &[],
            AttributeRule::None,
        ),
    ];
    for &(contract, arguments, inputs, outputs, attributes) in cases {
        let b = binding(contract, arguments, "");
        let signature = b
            .logical_signature()
            .unwrap_or_else(|e| panic!("{contract}: {e}"));
        assert_ports(&signature, inputs, outputs);
        assert_eq!(signature.attributes, attributes, "{contract}");
        assert_eq!(
            b.signature().unwrap_err().code,
            ErrorCode::Signature,
            "{contract}"
        );
        assert!(b.implementation.is_empty());
    }
}

#[test]
fn literal_rules_follow_the_logical_field() {
    for (field, scalar, vector) in [
        (
            "bls12-381.fr",
            AttributeRule::FieldDecimal,
            AttributeRule::FieldDecimals,
        ),
        (
            "bn254.fr",
            AttributeRule::Bn254Decimal,
            AttributeRule::Bn254Decimals,
        ),
        (
            "ristretto255.scalar",
            AttributeRule::RistrettoDecimal,
            AttributeRule::RistrettoDecimals,
        ),
        (
            "koala-bear",
            AttributeRule::KoalaBearDecimal,
            AttributeRule::KoalaBearDecimals,
        ),
        (
            "koala-bear.ext8-binomial3",
            AttributeRule::KoalaBearDecimal,
            AttributeRule::KoalaBearDecimals,
        ),
    ] {
        assert_eq!(
            binding("field.constant", &[field], "")
                .logical_signature()
                .unwrap()
                .attributes,
            scalar
        );
        assert_eq!(
            binding("vector.constant", &[field], "")
                .logical_signature()
                .unwrap()
                .attributes,
            vector
        );
    }
}

#[test]
fn open_selection_does_not_relax_nominal_requirements() {
    for (contract, arguments) in [
        ("index.add", vec!["bls12-381.fr"]),
        ("field.add", vec![]),
        ("field.add", vec!["bls12-381.g1"]),
        ("field.add", vec!["unknown-field"]),
        ("field.add", vec!["koala-bear", "extra"]),
        ("field.embed", vec!["bls12-381.fr"]),
        ("curve.msm", vec!["koala-bear"]),
        ("pairing.check", vec!["bls12-381.fr"]),
        ("poly.domain_root", vec!["bls12-381.fr"]),
        ("oracle.commit", vec!["multilinear.kzg.bls12-381/1"]),
        ("pcs.commit", vec!["koala-bear"]),
        ("random.index", vec!["koala-bear"]),
        ("transcript.draw_index", vec!["merlin3.bls12-381.fr64be/1"]),
        (
            "transcript.observe.field",
            vec![
                "merlin3.bls12-381.fr64be/1",
                "koala-bear",
                "zkcv.field.bls12-381.fr/1",
            ],
        ),
        (
            "transcript.observe.bool",
            vec!["merlin3.bls12-381.fr64be/1", "zkcv.index/1"],
        ),
        ("resource_unit.create", vec![]),
        ("resource_unit.create", vec!["invalid slot"]),
        ("fixed_vector.dot", vec!["koala-bear", "01"]),
        ("fixed_vector.unknown", vec!["koala-bear", "1"]),
        ("transcript.observe.fixed_vector", vec![]),
        ("unknown.contract", vec![]),
    ] {
        let b = binding(contract, &arguments, "");
        assert!(b.logical_signature().is_err(), "{b:?}");
        assert!(b.signature().is_err(), "{b:?}");
    }
}

#[test]
fn cross_field_observations_form_logically_but_unsupported_selections_refuse() {
    for (suite, provider, kind, domain, codec) in [
        (
            "merlin3.bls12-381.fr64be/1",
            "arkworks",
            "field",
            "koala-bear",
            "zkcv.field.koala-bear/1",
        ),
        (
            "merlin3.ristretto255.scalar64le/1",
            "dalek",
            "vector",
            "bls12-381.fr",
            "zkcv.vector.bls12-381.fr/1",
        ),
        (
            "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
            "plonky3",
            "group",
            "bn254.g1",
            "zkcv.group.bn254.g1/1",
        ),
        (
            "spongefish0.7.4.keccak.bls12-381.fr64be/1",
            "spongefish",
            "proof",
            "rows.merkle-keccak256.koala-bear/1",
            "zkcv.proof.rows-merkle-keccak256.koala-bear/1",
        ),
        (
            "merlin3.ristretto255.scalar64le/1",
            "dalek",
            "commitment",
            "multilinear.kzg.bls12-381/1",
            "zkcv.commitment.multilinear-kzg.bls12-381/1",
        ),
    ] {
        let contract = format!("transcript.observe.{kind}");
        let mut b = binding(&contract, &[suite, domain, codec], "");
        let logical = b.logical_signature().unwrap();
        let transcript = format!("transcript:{suite}");
        let payload = format!("{kind}:{domain}");
        assert_ports(&logical, &[&transcript, &payload], &[&transcript]);
        assert_eq!(logical.attributes, AttributeRule::MessageOrigin);
        assert_eq!(b.signature().unwrap_err().code, ErrorCode::Signature);

        b.implementation = format!("{provider}/{contract}");
        assert_eq!(
            b.logical_signature().unwrap_err().code,
            ErrorCode::Signature
        );
        assert_eq!(b.signature().unwrap_err().code, ErrorCode::Signature);
        let error = admit_supplied(&serde_json::to_vec(&carrier(&b)).unwrap(), &NoBackend)
            .err()
            .unwrap();
        assert_eq!(error.code, ErrorCode::Signature);

        b.implementation.clear();
        b.arguments[2] = "zkcv.bool/1".into();
        assert!(b.logical_signature().is_err(), "{b:?}");
    }
}

#[test]
fn selected_observations_keep_the_installed_suite_policy() {
    for (suite, provider, payload) in [
        (
            "merlin3.bls12-381.fr64be/1",
            "arkworks",
            "group:bls12-381.g1",
        ),
        (
            "merlin3.ristretto255.scalar64le/1",
            "dalek",
            "field:ristretto255.scalar",
        ),
        (
            "spongefish0.7.4.keccak.bls12-381.fr64be/1",
            "spongefish",
            "table:bls12-381.fr",
        ),
        (
            "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
            "plonky3",
            "vector:koala-bear",
        ),
        (
            "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
            "plonky3",
            "field:koala-bear.ext8-binomial3",
        ),
        (
            "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
            "plonky3",
            "commitment:rows.merkle-keccak256.koala-bear/1",
        ),
        (
            "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
            "plonky3",
            "proof:rows.merkle-keccak256.koala-bear.ext8-binomial3/1",
        ),
    ] {
        let ty = LogicalType::parse(payload).unwrap();
        let contract = format!("transcript.observe.{}", ty.kind().name());
        let mut b = binding(
            &contract,
            &[suite, ty.identity().name(), &ty.codec().unwrap()],
            "",
        );
        let logical = b.logical_signature().unwrap();
        b.implementation = format!("{provider}/{contract}");
        assert_eq!(b.logical_signature().unwrap(), logical);
        let selected = b.signature().unwrap();
        assert_eq!(selected.inputs[1].logical(), ty);
        assert_eq!(
            selected.inputs[0].logical().spelling(),
            format!("transcript:{suite}")
        );
        assert_eq!(selected.outputs, [selected.inputs[0].clone()]);
        assert_eq!(selected.attributes, AttributeRule::MessageOrigin);
    }
}

#[test]
fn explicit_selections_preserve_ports_and_exact_physical_layouts() {
    for (contract, arguments, implementation, representation, output, position) in [
        (
            "index.add",
            vec![],
            "native/index.add",
            Representation::Index,
            false,
            0,
        ),
        (
            "field.add",
            vec!["koala-bear"],
            "plonky3/field.add",
            Representation::KoalaBear,
            false,
            0,
        ),
        (
            "poly.fold",
            vec!["bls12-381.fr"],
            "arkworks-msb/poly.fold",
            Representation::TableMsb,
            true,
            0,
        ),
        (
            "vector.mul",
            vec!["bls12-381.fr"],
            "arkworks-diagonal/vector.mul",
            Representation::FrDiagonal,
            true,
            0,
        ),
        (
            "vector.dot",
            vec!["bls12-381.fr"],
            "arkworks-diagonal/vector.dot",
            Representation::FrDiagonal,
            false,
            1,
        ),
        (
            "curve.scale_each",
            vec!["ristretto255.group"],
            "dalek-diagonal/curve.scale_each",
            Representation::RistrettoDiagonal,
            true,
            0,
        ),
        (
            "curve.msm",
            vec!["ristretto255.group"],
            "dalek-vartime/curve.msm",
            Representation::RistrettoVector,
            false,
            1,
        ),
        (
            "resource_unit.pass",
            vec!["Slot.A"],
            "logical/resource_unit.pass",
            Representation::ResourceUnit,
            true,
            0,
        ),
        (
            "transcript.challenge",
            vec!["spongefish0.7.4.keccak.bls12-381.fr64be/1"],
            "spongefish/transcript.challenge",
            Representation::Resource,
            false,
            0,
        ),
    ] {
        let mut b = binding(contract, &arguments, "");
        let logical = b.logical_signature().unwrap();
        b.implementation = implementation.into();
        assert_eq!(b.logical_signature().unwrap(), logical, "{b:?}");
        let physical = b.signature().unwrap();
        let ports = if output {
            &physical.outputs
        } else {
            &physical.inputs
        };
        assert_eq!(ports[position].representation(), representation);
        assert_eq!(
            physical
                .inputs
                .iter()
                .map(PhysicalType::logical)
                .collect::<Vec<_>>(),
            logical.inputs
        );
        assert_eq!(
            physical
                .outputs
                .iter()
                .map(PhysicalType::logical)
                .collect::<Vec<_>>(),
            logical.outputs
        );
        assert_eq!(physical.attributes, logical.attributes);
    }
}

#[test]
fn invalid_explicit_implementations_refuse_at_both_stages() {
    for (contract, arguments, implementation) in [
        ("field.add", vec!["koala-bear"], "arkworks/field.add"),
        ("field.add", vec!["koala-bear"], "plonky3/field.mul"),
        ("field.add", vec!["bls12-381.fr"], "arkworks-msb/field.add"),
        (
            "vector.add",
            vec!["bls12-381.fr"],
            "arkworks-diagonal/vector.add",
        ),
        ("curve.msm", vec!["bls12-381.g1"], "dalek-vartime/curve.msm"),
        ("index.add", vec![], "native/unknown"),
        (
            "oracle.commit",
            vec!["rows.merkle-keccak256.koala-bear/1"],
            "arkworks/oracle.commit",
        ),
        ("pairing.check", vec!["bn254.fr"], "plonky3/pairing.check"),
        (
            "resource_unit.pass",
            vec!["Slot.A"],
            "logical/resource_unit.create",
        ),
        (
            "fixed_vector.dot",
            vec!["koala-bear", "4"],
            "unknown/fixed_vector.dot",
        ),
    ] {
        let b = binding(contract, &arguments, implementation);
        assert_eq!(
            b.logical_signature().unwrap_err().code,
            ErrorCode::Signature,
            "{b:?}"
        );
        assert_eq!(
            b.signature().unwrap_err().code,
            ErrorCode::Signature,
            "{b:?}"
        );
    }
}

#[test]
fn fixed_vectors_form_without_a_realization_but_explicit_choices_are_checked() {
    for operation in ["from_vector", "to_vector", "dot"] {
        for length in ["0", "4", "1048576"] {
            let contract = format!("fixed_vector.{operation}");
            let mut b = binding(&contract, &["bls12-381.fr", length], "");
            let logical = b.logical_signature().unwrap();
            assert!(
                logical
                    .inputs
                    .iter()
                    .chain(&logical.outputs)
                    .any(|t| t.fixed_vector_parts().is_some())
            );
            assert!(b.signature().is_err());
            let ty =
                LogicalType::parse(&format!("fixed_vector<field:bls12-381.fr,{length}>")).unwrap();
            let error = PhysicalType::default_for(ty).unwrap_err();
            assert_eq!(error.code, ErrorCode::Representation);
            assert_eq!(error.detail, "unrepresented logical type");
            b.implementation = format!("plonky3/{contract}");
            for error in [
                b.logical_signature().unwrap_err(),
                b.signature().unwrap_err(),
            ] {
                assert_eq!(error.code, ErrorCode::Representation);
                assert_eq!(error.detail, "unrepresented logical type");
            }
            b.arguments[0] = "koala-bear".into();
            assert!(b.logical_signature().is_ok());
            assert!(b.signature().is_ok());
        }
    }
}

#[test]
fn representation_refusals_are_distinct_from_formation_and_binding_errors() {
    let mut b = binding("fixed_vector.dot", &["bls12-381.fr", "4"], "");
    assert!(b.logical_signature().is_ok());
    for (length, implementation, code, label) in [
        (
            "4",
            "plonky3/fixed_vector.dot",
            ErrorCode::Representation,
            "Representation",
        ),
        ("04", "plonky3/fixed_vector.dot", ErrorCode::Type, "Type"),
        (
            "4",
            "unknown/fixed_vector.dot",
            ErrorCode::Signature,
            "Signature",
        ),
    ] {
        b.arguments[1] = length.into();
        b.implementation = implementation.into();
        let production_error =
            admit_supplied(&serde_json::to_vec(&carrier(&b)).unwrap(), &NoBackend)
                .err()
                .unwrap();
        for error in [
            b.logical_signature().unwrap_err(),
            b.signature().unwrap_err(),
            production_error,
        ] {
            assert_eq!(error.code, code);
            assert_eq!(error.code.as_str(), label);
            assert_eq!(error.code.to_string(), label);
            assert_eq!(error.to_string(), format!("{label}: {}", error.detail));
        }
    }
}

#[test]
fn physical_type_errors_separate_incompatible_representations_from_bad_types() {
    let logical = LogicalType::parse("field:koala-bear").unwrap();
    let error = PhysicalType::new(logical, Representation::Fr).unwrap_err();
    assert_eq!(error.code, ErrorCode::Representation);
    assert_eq!(
        error.detail,
        "representation does not implement logical type"
    );

    for (spelling, code, detail) in [
        (
            "field:koala-bear@arkworks.fr/1",
            ErrorCode::Representation,
            "representation does not implement logical type",
        ),
        (
            "field:koala-bear@uninstalled.field/1",
            ErrorCode::Representation,
            "uninstalled representation",
        ),
        (
            "fixed_vector<field:bls12-381.fr,4>@plonky3.fixed-vector/1",
            ErrorCode::Representation,
            "unrepresented logical type",
        ),
        (
            "fixed_vector<field:koala-bear,04>@plonky3.fixed-vector/1",
            ErrorCode::Type,
            "structural-natural",
        ),
        (
            "unknown<bool,4>@plonky3.fixed-vector/1",
            ErrorCode::Type,
            "uninstalled structural constructor",
        ),
        (
            "bool:@native.bool/1",
            ErrorCode::Type,
            "noncanonical nominal spelling",
        ),
        ("bool", ErrorCode::Type, "physical representation required"),
        ("bool@", ErrorCode::Type, "uninstalled representation"),
        (
            "bool@native.bool/1@native.bool/1",
            ErrorCode::Type,
            "uninstalled representation",
        ),
    ] {
        let error = PhysicalType::parse(spelling).unwrap_err();
        assert_eq!(error.code, code, "{spelling}");
        assert_eq!(error.detail, detail, "{spelling}");
    }
    assert_eq!(
        LogicalType::parse("unknown<bool,4>").unwrap_err().code,
        ErrorCode::Type
    );
}

#[test]
fn relayout_is_a_physical_only_contract() {
    let mut b = binding(
        "table.relayout",
        &["bls12-381.fr", "arkworks.mle-lsb/1", "arkworks.mle-msb/1"],
        "arkworks/table.relayout",
    );
    assert_eq!(
        b.logical_signature().unwrap_err().detail,
        "binding-adapter-at-logical-stage"
    );
    let physical = b.signature().unwrap();
    assert_eq!(
        physical.inputs[0].representation(),
        Representation::TableLsb
    );
    assert_eq!(
        physical.outputs[0].representation(),
        Representation::TableMsb
    );
    b.implementation.clear();
    assert!(b.logical_signature().is_err());
    assert!(b.signature().is_err());
    b.implementation = "arkworks/table.relayout".into();
    b.arguments[2] = b.arguments[1].clone();
    assert!(b.signature().is_err());
}

// No cryptographic implementations are installed by this backend. In particular,
// a well-formed binding cannot become executable just by passing its resolver.
#[derive(Clone)]
enum NoValue {}
impl Value for NoValue {
    fn type_name(&self) -> &str {
        match *self {}
    }
    fn physical_type(&self) -> PhysicalType {
        match *self {}
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        match *self {}
    }
    fn retained_bytes(&self) -> usize {
        match *self {}
    }
}
struct NoBackend;
impl Backend for NoBackend {
    type Value = NoValue;
    fn validate_value(&self, value: &NoValue) -> Result<(), BackendError> {
        match *value {}
    }
    fn enter_frame(&mut self, _: &Frame, _: &[NoValue]) -> Result<(), BackendError> {
        unreachable!()
    }
    fn leave_frame(&mut self, _: &Frame, _: FrameExit, _: &[NoValue]) -> Result<(), BackendError> {
        unreachable!()
    }
    fn apply(&mut self, _: &Invocation<'_>, _: &[NoValue]) -> Result<Vec<NoValue>, BackendError> {
        unreachable!()
    }
}

fn carrier(b: &OperationBinding) -> serde_json::Value {
    json!([
        "zkc.participants/1",
        [["op", b.contract, b.arguments, b.implementation]],
        "physical",
        [],
        [[
            "participant",
            "Participant",
            "instance",
            "role",
            [],
            [],
            [],
            [["return", []]]
        ]],
        [["entry", "Main", [["role", "Participant"]]]]
    ])
}

#[test]
fn production_decoder_requires_a_real_physical_selection() {
    for (contract, args, implementation) in [
        ("field.add", vec!["koala-bear"], "plonky3/field.add"),
        (
            "fixed_vector.dot",
            vec!["koala-bear", "4"],
            "plonky3/fixed_vector.dot",
        ),
        (
            "resource_unit.pass",
            vec!["Slot.A"],
            "logical/resource_unit.pass",
        ),
    ] {
        let mut b = binding(contract, &args, implementation);
        assert!(
            admit_supplied(&serde_json::to_vec(&carrier(&b)).unwrap(), &NoBackend).is_ok(),
            "{b:?}"
        );
        for implementation in ["", "unknown/provider"] {
            b.implementation = implementation.into();
            let error = admit_supplied(&serde_json::to_vec(&carrier(&b)).unwrap(), &NoBackend)
                .err()
                .unwrap();
            assert_eq!(error.code, ErrorCode::Signature);
        }
    }
    let b = binding(
        "fixed_vector.dot",
        &["bls12-381.fr", "4"],
        "plonky3/fixed_vector.dot",
    );
    let error = admit_supplied(&serde_json::to_vec(&carrier(&b)).unwrap(), &NoBackend)
        .err()
        .unwrap();
    assert_eq!(error.code, ErrorCode::Representation);
    assert_eq!(error.detail, "unrepresented logical type");
}

#[test]
fn production_admission_still_requires_backend_advertisement() {
    let b = binding("index.constant", &[], "native/index.constant");
    let mut value = carrier(&b);
    value[3] = json!([[
        "function",
        "Constant",
        [],
        ["index@native.index/1"],
        [["op", "site", "op", ["0"], [], ["x"]], ["return", ["x"]]],
        ["Constant", []]
    ]]);
    let error = admit_supplied(&serde_json::to_vec(&value).unwrap(), &NoBackend)
        .err()
        .unwrap();
    assert_eq!(error.code, ErrorCode::Backend);
    assert_eq!(
        error.detail,
        "installed signature mismatch: native/index.constant"
    );
}

fn variant_with_bytes(bytes: usize) -> String {
    let initial = variant("N", json!([["empty", []]]));
    assert!(bytes >= initial.len() && (bytes - initial.len()).is_multiple_of(2));
    let result = variant(
        &"N".repeat(1 + (bytes - initial.len()) / 2),
        json!([["empty", []]]),
    );
    assert_eq!(result.len(), bytes);
    result
}
fn structural_with_bytes(bytes: usize) -> String {
    let length = if bytes.is_multiple_of(2) { "0" } else { "10" };
    let overhead = format!("fixed_vector<,{length}>").len();
    let result = format!(
        "fixed_vector<{},{}>",
        variant_with_bytes(bytes - overhead),
        length
    );
    assert_eq!(result.len(), bytes);
    result
}

#[test]
fn logical_spelling_limit_excludes_the_outer_representation() {
    for bytes in [4095, 4096] {
        let spelling = structural_with_bytes(bytes);
        assert!(LogicalType::parse(&spelling).is_ok());
        // This type deliberately has no realization. Reaching selection proves
        // that the valid suffix did not consume the logical spelling allowance.
        let physical = format!("{spelling}@plonky3.fixed-vector/1");
        let error = PhysicalType::parse(&physical).unwrap_err();
        assert_eq!(error.code, ErrorCode::Representation);
        assert_eq!(error.detail, "unrepresented logical type");
        let mut value = carrier(&binding("index.constant", &[], "native/index.constant"));
        value[3] = json!([[
            "function",
            "Identity",
            [["x", physical]],
            [physical],
            [["return", ["x"]]],
            ["Identity", []]
        ]]);
        let error = admit_supplied(&serde_json::to_vec(&value).unwrap(), &NoBackend)
            .err()
            .unwrap();
        assert_eq!(error.code, ErrorCode::Representation);
        assert_eq!(error.detail, "unrepresented logical type");
    }
    let spelling = structural_with_bytes(4097);
    assert_eq!(
        LogicalType::parse(&spelling).unwrap_err().detail,
        "logical-type-limit"
    );
    assert_eq!(
        PhysicalType::parse(&format!("{spelling}@plonky3.fixed-vector/1"))
            .unwrap_err()
            .detail,
        "logical-type-limit"
    );
}

#[test]
fn representation_spelling_is_checked_independently() {
    for spelling in [
        "field:koala-bear",
        "field:koala-bear@",
        "field:koala-bear@unknown",
        "field:koala-bear@plonky3.koala-bear/1@native.index/1",
        "fixed_vector<field:koala-bear@plonky3.koala-bear/1,4>@plonky3.fixed-vector/1",
        "field:koala-bear@arkworks.fr/1",
    ] {
        assert!(PhysicalType::parse(spelling).is_err(), "{spelling}");
    }
    let suffix = "x".repeat(4097);
    assert_eq!(
        PhysicalType::parse(&format!("bool@{suffix}"))
            .unwrap_err()
            .detail,
        "physical type spelling limit"
    );
}

#[test]
fn variant_spelling_keeps_its_existing_larger_limit() {
    for bytes in [4096, 256 * 1024] {
        let spelling = variant_with_bytes(bytes);
        assert!(LogicalType::parse(&spelling).is_ok());
        let physical = PhysicalType::parse(&format!("{spelling}@logical.variant/1")).unwrap();
        assert_eq!(physical.logical().spelling(), spelling);
    }
    let spelling = variant_with_bytes(256 * 1024 + 2);
    assert_eq!(
        LogicalType::parse(&spelling).unwrap_err().detail,
        "variant:limit"
    );
    assert_eq!(
        PhysicalType::parse(&format!("{spelling}@logical.variant/1"))
            .unwrap_err()
            .detail,
        "physical type spelling limit"
    );
}
