use super::*;
use crate::{Domain, EntryPolicy, Policy, PublicInputs, PublicRolePolicy, Scalar, Value};
use serde_json::json;
use zkc_runtime::interactive::{Action, OperationBinding, Runner, StopKind, admit_supplied};

fn backend() -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(
            Domain::new("P", "session", "main", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .unwrap()
}
fn binding(contract: &str, arguments: &[&str], implementation: &str) -> OperationBinding {
    OperationBinding {
        contract: contract.into(),
        arguments: arguments.iter().map(|s| (*s).into()).collect(),
        implementation: implementation.into(),
    }
}
fn program(binding: &OperationBinding, attributes: &[&str]) -> Vec<u8> {
    let sig = binding.signature().unwrap();
    let names: Vec<_> = (0..sig.inputs.len()).map(|n| format!("a{n}")).collect();
    let ports: Vec<_> = names
        .iter()
        .zip(&sig.inputs)
        .map(|(name, ty)| json!([name, ty.spelling()]))
        .collect();
    let outputs: Vec<_> = sig.outputs.iter().map(|t| t.spelling()).collect();
    let returns: Vec<_> = (0..outputs.len()).map(|n| format!("r{n}")).collect();
    let returned = if sig.outputs.iter().any(|t| {
        matches!(
            t.representation(),
            zkc_runtime::interactive::Representation::FrDiagonal
                | zkc_runtime::interactive::Representation::RistrettoDiagonal
        )
    }) {
        vec![]
    } else {
        returns.clone()
    };
    let result_types = if returned.is_empty() { vec![] } else { outputs };
    let mut carrier = json!([
        "zkc.participants/1",
        [[
            "b",
            binding.contract,
            binding.arguments,
            binding.implementation
        ]],
        "physical",
        [[
            "function",
            "f",
            ports,
            result_types,
            [
                ["op", "site", "b", attributes, names, returns],
                ["return", returned]
            ],
            ["f", []]
        ]],
        [[
            "participant",
            "actor",
            "instance",
            "P",
            [],
            ports,
            result_types,
            [
                ["local", "work", "f", names, returned],
                ["return", returned]
            ]
        ]],
        [["entry", "main", [["P", "actor"]]]]
    ]);
    if matches!(
        binding.implementation.as_str(),
        "arkworks-diagonal/vector.mul" | "arkworks/vector.mul"
    ) {
        let dot = if binding.implementation.starts_with("arkworks-diagonal/") {
            "arkworks-diagonal/vector.dot"
        } else {
            "arkworks/vector.dot"
        };
        carrier[1].as_array_mut().unwrap().push(json!([
            "dot",
            "vector.dot",
            ["bls12-381.fr"],
            dot
        ]));
        carrier[3][0][3] = json!(["field:bls12-381.fr@arkworks.fr/1"]);
        carrier[3][0][4] = json!([
            ["op", "view", "b", [], ["a0", "a1"], ["view"]],
            ["op", "consume", "dot", [], ["a0", "view"], ["out"]],
            ["return", ["out"]]
        ]);
        carrier[4][0][6] = carrier[3][0][3].clone();
        carrier[4][0][7] = json!([
            ["local", "work", "f", ["a0", "a1"], ["out"]],
            ["return", ["out"]]
        ]);
    }
    if binding.contract == "curve.scale_each" {
        let msm = if binding.implementation.starts_with("dalek-diagonal/") {
            "dalek-diagonal/curve.msm"
        } else {
            "dalek/curve.msm"
        };
        carrier[1].as_array_mut().unwrap().push(json!([
            "msm",
            "curve.msm",
            ["ristretto255.group"],
            msm
        ]));
        carrier[3][0][3] = json!(["group:ristretto255.group@dalek.ristretto/1"]);
        carrier[3][0][4] = json!([
            ["op", "view", "b", [], ["a0", "a1"], ["view"]],
            ["op", "consume", "msm", [], ["a0", "view"], ["out"]],
            ["return", ["out"]]
        ]);
        carrier[4][0][6] = carrier[3][0][3].clone();
        carrier[4][0][7] = json!([
            ["local", "work", "f", ["a0", "a1"], ["out"]],
            ["return", ["out"]]
        ]);
    }
    serde_json::to_vec(&carrier).unwrap()
}
fn run(
    backend: NativeBackend,
    binding: &OperationBinding,
    attributes: &[&str],
    args: Vec<Value>,
) -> (std::result::Result<Vec<Value>, String>, NativeBackend) {
    let admitted = admit_supplied(&program(binding, attributes), &backend).unwrap();
    let mut runner = Runner::new(&admitted, "main", "P", "session", backend, args)
        .unwrap_or_else(|e| panic!("{}", e.error));
    loop {
        match runner.poll() {
            Action::Local(action) => runner.execute_local(&action.cut).unwrap(),
            Action::Stopped(stop) => {
                let result = match stop.kind {
                    StopKind::Backend(error) => Err(error.code),
                    other => panic!("unexpected stop: {other:?}"),
                };
                return (result, runner.into_backend());
            }
            Action::Returned(values) => return (Ok(values), runner.into_backend()),
            action => panic!("unexpected action: {action:?}"),
        }
    }
}
fn trap(
    _: &mut NativeBackend,
    _: &zkc_runtime::interactive::Invocation<'_>,
    _: &[Value],
) -> crate::Result<Vec<Value>> {
    panic!("handler ran before the common public-operand gate")
}
#[test]
fn duplicate_implementation_owners_refuse_before_execution() {
    let mut registry = installed().unwrap().clone();
    let entry = registry.get("arkworks/vector.dot").unwrap();
    assert_eq!(
        registry
            .insert("arkworks/vector.dot".into(), entry)
            .unwrap_err()
            .code,
        "refused:duplicate-implementation-owner"
    );
    // Even two identical declarations are a conflict, not an order-dependent alias.
    assert_eq!(
        registry
            .family(
                &["plonky3"],
                crate::fixed_vector::OPERATIONS,
                Signature::Custom(crate::fixed_vector::signature),
                fixed_vector
            )
            .unwrap_err()
            .code,
        "refused:duplicate-implementation-owner"
    );
}
#[test]
fn every_handler_family_passes_the_common_security_gate() {
    let cases = [
        (
            "bool.not",
            vec![],
            "arkworks/bool.not",
            vec![],
            vec![Value::Bool(true)],
        ),
        (
            "field.constant",
            vec!["bls12-381.fr"],
            "arkworks/field.constant",
            vec!["1"],
            vec![],
        ),
        (
            "vector.to_point",
            vec!["bls12-381.fr"],
            "arkworks/vector.to_point",
            vec![],
            vec![Value::Vector([].into())],
        ),
        (
            "curve.generator",
            vec!["bls12-381.g1"],
            "arkworks/curve.generator",
            vec![],
            vec![],
        ),
        (
            "random.draw",
            vec!["bls12-381.fr"],
            "arkworks/random.draw",
            vec![],
            vec![],
        ),
        (
            "poly.domain_root",
            vec!["koala-bear"],
            "plonky3/poly.domain_root",
            vec![],
            vec![Value::Index(1)],
        ),
        (
            "index.constant",
            vec![],
            "native/index.constant",
            vec!["1"],
            vec![],
        ),
        (
            "external.openvm.init",
            vec![],
            "native/external.openvm.init",
            vec![],
            vec![],
        ),
        (
            "commitments.empty",
            vec!["rows.merkle-keccak256.koala-bear/1"],
            "plonky3/commitments.empty",
            vec![],
            vec![],
        ),
        (
            "fixed_vector.from_vector",
            vec!["koala-bear", "0"],
            "plonky3/fixed_vector.from_vector",
            vec![],
            vec![Value::KoalaBearVector([].into())],
        ),
        (
            "resource_unit.create",
            vec!["Slot.A"],
            "logical/resource_unit.create",
            vec![],
            vec![],
        ),
        (
            "vector.mul",
            vec!["bls12-381.fr"],
            "arkworks-diagonal/vector.mul",
            vec![],
            vec![Value::Vector([].into()), Value::Vector([].into())],
        ),
        (
            "vector.dot",
            vec!["bls12-381.fr"],
            "arkworks-pairwise/vector.dot",
            vec![],
            vec![Value::Vector([].into()), Value::Vector([].into())],
        ),
        (
            "curve.msm",
            vec!["ristretto255.group"],
            "dalek-vartime/curve.msm",
            vec![],
            vec![
                Value::RistrettoVector([].into()),
                Value::RistrettoGroups([].into()),
            ],
        ),
    ];
    for (contract, arguments, implementation, attributes, mut args) in cases {
        let mut backend = backend();
        let mut registry = installed().unwrap().clone();
        let entry = registry.entries.get_mut(implementation).unwrap();
        entry.public_operands = true;
        entry.handler = trap;
        backend.implementations = Box::leak(Box::new(registry));
        if contract == "random.draw" {
            args.push(
                backend
                    .issue_rng(Domain::new("P", "session", "main", None), 1)
                    .unwrap(),
            );
        }
        let b = binding(contract, &arguments, implementation);
        let (result, backend) = run(backend, &b, &attributes, args);
        assert_eq!(
            result.unwrap_err(),
            "refused:public-operands-required",
            "{implementation}"
        );
        assert_eq!(backend.active_frames(), 0);
        assert_eq!(backend.live_resource_units(), 0);
        assert_eq!(backend.external_work_spent(), 0);
    }
}
#[test]
fn former_early_return_families_gate_their_actual_handlers() {
    for (contract, args, implementation, values) in [
        (
            "fixed_vector.from_vector",
            vec!["koala-bear", "0"],
            "plonky3/fixed_vector.from_vector",
            vec![Value::KoalaBearVector([].into())],
        ),
        (
            "resource_unit.create",
            vec!["Slot.A"],
            "logical/resource_unit.create",
            vec![],
        ),
    ] {
        let mut registry = installed().unwrap().clone();
        registry
            .entries
            .get_mut(implementation)
            .unwrap()
            .public_operands = true;
        let registry = Box::leak(Box::new(registry));
        let b = binding(contract, &args, implementation);
        let mut denied = backend();
        denied.implementations = registry;
        assert_eq!(
            run(denied, &b, &[], values.clone()).0.unwrap_err(),
            "refused:public-operands-required"
        );
        let mut permitted =
            backend().with_public_role_policy(PublicRolePolicy::new(["P".into()]).unwrap());
        permitted.implementations = registry;
        assert!(run(permitted, &b, &[], values).0.is_ok());
    }
}
fn first_handler(
    _: &mut NativeBackend,
    i: &zkc_runtime::interactive::Invocation<'_>,
    _: &[Value],
) -> crate::Result<Vec<Value>> {
    assert_eq!(i.kernel, "arkworks/vector.dot");
    Err(crate::refused("first-handler"))
}
fn second_handler(
    _: &mut NativeBackend,
    i: &zkc_runtime::interactive::Invocation<'_>,
    _: &[Value],
) -> crate::Result<Vec<Value>> {
    assert_eq!(i.kernel, "arkworks-pairwise/vector.dot");
    Err(crate::refused("second-handler"))
}
#[test]
fn identical_ports_preserve_exact_handler_selection() {
    let a = binding("vector.dot", &["bls12-381.fr"], "arkworks/vector.dot");
    let b = binding(
        "vector.dot",
        &["bls12-381.fr"],
        "arkworks-pairwise/vector.dot",
    );
    assert_eq!(a.signature().unwrap(), b.signature().unwrap());
    let mut registry = installed().unwrap().clone();
    registry.entries.get_mut(&a.implementation).unwrap().handler = first_handler;
    registry.entries.get_mut(&b.implementation).unwrap().handler = second_handler;
    let registry = Box::leak(Box::new(registry));
    for (binding, refusal) in [(a, "refused:first-handler"), (b, "refused:second-handler")] {
        let mut backend = backend();
        backend.implementations = registry;
        assert_eq!(
            run(
                backend,
                &binding,
                &[],
                vec![
                    Value::Vector([Scalar::from(2)].into()),
                    Value::Vector([Scalar::from(3)].into())
                ]
            )
            .0
            .unwrap_err(),
            refusal
        );
    }
}

#[test]
fn every_payload_has_explicit_identity_and_retained_charge() {
    use crate::{Bn254Scalar, KoalaBear, KoalaBearExt8, RistrettoScalar};
    use std::{collections::HashSet, sync::Arc};
    use zkc_runtime::interactive::{
        Identity as I, LogicalType, PhysicalType, Representation as R, ResourceDomain, Type,
        Value as RuntimeValue,
    };
    let policy = Policy::default();
    let mut seen = HashSet::new();
    let mut check = |value: Value, kind: Type, identity: I, bytes: usize| {
        assert_eq!(value.ty(), kind, "{value:?}");
        let logical = match kind {
            Type::Sequence => LogicalType::parse("sequence<index>").unwrap(),
            Type::FixedVector => LogicalType::parse("fixed_vector<field:koala-bear,2>").unwrap(),
            Type::FieldArray => LogicalType::field_array(I::Bls12381Fr, 2).unwrap(),
            Type::Variant => LogicalType::parse(&zkc_test_support::variants::logical(
                "Bulk",
                json!([["some", ["fixed_vector<field:koala-bear,2>"]]]),
            ))
            .unwrap(),
            Type::ResourceUnit => {
                LogicalType::resource_unit(ResourceDomain::parse("Slot.A").unwrap())
            }
            _ => LogicalType::new(kind, identity).unwrap(),
        };
        let representation = match value.payload_name() {
            "Sequence" => R::Sequence,
            "FixedVector" => R::FixedVector,
            "FieldArray" => R::FieldArray,
            "Variant" => R::Variant,
            "ResourceUnit" => R::ResourceUnit,
            "Bn254Field" => R::Bn254Fr,
            "Bn254Vector" => R::Bn254FrVector,
            "Bn254Polynomial" => R::Bn254Polynomial,
            "Bn254Round" => R::Bn254Round,
            "Bn254Matrix" => R::Bn254SparseCoo,
            "Bn254G1" => R::Bn254G1,
            "Bn254Gt" => R::Bn254Gt,
            "Bn254G1Vector" => R::Bn254G1Vector,
            "Bn254G2" => R::Bn254G2,
            "Bn254G2Vector" => R::Bn254G2Vector,
            "OracleRoot" => R::MerkleRoot,
            "OraclePath" => R::MerklePath,
            "OracleState" => R::MerkleState,
            "OracleRoots" => R::MerkleRoots,
            "OracleStates" => R::MerkleStates,
            "Index" => R::Index,
            "Indices" => R::Indices,
            "Matrix" => R::FrSparseCoo,
            "RistrettoMatrix" => R::DalekSparseCoo,
            "KoalaBearMatrix" => R::KoalaBearSparseCoo,
            "KoalaBearExt8Matrix" => R::KoalaBearExt8SparseCoo,
            "KoalaBearExt8Field" => R::KoalaBearExt8,
            "KoalaBearExt8Vector" => R::KoalaBearExt8Vector,
            "KoalaBearExt8Polynomial" => R::KoalaBearExt8Polynomial,
            "KoalaBearExt8Round" => R::KoalaBearExt8Round,
            "KoalaBearField" => R::KoalaBear,
            "KoalaBearVector" => R::KoalaBearVector,
            "KoalaBearPolynomial" => R::KoalaBearPolynomial,
            "KoalaBearRound" => R::KoalaBearRound,
            "Vector" => R::FrVector,
            "Polynomial" => R::Polynomial,
            "RistrettoField" => R::DalekScalar,
            "RistrettoVector" => R::DalekVector,
            "RistrettoPolynomial" => R::DalekPolynomial,
            "RistrettoRound" => R::DalekRound,
            "RistrettoGroup" => R::Ristretto,
            "RistrettoGroups" => R::RistrettoVector,
            "FrDiagonal" => R::FrDiagonal,
            "RistrettoDiagonal" => R::RistrettoDiagonal,
            "Field" => R::Fr,
            "Table" => R::TableLsb,
            "TableMsb" => R::TableMsb,
            "Point" => R::Point,
            "Round" => R::Round,
            "Bool" => R::Bool,
            "Rng" => R::Resource,
            "Commitment" => R::Pcs,
            "OpeningState" => R::Pcs,
            "Proof" => R::Pcs,
            "ProverKey" => R::Pcs,
            "VerifierKey" => R::Pcs,
            "Nonce" => R::Resource,
            "Transcript" => R::Resource,
            "Curve" => R::G1,
            "Groups" => R::Groups,
            name => panic!("missing physical fixture for {name}"),
        };
        let expected = PhysicalType::new(logical, representation).unwrap();
        assert_eq!(value.physical_type(), expected, "{value:?}");
        assert_eq!(value.retained_bytes(), bytes, "{value:?}");
        let cloned = value.clone();
        assert_eq!(cloned.retained_bytes(), bytes);
        assert_eq!(cloned.physical_type(), value.physical_type());
        assert!(
            seen.insert(value.payload_name()),
            "duplicate accounting fixture"
        );
        // Every payload is safe to clone/drop without executing a kernel.
        drop(cloned);
    };
    macro_rules! scalar_family {
        ($scalar:expr, $identity:ident, $field:ident, $vector:ident, $poly:ident, $round:ident, $matrix:ident, $width:expr) => {{
            let scalar = $scalar;
            check(Value::$field(scalar), Type::Field, I::$identity, 512);
            check(
                Value::$vector([scalar; 2].into()),
                Type::Vector,
                I::$identity,
                256 + 2 * $width,
            );
            check(
                Value::$poly([scalar; 2].into()),
                Type::Polynomial,
                I::$identity,
                256 + 2 * $width,
            );
            check(Value::$round([scalar; 3]), Type::Round, I::$identity, 512);
            let matrix = crate::matrix::from_entries(1, 1, &[(0, 0, scalar)], &policy).unwrap();
            check(
                Value::$matrix(matrix),
                Type::Matrix,
                I::$identity,
                264 + $width,
            );
        }};
    }
    scalar_family!(
        Scalar::from(1),
        Bls12381Fr,
        Field,
        Vector,
        Polynomial,
        Round,
        Matrix,
        32
    );
    scalar_family!(
        Bn254Scalar::from(1),
        Bn254Fr,
        Bn254Field,
        Bn254Vector,
        Bn254Polynomial,
        Bn254Round,
        Bn254Matrix,
        32
    );
    scalar_family!(
        RistrettoScalar::ONE,
        Ristretto255Scalar,
        RistrettoField,
        RistrettoVector,
        RistrettoPolynomial,
        RistrettoRound,
        RistrettoMatrix,
        32
    );
    scalar_family!(
        KoalaBear::new(1),
        KoalaBear,
        KoalaBearField,
        KoalaBearVector,
        KoalaBearPolynomial,
        KoalaBearRound,
        KoalaBearMatrix,
        4
    );
    scalar_family!(
        KoalaBearExt8::from(KoalaBear::new(1)),
        KoalaBearExt8,
        KoalaBearExt8Field,
        KoalaBearExt8Vector,
        KoalaBearExt8Polynomial,
        KoalaBearExt8Round,
        KoalaBearExt8Matrix,
        32
    );
    macro_rules! group_family {
        ($point:expr, $identity:ident, $point_variant:ident, $vector_variant:ident, $width:expr) => {{
            let point = $point;
            check(Value::$point_variant(point), Type::Group, I::$identity, 512);
            check(
                Value::$vector_variant([point; 2].into()),
                Type::Groups,
                I::$identity,
                256 + 2 * $width,
            );
        }};
    }
    group_family!(
        crate::GroupPoint::generator(),
        Bls12381G1,
        Curve,
        Groups,
        128
    );
    group_family!(
        crate::Bn254G1::generator(),
        Bn254G1,
        Bn254G1,
        Bn254G1Vector,
        std::mem::size_of::<crate::Bn254G1>()
    );
    group_family!(
        crate::Bn254G2::generator(),
        Bn254G2,
        Bn254G2,
        Bn254G2Vector,
        std::mem::size_of::<crate::Bn254G2>()
    );
    group_family!(
        curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT,
        Ristretto255Group,
        RistrettoGroup,
        RistrettoGroups,
        std::mem::size_of::<crate::RistrettoPoint>()
    );
    check(
        Value::Bn254Gt(crate::Bn254Gt::generator()),
        Type::Group,
        I::Bn254Gt,
        512,
    );
    check(Value::Bool(true), Type::Bool, I::None, 512);
    check(Value::Index(3), Type::Index, I::None, 512);
    check(Value::Indices([1, 2].into()), Type::Indices, I::None, 272);
    check(
        Value::Point([Scalar::from(1); 2].into()),
        Type::Point,
        I::Bls12381Fr,
        320,
    );
    let table =
        zkc_arkworks::Table::from_logical(&[Scalar::from(1); 2], &policy.ark_bounds()).unwrap();
    check(
        Value::Table(Arc::new(table.clone())),
        Type::Table,
        I::Bls12381Fr,
        320,
    );
    check(
        Value::TableMsb(Arc::new(
            zkc_arkworks::MsbTable::from_lsb(&table, &policy.ark_bounds()).unwrap(),
        )),
        Type::Table,
        I::Bls12381Fr,
        320,
    );
    let keys = crate::Keys::setup_for_development(1, &policy.ark_bounds()).unwrap();
    let state = keys.prover_key().commit(&table).unwrap();
    let (_, proof) = state.open(&[Scalar::from(2)]).unwrap();
    check(
        Value::Commitment(Arc::new(state.commitment().clone())),
        Type::Commitment,
        I::MultilinearKzgBls12381,
        512,
    );
    check(
        Value::OpeningState(Arc::new(state)),
        Type::OpeningState,
        I::MultilinearKzgBls12381,
        320 + 1536 + 512,
    );
    check(
        Value::Proof(Arc::new(proof)),
        Type::Proof,
        I::MultilinearKzgBls12381,
        448,
    );
    check(
        Value::ProverKey(Arc::new(keys.prover_key().clone())),
        Type::ProverKey,
        I::MultilinearKzgBls12381,
        1536,
    );
    check(
        Value::VerifierKey(Arc::new(keys.verifier_key().clone())),
        Type::VerifierKey,
        I::MultilinearKzgBls12381,
        384,
    );
    check(
        Value::FrDiagonal(Arc::new(
            crate::diagonal::Diagonal::new(
                [Scalar::from(1); 2].into(),
                [Scalar::from(1); 2].into(),
            )
            .unwrap(),
        )),
        Type::Vector,
        I::Bls12381Fr,
        896,
    );
    check(
        Value::RistrettoDiagonal(Arc::new(
            crate::diagonal::Diagonal::new(
                [RistrettoScalar::ONE; 2].into(),
                [curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT; 2].into(),
            )
            .unwrap(),
        )),
        Type::Groups,
        I::Ristretto255Group,
        768 + 64 + 2 * std::mem::size_of::<crate::RistrettoPoint>(),
    );
    let shape = crate::plonky3::oracle::Shape::new(1, 2, 2).unwrap();
    let (root, state) =
        crate::plonky3::oracle::commit(vec![KoalaBear::new(1); 2], shape, 4096).unwrap();
    let path = state.open(0).unwrap().1;
    let state = crate::oracle::State::Base(Arc::new(state));
    let domain = crate::oracle::Domain::Base;
    check(
        Value::OracleRoot(domain, root),
        Type::Commitment,
        I::MerkleKoalaBear,
        512,
    );
    check(
        Value::OraclePath(domain, path.into()),
        Type::Proof,
        I::MerkleKoalaBear,
        288,
    );
    check(
        Value::OracleState(state.clone()),
        Type::OpeningState,
        I::MerkleKoalaBear,
        360,
    );
    check(
        Value::OracleRoots(domain, [root; 2].into()),
        Type::Commitments,
        I::MerkleKoalaBear,
        320,
    );
    check(
        Value::OracleStates(domain, [state].into()),
        Type::OpeningStates,
        I::MerkleKoalaBear,
        616 + std::mem::size_of::<crate::oracle::State>(),
    );
    let logical = LogicalType::parse("fixed_vector<field:koala-bear,2>").unwrap();
    let fixed = Value::FixedVector(
        crate::FixedVector::new(logical, [KoalaBear::new(1); 2].into()).unwrap(),
    );
    check(fixed.clone(), Type::FixedVector, I::None, 1288);
    check(
        Value::FieldArray(
            crate::FieldArray::new(
                LogicalType::field_array(I::Bls12381Fr, 2).unwrap(),
                [Scalar::from(1); 2].into(),
            )
            .unwrap(),
        ),
        Type::FieldArray,
        I::None,
        1344,
    );
    let descriptor = LogicalType::parse(&zkc_test_support::variants::logical(
        "Bulk",
        json!([["some", ["fixed_vector<field:koala-bear,2>"]]]),
    ))
    .unwrap()
    .variant_descriptor()
    .unwrap()
    .clone();
    let variant_bytes = descriptor.retained_bytes() + 256 + 512 + 1288;
    let sequence_type = LogicalType::sequence(LogicalType::parse("index").unwrap()).unwrap();
    check(
        Value::Sequence(
            crate::Sequence::new(
                LogicalType::parse("index").unwrap(),
                vec![Value::Index(7)],
                &Policy::default(),
            )
            .unwrap(),
        ),
        Type::Sequence,
        I::None,
        256 + sequence_type.descriptor_bytes() + 512 + 512,
    );
    check(
        Value::pack_variant(descriptor, 0, vec![fixed]).unwrap(),
        Type::Variant,
        I::None,
        variant_bytes,
    );
    let mut native = backend();
    let domain = Domain::new("P", "session", "main", None);
    check(
        native.issue_rng(domain.clone(), 1).unwrap(),
        Type::Rng,
        I::Bls12381Fr,
        512,
    );
    check(
        native.issue_nonce(domain.clone(), 1).unwrap(),
        Type::Nonce,
        I::Bls12381Fr,
        512,
    );
    check(
        native
            .issue_transcript(domain, 1, &[1, 0, 0, 0, 0, 0, 0, 0, 0])
            .unwrap(),
        Type::Transcript,
        I::Merlin3Fr64Be,
        512,
    );
    let b = binding(
        "resource_unit.create",
        &["Slot.A"],
        "logical/resource_unit.create",
    );
    let (unit, _) = run(backend(), &b, &[], vec![]);
    check(unit.unwrap().remove(0), Type::ResourceUnit, I::None, 512);
    assert_eq!(seen, Value::PAYLOAD_NAMES.iter().copied().collect());
}

#[test]
fn wrong_kind_capability_wrappers_refuse_without_panicking() {
    use zkc_runtime::interactive::Identity as I;
    use zkc_runtime::interactive::{Backend, Value as RuntimeValue};
    let (unit, mut native) = run(
        backend(),
        &binding(
            "resource_unit.create",
            &["Slot.A"],
            "logical/resource_unit.create",
        ),
        &[],
        vec![],
    );
    let mut values = unit.unwrap();
    let domain = Domain::new("P", "session", "main", None);
    for field in [
        I::Bls12381Fr,
        I::Bn254Fr,
        I::KoalaBearExt8,
        I::Ristretto255Scalar,
    ] {
        values.push(native.issue_rng_for(field, domain.clone(), 1).unwrap());
    }
    for field in [I::Bls12381Fr, I::Ristretto255Scalar] {
        values.push(native.issue_nonce_for(field, domain.clone(), 1).unwrap());
    }
    for suite in [
        I::Merlin3Fr64Be,
        I::Merlin3KoalaBearExt8,
        I::Merlin3Ristretto64Le,
        I::Spongefish074KeccakFr64Be,
    ] {
        values.push(
            native
                .issue_transcript_for(suite, domain.clone(), 1, &[1, 0, 0, 0, 0, 0, 0, 0, 0])
                .unwrap(),
        );
    }
    for value in values {
        let token = value.capability().unwrap();
        for wrong in [
            Value::Rng(token.clone()),
            Value::Nonce(token.clone()),
            Value::Transcript(token.clone()),
        ] {
            assert_eq!(wrong.retained_bytes(), 512);
            assert_eq!(wrong.physical_type(), value.physical_type());
            assert!(wrong.validate_serializable().is_err());
            if wrong.ty() == value.ty() {
                native.validate_value(&wrong).unwrap();
            } else {
                assert_eq!(
                    native.validate_value(&wrong).unwrap_err().code,
                    "refused:capability-kind"
                );
                // Frame entry asks for physical_type before backend validation.
                // A public wrong-kind wrapper must refuse there without panic.
                let ty = value.physical_type().spelling();
                let carrier = serde_json::to_vec(&json!([
                    "zkc.participants/1",
                    [],
                    "physical",
                    [],
                    [[
                        "participant",
                        "actor",
                        "instance",
                        "P",
                        [],
                        [["arg", ty]],
                        [ty],
                        [["return", ["arg"]]]
                    ]],
                    [["entry", "main", [["P", "actor"]]]]
                ]))
                .unwrap();
                let admitted = admit_supplied(&carrier, &native).unwrap();
                native = match Runner::new(&admitted, "main", "P", "session", native, vec![wrong]) {
                    Err(error) => {
                        assert!(
                            error.error.to_string().contains("capability-kind"),
                            "{}",
                            error.error
                        );
                        error.backend
                    }
                    Ok(_) => panic!("wrong-kind entry unexpectedly accepted"),
                };
            }
        }
    }
}

#[test]
fn independent_same_port_provider_and_missing_owner_are_checked() {
    let mut registry = installed().unwrap().clone();
    let mut row = Alternative {
        identity: "independent/field.mul",
        original: "arkworks/field.mul",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Default,
        handler: Some(arithmetic),
        public_operands: false,
    };
    registry.alternative(&row).unwrap();
    let entry = registry.get(row.identity).unwrap();
    let exact = binding("field.mul", &["bls12-381.fr"], row.identity);
    let default = binding("field.mul", &["bls12-381.fr"], row.original);
    assert_eq!(
        entry.signature(&exact).unwrap(),
        registry
            .get(row.original)
            .unwrap()
            .signature(&default)
            .unwrap()
    );
    assert!(
        entry
            .signature(&binding("field.mul", &["bn254.fr"], row.identity))
            .is_none()
    );
    assert!(
        entry
            .signature(&binding("field.add", &["bls12-381.fr"], row.identity))
            .is_none()
    );
    assert!(registry.get("unregistered/field.mul").is_none());
    assert_eq!(
        registry.alternative(&row).unwrap_err().code,
        "refused:duplicate-implementation-owner"
    );
    row.identity = "missing/field.mul";
    row.original = "uninstalled/field.mul";
    assert_eq!(
        registry.alternative(&row).unwrap_err().code,
        "refused:implementation-owner-missing"
    );
    row.original = "plonky3/fixed_vector.dot";
    assert_eq!(
        registry.alternative(&row).unwrap_err().code,
        "refused:implementation-owner-shape"
    );
    row.original = "independent/field.mul";
    assert_eq!(
        registry.alternative(&row).unwrap_err().code,
        "refused:implementation-owner-shape"
    );
}

#[test]
fn fixed_implementations_reject_alternative_registration() {
    for original in [
        "arkworks/table.relayout",
        "plonky3/fixed_vector.dot",
        "arkworks/pairing.check",
        "plonky3/field.embed",
        "plonky3/vector.embed",
        "arkworks/bool.and",
        "arkworks/random.draw",
        "arkworks/transcript.challenge",
    ] {
        let mut registry = installed().unwrap().clone();
        assert_eq!(
            registry
                .alternative(&Alternative {
                    identity: "independent/fixed",
                    original,
                    primary: Identity::Bls12381Fr,
                    ports: crate::bindings::PortTransform::Default,
                    handler: None,
                    public_operands: false,
                })
                .unwrap_err()
                .code,
            "refused:implementation-owner-shape",
            "{original}"
        );
    }
}

#[test]
fn transcript_alternative_preserves_concrete_observation_policy() {
    let mut registry = installed().unwrap().clone();
    registry
        .alternative(&Alternative {
            identity: "independent/observation",
            original: "arkworks/transcript.observe.field",
            primary: Identity::Merlin3Fr64Be,
            ports: crate::bindings::PortTransform::Default,
            handler: None,
            public_operands: false,
        })
        .unwrap();
    let entry = registry.get("independent/observation").unwrap();
    for (suite, payload, codec, accepted) in [
        (
            "merlin3.bls12-381.fr64be/1",
            "bls12-381.fr",
            "zkcv.field.bls12-381.fr/1",
            true,
        ),
        (
            "merlin3.bls12-381.fr64be/1",
            "bn254.fr",
            "zkcv.field.bn254.fr/1",
            false,
        ),
        (
            "merlin3.bls12-381.fr64be/1",
            "bls12-381.fr",
            "wrong-codec",
            false,
        ),
        (
            "merlin3.ristretto255.scalar64le/1",
            "ristretto255.scalar",
            "zkcv.field.ristretto255.scalar/1",
            false,
        ),
        (
            "spongefish0.7.4.keccak.bls12-381.fr64be/1",
            "bls12-381.fr",
            "zkcv.field.bls12-381.fr/1",
            false,
        ),
    ] {
        assert_eq!(
            entry
                .signature(&binding(
                    "transcript.observe.field",
                    &[suite, payload, codec],
                    "independent/observation"
                ))
                .is_some(),
            accepted,
            "{suite} {payload} {codec}"
        );
    }
    assert_eq!(
        registry
            .alternative(&Alternative {
                identity: "independent/second",
                original: "independent/observation",
                primary: Identity::Merlin3Fr64Be,
                ports: crate::bindings::PortTransform::Default,
                handler: None,
                public_operands: false,
            })
            .unwrap_err()
            .code,
        "refused:implementation-owner-shape"
    );
}

#[test]
fn curve_alternative_requires_the_exact_group() {
    let mut registry = installed().unwrap().clone();
    registry
        .alternative(&Alternative {
            identity: "independent/bn254-add",
            original: "arkworks/curve.add",
            primary: Identity::Bn254G1,
            ports: crate::bindings::PortTransform::Default,
            handler: None,
            public_operands: false,
        })
        .unwrap();
    let entry = registry.get("independent/bn254-add").unwrap();
    assert!(
        entry
            .signature(&binding(
                "curve.add",
                &["bn254.g1"],
                "independent/bn254-add"
            ))
            .is_some()
    );
    assert!(
        entry
            .signature(&binding(
                "curve.add",
                &["bn254.g2"],
                "independent/bn254-add"
            ))
            .is_none()
    );
    assert!(
        entry
            .signature(&binding(
                "curve.add",
                &["bn254.fr"],
                "independent/bn254-add"
            ))
            .is_none()
    );
}

#[test]
fn transcript_table_alternative_preserves_state_and_transforms_payload() {
    let mut registry = installed().unwrap().clone();
    registry
        .alternative(&Alternative {
            identity: "independent/msb-observation",
            original: "arkworks/transcript.observe.table",
            primary: Identity::Merlin3Fr64Be,
            ports: crate::bindings::PortTransform::Msb,
            handler: None,
            public_operands: false,
        })
        .unwrap();
    let arguments = &[
        "merlin3.bls12-381.fr64be/1",
        "bls12-381.fr",
        "zkcv.table.bls12-381.fr/1",
    ];
    let entry = registry.get("independent/msb-observation").unwrap();
    let actual = entry
        .signature(&binding(
            "transcript.observe.table",
            arguments,
            "independent/msb-observation",
        ))
        .unwrap();
    let mut expected = registry
        .get("arkworks/transcript.observe.table")
        .unwrap()
        .signature(&binding(
            "transcript.observe.table",
            arguments,
            "arkworks/transcript.observe.table",
        ))
        .unwrap();
    expected.inputs[1] = zkc_runtime::interactive::PhysicalType::new(
        expected.inputs[1].logical(),
        zkc_runtime::interactive::Representation::TableMsb,
    )
    .unwrap();
    assert_eq!(actual, expected);
}

#[test]
fn family_rows_retain_field_literal_rules() {
    use zkc_runtime::interactive::AttributeRule as A;
    for (provider, field, single, multiple) in [
        (
            "arkworks",
            "bls12-381.fr",
            A::FieldDecimal,
            A::FieldDecimals,
        ),
        ("arkworks", "bn254.fr", A::Bn254Decimal, A::Bn254Decimals),
        (
            "dalek",
            "ristretto255.scalar",
            A::RistrettoDecimal,
            A::RistrettoDecimals,
        ),
        (
            "plonky3",
            "koala-bear",
            A::KoalaBearDecimal,
            A::KoalaBearDecimals,
        ),
        (
            "plonky3",
            "koala-bear.ext8-binomial3",
            A::KoalaBearDecimal,
            A::KoalaBearDecimals,
        ),
    ] {
        for (contract, rule) in [("field.constant", single), ("vector.constant", multiple)] {
            let implementation = format!("{provider}/{contract}");
            let signature = installed()
                .unwrap()
                .get(&implementation)
                .unwrap()
                .signature(&binding(contract, &[field], &implementation))
                .unwrap();
            assert_eq!(signature.attributes, rule, "{implementation} {field}");
        }
    }
}

#[test]
fn alternative_eligibility_matches_the_reviewed_native_set() {
    use std::collections::BTreeSet;
    let expected = [
        "curve.add",
        "curve.append",
        "curve.at",
        "curve.commit",
        "curve.concat",
        "curve.empty",
        "curve.equal",
        "curve.generator",
        "curve.get",
        "curve.length",
        "curve.msm",
        "curve.neg",
        "curve.nonidentity",
        "curve.response",
        "curve.scale",
        "curve.scale_each",
        "curve.split",
        "curve.vector_add",
        "curve.vector_scale",
        "field.add",
        "field.constant",
        "field.equal",
        "field.from_index",
        "field.inverse",
        "field.mul",
        "field.neg",
        "field.sub",
        "matrix.bilinear",
        "matrix.dimension",
        "matrix.identity_check",
        "matrix.mul_vector",
        "matrix.shape_check",
        "matrix.transpose_mul_vector",
        "pcs.check",
        "pcs.commit",
        "pcs.equal",
        "pcs.open",
        "poly.append_point",
        "poly.boundary",
        "poly.coefficient_count",
        "poly.coefficients",
        "poly.coset_evaluate",
        "poly.coset_interpolate",
        "poly.degree_check",
        "poly.divide_opening",
        "poly.domain_point",
        "poly.domain_points",
        "poly.domain_root",
        "poly.empty_point",
        "poly.equality_weights",
        "poly.evaluate",
        "poly.even_odd_fold",
        "poly.fold",
        "poly.from_coefficients",
        "poly.opening_quotient",
        "poly.product_round",
        "poly.product_sum",
        "poly.table_arity",
        "poly.round_evaluate",
        "poly.univariate_boundary",
        "poly.univariate_evaluate",
        "transcript.native.indexed.observe.bool",
        "transcript.native.indexed.observe.commitment",
        "transcript.native.indexed.observe.field",
        "transcript.native.indexed.observe.field_array",
        "transcript.native.indexed.observe.data",
        "transcript.native.indexed.observe.group",
        "transcript.native.indexed.observe.index",
        "transcript.native.indexed.observe.proof",
        "transcript.native.observe.bool",
        "transcript.native.observe.field",
        "transcript.native.observe.group",
        "transcript.observe.bool",
        "transcript.observe.commitment",
        "transcript.observe.commitments",
        "transcript.observe.field",
        "transcript.observe.group",
        "transcript.observe.groups",
        "transcript.observe.index",
        "transcript.observe.indices",
        "transcript.observe.matrix",
        "transcript.observe.point",
        "transcript.observe.polynomial",
        "transcript.observe.proof",
        "transcript.observe.round",
        "transcript.observe.table",
        "transcript.observe.vector",
        "vector.add",
        "vector.append",
        "vector.at",
        "vector.concat",
        "vector.constant",
        "vector.dot",
        "vector.empty",
        "vector.equal",
        "vector.fill",
        "vector.from_point",
        "vector.from_table",
        "vector.gather",
        "vector.geometric",
        "vector.get",
        "vector.interleave",
        "vector.inverse",
        "vector.kronecker",
        "vector.length",
        "vector.length_check",
        "vector.matvec",
        "vector.mul",
        "vector.powers",
        "vector.prefix_product",
        "vector.prefix_sum",
        "vector.rotate",
        "vector.scale",
        "vector.scatter_sum",
        "vector.slice",
        "vector.splat",
        "vector.split",
        "vector.sub",
        "vector.sum",
        "vector.to_point",
        "vector.to_table",
    ]
    .into_iter()
    .collect::<BTreeSet<_>>();
    let actual = installed()
        .unwrap()
        .entries
        .values()
        .filter_map(|entry| match entry.signature {
            Signature::Shaped(row, crate::bindings::Selection::Default) if row.alternatives => {
                Some(row.name)
            }
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(actual, expected);
}

/// Enumerate the actual owner rows so every newly installed alternative must
/// acquire an execution witness, including layout aliases with unchanged ports.
#[test]
fn every_alternative_executes_and_preserves_the_original_result() {
    use crate::RistrettoScalar as R;
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT as G;
    use std::sync::Arc;
    let policy = Policy::default();
    let scalar = Scalar::from;
    let vector = |values: &[u64]| Value::Vector(values.iter().copied().map(scalar).collect());
    let rvector =
        |values: &[u64]| Value::RistrettoVector(values.iter().copied().map(R::from).collect());
    let groups = || Value::RistrettoGroups([G * R::from(7u64), G * R::from(11u64)].into());
    let table = |values: &[u64]| {
        Value::table(
            &values.iter().copied().map(scalar).collect::<Vec<_>>(),
            &policy,
        )
        .unwrap()
    };
    for row in alternatives() {
        let contract = installed().unwrap().get(row.identity).unwrap().contract;
        let primary = if contract.starts_with("curve.") {
            "ristretto255.group"
        } else {
            "bls12-381.fr"
        };
        let inputs = match contract {
            "poly.product_sum" | "poly.product_round" => {
                vec![table(&[1, 2, 3, 5]), table(&[7, 11, 13, 17])]
            }
            "poly.fold" => vec![table(&[1, 2, 3, 5]), Value::Field(scalar(3))],
            "poly.evaluate" => vec![
                table(&[1, 2, 3, 5]),
                Value::Point([scalar(3), scalar(4)].into()),
            ],
            "poly.empty_point" => vec![],
            "poly.append_point" => vec![Value::Point([scalar(3)].into()), Value::Field(scalar(4))],
            "poly.boundary" => vec![Value::Round([1, 2, 3].map(scalar))],
            "poly.round_evaluate" => {
                vec![Value::Round([1, 2, 3].map(scalar)), Value::Field(scalar(4))]
            }
            "vector.from_table" => vec![table(&[1, 2, 3, 5])],
            "vector.to_table" => vec![vector(&[1, 2, 3, 5])],
            "vector.mul" | "vector.dot" => vec![vector(&[2, 3]), vector(&[5, 7])],
            "curve.scale_each" | "curve.msm" => vec![rvector(&[2, 3]), groups()],
            other => panic!("new alternative needs an execution fixture: {other}"),
        };
        let original_inputs = inputs.clone();
        let mut alternate_inputs = inputs;
        for value in &mut alternate_inputs {
            if row.identity.starts_with("arkworks-msb/")
                && let Value::Table(t) = value
            {
                *value = Value::TableMsb(Arc::new(
                    zkc_arkworks::MsbTable::from_lsb(t, &policy.ark_bounds()).unwrap(),
                ));
            }
        }
        let native =
            || backend().with_public_role_policy(PublicRolePolicy::new(["P".into()]).unwrap());
        // Diagonal views cannot cross entry boundaries. Exercise their consumers
        // through the producer in the same local frame, then compare its result.
        let (call, original, alternate) = match row.identity {
            "arkworks-diagonal/vector.dot" => (
                "vector.mul",
                "arkworks/vector.mul",
                "arkworks-diagonal/vector.mul",
            ),
            "dalek-diagonal/curve.msm" => (
                "curve.scale_each",
                "dalek/curve.scale_each",
                "dalek-diagonal/curve.scale_each",
            ),
            _ => (contract, row.original, row.identity),
        };
        let original = binding(call, &[primary], original);
        let alternate = binding(call, &[primary], alternate);
        assert!(
            String::from_utf8(program(&alternate, &[]))
                .unwrap()
                .contains(row.identity)
        );
        let expected = run(native(), &original, &[], original_inputs).0.unwrap();
        let actual = run(native(), &alternate, &[], alternate_inputs)
            .0
            .unwrap_or_else(|e| panic!("{}: {e}", row.identity));
        let normalize = |v: Value| match v {
            Value::TableMsb(t) => Value::Table(Arc::new(t.to_lsb(&policy.ark_bounds()).unwrap())),
            other => other,
        };
        let encode = |v: Value| native().encode_value(&normalize(v)).unwrap();
        assert_eq!(
            actual.into_iter().map(encode).collect::<Vec<_>>(),
            expected.into_iter().map(encode).collect::<Vec<_>>(),
            "{}",
            row.identity
        );
    }
}

#[test]
fn layout_aliases_inherit_security_requirements() {
    let mut registry = installed().unwrap().clone();
    registry
        .entries
        .get_mut("arkworks/field.mul")
        .unwrap()
        .public_operands = true;
    registry
        .alternative(&Alternative {
            identity: "alias/field.mul",
            original: "arkworks/field.mul",
            primary: zkc_runtime::interactive::Identity::Bls12381Fr,
            ports: crate::bindings::PortTransform::Default,
            handler: None,
            public_operands: false,
        })
        .unwrap();
    let original = registry.get("arkworks/field.mul").unwrap();
    let alias = registry.get("alias/field.mul").unwrap();
    assert!(alias.public_operands);
    assert!(std::ptr::fn_addr_eq(original.handler, alias.handler));
}

#[test]
fn collection_limits_follow_payload_storage() {
    use std::sync::Arc;
    use zkc_runtime::interactive::{Backend, Identity, LogicalType, Type};
    let mut native = backend();
    native.core.policy.max_table_elements = 2;
    let roots = Value::OracleRoots(crate::oracle::Domain::Base, Arc::from([[0u8; 32]; 3]));
    assert_eq!(
        native.validate_value(&roots).unwrap_err().code,
        "exhausted:element-limit"
    );
    native.core.policy.max_table_elements = 64;
    let path = Value::OraclePath(crate::oracle::Domain::Base, Arc::from([[0u8; 32]; 25]));
    assert_eq!(
        native.validate_value(&path).unwrap_err().code,
        "refused:oracle-path-length"
    );
    native.core.policy.max_value_bytes = 1800;
    let logical = LogicalType::fixed_vector(
        LogicalType::new(Type::Field, Identity::KoalaBear).unwrap(),
        64,
    )
    .unwrap();
    let fixed = Value::FixedVector(
        crate::FixedVector::new(logical, vec![crate::KoalaBear::new(1); 64].into()).unwrap(),
    );
    native.validate_value(&fixed).unwrap();
}
