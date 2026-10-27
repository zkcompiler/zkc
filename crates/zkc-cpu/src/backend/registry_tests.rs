use super::*;
use crate::{Domain, EntryPolicy, Policy, Scalar, Value};
use serde_json::json;
use zkc_runtime::interpreter::Runner;
use zkc_runtime::vm::Identity;
use zkc_runtime::vm::{Action, OperationBinding, StopKind};

fn backend() -> CpuBackend {
    CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn binding(contract: &str, arguments: &[&str], implementation: &str) -> OperationBinding {
    OperationBinding {
        contract: contract.into(),
        arguments: arguments.iter().map(|s| (*s).into()).collect(),
        implementation: implementation.into(),
        physical_arguments: vec![],
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
            zkc_runtime::vm::Representation::FrDiagonal
                | zkc_runtime::vm::Representation::RistrettoDiagonal
        )
    }) {
        vec![]
    } else {
        returns.clone()
    };
    let result_types = if returned.is_empty() { vec![] } else { outputs };
    let mut carrier = json!([
        "zkc.program/0",
        [[
            "b",
            binding.contract,
            binding.arguments,
            binding.implementation,
            binding.physical_arguments
        ]],
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
            ports,
            result_types,
            [
                ["local", "work", "f", names, returned],
                ["return", returned]
            ],
            []
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
            dot,
            []
        ]));
        carrier[2][0][3] = json!(["field:bls12-381.fr@arkworks.fr/0"]);
        carrier[2][0][4] = json!([
            ["op", "view", "b", [], ["a0", "a1"], ["view"]],
            ["op", "consume", "dot", [], ["a0", "view"], ["out"]],
            ["return", ["out"]]
        ]);
        carrier[3][0][5] = carrier[2][0][3].clone();
        carrier[3][0][6] = json!([
            ["local", "work", "f", ["a0", "a1"], ["out"]],
            ["return", ["out"]]
        ]);
    }
    if binding.contract == "curve.scale_each" && binding.arguments == ["ristretto255.group"] {
        let msm = if binding.implementation.starts_with("dalek-diagonal/") {
            "dalek-diagonal/curve.msm"
        } else {
            "dalek/curve.msm"
        };
        carrier[1].as_array_mut().unwrap().push(json!([
            "msm",
            "curve.msm",
            ["ristretto255.group"],
            msm,
            []
        ]));
        carrier[2][0][3] = json!(["group:ristretto255.group@dalek.ristretto/0"]);
        carrier[2][0][4] = json!([
            ["op", "view", "b", [], ["a0", "a1"], ["view"]],
            ["op", "consume", "msm", [], ["a0", "view"], ["out"]],
            ["return", ["out"]]
        ]);
        carrier[3][0][5] = carrier[2][0][3].clone();
        carrier[3][0][6] = json!([
            ["local", "work", "f", ["a0", "a1"], ["out"]],
            ["return", ["out"]]
        ]);
    }
    serde_json::to_vec(&carrier).unwrap()
}
fn run(
    backend: CpuBackend,
    binding: &OperationBinding,
    attributes: &[&str],
    args: Vec<Value>,
) -> (std::result::Result<Vec<Value>, String>, CpuBackend) {
    let admitted =
        zkc_runtime::vm::Program::decode(&program(binding, attributes), crate::cpu_contracts())
            .and_then(|program| {
                program.check_installation(&backend)?;
                Ok(program)
            })
            .unwrap();
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
                crate::fixed_vector::IMPLEMENTATIONS,
                Signature::Custom(crate::fixed_vector::signature),
                fixed_vector
            )
            .unwrap_err()
            .code,
        "refused:duplicate-implementation-owner"
    );
}

fn first_handler(
    _: &mut CpuBackend,
    i: &zkc_runtime::vm::Invocation<'_>,
    _: &[Value],
) -> crate::Result<Vec<Value>> {
    assert_eq!(i.binding.implementation(), "arkworks/vector.dot");
    Err(crate::refused("first-handler"))
}
fn second_handler(
    _: &mut CpuBackend,
    i: &zkc_runtime::vm::Invocation<'_>,
    _: &[Value],
) -> crate::Result<Vec<Value>> {
    assert_eq!(i.binding.implementation(), "arkworks-pairwise/vector.dot");
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
    registry.entries.get_mut(&a.implementation).unwrap().handler = Dispatch::Direct(first_handler);
    registry.entries.get_mut(&b.implementation).unwrap().handler = Dispatch::Direct(second_handler);
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
fn opening_state_lists_validate_every_members_nominal_domain_before_entry() {
    use crate::{KoalaBear, KoalaBearExt4, KoalaBearExt8, merkle, oracle};
    use std::sync::Arc;
    use zkc_runtime::vm::{Backend, Program, RuntimeError, Usage, Value as RuntimeValue};

    let shape = zkc_kernels::plonky3::oracle::Shape::new(1, 2, 8).unwrap();
    let base = vec![KoalaBear::new(3); 2];
    let (_, base_tree) =
        zkc_kernels::plonky3::oracle::commit(base.clone(), shape, 1 << 20).unwrap();
    let (_, extension_tree) = zkc_kernels::plonky3::oracle::commit(
        vec![KoalaBearExt8::from(KoalaBear::new(3)); 2],
        shape,
        1 << 20,
    )
    .unwrap();
    let (_, merkle_base) = zkc_kernels::plonky3::merkle::commit::<
        zkc_kernels::plonky3::merkle::poseidon2::Base,
    >(base, shape, 1 << 20)
    .unwrap();
    let (_, merkle_quartic) =
        zkc_kernels::plonky3::merkle::commit::<zkc_kernels::plonky3::merkle::poseidon2::Quartic>(
            vec![KoalaBearExt4::from(KoalaBear::new(3)); 2],
            shape,
            1 << 20,
        )
        .unwrap();
    let keccak_base = oracle::State::Base(Arc::new(base_tree));
    let keccak_extension = oracle::State::Extension(Arc::new(extension_tree));
    let poseidon_base = merkle::State::Poseidon2KoalaBear(Arc::new(merkle_base));
    let poseidon_extension = merkle::State::Poseidon2KoalaBearExt4(Arc::new(merkle_quartic));
    for (valid, invalid) in [
        (
            Value::OracleStates(oracle::Domain::Base, vec![keccak_base.clone()].into()),
            Value::OracleStates(
                oracle::Domain::Base,
                vec![keccak_base.clone(), keccak_extension.clone()].into(),
            ),
        ),
        (
            Value::OracleStates(oracle::Domain::Extension, vec![keccak_extension].into()),
            Value::OracleStates(oracle::Domain::Extension, vec![keccak_base].into()),
        ),
        (
            Value::MerkleTrees(
                merkle::Scheme::Poseidon2KoalaBear,
                vec![poseidon_base.clone()].into(),
            ),
            Value::MerkleTrees(
                merkle::Scheme::Poseidon2KoalaBear,
                vec![poseidon_base.clone(), poseidon_extension.clone()].into(),
            ),
        ),
        (
            Value::MerkleTrees(
                merkle::Scheme::Poseidon2KoalaBearExt4,
                vec![poseidon_extension].into(),
            ),
            Value::MerkleTrees(
                merkle::Scheme::Poseidon2KoalaBearExt4,
                vec![poseidon_base].into(),
            ),
        ),
    ] {
        let native = backend();
        native.validate_value(&valid).unwrap();
        assert_eq!(
            native.validate_value(&invalid).unwrap_err().code,
            "refused:oracle-domain"
        );
        // The entry declares the malformed list's full physical type. Its
        // contents still have to agree before any instruction or frame enters.
        let operation = binding(
            "opening_states.length",
            &[invalid.physical_type().logical().identity().name()],
            "plonky3/opening_states.length",
        );
        let admitted = Program::decode(&program(&operation, &[]), crate::cpu_contracts()).unwrap();
        let error = Runner::new(&admitted, "main", "P", "session", native, vec![invalid])
            .err()
            .expect("mismatched list member must refuse loading");
        assert!(matches!(error.error, RuntimeError::Backend(ref error)
            if error.code == "refused:oracle-domain"));
        assert_eq!(error.usage, Usage::default());
        let (outputs, _) = run(backend(), &operation, &[], vec![valid]);
        assert!(matches!(&outputs.unwrap()[..], [Value::Index(1)]));
    }
}

#[test]
fn every_payload_has_explicit_identity_and_retained_charge() {
    use crate::{
        BabyBear, BabyBearExt4, Bn254Scalar, Goldilocks, GoldilocksExt2, KoalaBear, KoalaBearExt4,
        KoalaBearExt8, RistrettoScalar,
    };
    use std::{collections::HashSet, sync::Arc};
    use zkc_runtime::vm::{
        Identity as I, LogicalType, PhysicalType, Representation as R, ResourceDomain, Type,
        Value as RuntimeValue,
    };
    let policy = Policy::default();
    let mut seen = HashSet::new();
    let mut classified = Vec::new();
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
        let representation =
            match value.payload_name() {
                "Sequence" => R::Sequence,
                "FixedVector" => R::FixedVector,
                "FieldArray" => R::FieldArray,
                "Variant" => R::Variant,
                "ResourceUnit" => R::ResourceUnit,
                "BlstField" | "BlstVector" | "BlstG1" | "BlstG1Vector" | "BlstG2"
                | "BlstG2Vector" => crate::operations::blst::physical(kind, identity)
                    .unwrap()
                    .representation(),
                "HaloField" | "HaloVector" | "HaloG1" | "HaloG1Vector" | "HaloG2"
                | "HaloG2Vector" => crate::operations::halo2curves::physical(kind, identity)
                    .unwrap()
                    .representation(),
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
                "Bls12381G2" => R::Bls12381G2,
                "Bls12381G2Vector" => R::Bls12381G2Vector,
                "Bls12381Gt" => R::Bls12381Gt,
                "OracleRoot" => R::MerkleRoot,
                "OraclePath" => R::MerklePath,
                "OracleState" => R::MerkleState,
                "OracleRoots" => R::MerkleRoots,
                "OracleStates" => R::MerkleStates,
                "MerkleDigest" => R::MerkleDigest,
                "MerkleProof" => R::MerkleProof,
                "MerkleTree" => R::MerkleTree,
                "MerkleDigests" => R::MerkleDigests,
                "MerkleTrees" => R::MerkleTrees,
                "Index" => R::Index,
                "Indices" => R::Indices,
                "Bytes" => R::Bytes,
                "Shake128State" => R::Shake128State,
                "QuotientMatrix" => R::QuotientMatrix,
                "Matrix" => R::FrSparseCoo,
                "RistrettoMatrix" => R::DalekSparseCoo,
                "KoalaBearMatrix" => R::KoalaBearSparseCoo,
                "KoalaBearExt8Matrix" => R::KoalaBearExt8SparseCoo,
                "KoalaBearExt8Field" => R::KoalaBearExt8,
                "KoalaBearExt8Vector" => R::KoalaBearExt8Vector,
                "KoalaBearExt8Polynomial" => R::KoalaBearExt8Polynomial,
                "KoalaBearExt8Round" => R::KoalaBearExt8Round,
                "KoalaBearExt4Matrix" => R::KoalaBearExt4SparseCoo,
                "KoalaBearExt4Field" => R::KoalaBearExt4,
                "KoalaBearExt4Vector" => R::KoalaBearExt4Vector,
                "KoalaBearExt4Polynomial" => R::KoalaBearExt4Polynomial,
                "KoalaBearExt4Round" => R::KoalaBearExt4Round,
                "BabyBearField" => R::BabyBear,
                "BabyBearVector" => R::BabyBearVector,
                "BabyBearPolynomial" => R::BabyBearPolynomial,
                "BabyBearRound" => R::BabyBearRound,
                "BabyBearMatrix" => R::BabyBearSparseCoo,
                "BabyBearExt4Field" => R::BabyBearExt4,
                "BabyBearExt4Vector" => R::BabyBearExt4Vector,
                "BabyBearExt4Polynomial" => R::BabyBearExt4Polynomial,
                "BabyBearExt4Round" => R::BabyBearExt4Round,
                "BabyBearExt4Matrix" => R::BabyBearExt4SparseCoo,
                "GoldilocksField" => R::Goldilocks,
                "GoldilocksVector" => R::GoldilocksVector,
                "GoldilocksPolynomial" => R::GoldilocksPolynomial,
                "GoldilocksRound" => R::GoldilocksRound,
                "GoldilocksMatrix" => R::GoldilocksSparseCoo,
                "GoldilocksExt2Field" => R::GoldilocksExt2,
                "GoldilocksExt2Vector" => R::GoldilocksExt2Vector,
                "GoldilocksExt2Polynomial" => R::GoldilocksExt2Polynomial,
                "GoldilocksExt2Round" => R::GoldilocksExt2Round,
                "GoldilocksExt2Matrix" => R::GoldilocksExt2SparseCoo,
                "Binary64Matrix" => R::Binary64SparseCoo,
                "Binary64Field" => R::Binary64,
                "Binary64Vector" => R::Binary64Vector,
                "Binary64Polynomial" => R::Binary64Polynomial,
                "Binary64Round" => R::Binary64Round,
                "Binary64Ext3Matrix" => R::Binary64Ext3SparseCoo,
                "Binary64Ext3Field" => R::Binary64Ext3,
                "Binary64Ext3Vector" => R::Binary64Ext3Vector,
                "Binary64Ext3Polynomial" => R::Binary64Ext3Polynomial,
                "Binary64Ext3Round" => R::Binary64Ext3Round,
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
                "EdwardsGroup" => R::EdwardsPrime,
                "EdwardsGroups" => R::EdwardsPrimeVector,
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
        let expected = if matches!(representation, R::Extension(_)) {
            crate::contracts::physical(kind, identity).unwrap().clone()
        } else {
            PhysicalType::new(logical, representation).unwrap()
        };
        assert_eq!(value.physical_type(), expected, "{value:?}");
        classified.push((value.clone(), expected.clone()));
        assert_eq!(value.retained_bytes(), bytes, "{value:?}");
        let cloned = value.clone();
        assert_eq!(cloned.retained_bytes(), bytes);
        assert_eq!(cloned.physical_type(), value.physical_type());
        assert!(
            seen.insert(value.payload_name()),
            "duplicate accounting fixture"
        );
        // Every payload is safe to clone/drop without executing an operation.
        drop(cloned);
    };
    use zkc_kernels::blst::bls12_381 as blst;
    check(
        Value::BlstField(blst::Scalar::from(1)),
        Type::Field,
        I::Bls12381Fr,
        512,
    );
    check(
        Value::BlstVector(Arc::new(
            blst::ScalarVector::filled(2, blst::Scalar::from(1)).unwrap(),
        )),
        Type::Vector,
        I::Bls12381Fr,
        320,
    );
    check(
        Value::BlstG1(blst::G1::generator()),
        Type::Group,
        I::Bls12381G1,
        512,
    );
    check(
        Value::BlstG1Vector(Arc::new(
            blst::G1Vector::filled(2, blst::G1::generator()).unwrap(),
        )),
        Type::Groups,
        I::Bls12381G1,
        256 + 2 * std::mem::size_of::<blst::G1Element>(),
    );
    check(
        Value::BlstG2(Arc::new(blst::G2::generator())),
        Type::Group,
        I::Bls12381G2,
        512,
    );
    check(
        Value::BlstG2Vector(Arc::new(
            blst::G2Vector::filled(2, blst::G2::generator()).unwrap(),
        )),
        Type::Groups,
        I::Bls12381G2,
        256 + 2 * std::mem::size_of::<blst::G2Element>(),
    );
    use zkc_kernels::halo2curves::bn254 as halo;
    check(
        Value::HaloField(halo::Scalar::from(1)),
        Type::Field,
        I::Bn254Fr,
        512,
    );
    check(
        Value::HaloVector(Arc::new(
            halo::ScalarVector::filled(2, halo::Scalar::from(1)).unwrap(),
        )),
        Type::Vector,
        I::Bn254Fr,
        320,
    );
    check(
        Value::HaloG1(halo::G1::generator()),
        Type::Group,
        I::Bn254G1,
        512,
    );
    check(
        Value::HaloG1Vector(Arc::new(
            halo::G1Vector::filled(2, halo::G1::generator()).unwrap(),
        )),
        Type::Groups,
        I::Bn254G1,
        256 + 2 * std::mem::size_of::<halo::G1Element>(),
    );
    check(
        Value::HaloG2(Arc::new(halo::G2::generator())),
        Type::Group,
        I::Bn254G2,
        512,
    );
    check(
        Value::HaloG2Vector(Arc::new(
            halo::G2Vector::filled(2, halo::G2::generator()).unwrap(),
        )),
        Type::Groups,
        I::Bn254G2,
        256 + 2 * std::mem::size_of::<halo::G2Element>(),
    );
    check(
        Value::Shake128State(Arc::new(crate::hash::Shake128State::default())),
        Type::Shake128State,
        I::None,
        crate::hash::Shake128State::RETAINED_BYTES,
    );
    let prepared = crate::operations::quotient::apply(
        "quotient.prepare_matrix",
        &[
            Value::Indices(vec![1, 2, 3, 4].into()),
            Value::Index(17),
            Value::Index(2),
            Value::Index(1),
            Value::Index(2),
            Value::Index(1),
        ],
        &Policy::default(),
        usize::MAX,
    )
    .unwrap()
    .remove(0);
    check(
        prepared,
        Type::QuotientMatrix,
        I::None,
        256 + 4 * 8
            + std::mem::size_of::<zkc_kernels::polynomial::quotient::rns::PreparedMatrix>()
            + std::mem::size_of::<Value>(),
    );
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
    scalar_family!(
        KoalaBearExt4::from(KoalaBear::new(1)),
        KoalaBearExt4,
        KoalaBearExt4Field,
        KoalaBearExt4Vector,
        KoalaBearExt4Polynomial,
        KoalaBearExt4Round,
        KoalaBearExt4Matrix,
        16
    );
    scalar_family!(
        BabyBear::new(1),
        BabyBear,
        BabyBearField,
        BabyBearVector,
        BabyBearPolynomial,
        BabyBearRound,
        BabyBearMatrix,
        4
    );
    scalar_family!(
        BabyBearExt4::from(BabyBear::new(1)),
        BabyBearExt4,
        BabyBearExt4Field,
        BabyBearExt4Vector,
        BabyBearExt4Polynomial,
        BabyBearExt4Round,
        BabyBearExt4Matrix,
        16
    );
    scalar_family!(
        Goldilocks::new(1),
        Goldilocks,
        GoldilocksField,
        GoldilocksVector,
        GoldilocksPolynomial,
        GoldilocksRound,
        GoldilocksMatrix,
        8
    );
    scalar_family!(
        GoldilocksExt2::from(Goldilocks::new(1)),
        GoldilocksExt2,
        GoldilocksExt2Field,
        GoldilocksExt2Vector,
        GoldilocksExt2Polynomial,
        GoldilocksExt2Round,
        GoldilocksExt2Matrix,
        16
    );
    scalar_family!(
        zkc_kernels::plonky3::binary::from_bits(3),
        Binary64,
        Binary64Field,
        Binary64Vector,
        Binary64Polynomial,
        Binary64Round,
        Binary64Matrix,
        8
    );
    scalar_family!(
        zkc_kernels::plonky3::binary::ext3_from_bits([3, 1, 2]),
        Binary64Ext3,
        Binary64Ext3Field,
        Binary64Ext3Vector,
        Binary64Ext3Polynomial,
        Binary64Ext3Round,
        Binary64Ext3Matrix,
        24
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
    group_family!(crate::G1::generator(), Bls12381G1, Curve, Groups, 128);
    group_family!(
        crate::EdwardsPrime::generator(),
        Edwards25519Prime,
        EdwardsGroup,
        EdwardsGroups,
        std::mem::size_of::<crate::EdwardsPrime>()
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
        crate::Bls12381G2::generator(),
        Bls12381G2,
        Bls12381G2,
        Bls12381G2Vector,
        std::mem::size_of::<crate::Bls12381G2>()
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
    check(
        Value::Bls12381Gt(std::sync::Arc::new(crate::Bls12381Gt::generator())),
        Type::Group,
        I::Bls12381Gt,
        1024,
    );
    check(Value::Bool(true), Type::Bool, I::None, 512);
    check(Value::Index(3), Type::Index, I::None, 512);
    check(Value::Indices([1, 2].into()), Type::Indices, I::None, 272);
    check(Value::Bytes([0, 255].into()), Type::Bytes, I::None, 258);
    check(
        Value::Point([Scalar::from(1); 2].into()),
        Type::Point,
        I::Bls12381Fr,
        320,
    );
    let table = zkc_kernels::arkworks::bls12_381::Table::from_logical(
        &[Scalar::from(1); 2],
        &policy.ark_bounds(),
    )
    .unwrap();
    check(
        Value::Table(Arc::new(table.clone())),
        Type::Table,
        I::Bls12381Fr,
        320,
    );
    check(
        Value::TableMsb(Arc::new(
            zkc_kernels::arkworks::bls12_381::MsbTable::from_lsb(&table, &policy.ark_bounds())
                .unwrap(),
        )),
        Type::Table,
        I::Bls12381Fr,
        320,
    );
    let keys = zkc_kernels::arkworks::bls12_381::Keys::setup_with_rng(
        1,
        &mut ark_std::rand::thread_rng(),
        &policy.ark_bounds(),
    )
    .unwrap();
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
    let shape = zkc_kernels::plonky3::oracle::Shape::new(1, 2, 2).unwrap();
    let (root, state) =
        zkc_kernels::plonky3::oracle::commit(vec![KoalaBear::new(1); 2], shape, 4096).unwrap();
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
    // Digest-generic carriers share one byte allocation per digest list.
    let (root, tree) = zkc_kernels::plonky3::merkle::commit::<
        zkc_kernels::plonky3::merkle::poseidon2::Base,
    >(vec![KoalaBear::new(1); 2], shape, 4096)
    .unwrap();
    let proof = zkc_kernels::plonky3::merkle::open(&tree, &[0]).unwrap().1;
    let tree = crate::merkle::State::Poseidon2KoalaBear(Arc::new(tree));
    let scheme = crate::merkle::Scheme::Poseidon2KoalaBear;
    check(
        Value::MerkleDigest(scheme, root.clone().into()),
        Type::Commitment,
        I::MerklePoseidon2KoalaBear,
        288,
    );
    check(
        Value::MerkleProof(scheme, proof.into()),
        Type::Proof,
        I::MerklePoseidon2KoalaBear,
        288,
    );
    check(
        Value::MerkleTree(tree.clone()),
        Type::OpeningState,
        I::MerklePoseidon2KoalaBear,
        360,
    );
    check(
        Value::MerkleDigests(scheme, [root.clone(), root].concat().into()),
        Type::Commitments,
        I::MerklePoseidon2KoalaBear,
        320,
    );
    check(
        Value::MerkleTrees(scheme, [tree].into()),
        Type::OpeningStates,
        I::MerklePoseidon2KoalaBear,
        616 + std::mem::size_of::<crate::merkle::State>(),
    );
    let logical = LogicalType::parse("fixed_vector<field:koala-bear,2>").unwrap();
    let fixed = Value::FixedVector(
        crate::FixedVector::new(
            zkc_runtime::vm::PhysicalType::default_for(logical).unwrap(),
            [KoalaBear::new(1); 2].into(),
        )
        .unwrap(),
    );
    let fixed_bytes = 1288 + fixed.physical_type().descriptor_bytes();
    check(fixed.clone(), Type::FixedVector, I::None, fixed_bytes);
    let array_type = zkc_runtime::vm::PhysicalType::default_for(
        LogicalType::field_array(I::Bls12381Fr, 2).unwrap(),
    )
    .unwrap();
    let array_bytes = 1344 + array_type.descriptor_bytes();
    check(
        Value::FieldArray(crate::FieldArray::new(array_type, [Scalar::from(1); 2].into()).unwrap()),
        Type::FieldArray,
        I::None,
        array_bytes,
    );
    let descriptor = LogicalType::parse(&zkc_test_support::variants::logical(
        "Bulk",
        json!([["some", ["fixed_vector<field:koala-bear,2>"]]]),
    ))
    .unwrap()
    .variant_descriptor()
    .unwrap()
    .clone();
    let variant_type =
        zkc_runtime::vm::PhysicalType::default_for(LogicalType::variant(descriptor)).unwrap();
    let variant_bytes = variant_type.descriptor_bytes() + 256 + 512 + fixed_bytes;
    let sequence_type = zkc_runtime::vm::PhysicalType::default_for(
        LogicalType::sequence(LogicalType::parse("index").unwrap()).unwrap(),
    )
    .unwrap();
    check(
        Value::Sequence(
            crate::Sequence::new(
                sequence_type.clone(),
                vec![Value::Index(7)],
                &Policy::default(),
            )
            .unwrap(),
        ),
        Type::Sequence,
        I::None,
        256 + sequence_type.descriptor_bytes() + 256 + 512 + 512,
    );
    check(
        Value::pack_variant(variant_type, 0, vec![fixed]).unwrap(),
        Type::Variant,
        I::None,
        variant_bytes,
    );
    let mut native = backend();
    let domain = Domain::new("P", "session", "main", None);
    check(
        native
            .issue_rng_for(Identity::Bls12381Fr, domain.clone(), 1)
            .unwrap(),
        Type::Rng,
        I::Bls12381Fr,
        512,
    );
    check(
        native
            .issue_nonce_for(Identity::Bls12381Fr, domain.clone(), 1)
            .unwrap(),
        Type::Nonce,
        I::Bls12381Fr,
        512,
    );
    check(
        native
            .issue_transcript_for(
                Identity::Merlin3Fr64Be,
                domain,
                1,
                &[1, 0, 0, 0, 0, 0, 0, 0, 0],
            )
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
    drop(check);
    assert_eq!(seen, Value::PAYLOAD_NAMES.iter().copied().collect());
    for (value, actual) in &classified {
        if let zkc_runtime::vm::Representation::Extension(representation) = actual.representation()
        {
            // Equal names and mathematical types in another catalog do not
            // authorize that catalog to classify an installed resident payload.
            let mut foreign = zkc_runtime::vm::ContractsBuilder::standard();
            let other = foreign
                .add_representation(representation.name(), actual.logical().clone())
                .unwrap();
            assert_eq!(actual.spelling(), other.spelling());
            assert_ne!(*actual, other);
            assert!(!value.has_type(&other));
            assert!(value.has_type(&actual.clone()));
        }
        for (_, expected) in &classified {
            assert_eq!(value.has_type(expected), actual == expected);
        }
        for spelling in [
            "sequence<field:bls12-381.fr>",
            "fixed_vector<field:koala-bear,3>",
        ] {
            let expected =
                PhysicalType::default_for(LogicalType::parse(spelling).unwrap()).unwrap();
            assert_eq!(value.has_type(&expected), *actual == expected);
        }
    }
}

#[test]
fn wrong_kind_capability_wrappers_refuse_without_panicking() {
    use zkc_runtime::vm::Identity as I;
    use zkc_runtime::vm::{Backend, Value as RuntimeValue};
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
        I::Spongefish080KeccakFr64Be,
        I::HashChainKeccak256Fr64Be,
        I::HashChainKeccak256KoalaBearExt8,
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
                    "zkc.program/0",
                    [],
                    [],
                    [[
                        "participant",
                        "actor",
                        "instance",
                        "P",
                        [["arg", ty]],
                        [ty],
                        [["return", ["arg"]]],
                        []
                    ]],
                    [["entry", "main", [["P", "actor"]]]]
                ]))
                .unwrap();
                let admitted = zkc_runtime::vm::Program::decode(&carrier, crate::cpu_contracts())
                    .and_then(|program| {
                        program.check_installation(&native)?;
                        Ok(program)
                    })
                    .unwrap();
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
        domains: &[zkc_runtime::vm::Identity::Bls12381Fr],
        ports: crate::bindings::PortTransform::Default,
        handler: Some(arithmetic),
        deterministic: true,
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
        "arkworks/pairing.apply",
        "plonky3/field.embed",
        "plonky3/vector.embed",
        "arkworks/bool.and",
        "arkworks/random.draw",
        "arkworks/transcript.native.indexed.challenge",
    ] {
        let mut registry = installed().unwrap().clone();
        assert_eq!(
            registry
                .alternative(&Alternative {
                    identity: "independent/fixed",
                    original,
                    domains: &[Identity::Bls12381Fr],
                    ports: crate::bindings::PortTransform::Default,
                    handler: None,
                    deterministic: true,
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
            original: "arkworks/transcript.native.indexed.observe.data",
            domains: &[Identity::Merlin3Fr64Be],
            ports: crate::bindings::PortTransform::Default,
            handler: None,
            deterministic: true,
        })
        .unwrap();
    let entry = registry.get("independent/observation").unwrap();
    for (suite, payload, accepted) in [
        ("merlin3.bls12-381.fr64be/0", "field:bls12-381.fr", true),
        ("merlin3.bls12-381.fr64be/0", "field:bn254.fr", true),
        ("merlin3.bls12-381.fr64be/0", "wrong-type", false),
        (
            "merlin3.ristretto255.scalar64le/0",
            "field:ristretto255.scalar",
            false,
        ),
        (
            "spongefish0.8.0.keccak.bls12-381.fr64be/0",
            "field:bls12-381.fr",
            false,
        ),
    ] {
        assert_eq!(
            entry
                .signature(&binding(
                    "transcript.native.indexed.observe.data",
                    &[suite, payload],
                    "independent/observation"
                ))
                .is_some(),
            accepted
        );
    }
    assert_eq!(
        registry
            .alternative(&Alternative {
                identity: "independent/second",
                original: "independent/observation",
                domains: &[Identity::Merlin3Fr64Be],
                ports: crate::bindings::PortTransform::Default,
                handler: None,
                deterministic: false,
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
            domains: &[Identity::Bn254G1],
            ports: crate::bindings::PortTransform::Default,
            handler: None,
            deterministic: true,
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
fn transcript_alternative_refuses_unsupported_table_payload() {
    let mut registry = installed().unwrap().clone();
    registry
        .alternative(&Alternative {
            identity: "independent/msb-observation",
            original: "arkworks/transcript.native.indexed.observe.data",
            domains: &[Identity::Merlin3Fr64Be],
            ports: crate::bindings::PortTransform::Msb,
            handler: None,
            deterministic: true,
        })
        .unwrap();
    assert!(
        registry
            .get("independent/msb-observation")
            .unwrap()
            .signature(&binding(
                "transcript.native.indexed.observe.data",
                &["merlin3.bls12-381.fr64be/0", "table:bls12-381.fr"],
                "independent/msb-observation"
            ))
            .is_none()
    );
}

#[test]
fn family_rows_retain_field_literal_rules() {
    use zkc_runtime::vm::AttributeRule as A;
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
        "curve.identity",
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
        "matrix.column_dot",
        "matrix.dimension",
        "matrix.get",
        "matrix.identity_check",
        "pairing.check",
        "matrix.mul_vector",
        "matrix.row_dot",
        "matrix.shape_check",
        "matrix.transpose_mul_vector",
        "multilinear.restrict_prefix",
        "pcs.check",
        "pcs.commit",
        "pcs.equal",
        "pcs.open",
        "poly.append_point",
        "poly.boundary",
        "poly.coefficient_count",
        "poly.coefficients",
        "poly.coset_evaluate",
        "poly.coset_evaluate_batch",
        "poly.coset_extend",
        "poly.coset_evaluate_at",
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
        "poly.opening_quotient_sum",
        "poly.product_round",
        "poly.product_sum",
        "poly.table_arity",
        "poly.round_evaluate",
        "poly.univariate_boundary",
        "poly.univariate_evaluate",
        "ring.point",
        "ring.rows",
        "ring.coefficients",
        "ring.affine_sum",
        "transcript.native.indexed.observe.data",
        "vector.add",
        "vector.append",
        "vector.at",
        "vector.concat",
        "vector.constant",
        "vector.dot",
        "vector.empty",
        "vector.equal",
        "vector.find_last",
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
        "vector.bit_reverse",
        "vector.bit_reverse_rows",
        "vector.scale",
        "vector.scatter_sum",
        "vector.slice",
        "vector.splat",
        "vector.split",
        "vector.sub",
        "vector.sum",
        "vector.product",
        "vector.to_point",
        "vector.to_table",
        "vector.transpose",
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
                    zkc_kernels::arkworks::bls12_381::MsbTable::from_lsb(t, &policy.ark_bounds())
                        .unwrap(),
                ));
            }
        }
        let native = || backend();
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
            Value::Point(v) | Value::Polynomial(v) => Value::Vector(v),
            Value::Round(v) => Value::Vector(v.into()),
            other => other,
        };
        let encode = |v: Value| native().encode_native_value(&normalize(v)).unwrap();
        assert_eq!(
            actual.into_iter().map(encode).collect::<Vec<_>>(),
            expected.into_iter().map(encode).collect::<Vec<_>>(),
            "{}",
            row.identity
        );
    }
}

#[test]
fn collection_limits_follow_payload_storage() {
    use zkc_runtime::vm::{Backend, Identity, LogicalType, Type, Value as _};
    let mut native = backend();
    native.core.policy.max_table_elements = 2;
    let roots = Value::OracleRoots(crate::oracle::Domain::Base, [[0u8; 32]; 3].into());
    assert_eq!(
        native.validate_value(&roots).unwrap_err().code,
        "exhausted:element-limit"
    );
    native.core.policy.max_table_elements = 64;
    let path = Value::OraclePath(crate::oracle::Domain::Base, [[0u8; 32]; 25].into());
    assert_eq!(
        native.validate_value(&path).unwrap_err().code,
        "refused:oracle-path-length"
    );
    let logical = LogicalType::fixed_vector(
        LogicalType::new(Type::Field, Identity::KoalaBear).unwrap(),
        64,
    )
    .unwrap();
    let fixed = Value::FixedVector(
        crate::FixedVector::new(
            zkc_runtime::vm::PhysicalType::default_for(logical).unwrap(),
            vec![crate::KoalaBear::new(1); 64].into(),
        )
        .unwrap(),
    );
    native.core.policy.max_value_bytes = fixed.retained_bytes();
    native.validate_value(&fixed).unwrap();
    native.core.policy.max_value_bytes -= 1;
    assert_eq!(
        native.validate_value(&fixed).unwrap_err().code,
        "exhausted:output-bytes"
    );
}

#[test]
fn every_exact_installation_has_a_supported_binding_and_impossible_owners_are_absent() {
    use zkc_runtime::vm::Backend;
    let native = backend();
    let runtime_rows = OperationBinding::installed_implementations().unwrap();
    let backend_rows = native.installed_implementations();
    let mut standard_rows = runtime_rows
        .into_iter()
        .filter(|(name, _)| !name.starts_with("blst/"))
        .collect::<Vec<_>>();
    let mut actual_standard = backend_rows
        .iter()
        .filter(|(name, _)| {
            !name.starts_with("blst/resident/")
                && !name.starts_with("halo2curves-axiom/resident/")
                && name != "native/representation.convert"
        })
        .cloned()
        .collect::<Vec<_>>();
    standard_rows.sort();
    actual_standard.sort();
    assert_eq!(standard_rows, actual_standard);
    let arguments: &[&[&str]] = &[
        &[],
        &["bls12-381.fr"],
        &["bn254.fr"],
        &["ristretto255.scalar"],
        &["koala-bear"],
        &["koala-bear.ext8-binomial3"],
        &["bls12-381.g1"],
        &["bn254.g1"],
        &["bn254.g2"],
        &["bn254.gt"],
        &["ristretto255.group"],
        &["edwards25519.prime"],
        &["multilinear.kzg.bls12-381/0"],
        &["rows.merkle-keccak256.koala-bear/0"],
        &["rows.merkle-keccak256.koala-bear.ext8-binomial3/0"],
        &["rows.merkle-poseidon2-16.koala-bear/0"],
        &["merlin3.bls12-381.fr64be/0"],
        &["merlin3.ristretto255.scalar64le/0"],
        &["merlin3.koala-bear.ext8-binomial3.rejection31le/0"],
        &["spongefish0.8.0.keccak.bls12-381.fr64be/0"],
        &["merlin3.bls12-381.fr64be/0", "field:bls12-381.fr"],
        &[
            "merlin3.ristretto255.scalar64le/0",
            "field:ristretto255.scalar",
        ],
        &[
            "merlin3.koala-bear.ext8-binomial3.rejection31le/0",
            "field:koala-bear",
        ],
        &[
            "spongefish0.8.0.keccak.bls12-381.fr64be/0",
            "field:bls12-381.fr",
        ],
        &["bls12-381.fr", "2"],
        &["koala-bear", "2"],
        &["bls12-381.fr", "1"],
        &["ristretto255.scalar", "1"],
        &["koala-bear", "1"],
        &["field:bls12-381.fr"],
        &["Slot.A"],
        &["bls12-381.fr", "arkworks.mle-lsb/0", "arkworks.mle-msb/0"],
    ];
    for (implementation, contract) in &backend_rows {
        if implementation.starts_with("blst/resident/")
            || implementation.starts_with("halo2curves-axiom/resident/")
            || implementation == "native/representation.convert"
        {
            continue;
        }
        assert!(
            arguments.iter().any(|args| {
                let binding = binding(contract, args, implementation);
                native
                    .binding_signature(&binding)
                    .is_some_and(|s| binding.signature().ok() == Some(s))
            }),
            "no independently admitted witness: {implementation}"
        );
    }
    for (implementation, contract, args) in [
        (
            "spongefish/random.draw",
            "random.draw",
            vec!["bls12-381.fr"],
        ),
        (
            "arkworks/random.index",
            "random.index",
            vec!["koala-bear.ext8-binomial3"],
        ),
        ("dalek/pairing.apply", "pairing.apply", vec!["bn254.fr"]),
        (
            "arkworks/field.embed",
            "field.embed",
            vec!["koala-bear.ext8-binomial3"],
        ),
        (
            "dalek/vector.to_table",
            "vector.to_table",
            vec!["bls12-381.fr"],
        ),
        (
            "dalek/poly.coset_evaluate",
            "poly.coset_evaluate",
            vec!["koala-bear"],
        ),
    ] {
        assert!(!backend_rows.iter().any(|(name, _)| name == implementation));
        let b = binding(contract, &args, implementation);
        assert!(native.binding_signature(&b).is_none());
        assert!(b.signature().is_err());
    }
}

#[test]
fn nested_transcript_observation_keeps_its_own_work_contract() {
    use zkc_runtime::vm::Backend;
    let native = backend();
    let observe = binding(
        "transcript.native.indexed.observe.data",
        &["merlin3.bls12-381.fr64be/0", "sequence<index>"],
        "arkworks/transcript.native.indexed.observe.data",
    );
    assert!(!native.prepare_binding(&observe).unwrap().sequence);
    let join = binding("bytes.join", &[], "native/bytes.join");
    assert!(native.prepare_binding(&join).unwrap().sequence);
}

#[test]
fn residue_field_and_profile_instances_have_independently_expected_ports() {
    use std::collections::BTreeMap;
    use zkc_runtime::vm::{
        AttributeRule as A, Backend, BoundSignature, LogicalType, OperationSignature, PhysicalType,
        Representation as R, Type, Type::*,
    };

    // These acceptance facts are authored here, independently of owner rows,
    // implementation-name inventories and either signature resolver.
    let carriers = [
        (
            Identity::BabyBear,
            [
                R::BabyBear,
                R::BabyBearVector,
                R::BabyBearSparseCoo,
                R::BabyBearPolynomial,
                R::BabyBearRound,
            ],
            Identity::MerklePoseidon2BabyBear,
        ),
        (
            Identity::BabyBearExt4,
            [
                R::BabyBearExt4,
                R::BabyBearExt4Vector,
                R::BabyBearExt4SparseCoo,
                R::BabyBearExt4Polynomial,
                R::BabyBearExt4Round,
            ],
            Identity::MerklePoseidon2BabyBearExt4,
        ),
        (
            Identity::Goldilocks,
            [
                R::Goldilocks,
                R::GoldilocksVector,
                R::GoldilocksSparseCoo,
                R::GoldilocksPolynomial,
                R::GoldilocksRound,
            ],
            Identity::MerklePoseidon2Goldilocks,
        ),
        (
            Identity::GoldilocksExt2,
            [
                R::GoldilocksExt2,
                R::GoldilocksExt2Vector,
                R::GoldilocksExt2SparseCoo,
                R::GoldilocksExt2Polynomial,
                R::GoldilocksExt2Round,
            ],
            Identity::MerklePoseidon2GoldilocksExt2,
        ),
    ];
    let neutral = |kind| {
        let representation = match kind {
            Bool => R::Bool,
            Index => R::Index,
            Indices => R::Indices,
            Bytes => R::Bytes,
            _ => panic!("missing independent neutral port: {kind:?}"),
        };
        PhysicalType::new(
            LogicalType::new(kind, Identity::None).unwrap(),
            representation,
        )
        .unwrap()
    };
    let mut expected = BTreeMap::new();
    let mut arguments = Vec::new();
    for (field, representations, scheme) in carriers {
        let port = |kind| {
            let representation = match kind {
                Field => representations[0],
                Vector => representations[1],
                Matrix => representations[2],
                Polynomial => representations[3],
                Round => representations[4],
                Rng => R::Resource,
                _ => return neutral(kind),
            };
            PhysicalType::new(LogicalType::new(kind, field).unwrap(), representation).unwrap()
        };
        let mut record = |names: &[&str], inputs: &[Type], outputs: &[Type], attributes| {
            for name in names {
                let declaration = binding(name, &[field.name()], &format!("plonky3/{name}"));
                let key = (
                    declaration.implementation,
                    declaration.contract,
                    declaration.arguments,
                );
                assert!(
                    expected
                        .insert(
                            key,
                            OperationSignature {
                                inputs: inputs.iter().copied().map(port).collect(),
                                outputs: outputs.iter().copied().map(port).collect(),
                                attributes,
                            }
                        )
                        .is_none(),
                    "duplicate acceptance instance: {name}"
                );
            }
        };
        record(&["field.constant"], &[], &[Field], A::ResidueLiteral(field));
        record(
            &["field.add", "field.sub", "field.mul"],
            &[Field, Field],
            &[Field],
            A::None,
        );
        record(&["field.neg", "field.inverse"], &[Field], &[Field], A::None);
        record(&["field.equal"], &[Field, Field], &[Bool], A::None);
        record(&["field.from_index"], &[Index], &[Field], A::None);
        record(
            &["vector.constant"],
            &[],
            &[Vector],
            A::ResidueLiterals(field),
        );
        record(&["vector.empty"], &[], &[Vector], A::None);
        record(
            &["vector.splat", "vector.powers"],
            &[Field],
            &[Vector],
            A::NaturalIndex,
        );
        record(
            &["vector.fill", "vector.geometric"],
            &[Field, Index],
            &[Vector],
            A::None,
        );
        record(
            &["vector.append", "vector.scale"],
            &[Vector, Field],
            &[Vector],
            A::None,
        );
        record(&["vector.find_last"], &[Vector, Field], &[Index], A::None);
        record(
            &[
                "vector.add",
                "vector.sub",
                "vector.mul",
                "vector.concat",
                "vector.interleave",
                "vector.kronecker",
                "multilinear.restrict_prefix",
            ],
            &[Vector, Vector],
            &[Vector],
            A::None,
        );
        record(
            &["vector.matvec"],
            &[Vector, Vector],
            &[Vector],
            A::MatrixShape,
        );
        record(&["vector.equal"], &[Vector, Vector], &[Bool], A::None);
        record(&["vector.dot"], &[Vector, Vector], &[Field], A::None);
        record(
            &["vector.sum", "vector.product"],
            &[Vector],
            &[Field],
            A::None,
        );
        record(
            &[
                "vector.inverse",
                "vector.prefix_sum",
                "vector.prefix_product",
                "vector.bit_reverse",
            ],
            &[Vector],
            &[Vector],
            A::None,
        );
        record(&["vector.split"], &[Vector], &[Vector, Vector], A::None);
        record(
            &["vector.rotate", "vector.bit_reverse_rows"],
            &[Vector, Index],
            &[Vector],
            A::None,
        );
        record(
            &["vector.slice", "vector.transpose"],
            &[Vector, Index, Index],
            &[Vector],
            A::None,
        );
        record(&["vector.get"], &[Vector, Index], &[Field], A::None);
        record(&["vector.at"], &[Vector], &[Field], A::NaturalIndex);
        record(&["vector.length"], &[Vector], &[Index], A::None);
        record(
            &["vector.length_check"],
            &[Vector],
            &[Bool],
            A::NaturalIndex,
        );
        record(&["vector.gather"], &[Vector], &[Vector], A::NaturalIndices);
        record(
            &["vector.scatter_sum"],
            &[Vector],
            &[Vector],
            A::ScatterShape,
        );
        record(
            &["matrix.mul_vector", "matrix.transpose_mul_vector"],
            &[Matrix, Vector],
            &[Vector],
            A::None,
        );
        record(
            &["matrix.bilinear"],
            &[Matrix, Vector, Vector],
            &[Field],
            A::None,
        );
        record(
            &["matrix.row_dot", "matrix.column_dot"],
            &[Matrix, Vector, Index],
            &[Field],
            A::None,
        );
        record(&["matrix.get"], &[Matrix, Index, Index], &[Field], A::None);
        record(&["matrix.dimension"], &[Matrix], &[Index], A::Unsigned64);
        record(
            &["matrix.shape_check"],
            &[Matrix],
            &[Bool],
            A::MatrixDimensions,
        );
        record(
            &["matrix.identity_check"],
            &[Matrix],
            &[Bool],
            A::MatrixIdentity,
        );
        record(
            &["poly.from_coefficients"],
            &[Vector],
            &[Polynomial],
            A::None,
        );
        record(&["poly.coefficients"], &[Polynomial], &[Vector], A::None);
        record(
            &["poly.coefficient_count"],
            &[Polynomial],
            &[Index],
            A::None,
        );
        record(
            &["poly.degree_check"],
            &[Polynomial],
            &[Bool],
            A::NaturalIndex,
        );
        record(
            &["poly.divide_opening"],
            &[Polynomial, Field, Field],
            &[Polynomial],
            A::None,
        );
        record(
            &["poly.univariate_evaluate"],
            &[Polynomial, Field],
            &[Field],
            A::None,
        );
        record(
            &["poly.univariate_boundary"],
            &[Polynomial],
            &[Field],
            A::None,
        );
        record(&["poly.boundary"], &[Round], &[Field], A::None);
        record(&["poly.round_evaluate"], &[Round, Field], &[Field], A::None);
        record(
            &["poly.coset_evaluate"],
            &[Polynomial, Field, Index],
            &[Vector],
            A::None,
        );
        record(
            &["poly.coset_interpolate"],
            &[Vector, Field],
            &[Polynomial],
            A::None,
        );
        record(
            &["poly.coset_evaluate_batch"],
            &[Vector, Index, Index, Field, Index],
            &[Vector],
            A::None,
        );
        record(
            &["poly.coset_evaluate_at"],
            &[Vector, Index, Index, Field, Field],
            &[Vector],
            A::None,
        );
        record(
            &["poly.coset_extend"],
            &[Vector, Index, Index, Field, Field, Index],
            &[Vector],
            A::None,
        );
        record(&["poly.domain_root"], &[Index], &[Field], A::None);
        record(
            &["poly.domain_point"],
            &[Field, Index, Index],
            &[Field],
            A::None,
        );
        record(&["poly.domain_points"], &[Field, Index], &[Vector], A::None);
        record(
            &["poly.even_odd_fold"],
            &[Vector, Field, Field],
            &[Vector],
            A::None,
        );
        record(
            &["poly.opening_quotient"],
            &[Vector, Field, Field, Field],
            &[Vector],
            A::None,
        );
        record(
            &["poly.opening_quotient_sum"],
            &[
                Vector, Index, Index, Field, Indices, Vector, Vector, Vector, Vector,
            ],
            &[Vector],
            A::None,
        );
        record(&["ring.point"], &[Vector], &[Vector], A::AssetIdentity);
        record(
            &["ring.rows", "ring.coefficients"],
            &[Vector, Index],
            &[Vector],
            A::AssetIdentity,
        );
        record(
            &["ring.affine_sum"],
            &[Vector, Vector, Index],
            &[Vector],
            A::AssetIdentity,
        );
        record(&["encoding.field_le"], &[Field], &[Bytes], A::None);
        record(&["encoding.fields_le"], &[Vector], &[Bytes], A::None);
        record(
            &["encoding.field_from_le"],
            &[Bytes],
            &[Bool, Field],
            A::None,
        );
        record(
            &["encoding.fields_from_le"],
            &[Bytes],
            &[Bool, Vector],
            A::None,
        );
        if matches!(field, Identity::BabyBear | Identity::BabyBearExt4) {
            record(
                &["encoding.field_montgomery_le"],
                &[Field],
                &[Bytes],
                A::None,
            );
            record(
                &["encoding.fields_montgomery_le"],
                &[Vector],
                &[Bytes],
                A::None,
            );
            record(
                &["encoding.field_from_montgomery_le"],
                &[Bytes],
                &[Bool, Field],
                A::None,
            );
            record(
                &["encoding.fields_from_montgomery_le"],
                &[Bytes],
                &[Bool, Vector],
                A::None,
            );
        }
        if matches!(field, Identity::BabyBearExt4 | Identity::GoldilocksExt2) {
            record(&["random.draw"], &[Rng], &[Field, Rng], A::None);
            record(&["random.vector"], &[Rng], &[Vector, Rng], A::NaturalIndex);
            record(&["random.index"], &[Rng, Index], &[Index, Rng], A::None);
        }
        arguments.push(vec![field.name().to_owned()]);

        if matches!(field, Identity::BabyBearExt4 | Identity::GoldilocksExt2) {
            let base = if field == Identity::BabyBearExt4 {
                carriers[0]
            } else {
                carriers[2]
            };
            for (contract, kind, representation) in [
                ("field.embed", Field, base.1[0]),
                ("vector.embed", Vector, base.1[1]),
            ] {
                expected.insert(
                    (
                        format!("plonky3/{contract}"),
                        contract.to_owned(),
                        vec![field.name().to_owned()],
                    ),
                    OperationSignature {
                        inputs: vec![
                            PhysicalType::new(
                                LogicalType::new(kind, base.0).unwrap(),
                                representation,
                            )
                            .unwrap(),
                        ],
                        outputs: vec![port(kind)],
                        attributes: A::None,
                    },
                );
            }
        }
        // Numeric parameters are families. Exercise empty, scalar, vector and
        // mixed masks, and both endpoints of the relation-table index range.
        for mask in ["", "0", "1", "01", "10"] {
            let args = vec![field.name().to_owned(), mask.to_owned()];
            arguments.push(args.clone());
            let inputs = std::iter::once(neutral(Index))
                .chain(
                    mask.bytes()
                        .map(|bit| port(if bit == b'0' { Field } else { Vector })),
                )
                .collect::<Vec<_>>();
            for (contract, output) in [
                ("numerical.map", Vector),
                ("numerical.sum", Field),
                ("numerical.product", Field),
            ] {
                expected.insert(
                    (
                        format!("plonky3/{contract}"),
                        contract.to_owned(),
                        args.clone(),
                    ),
                    OperationSignature {
                        inputs: inputs.clone(),
                        outputs: vec![port(output)],
                        attributes: A::NumericalExpression,
                    },
                );
            }
        }
        for table in ["0", "1", "10", "1048576"] {
            let args = vec![field.name().to_owned(), table.to_owned()];
            arguments.push(args.clone());
            for (contract, inputs, outputs) in [
                (
                    "relation.table_rows",
                    vec![Vector, Vector, Vector, Index],
                    vec![Vector],
                ),
                ("relation.table_shape", vec![Index], vec![Index; 7]),
                ("relation.table_input", vec![Index; 2], vec![Index; 3]),
                ("relation.table_scope", vec![Index; 2], vec![Index; 2]),
                ("relation.table_point", vec![Vector], vec![Vector]),
                ("relation.table_points", vec![Vector, Index], vec![Vector]),
                (
                    "relation.table_record_points",
                    vec![Vector, Index],
                    vec![Vector],
                ),
                ("relation.table_widths", vec![], vec![Index; 3]),
                ("relation.table_policy", vec![], vec![Index; 5]),
                ("relation.table_interactions", vec![Index], vec![Index; 2]),
                (
                    "relation.table_interaction",
                    vec![Index; 2],
                    vec![Index; 12],
                ),
            ] {
                expected.insert(
                    (
                        format!("plonky3/{contract}"),
                        contract.to_owned(),
                        args.clone(),
                    ),
                    OperationSignature {
                        inputs: inputs.into_iter().map(port).collect(),
                        outputs: outputs.into_iter().map(port).collect(),
                        attributes: A::AssetIdentity,
                    },
                );
            }
        }

        let row_port = |kind| match kind {
            Vector => port(Vector),
            Index | Indices | Bool => neutral(kind),
            _ => PhysicalType::new(
                LogicalType::new(kind, scheme).unwrap(),
                match kind {
                    Commitment => R::MerkleDigest,
                    Proof => R::MerkleProof,
                    OpeningState => R::MerkleTree,
                    Commitments => R::MerkleDigests,
                    OpeningStates => R::MerkleTrees,
                    _ => panic!("missing independent row port: {kind:?}"),
                },
            )
            .unwrap(),
        };
        let args = vec![scheme.name().to_owned()];
        arguments.push(args.clone());
        for (contract, inputs, outputs) in [
            (
                "oracle.commit",
                vec![Vector, Index],
                vec![Commitment, OpeningState],
            ),
            (
                "oracle.open",
                vec![OpeningState, Index],
                vec![Vector, Proof],
            ),
            (
                "oracle.check",
                vec![Commitment, Index, Index, Index, Vector, Proof],
                vec![Bool],
            ),
            (
                "oracle.open_many",
                vec![OpeningState, Indices],
                vec![Vector, Proof],
            ),
            (
                "oracle.check_many",
                vec![Commitment, Index, Index, Indices, Vector, Proof],
                vec![Bool],
            ),
            ("commitments.empty", vec![], vec![Commitments]),
            (
                "commitments.append",
                vec![Commitments, Commitment],
                vec![Commitments],
            ),
            ("commitments.at", vec![Commitments, Index], vec![Commitment]),
            ("commitments.length", vec![Commitments], vec![Index]),
            ("opening_states.empty", vec![], vec![OpeningStates]),
            (
                "opening_states.append",
                vec![OpeningStates, OpeningState],
                vec![OpeningStates],
            ),
            (
                "opening_states.at",
                vec![OpeningStates, Index],
                vec![OpeningState],
            ),
            ("opening_states.length", vec![OpeningStates], vec![Index]),
        ] {
            expected.insert(
                (
                    format!("plonky3/{contract}"),
                    contract.to_owned(),
                    args.clone(),
                ),
                OperationSignature {
                    inputs: inputs.into_iter().map(row_port).collect(),
                    outputs: outputs.into_iter().map(row_port).collect(),
                    attributes: A::None,
                },
            );
        }
        let suite = match field {
            Identity::BabyBearExt4 => Identity::Merlin3BabyBearExt4,
            Identity::GoldilocksExt2 => Identity::Merlin3GoldilocksExt2,
            _ => continue,
        };
        let state =
            PhysicalType::new(LogicalType::new(Transcript, suite).unwrap(), R::Resource).unwrap();
        let transcript_port = |kind| {
            if kind == Transcript {
                state.clone()
            } else {
                port(kind)
            }
        };
        let args = vec![suite.name().to_owned()];
        arguments.push(args.clone());
        for (contract, inputs, outputs, attributes) in [
            (
                "transcript.observe",
                vec![Transcript, Bytes, Bytes],
                vec![Transcript],
                A::None,
            ),
            (
                "transcript.challenge",
                vec![Transcript, Bytes],
                vec![Transcript, Field],
                A::None,
            ),
            (
                "transcript.index",
                vec![Transcript, Bytes, Index],
                vec![Transcript, Index],
                A::None,
            ),
            (
                "transcript.native.indexed.challenge",
                vec![Transcript, Indices],
                vec![Field, Transcript],
                A::NativeChallengeTemplate,
            ),
            (
                "transcript.native.indexed.index",
                vec![Transcript, Index, Indices],
                vec![Index, Transcript],
                A::NativeIndexTemplate,
            ),
        ] {
            expected.insert(
                (
                    format!("plonky3/{contract}"),
                    contract.to_owned(),
                    args.clone(),
                ),
                OperationSignature {
                    inputs: inputs.into_iter().map(transcript_port).collect(),
                    outputs: outputs.into_iter().map(transcript_port).collect(),
                    attributes,
                },
            );
        }
        let mut payloads = vec![
            neutral(Bool),
            neutral(Index),
            neutral(Indices),
            neutral(Bytes),
        ];
        for (identity, representations, _) in carriers {
            for (kind, representation) in [
                (Field, representations[0]),
                (Vector, representations[1]),
                (Matrix, representations[2]),
            ] {
                payloads.push(
                    PhysicalType::new(LogicalType::new(kind, identity).unwrap(), representation)
                        .unwrap(),
                );
            }
        }
        for payload in payloads {
            let args = vec![suite.name().to_owned(), payload.logical().spelling()];
            arguments.push(args.clone());
            let contract = "transcript.native.indexed.observe.data";
            expected.insert(
                (format!("plonky3/{contract}"), contract.to_owned(), args),
                OperationSignature {
                    inputs: vec![state.clone(), payload, neutral(Indices)],
                    outputs: vec![state.clone()],
                    attributes: A::NativeMessageTemplate,
                },
            );
        }
    }
    arguments.sort();
    arguments.dedup();
    let native = backend();
    let mut native_instances = BTreeMap::new();
    let mut runtime_instances = BTreeMap::new();
    for actual_native in [false, true] {
        let (rows, instances) = if actual_native {
            (native.installed_implementations(), &mut native_instances)
        } else {
            (
                OperationBinding::installed_implementations().unwrap(),
                &mut runtime_instances,
            )
        };
        for (implementation, contract) in rows {
            // This inventory concerns Plonky3 field/profile installations.
            // Optional logical resources accept arbitrary nominal names;
            // a slot named "baby-bear" is not a field implementation.
            if !implementation.starts_with("plonky3/") {
                continue;
            }
            for args in &arguments {
                let declaration = OperationBinding {
                    contract: contract.into(),
                    arguments: args.clone(),
                    implementation: implementation.clone(),
                    physical_arguments: vec![],
                };
                let signature: Option<BoundSignature> = if actual_native {
                    native.binding_signature(&declaration)
                } else {
                    declaration.signature().ok()
                };
                if let Some(signature) = signature {
                    instances.insert(
                        (implementation.clone(), contract.to_owned(), args.clone()),
                        signature,
                    );
                }
            }
        }
    }
    for (owner, instances) in [
        ("runtime", &runtime_instances),
        ("native", &native_instances),
    ] {
        assert_eq!(
            instances.keys().collect::<Vec<_>>(),
            expected.keys().collect::<Vec<_>>(),
            "{owner} nominal installation inventory"
        );
        for (instance, signature) in &expected {
            assert_eq!(
                instances.get(instance),
                Some(signature),
                "{owner} ports for {instance:?}"
            );
        }
    }

    // Removing one field admission leaves the implementation-name witness and
    // KoalaBear admission intact, but loses an independently required instance.
    let mut missing = installed().unwrap().clone();
    missing
        .entries
        .get_mut("plonky3/field.mul")
        .unwrap()
        .signature = Signature::Custom(|b| {
        if b.arguments == ["goldilocks.ext2-binomial7"] {
            None
        } else {
            installed()
                .unwrap()
                .get("plonky3/field.mul")
                .unwrap()
                .signature(b)
        }
    });
    assert_eq!(
        missing.implementations(),
        installed().unwrap().implementations()
    );
    assert!(
        missing
            .get("plonky3/field.mul")
            .unwrap()
            .signature(&binding("field.mul", &["koala-bear"], "plonky3/field.mul"))
            .is_some()
    );
    let lost = expected
        .iter()
        .filter(|((implementation, contract, args), signature)| {
            let declaration = OperationBinding {
                contract: contract.clone(),
                arguments: args.clone(),
                implementation: implementation.clone(),
                physical_arguments: vec![],
            };
            missing
                .get(implementation)
                .and_then(|entry| entry.signature(&declaration))
                .as_ref()
                != Some(*signature)
        })
        .map(|(key, _)| key.clone())
        .collect::<Vec<_>>();
    assert_eq!(
        lost,
        vec![(
            "plonky3/field.mul".to_owned(),
            "field.mul".to_owned(),
            vec!["goldilocks.ext2-binomial7".to_owned()]
        )]
    );
}

#[test]
fn actual_handler_timing_metadata_refuses_a_weakened_expected_contract_before_frames() {
    use zkc_runtime::vm::{
        Backend, ExecutionPolicy, ImplementationRequirements, InstalledOperation, Program,
        TimingRequirement,
    };
    let known = ImplementationRequirements {
        timing: TimingRequirement::VariableTime,
        timing_operands: &[0, 1],
    };
    let installed = installed().unwrap();
    assert_eq!(
        installed
            .get("blst/resident/curve.msm")
            .unwrap()
            .requirements,
        known
    );
    // Model an expected inventory that incorrectly says Unspecified while the
    // installed handler explicitly retains the independently known MSM premise.
    // Keeping the fixed ports and identity unchanged isolates metadata checking.
    let b = binding("curve.msm", &["bls12-381.g1"], "arkworks/curve.msm");
    let contracts = crate::cpu_contracts_with_policy(ExecutionPolicy::general_purpose());
    let expected = Program::decode(&program(&b, &[]), &contracts).unwrap();
    assert_eq!(
        contracts.resolve(b.clone()).unwrap().requirements(),
        ImplementationRequirements::default()
    );
    let mut inventory = installed.clone();
    inventory
        .entries
        .get_mut(&b.implementation)
        .unwrap()
        .requirements = known;
    let mut actual = backend().with_contracts(contracts).unwrap();
    actual.implementations = Box::leak(Box::new(inventory));
    assert_eq!(actual.prepare_binding(&b).unwrap().requirements(), known);
    assert!(expected.check_installation(&actual).is_err());
    let error = match Runner::new(
        &expected,
        "main",
        "P",
        "session",
        actual,
        vec![Value::Vector(vec![].into()), Value::Groups(vec![].into())],
    ) {
        Ok(_) => panic!("weakened timing contract entered a frame"),
        Err(error) => error,
    };
    assert_eq!(error.backend.active_frames(), 0);
}
