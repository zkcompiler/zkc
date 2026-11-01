#[path = "domains/support.rs"]
mod support;
use p3_field::PrimeCharacteristicRing;
use serde_json::json;
use support::{backend, one};
fn assert_value(a: &Value, b: &Value) {
    match (a, b) {
        (Value::GoldilocksExt2Polynomial(a), Value::GoldilocksExt2Polynomial(b)) => {
            assert_eq!(a, b)
        }
        _ => support::assert_value(a, b),
    }
}
use zkc_cpu::{BabyBear, BabyBearExt4, Goldilocks, GoldilocksExt2, Policy, Value};
use zkc_runtime::vm::{
    Backend, Identity, LogicalType, OperationBinding, PhysicalType, Type, Value as _,
};

fn binding(field: Identity, name: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![field.name().into()],
        implementation: format!("plonky3/{name}"),
        physical_arguments: vec![],
    }
}
fn call(field: Identity, name: &str, attrs: &[&str], args: Vec<Value>) -> Vec<Value> {
    one(
        backend(Policy::default()),
        binding(field, name),
        attrs,
        args,
    )
    .0
    .unwrap()
}
#[test]
fn all_installations_agree_on_bindings_and_execute_wide_literals() {
    let b = backend(Policy::default());
    for field in [
        Identity::BabyBear,
        Identity::BabyBearExt4,
        Identity::Goldilocks,
        Identity::GoldilocksExt2,
    ] {
        for name in [
            "field.constant",
            "field.add",
            "field.mul",
            "field.inverse",
            "vector.dot",
            "matrix.mul_vector",
            "poly.from_coefficients",
            "poly.coset_evaluate",
            "poly.coset_interpolate",
            "poly.domain_root",
            "poly.boundary",
            "poly.round_evaluate",
            "encoding.field_le",
            "encoding.fields_from_le",
        ] {
            let bind = binding(field, name);
            assert_eq!(
                Some(bind.signature().unwrap()),
                b.binding_signature(&bind),
                "{field:?}/{name}"
            );
        }
        for kind in [
            Type::Field,
            Type::Vector,
            Type::Matrix,
            Type::Polynomial,
            Type::Round,
        ] {
            let ty = PhysicalType::default_for(LogicalType::new(kind, field).unwrap()).unwrap();
            assert_eq!(PhysicalType::parse(&ty.spelling()).unwrap(), ty);
        }
    }
    for field in [Identity::Goldilocks, Identity::GoldilocksExt2] {
        let v = call(field, "field.constant", &["9007199254740993"], vec![]).remove(0);
        let mut wire = vec![];
        match &v {
            Value::GoldilocksField(v) => zkc_kernels::plonky3::residue::encode_into(v, &mut wire),
            Value::GoldilocksExt2Field(v) => {
                zkc_kernels::plonky3::residue::encode_into(v, &mut wire)
            }
            _ => panic!(),
        }
        assert_eq!(&wire[..8], &9007199254740993u64.to_le_bytes());
        assert!(
            zkc_runtime::ring::Expression::new(
                vec![],
                vec![zkc_runtime::ring::Node::Constant(
                    field,
                    "18446744069414584321".into()
                )],
                vec![0]
            )
            .is_err()
        );
    }
    assert!(
        binding(Identity::Goldilocks, "encoding.field_montgomery_le")
            .signature()
            .is_err()
    );
}
#[test]
fn nonbase_values_survive_native_frames_and_reject_equal_width_cross_field_frames() {
    let b = backend(Policy::default());
    let baby = Value::BabyBearExt4Field(BabyBearExt4::from([1, 2, 3, 4].map(BabyBear::from_u32)));
    let gold = Value::GoldilocksExt2Field(GoldilocksExt2::from([
        Goldilocks::from_u64(9007199254740993),
        Goldilocks::from_u64(1 << 63),
    ]));
    for value in [&baby, &gold] {
        let ty = value.physical_type();
        let wire = b.encode_native_value(value).unwrap();
        assert_value(&b.decode_native_value(&ty, &wire).unwrap(), value);
        let readable = if ty.logical().identity() == Identity::BabyBearExt4 {
            json!(["1", "2", "3", "4"])
        } else {
            json!(["9007199254740993", "9223372036854775808"])
        };
        assert_eq!(zkc_cpu::readable_wire(&ty, &readable, 1024).unwrap(), wire);
        assert!(b.decode_native_value(&ty, &wire[..wire.len() - 1]).is_err());
        let mut bad = wire.clone();
        let offset = bad.len()
            - if ty.logical().identity() == Identity::BabyBearExt4 {
                4
            } else {
                8
            };
        let p = if ty.logical().identity() == Identity::BabyBearExt4 {
            2013265921u64
        } else {
            18446744069414584321u64
        };
        let len = bad.len() - offset;
        bad[offset..].copy_from_slice(&p.to_le_bytes()[..len]);
        assert!(b.decode_native_value(&ty, &bad).is_err());
    }
    let koala = Value::KoalaBearExt4Field(zkc_cpu::KoalaBearExt4::from(
        [1, 2, 3, 4].map(zkc_cpu::KoalaBear::from_u32),
    ));
    for expected in [&baby, &gold, &koala] {
        for source in [&baby, &gold, &koala] {
            if expected.physical_type() != source.physical_type() {
                assert!(
                    b.decode_native_value(
                        &expected.physical_type(),
                        &b.encode_native_value(source).unwrap()
                    )
                    .is_err()
                );
            }
        }
    }
}
#[test]
fn normal_vm_executes_nonbase_multiply_cosets_and_prepared_numerical_plans() {
    let field = Identity::GoldilocksExt2;
    let x = GoldilocksExt2::from([Goldilocks::ZERO, Goldilocks::ONE]);
    assert_value(
        &call(
            field,
            "field.mul",
            &[],
            vec![Value::GoldilocksExt2Field(x), Value::GoldilocksExt2Field(x)],
        )[0],
        &Value::GoldilocksExt2Field(GoldilocksExt2::from(Goldilocks::from_u64(7))),
    );
    let coefficients = vec![x, x + GoldilocksExt2::ONE, x * x];
    let poly = call(
        field,
        "poly.from_coefficients",
        &[],
        vec![Value::GoldilocksExt2Vector(coefficients.clone().into())],
    )
    .remove(0);
    let values = call(
        field,
        "poly.coset_evaluate",
        &[],
        vec![poly.clone(), Value::GoldilocksExt2Field(x), Value::Index(8)],
    )
    .remove(0);
    assert_value(
        &call(
            field,
            "poly.coset_interpolate",
            &[],
            vec![values, Value::GoldilocksExt2Field(x)],
        )[0],
        &poly,
    );
    let mut bind = binding(field, "numerical.map");
    bind.arguments.push("1".into());
    let body = zkc_test_support::numerical_plan(json!([
        "zkc.ring/0",
        [field.name()],
        [
            ["input", 0],
            ["constant", field.name(), "9007199254740993"],
            ["add", 0, 1]
        ],
        [2]
    ]));
    let result = one(
        backend(Policy::default()),
        bind,
        &[&body],
        vec![
            Value::Index(3),
            Value::GoldilocksExt2Vector(coefficients.clone().into()),
        ],
    )
    .0
    .unwrap();
    let expected = Value::GoldilocksExt2Vector(
        coefficients
            .iter()
            .map(|v| *v + GoldilocksExt2::from(Goldilocks::from_u64(9007199254740993)))
            .collect::<Vec<_>>()
            .into(),
    );
    assert_value(&result[0], &expected);
}
#[test]
fn wide_ring_constants_work_in_scalar_packed_and_coefficient_paths() {
    use zkc_runtime::ring::{Expression, Node};
    let expression = Expression::new(
        vec![Identity::Goldilocks],
        vec![
            Node::Input(0),
            Node::Constant(Identity::Goldilocks, "18446744069414584320".into()),
            Node::Add(0, 1),
        ],
        vec![2],
    )
    .unwrap();
    let values = vec![Goldilocks::from_u64(1 << 63); 17];
    for packed in [false, true] {
        let out = zkc_cpu::ring::rows(
            &expression,
            Identity::Goldilocks,
            &values,
            17,
            packed,
            &Policy::default(),
            &mut Default::default(),
            usize::MAX,
        )
        .unwrap();
        assert_eq!(out, vec![Goldilocks::from_u64((1 << 63) - 1); 17]);
    }
    let out = zkc_cpu::ring::coefficients(
        &expression,
        Identity::Goldilocks,
        &[Goldilocks::ONE, Goldilocks::ONE],
        2,
        &Policy::default(),
        &mut Default::default(),
        usize::MAX,
    )
    .unwrap();
    assert_eq!(out, vec![Goldilocks::ZERO, Goldilocks::ONE]);
}

#[test]
fn vector_and_matrix_frames_preserve_nonbase_coordinates_and_limits() {
    let p = Policy::default();
    let b = backend(p);
    let x = GoldilocksExt2::from([Goldilocks::from_u64(1 << 63), Goldilocks::ONE]);
    let vector = Value::GoldilocksExt2Vector(vec![x, -x, x * x].into());
    let matrix =
        Value::goldilocks_ext2_matrix(2, 3, &[(0, 0, x), (0, 2, x * x), (1, 1, -x)], &p).unwrap();
    for value in [&vector, &matrix] {
        let wire = b.encode_native_value(value).unwrap();
        assert_value(
            value,
            &b.decode_native_value(&value.physical_type(), &wire)
                .unwrap(),
        );
        let mut bad = wire.clone();
        let offset = bad.len() - 8;
        bad[offset..].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(b.decode_native_value(&value.physical_type(), &bad).is_err());
        let limited = backend(Policy {
            max_table_elements: 2,
            ..p
        });
        assert!(
            limited
                .decode_native_value(&value.physical_type(), &wire)
                .is_err()
        );
    }
    let product = call(
        Identity::GoldilocksExt2,
        "matrix.mul_vector",
        &[],
        vec![matrix, vector],
    );
    assert_value(
        &product[0],
        &Value::GoldilocksExt2Vector(vec![x * x + (x * x) * (x * x), x * x].into()),
    );
}

#[test]
fn explicit_extension_rngs_and_service_contracts_execute_through_the_vm() {
    use zkc_runtime::vm::ServiceContract;
    for field in [Identity::BabyBearExt4, Identity::GoldilocksExt2] {
        let contract = ServiceContract::for_field(field).unwrap();
        assert_eq!(ServiceContract::parse(contract.name()).unwrap(), contract);
        let mut b = backend(Policy::default());
        let rng = b
            .issue_rng_for(field, zkc_cpu::Domain::new("P", "session", "main", None), 1)
            .unwrap();
        let result = one(b, binding(field, "random.draw"), &[], vec![rng])
            .0
            .unwrap();
        assert_eq!(result[0].physical_type().logical().identity(), field);
        assert_eq!(result[1].physical_type().kind(), Type::Rng);
    }
}

fn rng_handle(value: &Value) -> &zkc_cpu::Capability {
    let Value::Rng(handle) = value else {
        panic!("expected an RNG successor")
    };
    handle
}

fn rng_snapshot(backend: &zkc_cpu::CpuBackend, value: &Value) -> [u64; 3] {
    let state = backend.observe(rng_handle(value)).unwrap();
    assert_eq!(backend.active_frames(), 0);
    [state.generation, state.draw_count, state.budget]
}

#[test]
fn extension_rng_vectors_transition_once_and_refuse_stale_predecessors() {
    for field in [Identity::BabyBearExt4, Identity::GoldilocksExt2] {
        for (length, budget, expected) in [(0, 0, [1, 0, 0]), (1, 1, [1, 1, 0]), (3, 5, [1, 3, 2])]
        {
            let mut native = backend(Policy::default());
            let rng = native
                .issue_rng_for(field, support::domain(), budget)
                .unwrap();
            let (result, native) = one(
                native,
                binding(field, "random.vector"),
                &[&length.to_string()],
                vec![rng.clone()],
            );
            let result = result.unwrap();
            let empty = match field {
                Identity::BabyBearExt4 => Value::BabyBearExt4Vector(vec![].into()),
                Identity::GoldilocksExt2 => Value::GoldilocksExt2Vector(vec![].into()),
                _ => unreachable!(),
            };
            if length == 0 {
                assert_value(&result[0], &empty);
            }
            assert_eq!(result[0].physical_type(), empty.physical_type());
            let actual_length = match &result[0] {
                Value::BabyBearExt4Vector(values) => values.len(),
                Value::GoldilocksExt2Vector(values) => values.len(),
                _ => panic!("expected the installed RNG vector carrier"),
            };
            assert_eq!(actual_length, length);
            assert_eq!(rng_handle(&result[1]).identity(), field);
            assert_eq!(rng_handle(&result[1]).generation(), 1);
            assert_eq!(rng_snapshot(&native, &rng), expected);
            // Substitute at the operation boundary so stale admission cannot
            // prevent the handler itself from being exercised, even for n=0.
            let mut controlled = support::Controlled::new(native);
            controlled.substitute = Some(rng.clone());
            let (failure, controlled) = one(
                controlled,
                binding(field, "random.vector"),
                &["0"],
                vec![result[1].clone()],
            );
            assert_eq!(failure.unwrap_err(), "refused:capability-stale");
            assert_eq!(rng_snapshot(&controlled.inner, &rng), expected);
            let (next, native) = one(
                controlled.inner,
                binding(field, "random.vector"),
                &["0"],
                vec![result[1].clone()],
            );
            assert_eq!(rng_handle(&next.unwrap()[1]).generation(), 2);
            assert_eq!(rng_snapshot(&native, &rng), [2, expected[1], expected[2]]);
        }
    }
}

#[test]
fn extension_rng_vector_preflight_and_allocation_failures_preserve_the_handle() {
    for field in [Identity::BabyBearExt4, Identity::GoldilocksExt2] {
        for failure in ["output", "elements", "budget", "allocation"] {
            let policy = Policy {
                max_table_elements: if failure == "elements" { 2 } else { 16 },
                ..Policy::default()
            };
            let budget = if failure == "budget" { 2 } else { 5 };
            let mut native = backend(policy);
            let rng = native
                .issue_rng_for(field, support::domain(), budget)
                .unwrap();
            let mut controlled = support::Controlled::new(native);
            if failure == "output" {
                controlled.output_limit = Some(0);
            }
            let guard =
                (failure == "allocation").then(|| zkc_kernels::allocation::failure::after(0));
            let (result, controlled) = one(
                controlled,
                binding(field, "random.vector"),
                &["3"],
                vec![rng.clone()],
            );
            drop(guard);
            assert_eq!(
                result.unwrap_err(),
                match failure {
                    "output" => "exhausted:output-bytes",
                    "elements" => "exhausted:element-limit",
                    "budget" => "exhausted:resource-budget",
                    "allocation" => "exhausted:allocation",
                    _ => unreachable!(),
                }
            );
            assert_eq!(rng_snapshot(&controlled.inner, &rng), [0, 0, budget]);
            let (result, native) = one(
                controlled.inner,
                binding(field, "random.vector"),
                &["1"],
                vec![rng.clone()],
            );
            assert!(result.is_ok());
            assert_eq!(rng_snapshot(&native, &rng), [1, 1, budget - 1]);
        }
    }
}

#[test]
fn extension_rng_index_bounds_and_preflight_preserve_state_then_success_consumes() {
    for field in [Identity::BabyBearExt4, Identity::GoldilocksExt2] {
        let mut native = backend(Policy::default());
        let rng = native.issue_rng_for(field, support::domain(), 2).unwrap();
        for bound in [0, 3, u64::MAX] {
            let (result, next) = one(
                native,
                binding(field, "random.index"),
                &[],
                vec![rng.clone(), Value::Index(bound)],
            );
            assert_eq!(result.unwrap_err(), "refused:query-bound");
            assert_eq!(rng_snapshot(&next, &rng), [0, 0, 2]);
            native = next;
        }
        let mut controlled = support::Controlled::new(native);
        controlled.output_limit = Some(0);
        let (result, controlled) = one(
            controlled,
            binding(field, "random.index"),
            &[],
            vec![rng.clone(), Value::Index(1)],
        );
        assert_eq!(result.unwrap_err(), "exhausted:output-bytes");
        assert_eq!(rng_snapshot(&controlled.inner, &rng), [0, 0, 2]);
        // Bound one has the independent deterministic answer zero.
        let (result, native) = one(
            controlled.inner,
            binding(field, "random.index"),
            &[],
            vec![rng.clone(), Value::Index(1)],
        );
        let result = result.unwrap();
        assert_value(&result[0], &Value::Index(0));
        let successor = result[1].clone();
        assert_eq!(rng_snapshot(&native, &rng), [1, 1, 1]);
        let mut controlled = support::Controlled::new(native);
        controlled.substitute = Some(rng.clone());
        let (result, controlled) = one(
            controlled,
            binding(field, "random.index"),
            &[],
            vec![result[1].clone(), Value::Index(1)],
        );
        assert_eq!(result.unwrap_err(), "refused:capability-stale");
        assert_eq!(rng_snapshot(&controlled.inner, &rng), [1, 1, 1]);
        let (result, native) = one(
            controlled.inner,
            binding(field, "random.index"),
            &[],
            vec![successor, Value::Index(1)],
        );
        let successor = result.unwrap()[1].clone();
        assert_eq!(rng_snapshot(&native, &rng), [2, 2, 0]);
        let (result, native) = one(
            native,
            binding(field, "random.index"),
            &[],
            vec![successor, Value::Index(1)],
        );
        assert_eq!(result.unwrap_err(), "exhausted:resource-budget");
        assert_eq!(rng_snapshot(&native, &rng), [3, 3, 0]);
    }
}

#[test]
fn extension_rng_scalar_draws_consume_before_output_and_exhausted_budget_refusals() {
    for field in [Identity::BabyBearExt4, Identity::GoldilocksExt2] {
        let mut native = backend(Policy::default());
        let rng = native.issue_rng_for(field, support::domain(), 2).unwrap();
        let (result, native) = one(
            native,
            binding(field, "random.draw"),
            &[],
            vec![rng.clone()],
        );
        let result = result.unwrap();
        assert_eq!(result[0].physical_type().logical().identity(), field);
        assert_eq!(rng_snapshot(&native, &rng), [1, 1, 1]);
        let mut controlled = support::Controlled::new(native);
        controlled.substitute = Some(rng.clone());
        let (result, controlled) = one(
            controlled,
            binding(field, "random.draw"),
            &[],
            vec![result[1].clone()],
        );
        assert_eq!(result.unwrap_err(), "refused:capability-stale");
        assert_eq!(rng_snapshot(&controlled.inner, &rng), [1, 1, 1]);
        for budget in [0, 1] {
            let mut native = backend(Policy::default());
            let rng = native
                .issue_rng_for(field, support::domain(), budget)
                .unwrap();
            let mut controlled = support::Controlled::new(native);
            controlled.output_limit = Some(0);
            let (result, controlled) = one(
                controlled,
                binding(field, "random.draw"),
                &[],
                vec![rng.clone()],
            );
            assert_eq!(
                result.unwrap_err(),
                if budget == 0 {
                    "exhausted:resource-budget"
                } else {
                    "exhausted:output-bytes"
                }
            );
            assert_eq!(rng_snapshot(&controlled.inner, &rng), [1, 1, 0]);
            assert_eq!(
                controlled.inner.validate_value(&rng).unwrap_err().code,
                "refused:capability-stale"
            );
        }
    }
}

#[test]
fn residue_inverse_values_and_failure_precedence_use_installed_operations() {
    macro_rules! check {
        ($identity:ident, $s:ty, $field:ident, $vector:ident, $value:expr, $inverse:expr) => {{
            let field = Identity::$identity;
            let values = Value::$vector(vec![<$s>::ONE, -<$s>::ONE, $value].into());
            let expected = Value::$vector(vec![<$s>::ONE, -<$s>::ONE, $inverse].into());
            assert_value(
                &call(field, "vector.inverse", &[], vec![values.clone()])[0],
                &expected,
            );
            let empty = Value::$vector(vec![].into());
            assert_value(
                &call(field, "vector.inverse", &[], vec![empty.clone()])[0],
                &empty,
            );
            let zeros = Value::$vector(vec![<$s>::ONE, $value, <$s>::ZERO].into());
            for (input, limit, expected) in [
                (Value::$field(<$s>::ZERO), Some(0), "exhausted:output-bytes"),
                (Value::$field(<$s>::ZERO), None, "refused:zero-inverse"),
                (zeros.clone(), Some(0), "refused:zero-inverse"),
                (values.clone(), Some(0), "exhausted:output-bytes"),
            ] {
                let name = if matches!(&input, Value::$field(_)) {
                    "field.inverse"
                } else {
                    "vector.inverse"
                };
                let mut controlled = support::Controlled::new(backend(Policy::default()));
                controlled.output_limit = limit;
                assert_eq!(
                    one(controlled, binding(field, name), &[], vec![input])
                        .0
                        .unwrap_err(),
                    expected
                );
            }
            for (input, expected) in [
                (zeros, "refused:zero-inverse"),
                (values, "exhausted:allocation"),
            ] {
                let native = backend(Policy::default());
                let guard = zkc_kernels::allocation::failure::after(0);
                let result = one(native, binding(field, "vector.inverse"), &[], vec![input]).0;
                drop(guard);
                assert_eq!(result.unwrap_err(), expected);
            }
        }};
    }
    check!(
        BabyBear,
        BabyBear,
        BabyBearField,
        BabyBearVector,
        BabyBear::from_u64(2),
        BabyBear::from_u64(1_006_632_961)
    );
    check!(
        Goldilocks,
        Goldilocks,
        GoldilocksField,
        GoldilocksVector,
        Goldilocks::from_u64(2),
        Goldilocks::from_u64(9_223_372_034_707_292_161)
    );
    // X^-1 = nonresidue^-1 * X^(degree-1), computed in integer modular arithmetic.
    check!(
        BabyBearExt4,
        BabyBearExt4,
        BabyBearExt4Field,
        BabyBearExt4Vector,
        BabyBearExt4::from([0, 1, 0, 0].map(BabyBear::from_u32)),
        BabyBearExt4::from([0, 0, 0, 549_072_524].map(BabyBear::from_u32))
    );
    check!(
        GoldilocksExt2,
        GoldilocksExt2,
        GoldilocksExt2Field,
        GoldilocksExt2Vector,
        GoldilocksExt2::from([Goldilocks::ZERO, Goldilocks::ONE]),
        GoldilocksExt2::from([
            Goldilocks::ZERO,
            Goldilocks::from_u64(2_635_249_152_773_512_046)
        ])
    );
}

#[test]
fn registered_round_wrapping_and_substitution_keep_nonbase_coordinates() {
    macro_rules! check {
        ($s:ty, $id:ident, $base:ty) => {{
            use p3_field::BasedVectorSpace;
            let x = <$s as BasedVectorSpace<$base>>::from_basis_coefficients_fn(|i| {
                <$base>::from_usize(i + 2)
            });
            let seven = <$s>::from_u64(7);
            let round = Value::from([<$s>::ONE, x, seven]);
            let point = call(Identity::$id, "field.constant", &["3"], vec![]).remove(0);
            let result = call(
                Identity::$id,
                "poly.round_evaluate",
                &[],
                vec![round.clone(), point],
            );
            // 1 + 3*x + 7*3^2, with the higher coordinates retained.
            let expected = x * <$s>::from_u64(3) + <$s>::from_u64(64);
            let bytes = backend(Policy::default())
                .encode_native_value(&result[0])
                .unwrap();
            let mut encoded = Vec::new();
            zkc_kernels::plonky3::residue::encode_into(&expected, &mut encoded);
            assert_eq!(&bytes[6..], encoded);
            let boundary = call(Identity::$id, "poly.boundary", &[], vec![round]);
            let mut encoded = Vec::new();
            zkc_kernels::plonky3::residue::encode_into(&(x + <$s>::from_u64(9)), &mut encoded);
            let bytes = backend(Policy::default())
                .encode_native_value(&boundary[0])
                .unwrap();
            assert_eq!(&bytes[6..], encoded);
        }};
    }
    check!(BabyBear, BabyBear, BabyBear);
    check!(BabyBearExt4, BabyBearExt4, BabyBear);
    check!(Goldilocks, Goldilocks, Goldilocks);
    check!(GoldilocksExt2, GoldilocksExt2, Goldilocks);
}

#[test]
fn word_codec_bindings_preserve_montgomery_capabilities() {
    let backend = backend(Policy::default());
    for (field, montgomery) in [
        (Identity::KoalaBear, true),
        (Identity::KoalaBearExt4, true),
        (Identity::KoalaBearExt8, true),
        (Identity::BabyBear, true),
        (Identity::BabyBearExt4, true),
        (Identity::Goldilocks, false),
        (Identity::GoldilocksExt2, false),
    ] {
        for operation in [
            "encoding.field_le",
            "encoding.fields_le",
            "encoding.field_from_le",
            "encoding.fields_from_le",
        ] {
            let bind = binding(field, operation);
            assert!(bind.signature().is_ok(), "{field:?}/{operation}");
            assert!(
                backend.binding_signature(&bind).is_some(),
                "{field:?}/{operation}"
            );
        }
        for operation in [
            "encoding.field_montgomery_le",
            "encoding.fields_montgomery_le",
            "encoding.field_from_montgomery_le",
            "encoding.fields_from_montgomery_le",
        ] {
            let bind = binding(field, operation);
            assert_eq!(
                bind.signature().is_ok(),
                montgomery,
                "{field:?}/{operation}"
            );
            assert_eq!(
                backend.binding_signature(&bind).is_some(),
                montgomery,
                "{field:?}/{operation}"
            );
        }
    }
}
