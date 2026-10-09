use p3_field::{PrimeCharacteristicRing, PrimeField32};
use sha2::{Digest, Sha256};
use zkc_backends::{
    KoalaBear as F, KoalaBearExt8 as E, Policy,
    ring::{self, Budget, Registry},
};
use zkc_runtime::{
    interactive::Identity,
    ring::{Expression, Node},
};

#[path = "domains/support.rs"]
mod support;

fn product() -> Expression {
    Expression::new(
        vec![Identity::KoalaBear; 2],
        vec![
            Node::Input(0),
            Node::Input(1),
            Node::Mul(0, 1),
            Node::Add(0, 1),
        ],
        vec![2, 3],
    )
    .unwrap()
}
fn run<S: ring::Carrier>(e: &Expression, input: &[S], count: usize, packed: bool) -> Vec<S> {
    ring::rows(
        e,
        S::IDENTITY,
        input,
        count,
        packed,
        &Policy::default(),
        &mut Budget::default(),
        usize::MAX,
    )
    .unwrap()
}
fn poly_eval<S: ring::Carrier>(coefficients: &[S], point: S) -> S {
    coefficients
        .iter()
        .rev()
        .fold(S::ZERO, |v, c| v * point + *c)
}
#[test]
fn row_point_and_affine_substitutions_agree_with_independent_formulas() {
    let e = product();
    // Different residuals share the same admitted expression, including every
    // partial packed block length rather than only multiples of SIMD width.
    for count in 0..=zkc_backends::plonky3::PACKING_WIDTH * 2 + 3 {
        let input: Vec<_> = (0..2 * count).map(|i| F::new(i as u32 + 7)).collect();
        let expected: Vec<_> = input
            .as_chunks::<2>()
            .0
            .iter()
            .flat_map(|v| [v[0] * v[1], v[0] + v[1]])
            .collect();
        assert_eq!(run(&e, &input, count, false), expected);
        assert_eq!(run(&e, &input, count, true), expected);
    }
    let low: Vec<_> = (1..15).map(F::new).collect();
    let high: Vec<_> = (23..37).map(F::new).collect();
    let coefficients = ring::affine_sum(
        &e,
        Identity::KoalaBear,
        &low,
        &high,
        7,
        &Policy::default(),
        &mut Budget::default(),
        usize::MAX,
    )
    .unwrap();
    assert_eq!(coefficients.len(), 6);
    for point in [F::ZERO, F::ONE, F::new(2), F::new(37)] {
        let expected = low
            .as_chunks::<2>()
            .0
            .iter()
            .zip(high.as_chunks::<2>().0.iter())
            .fold([F::ZERO; 2], |mut sum, (a, b)| {
                let (x, y) = (a[0] + point * (b[0] - a[0]), a[1] + point * (b[1] - a[1]));
                sum[0] += x * y;
                sum[1] += x + y;
                sum
            });
        assert_eq!(poly_eval(&coefficients[..3], point), expected[0]);
        assert_eq!(poly_eval(&coefficients[3..], point), expected[1]);
    }
    // MLE([0,1])(r)^2 is r^2, while MLE([0,1]^2)(r) is r.
    let square = Expression::new(
        vec![Identity::KoalaBear],
        vec![Node::Input(0), Node::Mul(0, 0)],
        vec![1],
    )
    .unwrap();
    let coefficients = ring::coefficients(
        &square,
        Identity::KoalaBear,
        &[F::ZERO, F::ONE],
        2,
        &Policy::default(),
        &mut Budget::default(),
        usize::MAX,
    )
    .unwrap();
    assert_eq!(coefficients, [F::ZERO, F::ZERO, F::ONE]);
    assert_eq!(run(&square, &[F::new(2)], 1, false), [F::new(4)]);
}
#[test]
fn extension_products_embeddings_and_carrier_promotion() {
    let e = Expression::new(
        vec![Identity::KoalaBear, Identity::KoalaBearExt8],
        vec![
            Node::Input(0),
            Node::Embed(Identity::KoalaBearExt8, 0),
            Node::Input(1),
            Node::Mul(1, 2),
        ],
        vec![3],
    )
    .unwrap();
    let x = E::from([0, 1, 0, 0, 0, 0, 0, 0].map(F::new));
    let x7 = E::from([0, 0, 0, 0, 0, 0, 0, 1].map(F::new));
    assert_eq!(run(&e, &[x7, x], 1, false), [E::from(F::new(3))]);
    let lo = [E::from(F::new(3)), x, x7, E::from(F::new(5))];
    let hi = [x7 + E::ONE, x + E::ONE, x, E::from(F::new(11))];
    let coefficients = ring::affine_sum(
        &e,
        Identity::KoalaBearExt8,
        &lo,
        &hi,
        2,
        &Policy::default(),
        &mut Budget::default(),
        usize::MAX,
    )
    .unwrap();
    let r = E::from([1, 2, 3, 4, 5, 6, 7, 8].map(F::new));
    let bound: Vec<_> = lo.iter().zip(hi).map(|(a, b)| *a + r * (b - *a)).collect();
    let expected = (bound[0] * bound[1]) + (bound[2] * bound[3]);
    assert_eq!(poly_eval(&coefficients, r), expected);
    // The formerly base-field factor stays in Ext8 in the following round.
    assert_eq!(
        run(&e, &bound, 2, true),
        [bound[0] * bound[1], bound[2] * bound[3]]
    );
    assert!(
        ring::rows(
            &e,
            Identity::KoalaBear,
            &[F::ONE, F::ONE],
            1,
            false,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX
        )
        .is_err()
    );
    assert!(
        ring::rows(
            &e,
            Identity::KoalaBearExt8,
            &[F::ONE, F::ONE],
            1,
            false,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX
        )
        .is_err()
    );
}
#[test]
fn exact_cubic_coefficients_and_preflight_failures() {
    let e = Expression::new(
        vec![Identity::KoalaBear; 3],
        vec![
            Node::Input(0),
            Node::Input(1),
            Node::Input(2),
            Node::Mul(0, 1),
            Node::Mul(3, 2),
        ],
        vec![4],
    )
    .unwrap();
    let input = [1, 2, 3, 4, 5, 6].map(F::new);
    let c = ring::coefficients(
        &e,
        Identity::KoalaBear,
        &input,
        2,
        &Policy::default(),
        &mut Budget::default(),
        usize::MAX,
    )
    .unwrap();
    assert_eq!(
        c.iter().map(|v| v.as_canonical_u32()).collect::<Vec<_>>(),
        [15, 68, 100, 48]
    );
    for x in [0, 1, 2, 3, 9].map(F::new) {
        assert_eq!(
            poly_eval(&c, x),
            (F::ONE + F::new(2) * x) * (F::new(3) + F::new(4) * x) * (F::new(5) + F::new(6) * x)
        );
    }
    let mut budget = Budget { limit: 1, spent: 0 };
    assert!(
        ring::affine_sum(
            &e,
            Identity::KoalaBear,
            &input,
            &input,
            2,
            &Policy::default(),
            &mut budget,
            usize::MAX
        )
        .is_err()
    );
    assert_eq!(budget.spent, 0, "full bulk work refuses before execution");
    assert!(
        ring::rows(
            &e,
            Identity::KoalaBear,
            &input,
            3,
            true,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX
        )
        .is_err()
    );
    assert!(
        ring::coefficients(
            &e,
            Identity::KoalaBear,
            &input,
            2,
            &Policy::default(),
            &mut Budget::default(),
            1
        )
        .is_err()
    );
    let huge = vec![F::ONE; 3 * 23];
    assert!(
        ring::coefficients(
            &e,
            Identity::KoalaBear,
            &huge,
            23,
            &Policy::default(),
            &mut Budget::default(),
            usize::MAX
        )
        .is_err()
    );
}
#[test]
fn registry_identity_and_large_two_column_execution() {
    let e = product();
    let text = e.canonical();
    let digest = format!("{:x}", Sha256::digest(text.as_bytes()));
    let mut registry = Registry::default();
    assert!(registry.insert(&"0".repeat(64), &text).is_err());
    registry.insert(&digest, &text).unwrap();
    assert!(registry.insert(&digest, &text).is_err());
    assert!(registry.admitted_bytes() > text.len());
    let policy = Policy {
        max_table_elements: 1 << 20,
        ..Default::default()
    };
    let input: Vec<_> = (0..65536)
        .flat_map(|i| [F::new(i), F::new(i + 1)])
        .collect();
    let mut scalar_work = Budget::default();
    let mut packed_work = Budget::default();
    let scalar = ring::rows(
        &e,
        Identity::KoalaBear,
        &input,
        65536,
        false,
        &policy,
        &mut scalar_work,
        usize::MAX,
    )
    .unwrap();
    let packed = ring::rows(
        &e,
        Identity::KoalaBear,
        &input,
        65536,
        true,
        &policy,
        &mut packed_work,
        usize::MAX,
    )
    .unwrap();
    assert_eq!(scalar, packed);
    assert_eq!(
        scalar_work.spent, packed_work.spent,
        "logical work is independent of SIMD realization"
    );
    assert_eq!(scalar.len(), 131072);
}

#[test]
fn empty_batches_still_charge_preparation_and_keep_cumulative_work() {
    let e = product();
    let mut work = Budget::default();
    assert!(
        ring::rows::<F>(
            &e,
            Identity::KoalaBear,
            &[],
            0,
            false,
            &Policy::default(),
            &mut work,
            usize::MAX
        )
        .unwrap()
        .is_empty()
    );
    let first = work.spent;
    assert!(first > 0);
    assert!(
        ring::rows::<F>(
            &e,
            Identity::KoalaBear,
            &[],
            0,
            true,
            &Policy::default(),
            &mut work,
            usize::MAX
        )
        .unwrap()
        .is_empty()
    );
    assert_eq!(work.spent, first * 2);
    let previous = work.spent;
    let zero = ring::affine_sum::<F>(
        &e,
        Identity::KoalaBear,
        &[],
        &[],
        0,
        &Policy::default(),
        &mut work,
        usize::MAX,
    )
    .unwrap();
    assert!(zero.iter().all(|value| *value == F::ZERO));
    assert!(work.spent > previous);
    work.limit = work.spent;
    let previous = work.spent;
    assert!(
        ring::rows::<F>(
            &e,
            Identity::KoalaBear,
            &[],
            0,
            false,
            &Policy::default(),
            &mut work,
            usize::MAX
        )
        .is_err()
    );
    assert_eq!(work.spent, previous);
}

#[test]
fn runner_frames_retain_ring_work_after_a_later_operation_fails() {
    use serde_json::json;
    use zkc_backends::Value;
    use zkc_runtime::interactive::OperationBinding;

    let text = product().canonical();
    let digest = format!("{:x}", Sha256::digest(text.as_bytes()));
    let mut registry = Registry::default();
    registry.insert(&digest, &text).unwrap();
    let backend = support::backend(Policy::default())
        .with_ring_assets(registry)
        .unwrap()
        .with_ring_work_limit(36);
    let ring = OperationBinding {
        contract: "ring.point".into(),
        arguments: vec!["koala-bear".into()],
        implementation: "plonky3/ring.point".into(),
    };
    let at = OperationBinding {
        contract: "vector.at".into(),
        arguments: vec!["koala-bear".into()],
        implementation: "plonky3/vector.at".into(),
    };
    let signature = ring.signature().unwrap();
    let first = json!(["op", "evaluate", "b0", [digest], ["a0"], ["r"]]);
    let good = support::program(
        std::slice::from_ref(&ring),
        &signature.inputs,
        vec![first.clone()],
        &signature.outputs,
        &["r".into()],
    );
    let bad = support::program(
        &[ring, at.clone()],
        &signature.inputs,
        vec![first, json!(["op", "past_end", "b1", ["2"], ["r"], ["o"]])],
        &at.signature().unwrap().outputs,
        &["o".into()],
    );
    let input = || vec![Value::KoalaBearVector(vec![F::new(3), F::new(4)].into())];
    let (result, backend) = support::run_program(backend, &bad, input());
    assert!(result.is_err());
    assert_eq!(backend.active_frames(), 0);
    assert_eq!(backend.ring_work_spent(), 18);
    let (result, backend) = support::run_program(backend, &good, input());
    assert!(result.is_ok());
    assert_eq!(backend.ring_work_spent(), 36);
    let (result, backend) = support::run_program(backend, &good, input());
    assert_eq!(result.unwrap_err(), "exhausted:ring-work");
    assert_eq!(backend.ring_work_spent(), 36);
    assert_eq!(backend.active_frames(), 0);
    assert_eq!(backend.with_ring_work_limit(0).ring_work_spent(), 36);
}
