//! Public transform destinations must retain their exact shape and all coefficients.
use zkc_kernels::{
    KoalaBear as F,
    plonky3::polynomial::{Domain, Error, Kernels},
};
#[test]
fn coefficient_batch_does_not_silently_truncate_a_nonzero_tail() {
    let domain = Domain::new(2, F::new(3), 8).unwrap();
    let kernels = Kernels::default();
    let mut out = [F::new(19); 4];
    let bad = [1, 2, 0, 3, 4, 5].map(F::new);
    assert_eq!(
        kernels.coset_evaluate_batch_into(&bad, 2, 3, domain, &mut out),
        Err(Error::CoefficientCount)
    );
    assert_eq!(out, [F::new(19); 4]);
    let good = [1, 2, 0, 3, 4, 0].map(F::new);
    kernels
        .coset_evaluate_batch_into(&good, 2, 3, domain, &mut out)
        .unwrap();
    for (column, actual) in good.as_chunks::<3>().0.iter().zip(out.as_chunks::<2>().0) {
        assert_eq!(
            actual.as_slice(),
            kernels.evaluate(&column[..2], domain).unwrap()
        );
    }
}
#[test]
fn bn254_interpolation_checks_full_shape_before_writing() {
    use zkc_kernels::{
        Bn254Scalar as B,
        bn254::polynomial::{Domain, coset_evaluate_at_into},
        fields,
    };
    let domain = Domain::new(4, B::from(1u64)).unwrap();
    assert!(Domain::new(3, B::from(1u64)).is_none());
    assert!(Domain::new(4, B::from(0u64)).is_none());
    let mut weights = [B::from(19u64); 4];
    let mut out = [B::from(23u64); 1];
    assert_eq!(
        coset_evaluate_at_into(
            &[B::from(1u64); 3],
            domain,
            B::from(7u64),
            &mut weights,
            &mut out
        ),
        Err(fields::Error::LengthMismatch)
    );
    assert_eq!(weights, [B::from(19u64); 4]);
    assert_eq!(out, [B::from(23u64); 1]);
}
