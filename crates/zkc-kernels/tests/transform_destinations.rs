//! Public transform destinations must retain their exact shape and all coefficients.
use zkc_kernels::{
    KoalaBear as F,
    plonky3::polynomial::{CoefficientBatch, Domain, Error, Kernels},
};
#[test]
fn coefficient_batch_does_not_silently_truncate_a_nonzero_tail() {
    let domain = Domain::new(2, F::new(3), 8).unwrap();
    let kernels = Kernels::default();
    let mut out = [F::new(19); 4];
    let bad = [1, 2, 0, 3, 4, 5].map(F::new);
    assert_eq!(
        CoefficientBatch::new(&bad, 2, 3, domain)
            .and_then(|batch| batch.write_into(&kernels, &mut out)),
        Err(Error::CoefficientCount)
    );
    assert_eq!(out, [F::new(19); 4]);
    let good = [1, 2, 0, 3, 4, 0].map(F::new);
    CoefficientBatch::new(&good, 2, 3, domain)
        .unwrap()
        .write_into(&kernels, &mut out)
        .unwrap();
    for (column, actual) in good.as_chunks::<3>().0.iter().zip(out.as_chunks::<2>().0) {
        assert_eq!(
            actual.as_slice(),
            kernels.evaluate(&column[..2], domain).unwrap()
        );
    }
}

#[test]
fn coefficient_batch_admits_inputs_before_accepting_writable_storage() {
    let domain = Domain::new(2, F::new(3), 8).unwrap();
    assert!(matches!(
        CoefficientBatch::new(&[F::new(1); 5], 2, 3, domain),
        Err(Error::BatchShape)
    ));
    assert!(matches!(
        CoefficientBatch::new(&[], usize::MAX, 2, domain),
        Err(Error::SizeOverflow)
    ));
    assert!(matches!(
        CoefficientBatch::new(&[], usize::MAX, 0, domain),
        Err(Error::SizeOverflow)
    ));
    let coefficients = [F::new(1), F::new(2), F::new(3), F::new(4)];
    let batch = CoefficientBatch::new(&coefficients, 2, 2, domain).unwrap();
    let mut short = [F::new(19); 3];
    assert_eq!(
        batch.write_into(&Kernels::default(), &mut short),
        Err(Error::BatchShape)
    );
    assert_eq!(short, [F::new(19); 3]);
    // A checked borrow can serve separate private destinations without a new
    // coefficient scan, and a refused destination does not consume the batch.
    let mut first = [F::new(0); 4];
    let mut second = first;
    let kernels = Kernels::default();
    batch.write_into(&kernels, &mut first).unwrap();
    batch.write_into(&kernels, &mut second).unwrap();
    assert_eq!(first, second);
    assert_eq!(
        &first[..2],
        kernels.evaluate(&coefficients[..2], domain).unwrap()
    );
    assert_eq!(
        &first[2..],
        kernels.evaluate(&coefficients[2..], domain).unwrap()
    );
}

#[test]
fn coefficient_batches_allow_empty_columns_and_zero_polynomials() {
    let domain = Domain::new(2, F::new(3), 8).unwrap();
    let kernels = Kernels::default();
    CoefficientBatch::new(&[], 0, usize::MAX, domain)
        .unwrap()
        .write_into(&kernels, &mut [])
        .unwrap();
    let mut output = [F::new(19); 6];
    CoefficientBatch::new(&[], 3, 0, domain)
        .unwrap()
        .write_into(&kernels, &mut output)
        .unwrap();
    assert_eq!(output, [F::new(0); 6]);
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
