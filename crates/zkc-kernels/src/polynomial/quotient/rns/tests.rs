use super::*;
use crate::polynomial::quotient::Operands;

fn reference(
    matrix: &[u64],
    input: &[u64],
    q: u64,
    n: usize,
    rows: usize,
    columns: usize,
) -> Vec<u64> {
    let ring = Ring::new(q, n).unwrap();
    let mut result = vec![0; rows * n];
    let mut term = vec![0; n];
    for row in 0..rows {
        for col in 0..columns {
            let offset = (row * columns + col) * n;
            Operands::new(
                ring.polynomial(&matrix[offset..offset + n]).unwrap(),
                ring.polynomial(&input[col * n..(col + 1) * n]).unwrap(),
            )
            .unwrap()
            .multiply_into(&mut term)
            .unwrap();
            for (out, &value) in result[row * n..(row + 1) * n].iter_mut().zip(&term) {
                *out = ((*out as u128 + value as u128) % q as u128) as u64;
            }
        }
    }
    result
}
fn prepare(
    matrix: &[u64],
    q: u64,
    n: usize,
    rows: usize,
    columns: usize,
    b: u64,
) -> PreparedMatrix {
    let plan = Matrix::new(matrix, q, n, rows, columns, b).unwrap();
    let storage = vec![0; plan.storage_elements()];
    let mut scratch = vec![0; plan.scratch_elements()];
    plan.prepare(storage, &mut scratch).unwrap()
}
fn evaluate(m: &PreparedMatrix, input: &[u64]) -> Vec<u64> {
    let mut out = vec![0; m.output_elements()];
    let mut scratch = vec![0; m.scratch_elements().unwrap()];
    m.digits(input)
        .unwrap()
        .evaluate(&mut out, &mut scratch)
        .unwrap();
    out
}

#[test]
fn prime_and_composite_protocol_rings_match_schoolbook_with_all_profiles() {
    let mut profiles = [false; 3];
    for q in [
        2,
        16,
        17,
        12289,
        8380417,
        1u64 << 32,
        u64::MAX - 58,
        u64::MAX,
    ] {
        for n in [2, 4, 16, 256] {
            let (rows, columns) = (2, 3);
            let matrix: Vec<_> = (0..rows * columns * n)
                .map(|i| match i % 4 {
                    0 => q / 2,
                    1 => q - 1,
                    2 => (i as u64 * 12345) % q,
                    _ => 0,
                })
                .collect();
            let bound = (q / 2).min(128);
            let input: Vec<_> = (0..columns * n)
                .map(|i| {
                    residue(
                        (i as i128 % (bound as i128 + 1)) * if i % 2 == 0 { 1 } else { -1 },
                        q,
                    )
                })
                .collect();
            let prepared = prepare(&matrix, q, n, rows, columns, bound);
            profiles[prepared.limbs() - 1] = true;
            assert_eq!(
                evaluate(&prepared, &input),
                reference(&matrix, &input, q, n, rows, columns),
                "q={q}, n={n}"
            );
            assert_eq!(evaluate(&prepared, &input), evaluate(&prepared, &input));
        }
    }
    assert_eq!(profiles, [true; 3]);
}

#[test]
fn accumulation_is_chunked_before_centered_reconstruction_overflows() {
    let q = u64::MAX - 58;
    let n = 4;
    let b = 10_000_000;
    let columns = 7;
    let matrix = vec![q / 2; 2 * columns * n];
    let digits = vec![b; columns * n];
    let prepared = prepare(&matrix, q, n, 2, columns, b);
    assert!(prepared.chunk_columns() < columns);
    assert!(prepared.chunk_columns() > 0);
    assert_eq!(
        evaluate(&prepared, &digits),
        reference(&matrix, &digits, q, n, 2, columns)
    );
    let negative: Vec<_> = digits.iter().map(|&v| q - v).collect();
    assert_eq!(
        evaluate(&prepared, &negative),
        reference(&matrix, &negative, q, n, 2, columns)
    );
}

#[test]
fn strict_capacity_and_zero_bounds() {
    assert_eq!(capacity(35, 1, 1, 17), 1);
    assert_eq!(capacity(35, 1, 1, 18), 0);
    assert_eq!(capacity(35, 1, 1, 1), 17);
    assert_eq!(capacity(35, usize::MAX, u64::MAX, u64::MAX), 0);
    for (matrix, bound, input) in [
        (vec![0; 8], u64::MAX, vec![4; 4]),
        (vec![8; 8], 0, vec![0; 4]),
    ] {
        let prepared = prepare(&matrix, 17, 2, 2, 2, bound);
        assert_eq!(evaluate(&prepared, &input), vec![0; 4]);
    }
    assert!(matches!(
        Matrix::new(&[u64::MAX / 2; 4], u64::MAX, 2, 1, 2, u64::MAX),
        Err(Error::RnsCapacity)
    ));
}

#[test]
fn bad_inputs_and_destinations_refuse_without_writes() {
    assert!(matches!(
        Matrix::new(&[17; 4], 17, 2, 1, 2, 1),
        Err(Error::Residue)
    ));
    assert!(matches!(
        Matrix::new(&[0; 3], 17, 3, 1, 1, 1),
        Err(Error::TransformProfile)
    ));
    assert!(matches!(
        Matrix::new(&[], 17, 2, 0, 1, 1),
        Err(Error::Shape)
    ));
    let prepared = prepare(&[1; 4], 16, 2, 1, 2, 7);
    assert!(matches!(prepared.digits(&[8; 4]), Err(Error::DigitBound)));
    assert!(matches!(prepared.digits(&[16; 4]), Err(Error::Residue)));
    assert!(matches!(prepared.digits(&[]), Err(Error::Shape)));
    let mut output = [123; 2];
    assert_eq!(
        prepared
            .digits(&[15; 4])
            .unwrap()
            .evaluate(&mut output, &mut []),
        Err(Error::Destination)
    );
    assert_eq!(output, [123; 2]);
}

#[test]
fn loose_declared_bounds_use_the_canonical_protocol_range_for_planning() {
    let prepared = prepare(&[1; 8], 17, 4, 1, 2, u64::MAX);
    assert_eq!(prepared.limbs(), 1);
    assert_eq!(prepared.chunk_columns(), 2);
    assert_eq!(prepared.digit_bound(), u64::MAX);
    assert_eq!(prepared.ring(), Ring::new(17, 4).unwrap());
    assert_eq!((prepared.rows(), prepared.columns()), (1, 2));
    let input = [8, 9, 0, 16, 1, 2, 3, 4];
    assert_eq!(
        evaluate(&prepared, &input),
        reference(&[1; 8], &input, 17, 4, 1, 2)
    );
    // A zero matrix does not waive the input's declared range contract.
    let zero = prepare(&[0; 8], 17, 4, 1, 2, 0);
    assert!(matches!(zero.digits(&[1; 8]), Err(Error::DigitBound)));
}

#[test]
fn matrix_coordinates_use_one_forward_basis_for_both_directions() {
    for q in [16, 17, 12289] {
        for n in [2, 4, 8] {
            for position in 0..n {
                let mut matrix = vec![0; n];
                matrix[position] = 1;
                let prepared = prepare(&matrix, q, n, 1, 1, q / 2);
                for input_position in 0..n {
                    for coefficient in [1, q / 2, q - 1] {
                        let mut input = vec![0; n];
                        input[input_position] = coefficient;
                        assert_eq!(
                            evaluate(&prepared, &input),
                            reference(&matrix, &input, q, n, 1, 1),
                            "q={q}, n={n}, basis={position}, input={input_position}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn strict_lift_capacity_is_respected_on_both_sides_of_a_chunk_boundary() {
    let q = u64::MAX - 58;
    let n = 4;
    let bound = 10_000_000;
    let product: u128 = PRIMES.iter().map(|&p| u128::from(p)).product();
    let c = capacity(product, n, q / 2, bound);
    assert_eq!(c, 2);
    for columns in [c - 1, c, c + 1, 2 * c + 1] {
        let matrix = vec![q / 2; columns * n];
        let prepared = prepare(&matrix, q, n, 1, columns, bound);
        assert_eq!(prepared.chunk_columns(), c.min(columns));
        for input in [vec![bound; columns * n], vec![q - bound; columns * n]] {
            assert_eq!(
                evaluate(&prepared, &input),
                reference(&matrix, &input, q, n, 1, columns)
            );
        }
    }
}

#[test]
fn preparation_adopts_storage_and_keeps_its_complete_capacity() {
    let matrix = [1, 2, 3, 4];
    let plan = Matrix::new(&matrix, 17, 4, 1, 1, 8).unwrap();
    let mut storage = Vec::with_capacity(31);
    storage.resize(plan.storage_elements(), 0);
    let pointer = storage.as_ptr();
    let capacity = storage.capacity();
    let mut scratch = [0; 4];
    let prepared = plan.prepare(storage, &mut scratch).unwrap();
    assert_eq!(prepared.storage.as_ptr(), pointer);
    assert_eq!(prepared.storage_capacity(), capacity);
    assert_eq!(matrix, [1, 2, 3, 4]);
    let input = [16, 0, 2, 9];
    let alias = &input;
    assert_eq!(
        evaluate(&prepared, &input),
        reference(&matrix, &input, 17, 4, 1, 1)
    );
    assert_eq!(*alias, [16, 0, 2, 9]);
}
