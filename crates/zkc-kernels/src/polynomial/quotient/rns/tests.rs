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
    assert_eq!(capacity(35, 1, 1, 17), Ok(1));
    assert_eq!(capacity(35, 1, 1, 18), Ok(0));
    assert_eq!(capacity(35, 1, 1, 1), Ok(17));
    assert_eq!(
        capacity(35, usize::MAX, u64::MAX, u64::MAX),
        Err(Error::RnsCapacity)
    );
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
    assert!(std::mem::size_of::<PreparedMatrix>() + 32 < PreparedMatrix::RETAINED_OVERHEAD);
}
