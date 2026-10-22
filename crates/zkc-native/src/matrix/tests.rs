use super::*;
use std::fmt::Debug;

/// Dense arithmetic is independent of the providers and traverses every cell.
/// Bilinear expectations sum individual triple products, without row factoring.
struct Oracle<M, S> {
    zero: M,
    sample: fn(i64) -> M,
    add: fn(&M, &M) -> M,
    mul: fn(&M, &M) -> M,
    encode: fn(&M) -> S,
}

fn contractions<M: Clone, S: Coefficient + Debug>(oracle: Oracle<M, S>) {
    let p = Policy {
        max_numerical_bytes: 0,
        max_numerical_work: 0,
        ..Policy::default()
    };
    for (rows, columns) in [
        (0, 0),
        (0, 7),
        (9, 0),
        (1, 1),
        (9, 1),
        (3, 2),
        (1, 67),
        (7, 67),
    ] {
        let mut dense = vec![vec![oracle.zero.clone(); columns]; rows];
        for (r, row) in dense.iter_mut().enumerate() {
            for (c, a) in row.iter_mut().enumerate() {
                // Empty end/middle rows, one singleton row, a long row and
                // colliding transpose destinations. The first pair cancels.
                if rows == 1 || r == 1 || (r == 4 && c == 2) || r == 5 {
                    let n = if c < 2 {
                        if c == 0 { 7 } else { -7 }
                    } else {
                        (r * 13 + c) as i64 + 1
                    };
                    *a = (oracle.sample)(n);
                }
            }
        }
        let x: Vec<_> = (0..columns)
            .map(|c| (oracle.sample)(if c < 2 { 3 } else { c as i64 - 9 }))
            .collect();
        let y: Vec<_> = (0..rows).map(|r| (oracle.sample)(r as i64 - 3)).collect();
        let mut forward = vec![oracle.zero.clone(); rows];
        let mut transpose = vec![oracle.zero.clone(); columns];
        let mut bilinear_expected = oracle.zero.clone();
        for r in 0..rows {
            for c in 0..columns {
                let ax = (oracle.mul)(&dense[r][c], &x[c]);
                forward[r] = (oracle.add)(&forward[r], &ax);
                transpose[c] = (oracle.add)(&transpose[c], &(oracle.mul)(&dense[r][c], &y[r]));
                bilinear_expected = (oracle.add)(&bilinear_expected, &(oracle.mul)(&y[r], &ax));
            }
        }
        let encode = |v: &[M]| v.iter().map(oracle.encode).collect::<Vec<_>>();
        let entries: Vec<_> = dense
            .iter()
            .enumerate()
            .flat_map(|(r, row)| {
                row.iter().enumerate().filter_map(move |(c, a)| {
                    let a = (oracle.encode)(a);
                    (a != S::zero()).then_some((r as u32, c as u32, a))
                })
            })
            .collect();
        let m = from_entries(rows, columns, &entries, &p).unwrap();
        let alias = m.clone();
        let (x, y) = (encode(&x), encode(&y));
        let (saved_x, saved_y) = (x.clone(), y.clone());
        for (transposed, input, expected) in [
            (false, &x, encode(&forward)),
            (true, &y, encode(&transpose)),
        ] {
            let exact = size(expected.len(), std::mem::size_of::<S>()).unwrap();
            assert_eq!(mul(&m, input, transposed, &p, exact).unwrap(), expected);
            assert_eq!(
                mul(&m, input, transposed, &p, exact - 1).unwrap_err().code,
                "exhausted:output-bytes"
            );
            let mut bad = input.clone();
            bad.push(S::zero());
            assert_eq!(
                mul(&m, &bad, transposed, &p, 0).unwrap_err().code,
                "refused:matrix-shape"
            );
        }
        assert_eq!(
            bilinear(&m, &y, &x).unwrap(),
            (oracle.encode)(&bilinear_expected)
        );
        for (r, expected) in forward.iter().enumerate() {
            assert_eq!(row_dot(&m, &x, r).unwrap(), (oracle.encode)(expected));
        }
        for (c, expected) in transpose.iter().enumerate() {
            assert_eq!(column_dot(&m, &y, c).unwrap(), (oracle.encode)(expected));
        }
        assert_eq!(m.entries(), entries);
        assert_eq!(alias.entries().as_ptr(), m.entries().as_ptr());
        assert_eq!((x, y), (saved_x, saved_y));
    }
}

#[test]
fn signed_integer_dense_contractions_cover_prime_fields_and_modular_cancellation() {
    macro_rules! check {
        ($field:ty) => {
            contractions(Oracle {
                zero: 0i128,
                sample: i128::from,
                add: |a, b| a + b,
                mul: |a, b| a * b,
                // Negative integers encode representatives near the modulus,
                // exercising full-width coefficients and reduction.
                encode: |n| {
                    let v = <$field>::from(n.unsigned_abs() as u64);
                    if *n < 0 { -v } else { v }
                },
            });
        };
    }
    check!(crate::Scalar);
    check!(crate::Bn254Scalar);
    check!(crate::RistrettoScalar);
    contractions(Oracle {
        zero: 0i128,
        sample: i128::from,
        add: |a, b| a + b,
        mul: |a, b| a * b,
        encode: |n| crate::KoalaBear::new(n.rem_euclid(2_130_706_433) as u32),
    });
}

fn extension_sample<const N: usize>(n: i64) -> [u64; N] {
    std::array::from_fn(|i| (i128::from(n) * (i as i128 + 1)).rem_euclid(2_130_706_433) as u64)
}
fn extension_add<const N: usize>(a: &[u64; N], b: &[u64; N]) -> [u64; N] {
    std::array::from_fn(|i| (a[i] + b[i]) % 2_130_706_433)
}
fn extension_mul<const N: usize>(a: &[u64; N], b: &[u64; N]) -> [u64; N] {
    let mut out = [0; N];
    for i in 0..N {
        for j in 0..N {
            let term = u128::from(a[i]) * u128::from(b[j]) * if i + j >= N { 3 } else { 1 };
            out[(i + j) % N] = ((u128::from(out[(i + j) % N]) + term) % 2_130_706_433) as u64;
        }
    }
    out
}

#[test]
fn dense_extension_contractions_use_every_coordinate() {
    macro_rules! check {
        ($field:ty, $n:expr) => {
            contractions(Oracle {
                zero: [0; $n],
                sample: extension_sample::<$n>,
                add: extension_add::<$n>,
                mul: extension_mul::<$n>,
                encode: |a| {
                    <$field>::from_basis_coefficients_fn(|i| crate::KoalaBear::new(a[i] as u32))
                },
            });
        };
    }
    check!(crate::KoalaBearExt4, 4);
    check!(crate::KoalaBearExt8, 8);
}

/// Polynomial long division over GF(2), independent of provider multiplication.
fn binary_mul(a: u64, b: u64) -> u64 {
    let mut product = 0u128;
    for i in 0..64 {
        if b >> i & 1 != 0 {
            product ^= u128::from(a) << i;
        }
    }
    let modulus = (1u128 << 64) | 0x1b;
    for i in (64..128).rev() {
        if product >> i & 1 != 0 {
            product ^= modulus << (i - 64);
        }
    }
    product as u64
}

#[test]
fn characteristic_two_dense_contractions_include_high_bits_and_cubic_coordinates() {
    use zkc_kernels::plonky3::binary::ext3_from_bits;
    use zkc_kernels::plonky3::binary::from_bits;
    let sample = |n: i64| n.unsigned_abs().wrapping_mul(0x8000_0000_0000_001d);
    contractions(Oracle {
        zero: 0u64,
        sample,
        add: |a, b| a ^ b,
        mul: |a, b| binary_mul(*a, *b),
        encode: |a| from_bits(*a),
    });
    contractions(Oracle {
        zero: [0u64; 3],
        sample: |n| {
            let a = n.unsigned_abs().wrapping_mul(0x8000_0000_0000_001d);
            [a, a.rotate_left(13), a.rotate_left(41)]
        },
        add: |a, b| std::array::from_fn(|i| a[i] ^ b[i]),
        mul: |a, b| {
            let mut c = [0; 5];
            for i in 0..3 {
                for j in 0..3 {
                    c[i + j] ^= binary_mul(a[i], b[j]);
                }
            }
            [c[0] ^ c[3], c[1] ^ c[3] ^ c[4], c[2] ^ c[4]]
        },
        encode: |a| ext3_from_bits(*a),
    });
}

#[test]
fn canonical_coo_refusals_keep_order_before_contraction() {
    let p = Policy::default();
    let one = crate::Scalar::from(1);
    let zero = crate::Scalar::from(0);
    for (entries, error) in [
        (vec![(0, 0, one), (0, 0, -one)], "matrix-order"),
        (vec![(0, 0, one), (0, 0, zero)], "matrix-order"),
        (vec![(1, 0, one), (0, 0, one)], "matrix-order"),
        (vec![(0, 0, zero)], "matrix-zero"),
        (vec![(2, 0, zero)], "matrix-index"),
    ] {
        assert_eq!(
            from_entries(2, 2, &entries, &p).unwrap_err().code,
            format!("refused:{error}")
        );
    }
    let m = from_entries(2, 2, &[(0, 0, one)], &p).unwrap();
    for result in [
        row_dot(&m, &[], usize::MAX),
        column_dot(&m, &[], usize::MAX),
        bilinear(&m, &[], &[one, one]),
        bilinear(&m, &[one, one], &[]),
    ] {
        assert_eq!(result.unwrap_err().code, "refused:matrix-shape");
    }
    for result in [
        row_dot(&m, &[one, one], usize::MAX),
        column_dot(&m, &[one, one], usize::MAX),
    ] {
        assert_eq!(result.unwrap_err().code, "refused:matrix-index");
    }
}
