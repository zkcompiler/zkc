//! Exact scalar ingress and independent high-half-first table semantics.
mod common;
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
use ark_std::{
    UniformRand,
    rand::{SeedableRng, rngs::StdRng},
};
use common::{bounds, scalars};
use zkc_arkworks::{Bounds, Error, Scalar, Table, decode_scalar, encode_scalar, parse_decimal};

// Independent maintained high-half semantics: split logical halves recursively,
// rather than using bit reversal or the adapter's adjacent-pair loop.
fn logical_eval(values: &[Scalar], point: &[Scalar]) -> Scalar {
    if point.is_empty() {
        return values[0];
    }
    let (lo, hi) = values.split_at(values.len() / 2);
    (Scalar::ONE - point[0]) * logical_eval(lo, &point[1..])
        + point[0] * logical_eval(hi, &point[1..])
}

fn logical_restrict(values: &[Scalar], r: Scalar) -> Vec<Scalar> {
    let (lo, hi) = values.split_at(values.len() / 2);
    lo.iter()
        .zip(hi)
        .map(|(a, b)| *a * (Scalar::ONE - r) + *b * r)
        .collect()
}

#[test]
fn scalar_codec_is_exact_and_does_not_reduce() {
    let modulus = Scalar::MODULUS.to_bytes_le();
    for value in [
        Scalar::ZERO,
        Scalar::ONE,
        -Scalar::ONE,
        Scalar::from(1234u64),
    ] {
        let bytes = encode_scalar(&value).unwrap();
        assert_eq!(decode_scalar(&bytes).unwrap(), value);
        assert_eq!(parse_decimal(&value.to_string()).unwrap(), value);
        for end in 0..bytes.len() {
            assert!(decode_scalar(&bytes[..end]).is_err());
        }
        let mut trailing = bytes.to_vec();
        trailing.push(0);
        assert_eq!(decode_scalar(&trailing), Err(Error::InvalidEncoding));
    }
    assert_eq!(decode_scalar(&modulus), Err(Error::InvalidEncoding));
    assert_eq!(decode_scalar(&[255; 32]), Err(Error::InvalidEncoding));
    for invalid in [
        "",
        "00",
        "01",
        "+1",
        "-1",
        " 1",
        "1 ",
        "1\n",
        "1.0",
        "0x01",
        "１",
        "52435875175126190479447740508185965837690552500527637822603658699938581184513",
        "52435875175126190479447740508185965837690552500527637822603658699938581184514",
    ] {
        assert_eq!(
            parse_decimal(invalid),
            Err(Error::InvalidEncoding),
            "{invalid:?}"
        );
    }
    assert!(parse_decimal(&"9".repeat(10000)).is_err());
    assert_eq!(parse_decimal("0").unwrap(), Scalar::ZERO);
    assert_eq!(
        parse_decimal(
            "52435875175126190479447740508185965837690552500527637822603658699938581184512"
        )
        .unwrap(),
        -Scalar::ONE
    );
}

#[test]
fn malformed_table_ingress_and_explicit_limits() {
    for length in [0, 3, 5, 6, 7, 9] {
        assert_eq!(
            Table::from_logical(&vec![Scalar::ZERO; length], &bounds()).unwrap_err(),
            Error::InvalidTableLength
        );
    }
    let values = scalars(&[1, 2, 3, 4]);
    assert_eq!(
        Table::from_logical(&values, &Bounds::new(1, 4, 128, 10)).unwrap_err(),
        Error::ArityLimit
    );
    assert_eq!(
        Table::from_logical_vec(values.clone(), &Bounds::new(2, 3, 128, 10)).unwrap_err(),
        Error::ElementLimit
    );
    let t = Table::from_logical(&values, &bounds()).unwrap();
    let bytes = t.to_logical_bytes(&bounds()).unwrap();
    for cut in 0..bytes.len() {
        assert!(Table::from_logical_bytes(2, &bytes[..cut], &bounds()).is_err());
    }
    assert_eq!(
        Table::from_logical_bytes(2, &bytes, &Bounds::new(2, 4, 127, 10)).unwrap_err(),
        Error::ByteLimit
    );
    let all = Bounds::new(usize::MAX, usize::MAX, usize::MAX, usize::MAX);
    for n in [usize::BITS as usize, usize::MAX] {
        assert_eq!(
            Table::from_logical_bytes(n, &[], &all).unwrap_err(),
            Error::CapacityOverflow
        );
    }
    let mut bad = bytes.clone();
    bad[32..64].copy_from_slice(&Scalar::MODULUS.to_bytes_le());
    assert!(Table::from_logical_bytes(2, &bad, &bounds()).is_err());
    assert!(Table::from_logical_bytes(1, &bytes, &bounds()).is_err());
    let mut extra = bytes.clone();
    extra.push(0);
    assert!(Table::from_logical_bytes(2, &extra, &bounds()).is_err());
    assert_eq!(
        t.to_logical_bytes(&Bounds::new(10, 1024, 127, 100))
            .unwrap_err(),
        Error::ByteLimit
    );
    assert_eq!(t.logical_values().unwrap(), values);
}

#[test]
fn zero_variable_tables_are_first_class() {
    let t = Table::from_logical(&scalars(&[7]), &bounds()).unwrap();
    assert_eq!((t.arity(), t.len(), t.is_empty()), (0, 1, false));
    assert_eq!(t.evaluate(&[]).unwrap(), Scalar::from(7u64));
    assert_eq!(t.scalar_at_zero_arity().unwrap(), Scalar::from(7u64));
    assert_eq!(t.product_boolean_sum(&t).unwrap(), Scalar::from(49u64));
    assert_eq!(
        t.restrict_first(Scalar::ONE).unwrap_err(),
        Error::PositiveArityRequired
    );
    assert_eq!(t.round_product(&t), Err(Error::PositiveArityRequired));
    let bytes = t.to_logical_bytes(&bounds()).unwrap();
    assert_eq!(
        Table::from_logical_bytes(0, &bytes, &bounds())
            .unwrap()
            .logical_values()
            .unwrap(),
        scalars(&[7])
    );
    assert!(t.evaluate(&[Scalar::ZERO]).is_err());
}

#[test]
fn property_coordinates_rounds_and_custody() {
    let mut rng = StdRng::from_seed([83; 32]);
    for n in 0..=8 {
        for _ in 0..8 {
            let a: Vec<_> = (0..1usize << n).map(|_| Scalar::rand(&mut rng)).collect();
            let b: Vec<_> = (0..1usize << n).map(|_| Scalar::rand(&mut rng)).collect();
            let point: Vec<_> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
            let original = Table::from_logical(&a, &bounds()).unwrap();
            let alias = original.clone();
            let mut ta = original.clone();
            let mut tb = Table::from_logical_vec(b.clone(), &bounds()).unwrap();
            assert_eq!(original.logical_values().unwrap(), a);
            assert_eq!(original.evaluate(&point).unwrap(), logical_eval(&a, &point));
            let mut la = a.clone();
            let mut lb = b.clone();
            let mut claim: Scalar = a.iter().zip(&b).map(|(x, y)| *x * y).sum();
            assert_eq!(ta.product_boolean_sum(&tb).unwrap(), claim);
            for r in &point {
                let q = ta.round_product(&tb).unwrap();
                assert_eq!(q[0] + q[0] + q[1] + q[2], claim);
                // Compare the entire round polynomial at three independent points.
                for x in [Scalar::ZERO, Scalar::ONE, Scalar::from(2u64)] {
                    let ra = logical_restrict(&la, x);
                    let rb = logical_restrict(&lb, x);
                    let expected: Scalar = ra.iter().zip(&rb).map(|(u, v)| *u * v).sum();
                    assert_eq!(q[0] + x * (q[1] + x * q[2]), expected);
                }
                la = logical_restrict(&la, *r);
                lb = logical_restrict(&lb, *r);
                ta = ta.restrict_first(*r).unwrap();
                tb = tb.restrict_first(*r).unwrap();
                assert_eq!(ta.logical_values().unwrap(), la);
                assert_eq!(tb.logical_values().unwrap(), lb);
                claim = q[0] + *r * (q[1] + *r * q[2]);
            }
            assert_eq!(ta.scalar_at_zero_arity().unwrap(), logical_eval(&a, &point));
            assert_eq!(
                claim,
                ta.scalar_at_zero_arity().unwrap() * tb.scalar_at_zero_arity().unwrap()
            );
            assert_eq!(alias.logical_values().unwrap(), a);
            assert_eq!(original.logical_values().unwrap(), a);
        }
    }
}

#[test]
fn kernel_shapes_and_product_of_extensions() {
    let a = Table::from_logical(&scalars(&[0, 1]), &bounds()).unwrap();
    let b = Table::from_logical(&scalars(&[0, 1, 2, 3]), &bounds()).unwrap();
    assert!(a.round_product(&b).is_err());
    assert!(a.product_boolean_sum(&b).is_err());
    assert!(a.evaluate(&[]).is_err());
    assert!(a.evaluate(&scalars(&[1, 2])).is_err());
    assert_eq!(a.scalar_at_zero_arity(), Err(Error::ZeroArityRequired));
    assert_eq!(
        a.round_product(&a).unwrap(),
        [Scalar::ZERO, Scalar::ZERO, Scalar::ONE]
    );
    let value = a.evaluate(&scalars(&[2])).unwrap();
    assert_eq!(value * value, Scalar::from(4u64));
    assert_ne!(value * value, value); // Interpolating the product table would give 2.
}

#[test]
fn every_boolean_vertex_and_non_symmetric_order() {
    let values = scalars(&[2, 3, 5, 7, 11, 13, 17, 19]);
    let table = Table::from_logical(&values, &bounds()).unwrap();
    for (i, value) in values.iter().enumerate() {
        let point: Vec<_> = (0..3)
            .map(|bit| Scalar::from(((i >> (2 - bit)) & 1) as u64))
            .collect();
        assert_eq!(table.evaluate(&point).unwrap(), *value);
    }
    assert_eq!(
        table
            .restrict_first(Scalar::ZERO)
            .unwrap()
            .logical_values()
            .unwrap(),
        values[..4]
    );
    assert_eq!(
        table
            .restrict_first(Scalar::ONE)
            .unwrap()
            .logical_values()
            .unwrap(),
        values[4..]
    );
    let p = scalars(&[2, 3, 4]);
    let mut reversed = p.clone();
    reversed.reverse();
    assert_ne!(
        table.evaluate(&p).unwrap(),
        table.evaluate(&reversed).unwrap()
    );
}

#[test]
fn admission_can_exceed_the_old_finite_runtime_rank_limit() {
    // The older runtime fixes MAX_RANK=12. This crate's table semantics do not.
    let bounds = Bounds::new(13, 8192, 8192 * 32, 0);
    let logical: Vec<_> = (0..8192u64).map(Scalar::from).collect();
    let table = Table::from_logical(&logical, &bounds).unwrap();
    assert_eq!(table.arity(), 13);
    assert_eq!(table.logical_values().unwrap(), logical);
    assert_eq!(
        table.evaluate(&[Scalar::ONE; 13]).unwrap(),
        Scalar::from(8191u64)
    );
    let bytes = table.to_logical_bytes(&bounds).unwrap();
    assert_eq!(
        Table::from_logical_bytes(13, &bytes, &bounds)
            .unwrap()
            .logical_values()
            .unwrap(),
        logical
    );
}
