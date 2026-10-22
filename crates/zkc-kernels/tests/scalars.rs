//! Canonical scalar admission agrees with checked decode plus exact re-encoding.
use ark_ff::{BigInteger, PrimeField};
use ark_std::rand::{RngCore, SeedableRng, rngs::StdRng};
use zkc_kernels::Error;

fn check<F: PrimeField>(decode: fn(&[u8]) -> Result<F, Error>) {
    let modulus = F::MODULUS.to_bytes_le();
    let compare = |bytes: &[u8]| {
        // Independent wire predicate: fixed width and the unsigned integer < p.
        let canonical = bytes.len() == 32 && bytes.iter().rev().cmp(modulus.iter().rev()).is_lt();
        assert_eq!(decode(bytes).is_ok(), canonical, "{bytes:x?}");
        let mut input = bytes;
        let expected = F::deserialize_compressed(&mut input)
            .map_err(|_| Error::InvalidEncoding)
            .and_then(|value| {
                if !input.is_empty() {
                    return Err(Error::InvalidEncoding);
                }
                let mut canonical = Vec::new();
                value.serialize_compressed(&mut canonical).unwrap();
                if canonical != bytes {
                    return Err(Error::NonCanonicalEncoding);
                }
                Ok(value)
            });
        assert_eq!(decode(bytes), expected, "{bytes:x?}");
    };
    for value in [F::from(0), F::from(1), -F::from(1), F::from(u64::MAX)] {
        let mut bytes = Vec::new();
        value.serialize_compressed(&mut bytes).unwrap();
        assert_eq!(decode(&bytes).unwrap(), value);
        for end in 0..bytes.len() {
            compare(&bytes[..end]);
        }
        compare(&bytes);
        bytes.push(0);
        compare(&bytes);
    }
    assert_eq!(decode(&modulus), Err(Error::InvalidEncoding));
    compare(&modulus);
    let mut above = F::MODULUS;
    above.add_with_carry(&F::BigInt::from(1u64));
    compare(&above.to_bytes_le());
    compare(&[255; 32]);
    for bit in 0..256 {
        let mut bytes = [0; 32];
        bytes[bit / 8] = 1 << (bit % 8);
        compare(&bytes);
    }
    let mut rng = StdRng::seed_from_u64(0x5343414c4152);
    for _ in 0..1024 {
        let mut bytes = [0; 32];
        rng.fill_bytes(&mut bytes);
        compare(&bytes);
    }
}

#[test]
fn both_scalar_fields_preserve_exact_canonical_admission() {
    check(zkc_kernels::decode_scalar);
    check(zkc_kernels::bn254::decode_scalar);
}
