use super::*;
use crate::plonky3::{MODULUS, decode_quartic, encode_quartic};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use sha3::{Digest as _, Keccak256};

// Independent byte construction: do not call LeafHash, NodeHash or the leaf
// encoder when computing the expected digests.
fn leaf(width: usize, height: usize, coordinates: &[[u32; 4]]) -> Digest {
    let codec = b"koala-bear.ext4-binomial3.ascending-u32le/0";
    let mut hash = Keccak256::new();
    hash.update(b"zkc.oracle.keccak256.leaf/0\0");
    hash.update((codec.len() as u64).to_le_bytes());
    hash.update(codec);
    hash.update((width as u64).to_le_bytes());
    hash.update((height as u64).to_le_bytes());
    for word in coordinates.iter().flatten() {
        hash.update(word.to_le_bytes());
    }
    hash.finalize().into()
}

#[test]
fn quartic_codec_uses_exact_canonical_ascending_coordinates() {
    let coordinates = [1, 2, 3, MODULUS - 1];
    let value = KoalaBearExt4::from(coordinates.map(KoalaBear::new));
    let bytes: Vec<_> = coordinates
        .iter()
        .flat_map(|word| word.to_le_bytes())
        .collect();
    assert_eq!(encode_quartic(value).as_slice(), bytes);
    assert_eq!(decode_quartic(&bytes), Ok(value));
    let mut generic = Vec::new();
    super::super::words::encode_into(&value, super::super::words::Form::Canonical, &mut generic);
    assert_eq!(generic, bytes);
    for length in [0, 1, 4, 12, 15, 17, 32] {
        assert!(decode_quartic(&vec![0; length]).is_err());
    }
    for coordinate in 0..4 {
        for invalid in [MODULUS, MODULUS + 1, u32::MAX] {
            let mut malformed = bytes.clone();
            malformed[coordinate * 4..(coordinate + 1) * 4].copy_from_slice(&invalid.to_le_bytes());
            assert!(decode_quartic(&malformed).is_err());
            assert!(!super::super::words::valid_elements::<KoalaBearExt4>(
                &malformed
            ));
        }
    }
    let generator = KoalaBearExt4::from_basis_coefficients_fn(|i| {
        if i == 1 {
            KoalaBear::ONE
        } else {
            KoalaBear::ZERO
        }
    });
    assert_eq!(
        generator * generator * generator * generator,
        KoalaBearExt4::from_u32(3)
    );
}

#[test]
fn quartic_root_and_paths_match_independent_keccak_bytes() {
    for width in [1, 2, 7, 8, 16, 17] {
        let shape = Shape::new(width, 2, width * 2).unwrap();
        let coordinates: Vec<[u32; 4]> = (0..width * 2)
            .map(|i| std::array::from_fn(|j| (i * 19 + j * 7 + 1) as u32))
            .collect();
        let values: Vec<_> = coordinates
            .iter()
            .map(|words| KoalaBearExt4::from(words.map(KoalaBear::new)))
            .collect();
        let left = leaf(width, 2, &coordinates[..width]);
        let right = leaf(width, 2, &coordinates[width..]);
        let mut hash = Keccak256::new();
        hash.update(b"zkc.oracle.keccak256.node/0\0");
        hash.update(left);
        hash.update(right);
        let expected: Digest = hash.finalize().into();
        let (root, state) = commit(
            values,
            shape,
            shape.retained_bytes::<KoalaBearExt4>().unwrap(),
        )
        .unwrap();
        assert_eq!(root, expected);
        for (position, sibling) in [(0, right), (1, left)] {
            let (row, path) = state.open(position).unwrap();
            assert_eq!(path, vec![sibling]);
            assert_eq!(verify(root, shape, position, &row, &path), Ok(()));
        }
    }
}

#[test]
fn quartic_shape_and_element_codec_are_part_of_the_root() {
    let shape = Shape::new(1, 4, 16).unwrap();
    let (quartic, state) = commit(vec![KoalaBearExt4::ONE; 4], shape, 4096).unwrap();
    let (base, _) = commit(vec![KoalaBear::ONE; 4], shape, 4096).unwrap();
    let (octic, _) = commit(vec![Octic::ONE; 4], shape, 4096).unwrap();
    assert_ne!(quartic, base);
    assert_ne!(quartic, octic);
    let (row, path) = state.open(0).unwrap();
    assert_eq!(
        verify(base, shape, 0, &row, &path),
        Err(Error::Authentication)
    );
    assert_eq!(
        verify(octic, shape, 0, &row, &path),
        Err(Error::Authentication)
    );
    assert_eq!(
        verify(quartic, Shape::new(1, 3, 16).unwrap(), 0, &row, &path),
        Err(Error::Authentication)
    );
    assert!(matches!(
        commit(
            vec![KoalaBearExt4::ONE; 4],
            shape,
            shape.retained_bytes::<KoalaBearExt4>().unwrap() - 1
        ),
        Err(Error::ByteLimit)
    ));
}
