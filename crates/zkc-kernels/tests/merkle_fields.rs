//! Explicit field profiles; these tests do not assert whole-system compatibility.
use p3_commit::Mmcs;
use p3_field::{BasedVectorSpace, Field, PackedValue, PrimeCharacteristicRing, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;
use p3_symmetric::Permutation;
use poseidon2::{baby_bear, goldilocks};
use zkc_kernels::{
    cpu::CpuExecution,
    plonky3::{
        BabyBear, BabyBearExt4, Goldilocks, GoldilocksExt2, KoalaBear, KoalaBearExt4,
        merkle::{self, DecodeError, DigestWord, Error, Instance, poseidon2},
        oracle::Shape,
        residue::{PrimeWord, Residue},
    },
};

#[test]
fn baby_bear_permutation_matches_the_pinned_upstream_answer() {
    // p3-baby-bear 0.8.0: test_default_babybear_poseidon2_width_16.
    // https://github.com/Plonky3/Plonky3/blob/a21e3ed42905040ad49c519e402f018381c12d0c/baby-bear/src/poseidon2.rs#L599-L616
    let mut state = BabyBear::new_array([
        894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
        19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913,
    ]);
    let expected = BabyBear::new_array([
        516096821, 90309867, 1101817252, 1660784290, 360715097, 1789519026, 1788910906, 563338433,
        319524748, 1741414159, 1650859320, 894311162, 1121347488, 1692793758, 1052633829,
        1344246938,
    ]);
    baby_bear::permutation().permute_mut(&mut state);
    assert_eq!(state, expected);
}

#[test]
fn goldilocks_permutation_matches_the_pinned_upstream_answer() {
    // p3-goldilocks 0.8.0: test_default_goldilocks_poseidon2_width_8.
    // https://github.com/Plonky3/Plonky3/blob/a21e3ed42905040ad49c519e402f018381c12d0c/goldilocks/src/poseidon2.rs#L1235-L1253
    let mut state = Goldilocks::new_array([0, 1, 2, 3, 4, 5, 6, 7]);
    let expected = Goldilocks::new_array([
        0x020cf04a1b214d14,
        0x84e14aaaeacaed25,
        0x1ae0f640e81c7457,
        0xa4d204cbaeb0d8a5,
        0x0cf637b627b3a7ff,
        0x788d304d948b486b,
        0x7327133ea1949af4,
        0xf415abb924da395b,
    ]);
    goldilocks::permutation().permute_mut(&mut state);
    assert_eq!(state, expected);
}

fn distinct_states<B, P, const WIDTH: usize>(permutation: &P)
where
    B: Field,
    P: Permutation<[B; WIDTH]> + Permutation<[B::Packing; WIDTH]>,
{
    let input = |lane: usize| -> [B; WIDTH] {
        std::array::from_fn(|i| B::from_usize(1 + i * 7 + lane * 97))
    };
    let expected: Vec<[B; WIDTH]> = (0..B::Packing::WIDTH + 2)
        .map(|lane| permutation.permute(input(lane)))
        .collect();
    for pair in expected.windows(2) {
        assert_ne!(pair[0], pair[1]);
    }
    // Different states in every lane detect accidental broadcast/reordering.
    for start in [0, 1, 2] {
        let mut packed: [B::Packing; WIDTH] =
            std::array::from_fn(|i| B::Packing::from_fn(|lane| input(start + lane)[i]));
        permutation.permute_mut(&mut packed);
        for lane in 0..B::Packing::WIDTH {
            let actual: [B; WIDTH] = std::array::from_fn(|i| packed[i].as_slice()[lane]);
            assert_eq!(actual, expected[start + lane]);
        }
    }
}

#[test]
fn packed_permutations_preserve_distinct_ordered_states() {
    distinct_states::<BabyBear, _, 16>(baby_bear::permutation());
    distinct_states::<Goldilocks, _, 8>(goldilocks::permutation());
}

// Independent scalar composition: no installed Hash, Compress, MMCS or digest
// encoder is used. Known-answer tests above pin the underlying permutation.
fn scalar_root<B, P, const WIDTH: usize, const RATE: usize, const WORDS: usize>(
    values: &[B],
    row_width: usize,
    word_bytes: usize,
    permutation: &P,
) -> Vec<u8>
where
    B: PrimeField64,
    P: Permutation<[B; WIDTH]>,
{
    assert_eq!(WIDTH, 2 * WORDS);
    let mut layer: Vec<[B; WORDS]> = values
        .chunks_exact(row_width)
        .map(|row| {
            let mut state = [B::ZERO; WIDTH];
            for block in row.chunks(RATE) {
                // Partial overwrite keeps the previous block's remaining words.
                state[..block.len()].copy_from_slice(block);
                permutation.permute_mut(&mut state);
            }
            std::array::from_fn(|i| state[i])
        })
        .collect();
    while layer.len() > 1 {
        // p3-merkle-tree 0.8.0 pads each odd layer with one default digest,
        // rather than completing the leaves to a power of two up front.
        if !layer.len().is_multiple_of(2) {
            layer.push([B::ZERO; WORDS]);
        }
        layer = layer
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| {
                let mut state = [B::ZERO; WIDTH];
                state[..WORDS].copy_from_slice(&pair[0]);
                state[WORDS..].copy_from_slice(&pair[1]);
                permutation.permute_mut(&mut state);
                std::array::from_fn(|i| state[i])
            })
            .collect();
    }
    layer[0]
        .iter()
        .flat_map(|word| word.as_canonical_u64().to_le_bytes()[..word_bytes].to_vec())
        .collect()
}

fn table<E: Residue>(width: usize, height: usize) -> Vec<E> {
    (0..width * height)
        .map(|i| {
            E::from_basis_coefficients_fn(|coordinate| {
                // Goldilocks exercises bits above both the 32-bit and f64 boundaries.
                let high = if E::Base::WORD_BYTES == 8 {
                    (1 << 63) + (1 << 53)
                } else {
                    0
                };
                E::Base::from_u64(high + (i * 17 + coordinate * 101 + 1) as u64)
            })
        })
        .collect()
}

fn exercise_tree<I>(values: Vec<I::Element>, shape: Shape) -> (Vec<u8>, merkle::Tree<I>)
where
    I: Instance,
    I::Element: Residue,
    <I::Mmcs as Mmcs<I::Element>>::Commitment: Send,
    <I::Mmcs as Mmcs<I::Element>>::ProverData<RowMajorMatrix<I::Element>>: Send,
{
    let bytes = merkle::retained_bytes::<I>(shape).unwrap();
    assert_eq!(
        bytes,
        shape.elements() * std::mem::size_of::<I::Element>()
            + (2 * shape.height().next_power_of_two() - 1) * I::DIGEST_BYTES
            + 256,
    );
    assert_eq!(
        merkle::commit::<I>(values.clone(), shape, bytes - 1).unwrap_err(),
        Error::ByteLimit,
    );
    assert_eq!(
        merkle::commit::<I>(values[..values.len() - 1].to_vec(), shape, bytes).unwrap_err(),
        Error::ValueCount,
    );
    let (root, tree) = merkle::commit::<I>(values.clone(), shape, bytes).unwrap();
    assert_eq!(root.len(), 32);
    assert!(I::valid_digests(&root));
    for at in 0..shape.height() {
        let (rows, proof) = merkle::open(&tree, &[at]).unwrap();
        assert_eq!(rows, values[at * shape.width()..(at + 1) * shape.width()]);
        assert_eq!(proof.len(), shape.depth() * I::DIGEST_BYTES);
        assert_eq!(
            merkle::verify::<I>(&root, shape, &[at], &rows, &proof),
            Ok(true)
        );
        if shape.height() > 1 {
            assert_eq!(
                merkle::verify::<I>(&root, shape, &[(at + 1) % shape.height()], &rows, &proof),
                Ok(false),
            );
        }
    }
    // Reverse order, duplicate positions, and all-leaf proofs.
    for at in [
        vec![shape.height() - 1, 0, shape.height() / 2, 0],
        (0..shape.height()).rev().chain([0, 0]).collect(),
    ] {
        let (rows, proof) = merkle::open(&tree, &at).unwrap();
        let expected: Vec<_> = at
            .iter()
            .flat_map(|&i| {
                values[i * shape.width()..(i + 1) * shape.width()]
                    .iter()
                    .copied()
            })
            .collect();
        assert_eq!(rows, expected);
        assert_eq!(
            merkle::verify::<I>(&root, shape, &at, &rows, &proof),
            Ok(true)
        );
        if shape.height() > 1 {
            let mut positions = at.clone();
            positions[0] = (positions[0] + 1) % shape.height();
            assert_eq!(
                merkle::verify::<I>(&root, shape, &positions, &rows, &proof),
                Ok(false)
            );
        }
        if shape.height().is_power_of_two() && at.len() >= shape.height() + 2 {
            assert!(proof.is_empty());
        }
        let mut changed = rows.clone();
        // Mutate the last coordinate, including a non-base extension coordinate.
        changed[0] += I::Element::from_basis_coefficients_fn(|i| {
            if i + 1 == I::Element::DIMENSION {
                <I::Element as Residue>::Base::ONE
            } else {
                <I::Element as Residue>::Base::ZERO
            }
        });
        assert_eq!(
            merkle::verify::<I>(&root, shape, &at, &changed, &proof),
            Ok(false)
        );
        assert_eq!(
            merkle::verify::<I>(&root, shape, &at, &rows[..rows.len() - 1], &proof),
            Ok(false)
        );
        assert_eq!(
            merkle::verify::<I>(&root[..31], shape, &at, &rows, &proof),
            Ok(false)
        );
        let mut changed_root = root.clone();
        changed_root[0] ^= 1;
        assert_eq!(
            merkle::verify::<I>(&changed_root, shape, &at, &rows, &proof),
            Ok(false)
        );
        let mut long = proof.clone();
        long.extend_from_slice(&root);
        assert_eq!(
            merkle::verify::<I>(&root, shape, &at, &rows, &long),
            Ok(false)
        );
        if !proof.is_empty() {
            assert_eq!(
                merkle::verify::<I>(&root, shape, &at, &rows, &proof[..proof.len() - 1]),
                Ok(false)
            );
            let mut changed = proof.clone();
            changed[0] ^= 1;
            assert_eq!(
                merkle::verify::<I>(&root, shape, &at, &rows, &changed),
                Ok(false)
            );
        }
    }
    assert_eq!(merkle::open(&tree, &[]).unwrap_err(), Error::Positions);
    assert_eq!(
        merkle::open(&tree, &[shape.height()]).unwrap_err(),
        Error::Coordinate
    );
    assert_eq!(
        merkle::verify::<I>(&root, shape, &[], &[], &[]),
        Err(Error::Positions)
    );
    assert_eq!(
        merkle::verify::<I>(&root, shape, &[shape.height()], &[], &[]),
        Err(Error::Coordinate)
    );
    (root, tree)
}

macro_rules! field_trees {
    ($name:ident, $base:ty, $extension:ty, $base_instance:ty, $extension_instance:ty,
        $width:literal, $rate:literal, $words:literal, $word_bytes:literal, $permutation:expr) => {
        #[test]
        fn $name() {
            let cpu = CpuExecution::serial().unwrap();
            cpu.enter(|| {
                for height in [1, 2, 3, 5, 8, 13, 32] {
                    for width in [1, 3, 5] {
                        let values = table::<$extension>(width, height);
                        let flat: Vec<$base> = values
                            .iter()
                            .flat_map(|value| value.as_basis_coefficients_slice().iter().copied())
                            .collect();
                        let base_width = width * <$extension as BasedVectorSpace<$base>>::DIMENSION;
                        let expected = scalar_root::<$base, _, $width, $rate, $words>(
                            &flat,
                            base_width,
                            $word_bytes,
                            $permutation,
                        );
                        let (root, base_tree) = exercise_tree::<$base_instance>(
                            flat,
                            Shape::new(base_width, height, 1 << 16).unwrap(),
                        );
                        assert_eq!(root, expected); // Compare every root byte.
                        let (extension_root, extension_tree) = exercise_tree::<$extension_instance>(
                            values,
                            Shape::new(width, height, 1 << 16).unwrap(),
                        );
                        assert_eq!(extension_root, root);
                        for at in [vec![0], vec![height - 1, 0, height / 2, 0]] {
                            let (base_rows, base_proof) = merkle::open(&base_tree, &at).unwrap();
                            let (extension_rows, extension_proof) =
                                merkle::open(&extension_tree, &at).unwrap();
                            let flattened: Vec<$base> = extension_rows
                                .iter()
                                .flat_map(|value| {
                                    value.as_basis_coefficients_slice().iter().copied()
                                })
                                .collect();
                            assert_eq!(base_rows, flattened);
                            assert_eq!(base_proof, extension_proof);
                        }
                    }
                }
            });
        }
    };
}
field_trees!(
    baby_bear_trees_and_flattening,
    BabyBear,
    BabyBearExt4,
    baby_bear::Base,
    baby_bear::Quartic,
    16,
    8,
    8,
    4,
    baby_bear::permutation()
);
field_trees!(
    goldilocks_trees_and_flattening,
    Goldilocks,
    GoldilocksExt2,
    goldilocks::Base,
    goldilocks::Quadratic,
    8,
    4,
    4,
    8,
    goldilocks::permutation()
);
// Keep the existing KoalaBear byte construction under the same independent
// scalar composition check without changing its profile or defaults.
field_trees!(
    koala_bear_roots_remain_unchanged,
    KoalaBear,
    KoalaBearExt4,
    poseidon2::Base,
    poseidon2::Quartic,
    16,
    8,
    8,
    4,
    zkc_kernels::plonky3::poseidon2::permutation()
);

fn digest_codec<B: PrimeField64 + DigestWord, const WORDS: usize>(word_bytes: usize) {
    let digests = [[B::ZERO; WORDS], [B::NEG_ONE; WORDS]];
    let bytes = merkle::encode_digests(&digests);
    assert_eq!(bytes.len(), 64);
    let expected: Vec<_> = [0, B::ORDER_U64 - 1]
        .into_iter()
        .flat_map(|word| (0..WORDS).flat_map(move |_| word.to_le_bytes()[..word_bytes].to_vec()))
        .collect();
    assert_eq!(bytes, expected);
    assert_eq!(merkle::decode_digests::<B, WORDS>(&bytes).unwrap(), digests);
    assert_eq!(merkle::decode_digests::<B, WORDS>(&[]), Ok(vec![]));
    for length in [1, 31, 33, 63] {
        assert_eq!(
            merkle::decode_digests::<B, WORDS>(&bytes[..length]),
            Err(DecodeError::Invalid)
        );
    }
    for word in [B::ORDER_U64, u64::MAX] {
        for offset in [0, 32 - word_bytes, 64 - word_bytes] {
            let mut invalid = bytes.clone();
            invalid[offset..offset + word_bytes].copy_from_slice(&word.to_le_bytes()[..word_bytes]);
            assert_eq!(
                merkle::decode_digests::<B, WORDS>(&invalid),
                Err(DecodeError::Invalid)
            );
        }
    }
}

fn invalid_digests<I: Instance>(modulus: &[u8]) {
    assert!(I::valid_digests(&[]));
    assert!(I::valid_digests(&[0; 32]));
    assert!(I::commitment(&[0; 32]).is_ok());
    assert!(I::proof(&[]).is_ok());
    for length in [0, 1, 31, 33, 64] {
        assert!(matches!(
            I::commitment(&vec![0; length]),
            Err(DecodeError::Invalid)
        ));
    }
    for length in [1, 31, 33] {
        assert!(!I::valid_digests(&vec![0; length]));
        assert!(matches!(
            I::proof(&vec![0; length]),
            Err(DecodeError::Invalid)
        ));
    }
    let mut invalid = vec![0; 32];
    invalid[32 - modulus.len()..].copy_from_slice(modulus);
    assert!(!I::valid_digests(&invalid));
    assert!(matches!(I::commitment(&invalid), Err(DecodeError::Invalid)));
    assert!(matches!(I::proof(&invalid), Err(DecodeError::Invalid)));
}

#[test]
fn digest_codecs_reject_noncanonical_words_and_ragged_lengths() {
    digest_codec::<BabyBear, 8>(4);
    digest_codec::<Goldilocks, 4>(8);
    let baby = 2_013_265_921u32.to_le_bytes();
    let gold = 18_446_744_069_414_584_321u64.to_le_bytes();
    invalid_digests::<baby_bear::Base>(&baby);
    invalid_digests::<baby_bear::Quartic>(&baby);
    invalid_digests::<goldilocks::Base>(&gold);
    invalid_digests::<goldilocks::Quadratic>(&gold);
}

type Opening<E> = (Vec<E>, Vec<u8>);

fn worker_receipt<I>(workers: usize) -> (Vec<u8>, Vec<Opening<I::Element>>)
where
    I: Instance,
    I::Element: Residue,
    <I::Mmcs as Mmcs<I::Element>>::Commitment: Send,
    <I::Mmcs as Mmcs<I::Element>>::ProverData<RowMajorMatrix<I::Element>>: Send,
{
    CpuExecution::new(workers).unwrap().enter(|| {
        let shape = Shape::new(5, 1025, 1 << 16).unwrap();
        let (root, tree) =
            merkle::commit::<I>(table::<I::Element>(5, 1025), shape, 1 << 24).unwrap();
        let openings = [vec![0], vec![512], vec![1024], vec![1024, 1, 511, 511, 0]]
            .into_iter()
            .map(|at| {
                let (rows, proof) = merkle::open(&tree, &at).unwrap();
                assert_eq!(
                    merkle::verify::<I>(&root, shape, &at, &rows, &proof),
                    Ok(true)
                );
                (rows, proof)
            })
            .collect();
        (root, openings)
    })
}

#[test]
fn workers_preserve_complete_roots_rows_and_single_and_multi_proofs() {
    macro_rules! equal_workers {
        ($instance:ty) => {
            let expected = worker_receipt::<$instance>(1);
            for workers in [1, 2, 4]
                .into_iter()
                .filter(|&n| cfg!(feature = "parallel") || n == 1)
            {
                assert_eq!(worker_receipt::<$instance>(workers), expected);
            }
        };
    }
    equal_workers!(baby_bear::Base);
    equal_workers!(baby_bear::Quartic);
    equal_workers!(goldilocks::Base);
    equal_workers!(goldilocks::Quadratic);
}

#[cfg(feature = "test-utils")]
#[test]
fn decoding_exhaustion_remains_distinct_from_false_openings() {
    fn check<I>()
    where
        I: Instance,
        I::Element: Residue,
        <I::Mmcs as Mmcs<I::Element>>::Commitment: Send,
        <I::Mmcs as Mmcs<I::Element>>::ProverData<RowMajorMatrix<I::Element>>: Send,
    {
        let shape = Shape::new(2, 8, 16).unwrap();
        let (root, tree) = merkle::commit::<I>(table::<I::Element>(2, 8), shape, 1 << 20).unwrap();
        let (rows, proof) = merkle::open(&tree, &[1]).unwrap();
        for successful in [0, 1] {
            let _guard = zkc_kernels::allocation::failure::after(successful);
            assert_eq!(
                merkle::verify::<I>(&root, shape, &[1], &rows, &proof),
                Err(Error::Allocation)
            );
        }
        assert_eq!(
            merkle::verify::<I>(&root, shape, &[1], &rows, &proof),
            Ok(true)
        );
    }
    check::<baby_bear::Base>();
    check::<baby_bear::Quartic>();
    check::<goldilocks::Base>();
    check::<goldilocks::Quadratic>();
}
