//! The Poseidon2 row-commitment kernels against Plonky3 0.8.0's
//! `MerkleTreeMmcs` and `PrunedMerklePaths`, constructed directly here with
//! scalar types, and against a reference model written from the scheme's
//! definition in docs/spec/domains/oracles.md. The reference makes every
//! permutation call explicit: one call per absorbed leaf block, one per
//! compression. Quartic-extension rows are compared with Plonky3's
//! `ExtensionMmcs` over the same scalar tree. These are deterministic
//! agreement checks with the pinned upstream layout; they establish nothing
//! about collision resistance, binding or extraction.
#[path = "domains/support.rs"]
mod support;

use p3_commit::{ExtensionMmcs, Mmcs};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_matrix::{Dimensions, dense::RowMajorMatrix};
use p3_merkle_tree::{MerkleTreeMmcs, PrunedMerklePaths};
use p3_symmetric::{PaddingFreeSponge, Permutation, TruncatedPermutation};
use std::collections::BTreeSet;
use support::{backend, one};
use zkc_native::{KoalaBearExt4, Policy, Value};
use zkc_runtime::vm::{OperationBinding, Value as RuntimeValue};

type Perm = Poseidon2KoalaBear<16>;
type Upstream = MerkleTreeMmcs<
    KoalaBear,
    KoalaBear,
    PaddingFreeSponge<Perm, 16, 8, 8>,
    TruncatedPermutation<Perm, 2, 8, 16>,
    2,
    8,
>;
type Digest = [u32; 8];
/// A tampering class: its name, the supplied proof digests, rows and root.
type Tampered = (&'static str, Vec<Digest>, Vec<Vec<u32>>, Digest);
const SCHEME: &str = "rows.merkle-poseidon2-16.koala-bear/0";
const QUARTIC: &str = "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0";
type UpstreamQuartic = ExtensionMmcs<KoalaBear, KoalaBearExt4, Upstream>;

fn upstream() -> Upstream {
    Upstream::new(
        PaddingFreeSponge::new(default_koalabear_poseidon2_16()),
        TruncatedPermutation::new(default_koalabear_poseidon2_16()),
        0,
    )
}

/// Reference model. Every call to `permute` is one permutation call that a
/// verifier makes; nothing is batched or skipped.
struct Reference {
    calls: usize,
}
impl Reference {
    fn permute(&mut self, state: [u32; 16]) -> [u32; 16] {
        self.calls += 1;
        let mut state = state.map(KoalaBear::new);
        default_koalabear_poseidon2_16().permute_mut(&mut state);
        state.map(|x| x.as_canonical_u32())
    }
    /// Overwrite sponge: each block of up to eight elements overwrites the
    /// state's first positions, then one permutation; output the first eight.
    fn leaf(&mut self, row: &[u32]) -> Digest {
        assert!(!row.is_empty());
        let mut state = [0u32; 16];
        for block in row.chunks(8) {
            state[..block.len()].copy_from_slice(block);
            state = self.permute(state);
        }
        state[..8].try_into().unwrap()
    }
    /// Truncated permutation: the first eight elements of P(left || right).
    fn node(&mut self, left: Digest, right: Digest) -> Digest {
        let mut state = [0u32; 16];
        state[..8].copy_from_slice(&left);
        state[8..].copy_from_slice(&right);
        self.permute(state)[..8].try_into().unwrap()
    }
    /// Layer 0 holds one leaf digest per row, then zero digests up to an even
    /// length; every later layer compresses adjacent pairs and pads the same
    /// way, until one digest remains. Padding digests are not hash outputs.
    fn layers(&mut self, rows: &[Vec<u32>]) -> Vec<Vec<Digest>> {
        let pad = |mut layer: Vec<Digest>| {
            if layer.len() > 1 && layer.len() % 2 == 1 {
                layer.push([0; 8]);
            }
            layer
        };
        let mut layers = vec![pad(rows.iter().map(|r| self.leaf(r)).collect())];
        while layers.last().unwrap().len() > 1 {
            let previous = layers.last().unwrap().clone();
            let next = previous
                .chunks(2)
                .map(|pair| self.node(pair[0], pair[1]))
                .collect();
            layers.push(pad(next));
        }
        layers
    }
    /// Boundary digests of the distinct queried leaves: level by level from the
    /// leaves, parents ascending, and in each parent the child positions that
    /// cover no queried leaf, ascending.
    fn frontier(layers: &[Vec<Digest>], queries: &[usize]) -> Vec<Digest> {
        let mut nodes: BTreeSet<usize> = queries.iter().copied().collect();
        let mut out = Vec::new();
        for layer in &layers[..layers.len() - 1] {
            let parents: BTreeSet<usize> = nodes.iter().map(|n| n / 2).collect();
            for parent in &parents {
                for child in [2 * parent, 2 * parent + 1] {
                    if !nodes.contains(&child) {
                        out.push(layer[child]);
                    }
                }
            }
            nodes = parents;
        }
        out
    }
}

fn bytes(digests: &[Digest]) -> Vec<u8> {
    digests
        .iter()
        .flatten()
        .flat_map(|w| w.to_le_bytes())
        .collect()
}
fn words(digests: &[[KoalaBear; 8]]) -> Vec<Digest> {
    digests
        .iter()
        .map(|d| d.map(|x| x.as_canonical_u32()))
        .collect()
}
fn binding(scheme: &str, name: &str) -> OperationBinding {
    OperationBinding {
        contract: name.into(),
        arguments: vec![scheme.into()],
        implementation: format!("plonky3/{name}"),
        physical_arguments: vec![],
    }
}
fn kernel_in(scheme: &str, name: &str, args: Vec<Value>) -> Result<Vec<Value>, String> {
    one(backend(Policy::default()), binding(scheme, name), &[], args).0
}
fn kernel(name: &str, args: Vec<Value>) -> Result<Vec<Value>, String> {
    kernel_in(SCHEME, name, args)
}
fn vector(values: &[u32]) -> Value {
    Value::KoalaBearVector(
        values
            .iter()
            .map(|x| KoalaBear::new(*x))
            .collect::<Vec<_>>()
            .into(),
    )
}
fn quartic(coordinates: [u32; 4]) -> KoalaBearExt4 {
    KoalaBearExt4::from(coordinates.map(KoalaBear::new))
}
fn quartic_vector(values: &[KoalaBearExt4]) -> Value {
    Value::koala_bear_ext4_vector(values, &Policy::default()).unwrap()
}
fn indices(values: &[usize]) -> Value {
    Value::Indices(values.iter().map(|x| *x as u64).collect::<Vec<_>>().into())
}
fn digest_bytes(value: &Value) -> Vec<u8> {
    match value {
        Value::MerkleDigest(_, d) | Value::MerkleProof(_, d) => d.to_vec(),
        other => panic!("not a digest carrier: {other:?}"),
    }
}

struct Case {
    width: usize,
    height: usize,
    queries: Vec<usize>,
}

fn cases() -> Vec<Case> {
    let mut out = Vec::new();
    for height in [1, 2, 3, 5, 8, 13, 16, 31, 64] {
        for width in [1, 7, 8, 9, 17] {
            let last = height - 1;
            for queries in [
                vec![0],
                vec![last],
                vec![last, 0, last / 2, last],
                (0..height).step_by(3).collect(),
                (0..height).rev().collect(),
            ] {
                out.push(Case {
                    width,
                    height,
                    queries,
                });
            }
        }
    }
    out
}

#[test]
fn kernel_upstream_and_reference_agree_on_roots_rows_and_pruned_proofs() {
    let upstream = upstream();
    for case in cases() {
        let Case {
            width,
            height,
            ref queries,
        } = case;
        let table: Vec<u32> = (0..width * height)
            .map(|i| (i as u32).wrapping_mul(2_654_435_761) % 2_130_706_433)
            .collect();
        let rows: Vec<Vec<u32>> = table.chunks(width).map(|r| r.to_vec()).collect();
        // Reference.
        let mut reference = Reference { calls: 0 };
        let layers = reference.layers(&rows);
        let root = *layers.last().unwrap().first().unwrap();
        let frontier = Reference::frontier(&layers, queries);
        // Upstream, called as a Plonky3 configuration would.
        let matrix = RowMajorMatrix::new(table.iter().map(|x| KoalaBear::new(*x)).collect(), width);
        let (cap, data) = upstream.commit(vec![matrix]);
        let (opened, pruned) = upstream.open_multi_batch(queries, &data);
        assert_eq!(words(cap.roots()), [root]);
        assert_eq!(words(&pruned.sibling_hashes), frontier);
        // Kernels.
        let committed = kernel(
            "oracle.commit",
            vec![vector(&table), Value::Index(width as u64)],
        )
        .unwrap();
        assert_eq!(digest_bytes(&committed[0]), bytes(&[root]));
        let opening = kernel(
            "oracle.open_many",
            vec![committed[1].clone(), indices(queries)],
        )
        .unwrap();
        let expected_rows: Vec<u32> = queries.iter().flat_map(|q| rows[*q].clone()).collect();
        assert!(matches!(&opening[0], Value::KoalaBearVector(v)
            if v.iter().map(|x| x.as_canonical_u32()).eq(expected_rows.iter().copied())));
        assert_eq!(
            opened
                .iter()
                .flat_map(|o| o[0].iter().map(|x| x.as_canonical_u32()))
                .collect::<Vec<_>>(),
            expected_rows
        );
        assert_eq!(digest_bytes(&opening[1]), bytes(&frontier));
        let check = |root: Value, at: &[usize], rows: Value, proof: Value| {
            kernel(
                "oracle.check_many",
                vec![
                    root,
                    Value::Index(width as u64),
                    Value::Index(height as u64),
                    indices(at),
                    rows,
                    proof,
                ],
            )
        };
        let accepted = check(
            committed[0].clone(),
            queries,
            opening[0].clone(),
            opening[1].clone(),
        )
        .unwrap();
        assert!(matches!(accepted[..], [Value::Bool(true)]));
        let dims = [Dimensions { width, height }];
        let upstream_verify = |proof: &PrunedMerklePaths<KoalaBear, 8>,
                               rows: &[Vec<KoalaBear>],
                               at: &[usize]| {
            let opened: Vec<Vec<Vec<KoalaBear>>> = rows.iter().map(|r| vec![r.clone()]).collect();
            upstream
                .verify_multi_batch(&cap, &dims, at, &opened, proof)
                .is_ok()
        };
        let upstream_rows: Vec<Vec<KoalaBear>> = opened.iter().map(|o| o[0].clone()).collect();
        assert!(upstream_verify(&pruned, &upstream_rows, queries));
        // A single position's pruned proof is its complete path, as for `open`.
        if queries.len() == 1 {
            let single = kernel(
                "oracle.open",
                vec![committed[1].clone(), Value::Index(queries[0] as u64)],
            )
            .unwrap();
            assert_eq!(digest_bytes(&single[1]), bytes(&frontier));
            let checked = kernel(
                "oracle.check",
                vec![
                    committed[0].clone(),
                    Value::Index(width as u64),
                    Value::Index(height as u64),
                    Value::Index(queries[0] as u64),
                    single[0].clone(),
                    single[1].clone(),
                ],
            )
            .unwrap();
            assert!(matches!(checked[..], [Value::Bool(true)]));
        }
        // Each tampering class is rejected by both verifiers.
        let tampered: Vec<Tampered> = {
            let mut cases = Vec::new();
            let opened_rows: Vec<Vec<u32>> = queries.iter().map(|q| rows[*q].clone()).collect();
            if !frontier.is_empty() {
                cases.push((
                    "short",
                    frontier[..frontier.len() - 1].to_vec(),
                    opened_rows.clone(),
                    root,
                ));
                let mut changed = frontier.clone();
                changed[0][0] = (changed[0][0] + 1) % 2_130_706_433;
                cases.push(("sibling", changed, opened_rows.clone(), root));
            }
            let mut longer = frontier.clone();
            longer.push(root);
            cases.push(("long", longer, opened_rows.clone(), root));
            let mut other = root;
            other[7] = (other[7] + 1) % 2_130_706_433;
            cases.push(("root", frontier.clone(), opened_rows.clone(), other));
            let mut changed = opened_rows.clone();
            changed[0][0] = (changed[0][0] + 1) % 2_130_706_433;
            cases.push(("row", frontier.clone(), changed, root));
            if let Some(duplicate) =
                (1..queries.len()).find(|&i| queries[..i].contains(&queries[i]))
            {
                let mut inconsistent = opened_rows.clone();
                inconsistent[duplicate][width - 1] =
                    (inconsistent[duplicate][width - 1] + 1) % 2_130_706_433;
                cases.push(("duplicate", frontier.clone(), inconsistent, root));
            }
            cases
        };
        for (class, digests, opened_rows, root) in tampered {
            let flat: Vec<u32> = opened_rows.iter().flatten().copied().collect();
            let result = check(
                Value::MerkleDigest(committed_scheme(&committed[0]), bytes(&[root]).into()),
                queries,
                vector(&flat),
                Value::MerkleProof(committed_scheme(&committed[0]), bytes(&digests).into()),
            )
            .unwrap();
            assert!(
                matches!(result[..], [Value::Bool(false)]),
                "{class} {width}x{height} {queries:?}"
            );
            let proof = PrunedMerklePaths {
                sibling_hashes: digests.iter().map(|d| d.map(KoalaBear::new)).collect(),
            };
            let rows: Vec<Vec<KoalaBear>> = opened_rows
                .iter()
                .map(|r| r.iter().map(|x| KoalaBear::new(*x)).collect())
                .collect();
            let cap = p3_symmetric::MerkleCap::new(vec![root.map(KoalaBear::new)]);
            let opened: Vec<Vec<Vec<KoalaBear>>> = rows.iter().map(|r| vec![r.clone()]).collect();
            assert!(
                upstream
                    .verify_multi_batch(&cap, &dims, queries, &opened, &proof)
                    .is_err(),
                "{class}"
            );
        }
        // Positions are verifier inputs: one at the height refuses, while
        // upstream reports an out-of-bounds error.
        let refused = check(
            committed[0].clone(),
            &[height],
            vector(&rows[0]),
            opening[1].clone(),
        )
        .unwrap_err();
        assert!(refused.contains("oracle-coordinate"), "{refused}");
        assert!(
            upstream
                .verify_multi_batch(
                    &cap,
                    &dims,
                    &[height],
                    &[vec![upstream_rows[0].clone()]],
                    &pruned
                )
                .is_err()
        );
    }
}

fn committed_scheme(value: &Value) -> zkc_native::merkle::Scheme {
    match value {
        Value::MerkleDigest(scheme, _) => *scheme,
        other => panic!("not a root: {other:?}"),
    }
}

#[test]
fn quartic_rows_hash_their_ascending_base_coordinates() {
    let upstream = UpstreamQuartic::new(upstream());
    for (width, height, queries) in [
        (1, 1, vec![0]),
        (2, 5, vec![4, 0, 2, 2]),
        (3, 16, vec![15, 1, 2, 9]),
        (5, 13, (0..13).rev().collect::<Vec<_>>()),
    ] {
        let table: Vec<[u32; 4]> = (0..width * height)
            .map(|i| {
                std::array::from_fn(|j| {
                    ((4 * i + j) as u32).wrapping_mul(2_654_435_761) % 2_130_706_433
                })
            })
            .collect();
        let values: Vec<KoalaBearExt4> = table.iter().copied().map(quartic).collect();
        // Reference: a row of w extension elements is the base row of 4w
        // coordinates, each element contributing c0, c1, c2, c3 in order.
        let rows: Vec<Vec<u32>> = table
            .chunks(width)
            .map(|row| row.iter().flatten().copied().collect())
            .collect();
        let mut reference = Reference { calls: 0 };
        let layers = reference.layers(&rows);
        let root = *layers.last().unwrap().first().unwrap();
        let frontier = Reference::frontier(&layers, &queries);
        // Upstream extension adapter over the scalar tree.
        let (cap, data) = upstream.commit(vec![RowMajorMatrix::new(values.clone(), width)]);
        let (opened, pruned) = upstream.open_multi_batch(&queries, &data);
        assert_eq!(words(cap.roots()), [root]);
        assert_eq!(words(&pruned.sibling_hashes), frontier);
        // Kernels.
        let committed = kernel_in(
            QUARTIC,
            "oracle.commit",
            vec![quartic_vector(&values), Value::Index(width as u64)],
        )
        .unwrap();
        assert_eq!(digest_bytes(&committed[0]), bytes(&[root]));
        let opening = kernel_in(
            QUARTIC,
            "oracle.open_many",
            vec![committed[1].clone(), indices(&queries)],
        )
        .unwrap();
        let expected: Vec<KoalaBearExt4> = queries
            .iter()
            .flat_map(|q| values[q * width..(q + 1) * width].to_vec())
            .collect();
        assert!(matches!(&opening[0], Value::KoalaBearExt4Vector(v) if v[..] == expected[..]));
        assert_eq!(
            opened.iter().flat_map(|o| o[0].clone()).collect::<Vec<_>>(),
            expected
        );
        assert_eq!(digest_bytes(&opening[1]), bytes(&frontier));
        let check = |rows: &[KoalaBearExt4], proof: Value| {
            kernel_in(
                QUARTIC,
                "oracle.check_many",
                vec![
                    committed[0].clone(),
                    Value::Index(width as u64),
                    Value::Index(height as u64),
                    indices(&queries),
                    quartic_vector(rows),
                    proof,
                ],
            )
            .unwrap()
        };
        assert!(matches!(
            check(&expected, opening[1].clone())[..],
            [Value::Bool(true)]
        ));
        let dims = [Dimensions { width, height }];
        let upstream_verify = |rows: &[KoalaBearExt4]| {
            let opened: Vec<Vec<Vec<KoalaBearExt4>>> =
                rows.chunks(width).map(|r| vec![r.to_vec()]).collect();
            upstream
                .verify_multi_batch(&cap, &dims, &queries, &opened, &pruned)
                .is_ok()
        };
        assert!(upstream_verify(&expected));
        // Changing any one coordinate of an opened element is rejected by both.
        for coordinate in 0..4 {
            let mut changed = expected.clone();
            let mut parts = table[queries[0] * width];
            parts[coordinate] = (parts[coordinate] + 1) % 2_130_706_433;
            changed[0] = quartic(parts);
            assert!(matches!(
                check(&changed, opening[1].clone())[..],
                [Value::Bool(false)]
            ));
            assert!(!upstream_verify(&changed));
        }
        // The same table flattened into base rows of width 4w commits to the
        // same root and opens with the same pruned proof.
        let flat: Vec<u32> = table.iter().flatten().copied().collect();
        let base = kernel(
            "oracle.commit",
            vec![vector(&flat), Value::Index(4 * width as u64)],
        )
        .unwrap();
        assert_eq!(digest_bytes(&base[0]), digest_bytes(&committed[0]));
        let base_opening =
            kernel("oracle.open_many", vec![base[1].clone(), indices(&queries)]).unwrap();
        assert_eq!(digest_bytes(&base_opening[1]), digest_bytes(&opening[1]));
        // Roots and proofs are scheme-bound carriers: equal bytes under the
        // base scheme are a different physical type, which an Entry or a
        // quartic verifier port does not admit.
        assert_ne!(base[0].physical_type(), committed[0].physical_type());
        assert_ne!(base_opening[1].physical_type(), opening[1].physical_type());
    }
}

#[test]
fn reference_hash_calls_match_the_documented_counts() {
    // A table of height h and width w costs h * ceil(w/8) leaf calls and one
    // call per compressed pair on every layer.
    for (width, height, calls) in [(1, 1, 1), (8, 2, 3), (9, 3, 6 + 3), (17, 5, 15 + 3 + 2 + 1)] {
        let rows: Vec<Vec<u32>> = (0..height).map(|i| vec![i as u32 + 1; width]).collect();
        let mut reference = Reference { calls: 0 };
        reference.layers(&rows);
        assert_eq!(reference.calls, calls, "{width}x{height}");
    }
}

#[test]
fn empty_position_lists_refuse_instead_of_accepting_vacuously() {
    let committed = kernel(
        "oracle.commit",
        vec![vector(&[1, 2, 3, 4]), Value::Index(2)],
    )
    .unwrap();
    let error = kernel("oracle.open_many", vec![committed[1].clone(), indices(&[])]).unwrap_err();
    assert!(error.contains("oracle-positions"), "{error}");
    let error = kernel(
        "oracle.check_many",
        vec![
            committed[0].clone(),
            Value::Index(2),
            Value::Index(2),
            indices(&[]),
            vector(&[]),
            Value::MerkleProof(committed_scheme(&committed[0]), Vec::new().into()),
        ],
    )
    .unwrap_err();
    assert!(error.contains("oracle-positions"), "{error}");
    // Upstream instead accepts an empty query set with an empty proof.
    let upstream = upstream();
    let (cap, _) = upstream.commit(vec![RowMajorMatrix::new(vec![KoalaBear::ONE; 4], 2)]);
    let empty: &[Vec<Vec<KoalaBear>>] = &[];
    assert!(
        upstream
            .verify_multi_batch(
                &cap,
                &[Dimensions {
                    width: 2,
                    height: 2
                }],
                &[],
                empty,
                &PrunedMerklePaths {
                    sibling_hashes: vec![]
                }
            )
            .is_ok()
    );
}

#[test]
fn native_frames_carry_canonical_digest_words_only() {
    let b = backend(Policy::default());
    let base = vector(&[5, 6, 7]);
    let extension = quartic_vector(&[
        quartic([5, 0, 1, 2]),
        quartic([6, 7, 8, 9]),
        quartic([3; 4]),
    ]);
    for (scheme, values) in [(SCHEME, base), (QUARTIC, extension)] {
        let committed = kernel_in(scheme, "oracle.commit", vec![values, Value::Index(1)]).unwrap();
        let opening = kernel_in(
            scheme,
            "oracle.open_many",
            vec![committed[1].clone(), indices(&[2, 0])],
        )
        .unwrap();
        frames(&b, &committed[0], &opening[1]);
    }
}

fn frames(b: &zkc_native::NativeBackend, root: &Value, proof: &Value) {
    for (value, tag, prefix) in [(root, 71, 6), (proof, 72, 10)] {
        assert!(value.physical_type().logical().is_native_message_data());
        let frame = b.encode_native_value(value).unwrap();
        assert_eq!(&frame[..6], [b'Z', b'K', b'C', b'V', 0, tag]);
        assert_eq!(&frame[prefix..], digest_bytes(value));
        let back = b
            .decode_native_value(&value.physical_type(), &frame)
            .unwrap();
        assert_eq!(digest_bytes(&back), digest_bytes(value));
        assert_eq!(back.physical_type(), value.physical_type());
        // A word at the modulus is not canonical; a truncated frame is not whole.
        let mut noncanonical = frame.clone();
        noncanonical[prefix..prefix + 4].copy_from_slice(&2_130_706_433u32.to_le_bytes());
        assert!(
            b.decode_native_value(&value.physical_type(), &noncanonical)
                .is_err()
        );
        assert!(
            b.decode_native_value(&value.physical_type(), &frame[..frame.len() - 1])
                .is_err()
        );
    }
}
