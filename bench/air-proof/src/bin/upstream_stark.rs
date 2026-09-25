//! Whole upstream STARK context, NOT a matched compiler-overhead baseline.
//! One two-column Fibonacci AIR, no inter-AIR permutation. Hash, profile,
//! framing and batching differ from zkc's route.
//!
//! The Fibonacci AIR follows `p3-uni-stark` 0.5.1 `tests/fib_air.rs`, with safe
//! slice indexing in place of that test's row casts.
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::{PrimeCharacteristicRing, extension::BinomialExtensionField};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_keccak::Keccak256Hash;
use p3_koala_bear::KoalaBear;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher};
use p3_uni_stark::{StarkConfig, prove, verify};
use std::time::Instant;

type F = KoalaBear;
type E = BinomialExtensionField<F, 8>;
type M = MerkleTreeMmcs<
    F,
    u8,
    SerializingHasher<Keccak256Hash>,
    CompressionFunctionFromHasher<Keccak256Hash, 2, 32>,
    2,
    32,
>;
type EM = ExtensionMmcs<F, E, M>;
type C = SerializingChallenger32<F, HashChallenger<u8, Keccak256Hash, 32>>;
type P = TwoAdicFriPcs<F, Radix2DitParallel<F>, M, EM>;
type Config = StarkConfig<P, E, C>;

struct Fibonacci;
impl<F> BaseAir<F> for Fibonacci {
    fn width(&self) -> usize {
        2
    }
    fn num_public_values(&self) -> usize {
        3
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(2)
    }
}
impl<AB: AirBuilder> Air<AB> for Fibonacci {
    fn eval(&self, b: &mut AB) {
        let trace = b.main();
        let row = trace.current_slice();
        let next = trace.next_slice();
        let public = b.public_values();
        let (a, c, last) = (public[0], public[1], public[2]);
        b.when_first_row().assert_eq(row[0], a);
        b.when_first_row().assert_eq(row[1], c);
        b.when_transition().assert_eq(next[0], row[1]);
        b.when_transition().assert_eq(next[1], row[0] + row[1]);
        b.when_last_row().assert_eq(row[1], last);
    }
}
fn config() -> Config {
    let mmcs = M::new(
        SerializingHasher::new(Keccak256Hash),
        CompressionFunctionFromHasher::new(Keccak256Hash),
        0,
    );
    let params = FriParameters {
        log_blowup: 3,
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 32,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
        mmcs: EM::new(mmcs.clone()),
    };
    Config::new(
        P::new(Radix2DitParallel::default(), mmcs, params),
        C::from_hasher(vec![], Keccak256Hash),
    )
}
fn main() {
    let config = config();
    println!(
        "{{\"route\":\"upstream p3-uni-stark 0.5.1, one Fibonacci AIR\",\"matched\":false,\"blowup\":8,\"queries\":32,\"cases\":["
    );
    for (case, n) in [16, 128, 512, 2048, 8192].into_iter().enumerate() {
        let (mut a, mut b) = (F::ZERO, F::ONE);
        let mut values = Vec::with_capacity(2 * n);
        for _ in 0..n {
            values.extend([a, b]);
            (a, b) = (b, a + b);
        }
        let public = vec![F::ZERO, F::ONE, values[2 * n - 1]];
        let trace = RowMajorMatrix::new(values, 2);
        let mut prover = Vec::new();
        let mut verifier = Vec::new();
        let mut size = 0;
        for i in 0..4 {
            let trace = trace.clone(); // witness copying is outside timing
            let start = Instant::now();
            let proof = prove(&config, &Fibonacci, trace, &public);
            let pt = start.elapsed().as_secs_f64() * 1000.;
            let start = Instant::now();
            verify(&config, &Fibonacci, &proof, &public).unwrap();
            let vt = start.elapsed().as_secs_f64() * 1000.;
            size = postcard::to_allocvec(&proof).unwrap().len();
            if i > 0 {
                prover.push(pt);
                verifier.push(vt);
            }
        }
        prover.sort_by(f64::total_cmp);
        verifier.sort_by(f64::total_cmp);
        println!(
            "{}{{\"height\":{n},\"prover_ms\":{},\"verifier_ms\":{},\"postcard_bytes\":{size}}}",
            if case == 0 { "" } else { "," },
            prover[1],
            verifier[1]
        );
    }
    println!("]}}");
}
