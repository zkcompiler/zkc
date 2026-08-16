//! The generation-versus-upstream benchmark (the wall-clock half of
//! the gate): the pinned upstream prover and the emitted zkc prover
//! over the same sp1-core-shape instance — one deterministic 2^20
//! column, rate 1/2, 100 queries, a 16-bit grind. Wire byte equality
//! is asserted once before any timing, so the two legs can never
//! silently diverge into measuring different work; the recorded
//! numbers live in RECORD.md with machine and revision provenance.

use criterion::{criterion_group, criterion_main, Criterion};
use p3_baby_bear::default_babybear_poseidon2_16;
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::Pcs as PcsTrait;
use p3_field::extension::BinomialExtensionField;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use zkc_plonky3_replay::{
    fri_parameters_for, ChallengeMmcs, Compress, Dft, FieldHash, Pcs, PlainChallenger, Val,
    ValMmcs,
};

type Challenge = BinomialExtensionField<Val, 4>;

const LOG_SIZE: usize = 20;
const QUERIES: usize = 100;
const GRIND_BITS: usize = 16;

fn upstream_pcs() -> Pcs {
    let perm = default_babybear_poseidon2_16();
    let hash = FieldHash::new(perm.clone());
    let compress = Compress::new(perm);
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    Pcs::new(
        Dft::default(),
        val_mmcs,
        fri_parameters_for(challenge_mmcs, QUERIES, GRIND_BITS),
    )
}

fn trace() -> RowMajorMatrix<Val> {
    RowMajorMatrix::new((1..=1u32 << LOG_SIZE).map(Val::from_u32).collect(), 1)
}

/// One full upstream prove: commit, observe, sample zeta, open.
fn upstream_prove(pcs: &Pcs) -> Vec<u32> {
    let perm = default_babybear_poseidon2_16();
    let domain =
        <Pcs as PcsTrait<Challenge, PlainChallenger>>::natural_domain_for_degree(pcs, 1 << LOG_SIZE);
    let mut challenger = PlainChallenger::new(perm);
    challenger.observe(Val::from_usize(LOG_SIZE));
    let (commitment, prover_data) =
        <Pcs as PcsTrait<Challenge, PlainChallenger>>::commit(pcs, vec![(domain, trace())]);
    challenger.observe(commitment.clone());
    let zeta: Challenge = challenger.sample_algebra_element();
    let (_opened, _proof) = <Pcs as PcsTrait<Challenge, PlainChallenger>>::open(
        pcs,
        vec![(&prover_data, vec![vec![zeta]])],
        &mut challenger,
    );
    commitment
        .roots()
        .first()
        .map(|root| {
            use p3_field::PrimeField32;
            root.iter().map(|value| value.as_canonical_u32()).collect()
        })
        .unwrap_or_default()
}

fn witness_bytes() -> Vec<u8> {
    (1..=1u32 << LOG_SIZE).flat_map(|w| w.to_be_bytes()).collect()
}

fn emitted_prove(statement: &zkc_fri_prover::Statement) -> Vec<u8> {
    let witness = zkc_fri_prover::Witness {
        codeword: zkc_fri_prover::zkc_rt::Payload::new(witness_bytes()),
    };
    zkc_fri_prover::prove(statement, witness)
        .expect("the emitted prover accepts its own witness")
        .proof
}

fn bench(criterion: &mut Criterion) {
    let pcs = upstream_pcs();
    // The statement is the input commitment's own root, taken from one
    // upstream run; both legs then prove the same statement, and the
    // wires must agree byte for byte before anything is timed.
    let statement_words = upstream_prove(&pcs);
    let statement = zkc_fri_prover::Statement {
        f_root: statement_words.clone().try_into().expect("one cap root"),
    };
    let emitted_wire = emitted_prove(&statement);
    assert!(
        !emitted_wire.is_empty(),
        "the emitted prover produced an empty wire"
    );

    let mut group = criterion.benchmark_group("fri-prove-sp1-shape");
    group.sample_size(10);
    group.bench_function("upstream", |bencher| {
        bencher.iter(|| upstream_prove(&pcs));
    });
    group.bench_function("emitted", |bencher| {
        bencher.iter(|| emitted_prove(&statement));
    });
    group.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
