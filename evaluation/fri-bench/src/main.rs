//! The allocation half of the gate: one emitted prove and one upstream
//! prove under a counting allocator, reported as totals — criterion
//! owns wall clock, this mode owns bytes. Run after gen.py:
//! `cargo run --release`.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, Ordering};

struct Counting;

static ALLOCATIONS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        BYTES.fetch_add(layout.size() as u64, Ordering::Relaxed);
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

fn snapshot() -> (u64, u64) {
    (
        ALLOCATIONS.load(Ordering::Relaxed),
        BYTES.load(Ordering::Relaxed),
    )
}

fn main() {
    use p3_baby_bear::default_babybear_poseidon2_16;
    use p3_challenger::{CanObserve, FieldChallenger};
    use p3_commit::Pcs as PcsTrait;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{PrimeCharacteristicRing, PrimeField32};
    use p3_matrix::dense::RowMajorMatrix;
    use zkc_plonky3_replay::{
        fri_parameters_for, ChallengeMmcs, Compress, Dft, FieldHash, Pcs, PlainChallenger, Val,
        ValMmcs,
    };
    type Challenge = BinomialExtensionField<Val, 4>;
    const LOG_SIZE: usize = 20;

    let perm = default_babybear_poseidon2_16();
    let hash = FieldHash::new(perm.clone());
    let compress = Compress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let pcs = Pcs::new(
        Dft::default(),
        val_mmcs,
        fri_parameters_for(challenge_mmcs, 100, 16, 1, 0),
    );
    let domain =
        <Pcs as PcsTrait<Challenge, PlainChallenger>>::natural_domain_for_degree(&pcs, 1 << LOG_SIZE);
    let trace =
        RowMajorMatrix::new((1..=1u32 << LOG_SIZE).map(Val::from_u32).collect::<Vec<_>>(), 1);

    let before = snapshot();
    let mut challenger = PlainChallenger::new(perm);
    challenger.observe(Val::from_usize(LOG_SIZE));
    let (commitment, prover_data) =
        <Pcs as PcsTrait<Challenge, PlainChallenger>>::commit(&pcs, vec![(domain, trace)]);
    challenger.observe(commitment.clone());
    let zeta: Challenge = challenger.sample_algebra_element();
    let _ = <Pcs as PcsTrait<Challenge, PlainChallenger>>::open(
        &pcs,
        vec![(&prover_data, vec![vec![zeta]])],
        &mut challenger,
    );
    let after_upstream = snapshot();

    let statement = zkc_fri_prover::Statement {
        f_root: core::array::from_fn(|i| commitment.roots()[0][i].as_canonical_u32()),
    };
    let witness = zkc_fri_prover::Witness {
        codeword: zkc_fri_prover::zkc_rt::Payload::new(
            (1..=1u32 << LOG_SIZE)
                .flat_map(|w| w.to_be_bytes())
                .collect::<Vec<u8>>(),
        ),
    };
    let _ = zkc_fri_prover::prove(&statement, witness).expect("emitted prove");
    let after_emitted = snapshot();

    println!(
        "upstream: {} allocations, {} bytes",
        after_upstream.0 - before.0,
        after_upstream.1 - before.1
    );
    println!(
        "emitted: {} allocations, {} bytes",
        after_emitted.0 - after_upstream.0,
        after_emitted.1 - after_upstream.1
    );
}
