//! Executable observations of one immutable Plonky3 challenger revision.
//!
//! This is deliberately an upstream observation tool, not a zkc backend and
//! not an implementation of Poseidon2. Every cryptographic operation below
//! calls the pinned Plonky3 crates. The emitted JSON is compared with the
//! checked-in fixture by the lit suite.

use p3_baby_bear::{
    BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS, BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16, BabyBear,
    Poseidon2BabyBear, default_babybear_poseidon2_16,
};
use p3_challenger::{CanObserve, CanSample, CanSampleBits, DuplexChallenger};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use p3_symmetric::Permutation;

const REVISION: &str = "3da346791c813433b201299afc3d10bf42f8a078";
const WIDTH: usize = 16;
const RATE: usize = 8;

type PoseidonPermutation = Poseidon2BabyBear<WIDTH>;
type Challenger = DuplexChallenger<BabyBear, PoseidonPermutation, WIDTH, RATE>;
type Challenge = BinomialExtensionField<BabyBear, 4>;

fn value(n: u32) -> BabyBear {
    BabyBear::from_u32(n)
}

fn field_array(values: &[BabyBear]) -> String {
    let body = values
        .iter()
        .map(|item| item.as_canonical_u64().to_string())
        .collect::<Vec<_>>()
        .join(",");
    format!("[{body}]")
}

fn integer_array(values: &[usize]) -> String {
    let body = values
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",");
    format!("[{body}]")
}

fn observe(challenger: &mut Challenger, values: &[u32]) {
    for item in values {
        challenger.observe(value(*item));
    }
}

fn canonical_permutation_vector() -> String {
    let input = BabyBear::new_array([
        894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
        19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913,
    ]);
    let mut output = input;
    default_babybear_poseidon2_16().permute_mut(&mut output);
    format!(
        "{{\"input\":{},\"output\":{}}}",
        field_array(&input),
        field_array(&output)
    )
}

fn extension_vector(observations: &[u32]) -> String {
    let mut challenger = Challenger::new(default_babybear_poseidon2_16());
    observe(&mut challenger, observations);
    let challenge: Challenge = challenger.sample();
    format!(
        concat!(
            "{{\"challenge_coefficients\":{},",
            "\"input_buffer_len\":{},\"observations\":{},",
            "\"output_buffer_len\":{},\"state\":{}}}"
        ),
        field_array(challenge.as_basis_coefficients_slice()),
        challenger.input_buffer.len(),
        integer_array(
            &observations
                .iter()
                .map(|item| *item as usize)
                .collect::<Vec<_>>()
        ),
        challenger.output_buffer.len(),
        field_array(&challenger.sponge_state),
    )
}

fn length_separation_vector() -> String {
    let mut one = Challenger::new(default_babybear_poseidon2_16());
    observe(&mut one, &[1]);
    let one_sample: BabyBear = one.sample();

    let mut one_zero = Challenger::new(default_babybear_poseidon2_16());
    observe(&mut one_zero, &[1, 0]);
    let one_zero_sample: BabyBear = one_zero.sample();

    format!(
        concat!(
            "{{\"one_sample\":{},\"one_state\":{},",
            "\"one_zero_sample\":{},\"one_zero_state\":{},",
            "\"states_differ\":{}}}"
        ),
        one_sample.as_canonical_u64(),
        field_array(&one.sponge_state),
        one_zero_sample.as_canonical_u64(),
        field_array(&one_zero.sponge_state),
        one.sponge_state != one_zero.sponge_state,
    )
}

fn output_discard_vector() -> String {
    let mut challenger = Challenger::new(default_babybear_poseidon2_16());
    observe(&mut challenger, &[1]);
    let first: BabyBear = challenger.sample();
    let buffered_before_observe = challenger.output_buffer.len();
    challenger.observe(value(2));
    let buffered_after_observe = challenger.output_buffer.len();
    let second: BabyBear = challenger.sample();

    format!(
        concat!(
            "{{\"buffered_after_observe\":{},",
            "\"buffered_before_observe\":{},\"first_sample\":{},",
            "\"second_sample\":{},\"state_after_second_sample\":{}}}"
        ),
        buffered_after_observe,
        buffered_before_observe,
        first.as_canonical_u64(),
        second.as_canonical_u64(),
        field_array(&challenger.sponge_state),
    )
}

fn empty_squeeze_vector() -> String {
    let mut challenger = Challenger::new(default_babybear_poseidon2_16());
    observe(&mut challenger, &[1, 2, 3, 4, 5, 6, 7, 8]);
    let state_before = challenger.sponge_state;
    let first_rate = (0..RATE)
        .map(|_| {
            let item: BabyBear = challenger.sample();
            item.as_canonical_u64() as usize
        })
        .collect::<Vec<_>>();
    let ninth: BabyBear = challenger.sample();
    format!(
        concat!(
            "{{\"first_rate_outputs\":{},\"ninth_output\":{},",
            "\"state_after_empty_squeeze\":{},",
            "\"state_before_empty_squeeze\":{}}}"
        ),
        integer_array(&first_rate),
        ninth.as_canonical_u64(),
        field_array(&challenger.sponge_state),
        field_array(&state_before),
    )
}

fn low_bits_vector() -> String {
    let mut challenger = Challenger::new(default_babybear_poseidon2_16());
    observe(&mut challenger, &[1, 2, 3]);
    let sampled = challenger.sample_bits(8);
    let source_word = challenger.sponge_state[RATE - 1].as_canonical_u64();
    format!(
        concat!(
            "{{\"bits\":8,\"mask\":255,\"sampled\":{},",
            "\"source_word\":{}}}"
        ),
        sampled, source_word,
    )
}

fn main() {
    println!(
        concat!(
            "{{",
            "\"profile\":{{\"alphabet_order\":2013265921,",
            "\"capacity\":8,\"extension_degree\":4,",
            "\"extension_nonresidue\":11,",
            "\"poseidon2_rounds\":{{\"external_half\":{},\"partial\":{}}},",
            "\"rate\":8,\"width\":16}},",
            "\"revision\":\"{}\",",
            "\"schema\":\"zkc.upstream.plonky3_duplex_trace\",",
            "\"source_files\":[",
            "{{\"path\":\"baby-bear/src/baby_bear.rs\",\"sha256\":\"0475213ebcb2338c2ad09e1e3342c8c696ca4b1001a31e9d3b836c68927d4011\"}},",
            "{{\"path\":\"baby-bear/src/poseidon2.rs\",\"sha256\":\"94dd94e267e66922104010624f42ba7836805dc2fafe7482d684cd2e042a7327\"}},",
            "{{\"path\":\"challenger/src/duplex_challenger.rs\",\"sha256\":\"4d8950ec84bafef5174a9c8dc5c6b54238959937b207613731c02c3d15f391c3\"}},",
            "{{\"path\":\"field/src/extension/mod.rs\",\"sha256\":\"aac05a6fdcc6f309792680d356c00ee491b4ad79790f746a04119523fe68ec38\"}},",
            "{{\"path\":\"monty-31/src/monty_31.rs\",\"sha256\":\"20593fc7389dabf16ccd666a20bf517f4c6b78a6c8dc7870a20e3855365b5fcf\"}}],",
            "\"vectors\":{{",
            "\"canonical_permutation\":{},",
            "\"empty_squeeze\":{},",
            "\"full_absorb_ext4\":{},",
            "\"length_separation\":{},",
            "\"output_discard\":{},",
            "\"partial_absorb_ext4\":{},",
            "\"sample_bits\":{}",
            "}}",
            "}}"
        ),
        BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS,
        BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_16,
        REVISION,
        canonical_permutation_vector(),
        empty_squeeze_vector(),
        extension_vector(&[1, 2, 3, 4, 5, 6, 7, 8]),
        length_separation_vector(),
        output_discard_vector(),
        extension_vector(&[1, 2]),
        low_bits_vector(),
    );
}
