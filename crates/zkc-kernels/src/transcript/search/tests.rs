use super::*;
use crate::numerical::{Limits, Usage};
use sha3::{Digest as _, Keccak256};

fn call(work: u64, memory: usize, outputs: usize) -> Call {
    Call::new(Limits {
        work,
        memory,
        outputs,
    })
}
fn input(chain: &KeccakChain) -> NonceInput<'_> {
    NonceInput {
        chain,
        witness_label: b"explicit-witness-label",
        prefix: b"explicit-envelope-prefix",
        suffix: b"explicit-envelope-suffix",
        request_label: b"explicit-request-label",
        total_output_bytes: 72,
    }
}

// Independent two-stage byte construction, including the witness envelope and
// final request length. Do not use the chain's framing or search hash helpers.
fn reference(input: &NonceInput<'_>, nonce: u64) -> Digest {
    fn frame(hash: &mut Keccak256, tag: u8, label: &[u8], value: &[u8]) {
        hash.update([tag]);
        hash.update((label.len() as u64).to_be_bytes());
        hash.update(label);
        hash.update((value.len() as u64).to_be_bytes());
        hash.update(value);
    }
    let witness = [input.prefix, &nonce.to_le_bytes(), input.suffix].concat();
    let mut absorb = Keccak256::new();
    absorb.update(b"zkc.hash-chain.absorb/0\0");
    absorb.update(input.chain.state());
    frame(&mut absorb, 1, input.witness_label, &witness);
    let mut request = Keccak256::new();
    request.update(b"zkc.hash-chain.request/0\0");
    request.update(absorb.finalize());
    frame(
        &mut request,
        2,
        input.request_label,
        &input.total_output_bytes.to_be_bytes(),
    );
    request.update(0u64.to_be_bytes());
    request.finalize().into()
}

#[test]
fn search_matches_independent_two_stage_bytes_and_earliest_candidate() {
    let chain = KeccakChain::bind("test-only-suite", b"test-only-binding");
    let state = *chain.state();
    for length in [8, 32, 64, 72, 136] {
        let mut input = input(&chain);
        input.total_output_bytes = length;
        for gate in [ZeroBits::LowLe(3), ZeroBits::LeadingBe(3)] {
            let expected = (11..523).find(|nonce| gate.accepts(&reference(&input, *nonce)));
            assert!(expected.is_some());
            let call = call(100_000, 100_000, 8);
            let report = search_nonce(&call, &input, 11, 512, gate);
            assert_eq!(report.outcome, Ok(expected));
            let receipt = report.receipt;
            assert_eq!(receipt.failing_prefix, expected.unwrap() - 11);
            assert_eq!(
                receipt.evaluated,
                receipt.failing_prefix + 1 + receipt.evaluated_after_match
            );
            assert_eq!(receipt.output_bytes, 8);
            assert_eq!(receipt.admitted_work, receipt.executed_permutation_lanes);
            assert_eq!(
                call.usage(),
                Usage {
                    work: receipt.admitted_work,
                    memory: 8,
                    outputs: 8
                }
            );
        }
    }
    assert_eq!(chain.state(), &state);
}

#[test]
fn gate_bit_conventions_include_zero_and_the_full_word() {
    let mut digest = [255; 32];
    digest[0] = 0x80;
    assert!(ZeroBits::LowLe(7).accepts(&digest));
    assert!(!ZeroBits::LowLe(8).accepts(&digest));
    digest[0] = 1;
    assert!(ZeroBits::LeadingBe(7).accepts(&digest));
    assert!(!ZeroBits::LeadingBe(8).accepts(&digest));
    for gate in [ZeroBits::LowLe(64), ZeroBits::LeadingBe(64)] {
        assert!(!gate.accepts(&digest));
        digest[..8].fill(0);
        assert!(gate.accepts(&digest));
        digest[7] = 1;
        assert!(!gate.accepts(&digest));
    }
    assert!(ZeroBits::LowLe(0).accepts(&digest));
}

#[test]
fn validation_precedes_empty_search_and_zero_gate_elision() {
    let chain = KeccakChain::bind("test-only-suite", b"binding");
    let mut input = input(&chain);
    for (first, attempts, gate, error) in [
        (0, 0, ZeroBits::LowLe(65), Error::Gate),
        (0, 1, ZeroBits::LeadingBe(65), Error::Gate),
        (u64::MAX, 2, ZeroBits::LowLe(0), Error::Range),
    ] {
        let call = call(0, 0, 0);
        let report = search_nonce(&call, &input, first, attempts, gate);
        assert_eq!(report.outcome, Err(error));
        assert_eq!(report.receipt, Receipt::default());
        assert_eq!(
            call.usage(),
            Usage {
                work: 0,
                memory: 0,
                outputs: 0
            }
        );
    }
    input.total_output_bytes = 7;
    let report = search_nonce(&call(0, 0, 0), &input, 0, 0, ZeroBits::LowLe(1));
    assert_eq!(report.outcome, Err(Error::Length));
    input.total_output_bytes = 0;
    assert_eq!(
        search_nonce(&call(0, 0, 0), &input, u64::MAX, 0, ZeroBits::LowLe(0)).outcome,
        Ok(None)
    );
    let call = call(0, 8, 8);
    let report = search_nonce(&call, &input, u64::MAX, 1, ZeroBits::LowLe(0));
    assert_eq!(report.outcome, Ok(Some(u64::MAX)));
    assert_eq!(report.receipt.evaluated, 0);
    assert_eq!(
        call.usage(),
        Usage {
            work: 0,
            memory: 8,
            outputs: 8
        }
    );
}

#[test]
fn padded_tail_and_wide_streaming_charge_all_physical_lanes() {
    let chain = KeccakChain::bind("test-only-suite", b"binding");
    for size in [0, 1, 135, 136, 137, 4096, 32768] {
        let prefix = vec![9; size];
        let mut input = input(&chain);
        input.prefix = &prefix;
        let attempts = LANES as u64 + 1;
        assert!((0..attempts).all(|nonce| !ZeroBits::LowLe(64).accepts(&reference(&input, nonce))));
        let plan = Plan::new(&input, attempts).unwrap();
        let call = call(1_000_000, 100_000, 8);
        let report = search_nonce(&call, &input, 0, attempts, ZeroBits::LowLe(64));
        assert_eq!(report.outcome, Ok(None));
        assert_eq!(report.receipt.evaluated, attempts);
        assert_eq!(report.receipt.failing_prefix, attempts);
        let batches = attempts.div_ceil(plan.capacity as u64);
        assert_eq!(report.receipt.admitted_work, batches * plan.work);
        assert_eq!(
            report.receipt.padded_candidates,
            batches * plan.lanes as u64 - attempts
        );
        assert_eq!(report.receipt.peak_memory, 8 + plan.workspace_bytes);
        assert_eq!(
            call.usage(),
            Usage {
                work: batches * plan.work,
                memory: 0,
                outputs: 0
            }
        );
    }
}

#[test]
fn exact_rate_boundaries_in_both_stages_charge_independent_permutation_counts() {
    let chain = KeccakChain::bind("test-only-suite", b"binding");
    for absorption_bytes in [135, 136, 137, 271, 272, 273] {
        for request_bytes in [135, 136, 137, 271, 272, 273] {
            let mut input = input(&chain);
            // Count literal frame fields independently of Plan and its writers.
            let absorption_fixed = b"zkc.hash-chain.absorb/0\0".len()
                + 32
                + 1
                + 8
                + input.witness_label.len()
                + 8
                + 8
                + input.suffix.len();
            let request_fixed = b"zkc.hash-chain.request/0\0".len() + 32 + 1 + 8 + 8 + 8 + 8;
            let prefix = vec![9; absorption_bytes - absorption_fixed];
            let label = vec![7; request_bytes - request_fixed];
            input.prefix = &prefix;
            input.request_label = &label;
            let attempts = LANES as u64 + 1;
            assert!(
                (0..attempts).all(|nonce| !ZeroBits::LowLe(64).accepts(&reference(&input, nonce)))
            );
            let permutations = (absorption_bytes / 136 + 1 + request_bytes / 136 + 1) as u64;
            let batches = attempts.div_ceil(LANES as u64);
            let units = batches * LANES as u64 * permutations;
            let call = call(units, 100_000, 8);
            let report = search_nonce(&call, &input, 0, attempts, ZeroBits::LowLe(64));
            assert_eq!(report.outcome, Ok(None));
            assert_eq!(report.receipt.executed_permutation_lanes, units);
            assert_eq!(report.receipt.admitted_work, units);
            assert_eq!(
                report.receipt.padded_candidates,
                batches * LANES as u64 - attempts
            );
        }
    }
}

#[test]
fn final_nonce_can_be_evaluated_without_an_exclusive_end_overflow() {
    let chain = KeccakChain::bind("test-only-suite", b"binding");
    let input = input(&chain);
    let gate = ZeroBits::LowLe(64);
    let expected = gate
        .accepts(&reference(&input, u64::MAX))
        .then_some(u64::MAX);
    let report = search_nonce(&call(100, 100, 8), &input, u64::MAX, 1, gate);
    assert_eq!(report.outcome, Ok(expected));
    assert_eq!(report.receipt.evaluated, 1);
    assert_eq!(report.receipt.lanes, 1);
}

#[test]
fn successful_single_candidate_and_short_tail_match_the_independent_search() {
    let chain = KeccakChain::bind("test-only-suite", b"binding");
    let input = input(&chain);
    let gate = ZeroBits::LowLe(3);
    let passed: Vec<_> = (0..4096)
        .map(|nonce| gate.accepts(&reference(&input, nonce)))
        .collect();
    let winner = passed.iter().position(|value| *value).unwrap() as u64;
    let single = search_nonce(&call(100_000, 100_000, 8), &input, winner, 1, gate);
    assert_eq!(single.outcome, Ok(Some(winner)));
    assert_eq!(single.receipt.evaluated, 1);
    assert_eq!(single.receipt.lanes, 1);
    assert_eq!(single.receipt.failing_prefix, 0);
    assert_eq!(single.receipt.padded_candidates, 0);

    let first = passed
        .windows(LANES + 1)
        .position(|window| window[..LANES].iter().all(|value| !value) && window[LANES])
        .unwrap() as u64;
    let call = call(100_000, 100_000, 8);
    let tail = search_nonce(&call, &input, first, LANES as u64 + 1, gate);
    assert_eq!(tail.outcome, Ok(Some(first + LANES as u64)));
    assert_eq!(tail.receipt.evaluated, LANES as u64 + 1);
    assert_eq!(tail.receipt.failing_prefix, LANES as u64);
    assert_eq!(tail.receipt.evaluated_after_match, 0);
    assert_eq!(tail.receipt.padded_candidates, LANES as u64 - 1);
    assert_eq!(call.usage().memory, 8);
    assert_eq!(call.usage().outputs, 8);
}

#[test]
fn failures_retain_completed_frontiers_and_accepted_work_only() {
    let chain = KeccakChain::bind("test-only-suite", b"binding");
    let input = input(&chain);
    let attempts = LANES as u64 + 1;
    let plan = Plan::new(&input, attempts).unwrap();
    for (work, memory, outputs, expected) in [
        (0, 100_000, 7, numerical::Error::OutputBytes),
        (0, 100_000, 8, numerical::Error::Work),
        (plan.work, 7, 8, numerical::Error::Memory),
        (plan.work, 8, 8, numerical::Error::Memory),
        (plan.work, 100_000, 8, numerical::Error::Work),
    ] {
        let call = call(work, memory, outputs);
        let report = search_nonce(&call, &input, 0, attempts, ZeroBits::LowLe(64));
        assert_eq!(report.outcome, Err(Error::Numerical(expected)));
        assert_eq!(call.usage().work, report.receipt.admitted_work);
        assert_eq!(call.usage().memory, 0);
        assert_eq!(call.usage().outputs, 0);
        if expected == numerical::Error::Work && work == plan.work {
            assert_eq!(report.receipt.evaluated, plan.capacity as u64);
            assert_eq!(report.receipt.failing_prefix, plan.capacity as u64);
        }
    }
}

#[test]
fn every_scratch_allocation_failure_has_a_receipt_and_no_published_output() {
    if LANES == 1 {
        return;
    }
    let chain = KeccakChain::bind("test-only-suite", b"binding");
    let input = input(&chain);
    let plan = Plan::new(&input, LANES as u64).unwrap();
    for allocation in 0..2 {
        let call = call(100_000, 100_000, 8);
        let _failure = crate::allocation::failure::after(allocation);
        let report = search_nonce(&call, &input, 0, LANES as u64, ZeroBits::LowLe(1));
        assert_eq!(
            report.outcome,
            Err(Error::Numerical(numerical::Error::Allocation))
        );
        assert_eq!(report.receipt.admitted_work, plan.work);
        assert_eq!(report.receipt.executed_permutation_lanes, 0);
        assert_eq!(report.receipt.evaluated, 0);
        assert_eq!(report.receipt.peak_memory, 8 + plan.workspace_bytes);
        assert_eq!(
            call.usage(),
            Usage {
                work: plan.work,
                memory: 0,
                outputs: 0
            }
        );
    }
}

#[test]
fn final_reply_length_changes_the_search_and_prior_call_usage_is_preserved() {
    let chain = KeccakChain::bind("test-only-suite", b"binding");
    let mut input = input(&chain);
    let mut hits = Vec::new();
    for length in [32, 72] {
        let call = call(1_000_000, 100_000, 24);
        call.work(17).unwrap();
        call.scalar(16).unwrap().finish(|| Ok::<_, ()>(())).unwrap();
        input.total_output_bytes = length;
        let report = search_nonce(&call, &input, 0, 4096, ZeroBits::LowLe(7));
        let expected =
            (0..4096).find(|nonce| ZeroBits::LowLe(7).accepts(&reference(&input, *nonce)));
        assert_eq!(report.outcome, Ok(expected));
        hits.push(expected.unwrap());
        assert_eq!(call.usage().work, 17 + report.receipt.admitted_work);
        assert_eq!(call.usage().memory, 24);
        assert_eq!(call.usage().outputs, 24);
    }
    assert_ne!(hits[0], hits[1]);
}
