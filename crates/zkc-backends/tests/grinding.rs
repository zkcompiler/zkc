use std::collections::VecDeque;
use zkc_backends::{
    choices::Namespace,
    external::{
        Work,
        grinding::{Candidates, Limits, Progress, Search, Usage},
        openvm::{Duplex, MODULUS},
    },
};
use zkc_runtime::interactive::BackendError;

struct Tape {
    values: VecDeque<u32>,
    calls: Vec<Namespace>,
}
impl Candidates for Tape {
    fn next(&mut self, namespace: &Namespace) -> Result<u32, BackendError> {
        self.calls.push(namespace.clone());
        self.values
            .pop_front()
            .ok_or_else(|| BackendError::new("exhausted:test-tape"))
    }
}
fn search(values: &[u32], bits: u32, limits: Limits) -> Search<Tape> {
    let mut seed = Duplex::new();
    seed.observe(&[42]).unwrap();
    Search::new(
        &seed,
        bits,
        Namespace::new("P", "grinding").unwrap(),
        Tape {
            values: values.iter().copied().collect(),
            calls: vec![],
        },
        limits,
    )
    .unwrap()
}
fn code(progress: &Progress) -> &str {
    let Progress::Stopped(error) = progress else {
        panic!("not stopped: {progress:?}")
    };
    &error.code
}

#[test]
fn fixed_candidates_reproduce_the_pinned_witness_without_live_trial_effects() {
    // Pinned upstream joint probe: observe(42), bits=3, selected witness=2.
    // The candidate order here is explicit; upstream parallel search is not
    // required to select its first successful witness in sequential order.
    let limits = Limits {
        candidates: 3,
        work: 9,
    };
    let mut split = search(&[0, 1, 2], 3, limits);
    let seed = split.seed();
    assert_eq!(split.advance(0), &Progress::Pending);
    assert_eq!(split.usage(), Usage::default());
    assert_eq!(split.advance(1), &Progress::Pending);
    assert_eq!(split.advance(1), &Progress::Pending);
    assert_eq!(split.advance(1), &Progress::Found(2));
    assert_eq!(split.seed(), seed);
    assert_eq!(
        split.usage(),
        Usage {
            candidate_calls: 3,
            trials: 3,
            work: Work {
                observes: 3,
                samples: 3,
                permutations: 3,
                ..Work::default()
            },
        }
    );
    assert_eq!(
        split.source().calls,
        vec![Namespace::new("P", "grinding").unwrap(); 3]
    );
    let mut whole = search(&[0, 1, 2], 3, limits);
    assert_eq!(whole.advance(30), split.progress());
    assert_eq!(whole.usage(), split.usage());
    assert_eq!(split.advance(30), &Progress::Found(2));
    assert_eq!(split.source().calls.len(), 3);
    let mut live = Duplex::from_snapshot(seed.clone()).unwrap();
    assert!(live.check_witness(3, 2).unwrap().value);
    assert_ne!(live.snapshot(), seed);
    // The live state contains one selected witness check, not three trials.
    let mut failed_direct = Duplex::from_snapshot(seed).unwrap();
    assert!(!failed_direct.check_witness(3, 0).unwrap().value);
    assert_ne!(failed_direct.snapshot(), split.seed());
}

#[test]
fn separate_candidate_and_work_limits_are_absorbing_and_preserve_spent_work() {
    for (limits, expected, calls) in [
        (
            Limits {
                candidates: 2,
                work: 9,
            },
            "exhausted:grinding-candidates",
            2,
        ),
        (
            Limits {
                candidates: 3,
                work: 6,
            },
            "exhausted:grinding-work",
            2,
        ),
        (
            Limits {
                candidates: 0,
                work: 9,
            },
            "exhausted:grinding-candidates",
            0,
        ),
        (
            Limits {
                candidates: 3,
                work: 2,
            },
            "exhausted:grinding-work",
            0,
        ),
    ] {
        let mut run = search(&[0, 1, 2], 3, limits);
        assert_eq!(code(run.advance(8)), expected);
        let usage = run.usage();
        assert_eq!(usage.candidate_calls, calls);
        assert_eq!(usage.trials, calls);
        assert_eq!(usage.work.units().unwrap(), calls * 3);
        assert_eq!(code(run.advance(8)), expected);
        assert_eq!(run.usage(), usage);
    }
}

#[test]
fn provider_failure_and_noncanonical_candidates_do_not_invent_crypto_work() {
    for (values, error, calls) in [
        (vec![0], "exhausted:test-tape", 2),
        (vec![0, MODULUS], "refused:grinding-candidate", 2),
        (vec![u32::MAX], "refused:grinding-candidate", 1),
    ] {
        let mut run = search(
            &values,
            3,
            Limits {
                candidates: 8,
                work: 30,
            },
        );
        assert_eq!(code(run.advance(8)), error);
        assert_eq!(run.usage().candidate_calls, calls);
        assert_eq!(run.usage().trials, calls - 1);
        assert_eq!(run.usage().work.units().unwrap(), 3 * (calls - 1));
        assert_eq!(run.source().calls.len() as u64, calls);
    }
}

#[test]
fn zero_difficulty_is_no_search_and_invalid_difficulty_is_refused() {
    let mut zero = search(
        &[],
        0,
        Limits {
            candidates: 0,
            work: 0,
        },
    );
    assert_eq!(zero.advance(1), &Progress::Found(0));
    assert_eq!(zero.usage(), Usage::default());
    assert!(zero.source().calls.is_empty());
    let mut live = Duplex::from_snapshot(zero.seed()).unwrap();
    assert!(live.check_witness(0, 0).unwrap().value);
    assert_eq!(live.snapshot(), zero.seed());
    let error = Search::new(
        &live,
        31,
        Namespace::new("P", "grinding").unwrap(),
        Tape {
            values: VecDeque::new(),
            calls: vec![],
        },
        Limits {
            candidates: 8,
            work: 30,
        },
    )
    .err()
    .unwrap();
    assert_eq!(error.code, "refused:grinding-bit-width");
}
