use std::ops::ControlFlow::{Break, Continue};
use zkc_runtime::{Outcome, Stop, iteration::Execution};

type Prefix = Execution<usize, usize, std::ops::ControlFlow<usize, ()>>;

fn attempt(target: usize) -> impl FnMut((), usize) -> Prefix {
    move |(), state| Prefix {
        outcome: Outcome::Returned(if state < target {
            Continue(())
        } else {
            Break(state)
        }),
        state: state + 1,
        events: vec![state],
    }
}

#[test]
fn prefixes_resume_without_rewinding_and_finished_results_are_stable() {
    for target in 0..16 {
        for first in 0..20 {
            for second in 0..20 {
                let one = Prefix::pending((), 0).advance(first + second, attempt(target));
                let split = Prefix::pending((), 0)
                    .advance(first, attempt(target))
                    .advance(second, attempt(target));
                assert_eq!(one, split);
                let calls = (first + second).min(target + 1);
                assert_eq!(one.state, calls);
                assert_eq!(one.events, (0..calls).collect::<Vec<_>>());
                assert_eq!(
                    one.outcome,
                    Outcome::Returned(if first + second > target {
                        Break(target)
                    } else {
                        Continue(())
                    })
                );
            }
        }
    }
}

#[test]
fn approximation_and_deployment_exhaustion_are_distinct() {
    let pending = Prefix::pending((), 0).advance(2, attempt(2));
    assert_eq!(pending.outcome, Outcome::Returned(Continue(())));
    let capped = pending.close();
    assert_eq!(capped.outcome, Outcome::Stopped(Stop::Exhausted));
    assert_eq!(capped.state, 2);
    assert_eq!(capped.events, vec![0, 1]);
}

#[test]
fn fatal_stops_preserve_effects_and_never_retry() {
    let mut calls = 0;
    let stopped = Prefix::pending((), 4).advance(10, |(), state| {
        calls += 1;
        Prefix {
            outcome: Outcome::Stopped(Stop::Reject),
            state: state + 1,
            events: vec![state],
        }
    });
    assert_eq!(calls, 1);
    assert_eq!(stopped.state, 5);
    assert_eq!(stopped.events, vec![4]);
    let stable = stopped
        .advance(100, |_, _| panic!("continued after fatal stop"))
        .close();
    assert_eq!(stable.outcome, Outcome::Stopped(Stop::Reject));
}

#[test]
fn continuation_values_are_passed_and_every_stop_is_absorbing() {
    let result = Execution::pending(3, 0).advance(10, |left, state| Execution {
        outcome: Outcome::Returned(if left == 0 {
            Break(state)
        } else {
            Continue(left - 1)
        }),
        state: state + left,
        events: vec![left],
    });
    assert_eq!(result.outcome, Outcome::Returned(Break(6)));
    assert_eq!(result.events, vec![3, 2, 1, 0]);
    for reason in [
        Stop::Reject,
        Stop::Abort,
        Stop::Exhausted,
        Stop::Incomplete,
        Stop::Refused,
    ] {
        let stopped: Prefix = Execution {
            outcome: Outcome::Stopped(reason),
            state: 7,
            events: vec![1, 4],
        };
        let result = stopped
            .advance(10, |_, _| panic!("resumed terminal result"))
            .close();
        assert_eq!(result.outcome, Outcome::Stopped(reason));
        assert_eq!((result.state, result.events), (7, vec![1, 4]));
    }
}

#[test]
fn stateful_callbacks_must_survive_resumption() {
    fn stateful() -> impl FnMut((), usize) -> Prefix {
        let mut calls = 0;
        move |(), state| {
            calls += 1;
            Prefix {
                outcome: Outcome::Returned(if calls == 2 {
                    Break(calls)
                } else {
                    Continue(())
                }),
                state: state + 1,
                events: vec![calls],
            }
        }
    }

    let whole = Prefix::pending((), 0).advance(2, stateful());
    let mut retained = stateful();
    let resumed = Prefix::pending((), 0)
        .advance(1, &mut retained)
        .advance(1, &mut retained);
    assert_eq!(whole, resumed);
    assert_eq!(resumed.outcome, Outcome::Returned(Break(2)));
    assert_eq!(resumed.events, [1, 2]);

    let reset = Prefix::pending((), 0)
        .advance(1, stateful())
        .advance(1, stateful());
    assert_eq!(reset.state, whole.state);
    assert_eq!(reset.outcome, Outcome::Returned(Continue(())));
    assert_eq!(reset.events, [1, 1]);
    assert_ne!(reset, whole);
}
