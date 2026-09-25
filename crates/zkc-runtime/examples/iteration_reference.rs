//! Deterministic finite-controller corpus compared against the Lean evaluator.
use std::ops::ControlFlow::{Break, Continue};
use zkc_runtime::{Outcome, Stop, iteration::Execution};

fn stop_tag(reason: Stop) -> &'static str {
    match reason {
        Stop::Reject => "reject",
        Stop::Abort => "abort",
        Stop::Exhausted => "exhausted",
        Stop::Incomplete => "incomplete",
        Stop::Refused => "refused",
    }
}

fn result_tag(outcome: &Outcome<usize>) -> String {
    match outcome {
        Outcome::Returned(value) => format!("returned:{value}"),
        Outcome::Stopped(reason) => stop_tag(*reason).into(),
    }
}

fn prefix_tag(outcome: &Outcome<std::ops::ControlFlow<usize, usize>>) -> String {
    match outcome {
        Outcome::Returned(Continue(next)) => format!("pending:{next}"),
        Outcome::Returned(Break(value)) => format!("returned:{value}"),
        Outcome::Stopped(reason) => stop_tag(*reason).into(),
    }
}

fn record<A>(result: &Execution<usize, usize, A>, tag: String) -> String {
    let events = result
        .events
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(",");
    format!("{tag}|{}|{events}", result.state)
}

fn countdown(
    left: usize,
    state: usize,
) -> Execution<usize, usize, std::ops::ControlFlow<usize, usize>> {
    Execution {
        outcome: Outcome::Returned(if left == 0 {
            Break(state)
        } else {
            Continue(left - 1)
        }),
        state: state + left,
        events: vec![left],
    }
}

fn main() {
    for target in 0..6 {
        for fuel in 0..9 {
            for initial in 0..4 {
                for fatal in [false, true] {
                    let result =
                        Execution::pending((), initial).advance(fuel, |(), state| Execution {
                            outcome: if fatal {
                                Outcome::Stopped(Stop::Reject)
                            } else {
                                Outcome::Returned(if state < target {
                                    Continue(())
                                } else {
                                    Break(state)
                                })
                            },
                            state: state + 1,
                            events: vec![state],
                        });
                    let tag = match result.outcome {
                        Outcome::Returned(Continue(())) => "pending".into(),
                        Outcome::Returned(Break(value)) => format!("returned:{value}"),
                        Outcome::Stopped(reason) => stop_tag(reason).into(),
                    };
                    let events = result
                        .events
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(",");
                    println!(
                        "{target}|{fuel}|{initial}|{fatal}|{tag}|{}|{events}",
                        result.state
                    );
                }
            }
        }
    }
    for seed in [0, 1, 3] {
        for initial in [0, 4] {
            for first in 0..6 {
                for second in 0..6 {
                    let whole =
                        Execution::pending(seed, initial).advance(first + second, countdown);
                    let split = Execution::pending(seed, initial)
                        .advance(first, countdown)
                        .advance(second, countdown);
                    let key = format!("resume|{seed}|{initial}|{first}|{second}");
                    println!("{key}|whole|{}", record(&whole, prefix_tag(&whole.outcome)));
                    println!("{key}|split|{}", record(&split, prefix_tag(&split.outcome)));
                    let closed_whole = whole.close();
                    let closed_split = split.close();
                    println!(
                        "{key}|close-whole|{}",
                        record(&closed_whole, result_tag(&closed_whole.outcome))
                    );
                    println!(
                        "{key}|close-split|{}",
                        record(&closed_split, result_tag(&closed_split.outcome))
                    );
                }
            }
        }
    }
    for reason in [
        Stop::Reject,
        Stop::Abort,
        Stop::Exhausted,
        Stop::Incomplete,
        Stop::Refused,
    ] {
        for fuel in [0, 1, 3] {
            let result = Execution::pending((), 0).advance(fuel, |(), state| Execution {
                outcome: if state == 0 {
                    Outcome::Returned(Continue::<usize, ()>(()))
                } else {
                    Outcome::Stopped(reason)
                },
                state: state + 1,
                events: vec![state],
            });
            let tag = match result.outcome {
                Outcome::Returned(Continue(())) => "pending".into(),
                Outcome::Returned(Break(value)) => format!("returned:{value}"),
                Outcome::Stopped(why) => stop_tag(why).into(),
            };
            let key = format!("stop|{}|{fuel}", stop_tag(reason));
            println!("{key}|prefix|{}", record(&result, tag));
            let closed = result.close();
            println!(
                "{key}|close|{}",
                record(&closed, result_tag(&closed.outcome))
            );
        }
    }
}
