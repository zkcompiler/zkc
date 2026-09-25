use std::ops::ControlFlow;
use zkc_runtime::{
    Outcome, Stop,
    attempt::{Context, Controller, Decision, Event, Limits},
};

fn retry_then_finish(
    attempt: u64,
    context: &mut Context<Vec<u64>>,
) -> Result<Decision<&'static str, u64>, Stop> {
    context.state_mut().push(attempt);
    context.append(&[attempt as u8])?;
    Ok(if attempt < 2 {
        Decision::Retry("zero-challenge")
    } else {
        Decision::Complete(attempt)
    })
}

fn controller() -> Controller<Vec<u64>, &'static str, u64> {
    Controller::new(
        Vec::new(),
        Limits {
            attempts: 4,
            proof_bytes: 8,
        },
    )
}

#[test]
fn discarded_output_does_not_rewind_state_and_only_completed_bytes_escape() {
    let result = controller().advance(4, retry_then_finish).close();
    let Outcome::Returned(proof) = result.outcome else {
        panic!("not produced")
    };
    assert_eq!(proof.bytes, [2]);
    assert_eq!(proof.attempt, 2);
    assert_eq!(result.state, [0, 1, 2]);
    assert_eq!(result.events.len(), 6);
    assert!(matches!(result.events[1], Event::Retried { bytes: 1, .. }));
    assert!(matches!(result.events[5], Event::Produced { bytes: 1, .. }));
}

#[test]
fn scheduling_fuel_preserves_pending_and_resumption() {
    let pending = controller().advance(1, retry_then_finish);
    assert_eq!(
        pending.prefix().outcome,
        Outcome::Returned(ControlFlow::Continue(1))
    );
    let split = pending.advance(3, retry_then_finish).close();
    assert_eq!(split, controller().advance(4, retry_then_finish).close());
    let stopped = controller().advance(1, retry_then_finish).close();
    assert_eq!(stopped.outcome, Outcome::Stopped(Stop::Exhausted));
    assert_eq!(stopped.state, [0]);
}

#[test]
fn ignored_buffer_failure_cannot_produce_a_truncated_proof() {
    let result = controller()
        .advance(1, |_, context| {
            context.state_mut().push(7);
            context.append(&[1, 2])?;
            assert_eq!(context.append(&[3; 9]), Err(Stop::Exhausted));
            Ok(Decision::Complete(7))
        })
        .close();
    assert_eq!(result.outcome, Outcome::Stopped(Stop::Exhausted));
    assert_eq!(result.state, [7]);
    assert!(matches!(result.events[1], Event::Stopped { bytes: 2, .. }));
}

#[test]
fn terminal_failures_are_absorbing_and_keep_effects() {
    for reason in [
        Stop::Reject,
        Stop::Abort,
        Stop::Refused,
        Stop::Exhausted,
        Stop::Incomplete,
    ] {
        let result = controller()
            .advance(1, |_, context| {
                context.state_mut().push(9);
                context.append(&[4])?;
                Err(reason)
            })
            .advance(3, |_, _| panic!("terminal body restarted"))
            .close();
        assert_eq!(result.outcome, Outcome::Stopped(reason));
        assert_eq!(result.state, [9]);
        assert_eq!(result.events.len(), 2);
    }
}

#[test]
fn deployment_limit_does_not_invoke_an_extra_attempt() {
    let result = Controller::new(
        0,
        Limits {
            attempts: 2,
            proof_bytes: 0,
        },
    )
    .advance(9, |_, context| {
        *context.state_mut() += 1;
        Ok::<Decision<(), ()>, Stop>(Decision::Retry(()))
    })
    .close();
    assert_eq!(result.outcome, Outcome::Stopped(Stop::Exhausted));
    assert_eq!(result.state, 2);
    assert_eq!(result.events.len(), 5);
    assert_eq!(
        result.events[4],
        Event::Stopped {
            attempt: 2,
            reason: Stop::Exhausted,
            bytes: 0,
        }
    );
    let empty = Controller::new(
        0,
        Limits {
            attempts: 0,
            proof_bytes: 0,
        },
    )
    .advance(1, |_, _| -> Result<Decision<(), ()>, Stop> {
        panic!("zero budget")
    })
    .close();
    assert_eq!(empty.state, 0);
    assert_eq!(
        empty.events,
        [Event::Stopped {
            attempt: 0,
            reason: Stop::Exhausted,
            bytes: 0,
        }]
    );
}
