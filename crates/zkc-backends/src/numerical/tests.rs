use super::*;
use crate::refused;
use std::{panic::AssertUnwindSafe, sync::Arc};

fn policy(memory: usize) -> Policy {
    Policy {
        max_numerical_bytes: memory,
        ..Policy::default()
    }
}

fn code<T>(result: Result<T>) -> String {
    match result {
        Ok(_) => panic!("expected numerical refusal"),
        Err(error) => error.code,
    }
}

fn bytes(data: Vec<u8>) -> Result<Value> {
    Ok(Value::Bytes(data.into()))
}

#[test]
fn work_is_accumulated_checked_and_not_refunded() {
    let call = Call::new(
        &Policy {
            max_numerical_work: 3,
            ..policy(0)
        },
        0,
    );
    call.work(2).unwrap();
    assert_eq!(code(call.work(2)), "exhausted:numerical-work");
    assert_eq!(call.work.get(), 2);
    call.work(1).unwrap();
    call.work(0).unwrap();
    assert_eq!(code(call.work(1)), "exhausted:numerical-work");

    let call = Call::new(
        &Policy {
            max_numerical_work: u64::MAX,
            ..policy(0)
        },
        0,
    );
    call.work(u64::MAX).unwrap();
    assert_eq!(code(call.work(1)), "exhausted:numerical-work");
    assert_eq!(call.work.get(), u64::MAX);
}

#[test]
fn checked_work_formula_charges_setup_and_refuses_overflow_without_spending() {
    let call = Call::new(
        &Policy {
            max_numerical_work: u64::MAX,
            ..policy(0)
        },
        0,
    );
    call.work_items(0, u64::MAX, 1).unwrap();
    assert_eq!(call.work.get(), 1);
    for (len, rate, setup) in [(2, u64::MAX, 0), (1, u64::MAX, 1)] {
        assert_eq!(
            code(call.work_items(len, rate, setup)),
            "exhausted:numerical-work"
        );
        assert_eq!(call.work.get(), 1);
    }
    call.work_items(3, 2, 1).unwrap();
    assert_eq!(call.work.get(), 8);
}

#[test]
fn inline_scalar_reserves_exact_storage_without_a_staging_buffer() {
    for (memory, available, tuple_limit, error) in [
        (512, 512, 512, None),
        (511, 512, 512, Some("exhausted:numerical-bytes")),
        (0, 511, 512, Some("exhausted:output-bytes")),
        (0, 512, 511, Some("exhausted:output-bytes")),
    ] {
        let p = Policy {
            max_value_bytes: tuple_limit,
            ..policy(memory)
        };
        let call = Call::new(&p, available);
        let result = call.scalar(512);
        if let Some(error) = error {
            assert_eq!(code(result), error);
            assert_eq!(call.memory.get(), 0);
            assert_eq!(call.outputs.get(), 0);
        } else {
            let value = result
                .unwrap()
                .finish(|| {
                    assert_eq!(call.memory.get(), 512);
                    assert_eq!(call.outputs.get(), 512);
                    assert_eq!(code(call.scratch(1, 0u8)), "exhausted:numerical-bytes");
                    Ok(Value::Index(7))
                })
                .unwrap();
            drop(value);
            assert_eq!(call.memory.get(), 512);
            assert_eq!(call.outputs.get(), 512);
        }
    }
}

#[test]
fn scalar_and_vector_results_share_both_tuple_ceilings_and_live_storage() {
    for (available, tuple_limit) in [(770, 770), (769, 770), (770, 769)] {
        let p = Policy {
            max_value_bytes: tuple_limit,
            ..policy(772)
        };
        let call = Call::new(&p, available);
        call.scalar(512)
            .unwrap()
            .finish(|| Ok(Value::Index(1)))
            .unwrap();
        let result = call.output(2, 3u8, 258);
        if available == 770 && tuple_limit == 770 {
            let result = result.unwrap();
            assert_eq!(call.memory.get(), 772);
            result.finish(bytes).unwrap();
            assert_eq!(call.memory.get(), 770);
            assert_eq!(call.outputs.get(), 770);
            assert_eq!(code(call.scalar(1)), "exhausted:output-bytes");
        } else {
            assert_eq!(code(result), "exhausted:output-bytes");
            assert_eq!(call.memory.get(), 512);
            assert_eq!(call.outputs.get(), 512);
        }
    }
    // The result allowance fits, but live scalar + staging + final does not.
    let call = Call::new(&policy(771), 770);
    call.scalar(512)
        .unwrap()
        .finish(|| Ok(Value::Index(1)))
        .unwrap();
    assert_eq!(code(call.output(2, 0u8, 258)), "exhausted:numerical-bytes");
    assert_eq!(call.memory.get(), 512);
    assert_eq!(call.outputs.get(), 512);
}

#[test]
fn abandoned_failed_and_unwinding_scalar_results_release_storage_but_not_work() {
    let call = Call::new(&policy(512), 512);
    call.work(3).unwrap();
    let result = call.scalar(512).unwrap();
    drop(result);
    assert_eq!(call.memory.get(), 0);
    assert_eq!(call.outputs.get(), 0);
    let error = call
        .scalar(512)
        .unwrap()
        .finish(|| Err(refused("scalar-test")));
    assert_eq!(code(error), "refused:scalar-test");
    assert_eq!(call.memory.get(), 0);
    assert_eq!(call.outputs.get(), 0);
    assert!(
        std::panic::catch_unwind(AssertUnwindSafe(|| {
            let _ = call
                .scalar(512)
                .unwrap()
                .finish(|| panic!("scalar failure"));
        }))
        .is_err()
    );
    assert_eq!(call.memory.get(), 0);
    assert_eq!(call.outputs.get(), 0);
    assert_eq!(call.work.get(), 3);
    call.scalar(512)
        .unwrap()
        .finish(|| Ok(Value::Index(2)))
        .unwrap();
}

#[test]
fn policy_is_copied_and_new_limits_participate_in_equality() {
    let original = Policy::default();
    assert_eq!(original.max_numerical_work, 1 << 26);
    assert_eq!(original.max_numerical_bytes, 256 << 20);
    let mut changed = original;
    let call = Call::new(&changed, 256);
    changed.max_numerical_work = 0;
    assert_ne!(original, changed);
    changed = original;
    changed.max_numerical_bytes = 0;
    assert_ne!(original, changed);
    call.work(1).unwrap();
    call.scratch(1, 0u8).unwrap();
}

#[test]
fn aggregate_outputs_accept_exact_and_refuse_one_short() {
    let retained = 258;
    for (available, tuple_limit) in [
        (2 * retained, 2 * retained),
        (2 * retained - 1, 2 * retained),
        (2 * retained, 2 * retained - 1),
    ] {
        let p = Policy {
            max_value_bytes: tuple_limit,
            ..policy(4096)
        };
        let call = Call::new(&p, available);
        let first = call.output(2, 0u8, retained).unwrap();
        drop(first.finish(bytes).unwrap());
        // Dropping a published Value does not refund this call's finished output.
        assert_eq!(call.outputs.get(), retained);
        assert_eq!(call.memory.get(), retained);
        let second = call.output(2, 0u8, retained);
        if available == 2 * retained && tuple_limit == 2 * retained {
            second.unwrap().finish(bytes).unwrap();
            // The complete tuple must fit both independent output ceilings.
            assert_eq!(call.outputs.get(), 2 * retained);
            assert_eq!(call.memory.get(), 2 * retained);
        } else {
            assert_eq!(code(second), "exhausted:output-bytes");
            assert_eq!(call.outputs.get(), retained);
            assert_eq!(call.memory.get(), retained);
        }
    }
}

#[test]
fn unfinished_outputs_share_allowance_and_release_it_when_abandoned() {
    let call = Call::new(&policy(1024), 258);
    let output = call.output(2, 0u8, 258).unwrap();
    assert_eq!(code(call.output(0, 0u8, 1)), "exhausted:output-bytes");
    assert_eq!(call.outputs.get(), 258);
    drop(output);
    assert_eq!(call.outputs.get(), 0);
    assert_eq!(call.memory.get(), 0);
    call.output(2, 0u8, 258).unwrap().finish(bytes).unwrap();
}

#[test]
fn per_value_and_aggregate_preflight_precede_workspace_allocation() {
    let p = Policy {
        max_value_bytes: 257,
        ..policy(0)
    };
    let call = Call::new(&p, usize::MAX);
    assert_eq!(code(call.output(2, 0u8, 258)), "exhausted:output-bytes");
    let call = Call::new(&policy(0), 257);
    assert_eq!(code(call.output(2, 0u8, 258)), "exhausted:output-bytes");
    assert_eq!(call.outputs.get(), 0);
    assert_eq!(call.memory.get(), 0);
}

#[test]
fn live_scratch_accepts_exact_and_refuses_one_short() {
    for limit in [20, 19] {
        let call = Call::new(&policy(limit), 0);
        let mut first = call.scratch(3, 1u32).unwrap();
        first.as_mut()[1] = 7;
        assert_eq!(first.as_ref(), &[1, 7, 1]);
        let second = call.scratch(2, 2u32);
        if limit == 20 {
            let second = second.unwrap();
            assert_eq!(call.memory.get(), 20);
            drop(first);
            assert_eq!(call.memory.get(), 8);
            drop(second);
        } else {
            assert_eq!(code(second), "exhausted:numerical-bytes");
            assert_eq!(call.memory.get(), 12);
            drop(first);
        }
        assert_eq!(call.memory.get(), 0);
        call.scratch(3, 0u32).unwrap();
    }
}

#[test]
fn scratch_staging_and_final_storage_share_the_live_memory_limit() {
    // 16 scratch bytes + 32 staging bytes + 288 conservative final bytes.
    for limit in [336, 335] {
        let call = Call::new(&policy(limit), 288);
        let scratch = call.scratch(2, 0u64).unwrap();
        let output = call.output(4, 0u64, 288);
        if limit == 336 {
            let output = output.unwrap();
            assert_eq!(call.memory.get(), 336);
            drop(output);
        } else {
            assert_eq!(code(output), "exhausted:numerical-bytes");
        }
        assert_eq!(call.memory.get(), 16);
        assert_eq!(call.outputs.get(), 0);
        drop(scratch);
        call.output(4, 0u64, 288).unwrap();
        assert_eq!(call.memory.get(), 0);
    }
}

#[test]
fn freezing_reserves_vec_and_final_storage_at_the_same_time() {
    let call = Call::new(&policy(264), 260);
    let output = call.output(4, 3u8, 260).unwrap();
    let value = output
        .finish(|data| {
            assert_eq!(call.memory.get(), 264);
            assert_eq!(code(call.scratch(1, 0u8)), "exhausted:numerical-bytes");
            let final_storage = Value::Bytes(data.into());
            assert_eq!(call.memory.get(), 264);
            assert_eq!(code(call.scratch(1, 0u8)), "exhausted:numerical-bytes");
            Ok(final_storage)
        })
        .unwrap();
    assert_eq!(call.memory.get(), 260);
    let scratch = call.scratch(4, 0u8).unwrap();
    assert_eq!(call.memory.get(), 264);
    drop(scratch);
    drop(value);
    assert_eq!(call.memory.get(), 260);
}

#[test]
fn failed_finish_does_not_return_partial_output_and_releases_reservations() {
    let input = [4u8, 5, 6];
    let call = Call::new(&policy(262), 259);
    call.work(3).unwrap();
    let mut output = call.output(3, 0u8, 259).unwrap();
    output.as_mut_slice()[0] = input[0];
    let result = output.finish(|data| {
        assert_eq!(data, [4, 0, 0]);
        Err(refused("numerical-test"))
    });
    assert_eq!(code(result), "refused:numerical-test");
    assert_eq!(input, [4, 5, 6]);
    assert_eq!(call.memory.get(), 0);
    assert_eq!(call.outputs.get(), 0);
    assert_eq!(call.work.get(), 3);
    call.output(3, 0u8, 259).unwrap().finish(bytes).unwrap();
}

#[test]
fn checked_payload_and_counter_overflow_leave_no_reservation() {
    let call = Call::new(&policy(usize::MAX), usize::MAX);
    assert_eq!(
        code(call.scratch(usize::MAX, 0u64)),
        "exhausted:numerical-bytes"
    );
    assert_eq!(
        code(call.scratch(isize::MAX as usize + 1, 0u8)),
        "exhausted:numerical-bytes"
    );
    assert_eq!(
        code(call.output(usize::MAX, 0u64, 256)),
        "exhausted:numerical-bytes"
    );
    assert_eq!(call.outputs.get(), 0);
    assert_eq!(call.memory.get(), 0);

    // Exercise addition overflow without asking the allocator for huge storage.
    let counter = Cell::new(usize::MAX);
    for reason in ["output-bytes", "numerical-bytes"] {
        assert_eq!(
            code(Reservation::new(&counter, 1, usize::MAX, reason)),
            format!("exhausted:{reason}")
        );
        assert_eq!(counter.get(), usize::MAX);
    }
}

#[test]
fn allocator_capacity_failure_releases_the_buffer_reservation() {
    let call = Call::new(&policy(32), 0);
    let reservation = call.reserve_memory(32).unwrap();
    // Vec rejects this capacity before any allocation or initialization.
    assert_eq!(
        code(Buffer::new(usize::MAX, 0u64, reservation)),
        "exhausted:allocation"
    );
    assert_eq!(call.memory.get(), 0);
    call.scratch(4, 0u64).unwrap();
}

#[test]
fn failed_initialization_and_freeze_unwind_release_reservations() {
    struct CloneFailure(u8);
    impl Clone for CloneFailure {
        fn clone(&self) -> Self {
            panic!("clone failure: {}", self.0);
        }
    }
    let call = Call::new(&policy(1024), 258);
    assert!(
        std::panic::catch_unwind(AssertUnwindSafe(|| {
            let _ = call.output(2, CloneFailure(0), 258);
        }))
        .is_err()
    );
    assert_eq!(call.memory.get(), 0);
    assert_eq!(call.outputs.get(), 0);
    assert!(
        std::panic::catch_unwind(AssertUnwindSafe(|| {
            let output = call.output(2, 0u8, 258).unwrap();
            let _ = output.finish(|_| panic!("freeze failure"));
        }))
        .is_err()
    );
    assert_eq!(call.memory.get(), 0);
    assert_eq!(call.outputs.get(), 0);
}

#[test]
fn empty_storage_still_reserves_positive_final_representation_bytes() {
    let call = Call::new(&policy(0), 256);
    let scratch = call.scratch(0, 0u64).unwrap();
    assert!(scratch.as_ref().is_empty());
    assert_eq!(call.memory.get(), 0);
    assert_eq!(code(call.output(0, 0u64, 256)), "exhausted:numerical-bytes");
    assert_eq!(call.outputs.get(), 0);
    for limit in [256, 255] {
        let call = Call::new(&policy(limit), 256);
        let output = call.output(0, 0u8, 256);
        if limit == 256 {
            output.unwrap().finish(bytes).unwrap();
            assert_eq!(call.memory.get(), 256);
            assert_eq!(call.outputs.get(), 256);
        } else {
            assert_eq!(code(output), "exhausted:numerical-bytes");
            assert_eq!(call.memory.get(), 0);
        }
    }
    let call = Call::new(&policy(256), 255);
    assert_eq!(code(call.output(0, 0u8, 256)), "exhausted:output-bytes");
}

#[test]
fn row_major_checks_asymmetric_shape_and_transpose_indexing() {
    let data = [1, 2, 3, 4, 5, 6];
    let view = RowMajor::new(&data, 2, 3).unwrap();
    assert_eq!((view.rows(), view.cols()), (2, 3));
    assert_eq!(view.row(0), Some(&data[..3]));
    assert_eq!(view.row(1), Some(&data[3..]));
    for row in 0..3 {
        for col in 0..2 {
            assert_eq!(view.transpose(row, col), Some(&data[col * 3 + row]));
        }
    }
    assert_eq!(view.get(1, 2), Some(&6));
    assert_eq!(view.get(2, 0), None);
    assert_eq!(view.get(0, 3), None);
    assert_eq!(view.transpose(3, 0), None);
    assert_eq!(view.transpose(0, 2), None);
    assert_eq!(view.row(2), None);
    assert!(RowMajor::new(&data, 3, 3).is_none());
    assert!(RowMajor::new(&data, usize::MAX, 2).is_none());
    assert!(RowMajor::new(&data, 0, 6).is_none());
}

#[test]
fn row_major_preserves_distinct_zero_axes_and_checks_bounds() {
    let data: [u8; 0] = [];
    let no_rows = RowMajor::new(&data, 0, 5).unwrap();
    assert_eq!((no_rows.rows(), no_rows.cols()), (0, 5));
    assert_eq!(no_rows.row(0), None);
    assert_eq!(no_rows.transpose(0, 0), None);
    let no_cols = RowMajor::new(&data, 5, 0).unwrap();
    assert_eq!((no_cols.rows(), no_cols.cols()), (5, 0));
    assert_eq!(no_cols.row(4), Some(&data[..]));
    assert_eq!(no_cols.row(5), None);
    assert_eq!(no_cols.get(4, 0), None);
    assert_eq!(no_cols.transpose(0, 0), None);
    assert!(RowMajor::new(&data, 0, 0).unwrap().row(0).is_none());
    assert!(RowMajor::new(&data, usize::MAX, 2).is_none());
    let huge_empty = RowMajor::new(&data, usize::MAX, 0).unwrap();
    assert_eq!(huge_empty.row(usize::MAX - 1), Some(&data[..]));
    assert!(RowMajor::new(&data, 0, usize::MAX).is_some());
}

#[test]
fn repeated_immutable_input_aliases_remain_unchanged() {
    let input: Arc<[u64]> = vec![1, 2, 3, 4].into();
    let alias = Arc::clone(&input);
    let left = RowMajor::new(&input, 2, 2).unwrap();
    let right = RowMajor::new(&alias, 2, 2).unwrap();
    let call = Call::new(&policy(320), 288);
    let mut output = call.output(4, 0u64, 288).unwrap();
    for row in 0..2 {
        for col in 0..2 {
            output.as_mut_slice()[row * 2 + col] =
                left.get(row, col).unwrap() + right.get(row, col).unwrap();
        }
    }
    let Value::Indices(result) = output
        .finish(|data| Ok(Value::Indices(data.into())))
        .unwrap()
    else {
        panic!("expected indices");
    };
    assert_eq!(&*input, &[1, 2, 3, 4]);
    assert_eq!(&*alias, &[1, 2, 3, 4]);
    assert_eq!(&*result, &[2, 4, 6, 8]);
    assert!(Arc::ptr_eq(&input, &alias));
    assert!(!Arc::ptr_eq(&input, &result));
}
