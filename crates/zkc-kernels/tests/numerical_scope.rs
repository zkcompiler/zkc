//! Independent payload accounting, publication and unwind boundaries.
use std::panic::AssertUnwindSafe;
use zkc_kernels::{
    matrix::RowMajor,
    numerical::{Call, Error, Limits, Usage, payload_bytes},
};

#[test]
fn owned_output_adopts_the_same_allocation_at_the_single_buffer_boundary() {
    struct Owner(Vec<u32>);
    let call = Call::new(Limits {
        work: 0,
        memory: 19,
        outputs: 16,
    });
    let scratch = call.scratch(3, 0u8).unwrap();
    // Ordinary construction still needs both the staging and final buffers.
    assert!(matches!(call.output(4, 0u32, 16), Err(Error::Memory)));
    assert_eq!(call.usage().memory, 3);
    assert_eq!(call.usage().outputs, 0);
    let mut output = call.output_owned(4, 0u32, 16).unwrap();
    output.as_mut_slice().copy_from_slice(&[2, 3, 5, 7]);
    let pointer = output.as_mut_slice().as_ptr();
    let value = output
        .finish(|data| {
            assert_eq!(data.as_ptr(), pointer);
            assert_eq!(data.len(), 4);
            let capacity = data.capacity();
            let owner = Owner(data);
            assert_eq!(owner.0.as_ptr(), pointer);
            assert_eq!(owner.0.capacity(), capacity);
            assert_eq!(call.usage().memory, 19);
            assert_eq!(call.usage().outputs, 16);
            Ok::<_, ()>(owner)
        })
        .unwrap();
    assert_eq!(value.0.as_ptr(), pointer);
    assert_eq!(value.0, [2, 3, 5, 7]);
    drop(value);
    drop(scratch);
    assert_eq!(call.usage().memory, 16);
    assert_eq!(call.usage().outputs, 16);
}

#[test]
fn owned_output_floors_retention_at_typed_payload_and_checks_both_limits() {
    // The payload is twelve bytes, even when a caller supplies a smaller bound.
    for retained in [0, 11, 12, 17] {
        let bound = retained.max(payload_bytes::<[u16; 2]>(3).unwrap());
        for (memory, outputs, expected) in [
            (bound - 1, bound, Some(Error::Memory)),
            (bound, bound - 1, Some(Error::OutputBytes)),
            (bound, bound, None),
        ] {
            let call = Call::new(Limits {
                work: 0,
                memory,
                outputs,
            });
            match expected {
                Some(expected) => {
                    assert!(matches!(
                        call.output_owned(3, [0u16; 2], retained),
                        Err(error) if error == expected
                    ));
                    assert_eq!(call.usage().memory, 0);
                    assert_eq!(call.usage().outputs, 0);
                }
                None => {
                    let output = call.output_owned(3, [0u16; 2], retained).unwrap();
                    assert_eq!(call.usage().memory, bound);
                    assert_eq!(call.usage().outputs, bound);
                    output.finish(Ok::<_, ()>).unwrap();
                    assert_eq!(call.usage().memory, bound);
                    assert_eq!(call.usage().outputs, bound);
                }
            }
        }
    }
}

#[test]
fn owned_output_checks_aggregate_live_and_finished_charges() {
    let call = Call::new(Limits {
        work: 0,
        memory: 20,
        outputs: 16,
    });
    let first = call.output_owned(2, 0u32, 0).unwrap();
    let second = call.output_owned(2, 0u32, 0).unwrap();
    let full = call.usage();
    assert!(matches!(
        call.output_owned(1, 0u8, 1),
        Err(Error::OutputBytes)
    ));
    assert_eq!(call.usage(), full);
    drop(second);
    first.finish(Ok::<_, ()>).unwrap();
    let scratch = call.scratch(5, 0u8).unwrap();
    let baseline = call.usage();
    assert!(matches!(call.output_owned(2, 0u32, 0), Err(Error::Memory)));
    assert_eq!(call.usage(), baseline);
    drop(scratch);
    call.output_owned(2, 0u32, 0)
        .unwrap()
        .finish(Ok::<_, ()>)
        .unwrap();
    assert_eq!(call.usage(), full);
}

#[test]
fn owned_output_empty_zero_sized_and_overflow_boundaries() {
    let call = Call::new(Limits {
        work: 0,
        memory: 0,
        outputs: 0,
    });
    assert!(
        call.output_owned(0, 0u64, 0)
            .unwrap()
            .as_mut_slice()
            .is_empty()
    );
    let empty = call
        .output_owned(0, 0u64, 0)
        .unwrap()
        .finish(Ok::<_, ()>)
        .unwrap();
    assert!(empty.is_empty());
    let units = call
        .output_owned(3, (), 0)
        .unwrap()
        .finish(Ok::<_, ()>)
        .unwrap();
    assert_eq!(units.len(), 3);
    for len in [isize::MAX as usize, usize::MAX] {
        assert!(matches!(
            call.output_owned(len, 0u16, 0),
            Err(Error::Memory)
        ));
    }
    assert!(matches!(
        call.output_owned(0, 0u64, 1),
        Err(Error::OutputBytes)
    ));
    assert!(matches!(
        call.output_owned(1, 0u8, 0),
        Err(Error::OutputBytes)
    ));
    assert_eq!(
        call.usage(),
        Usage {
            work: 0,
            memory: 0,
            outputs: 0
        }
    );

    let call = Call::new(Limits {
        work: 0,
        memory: usize::MAX,
        outputs: usize::MAX,
    });
    assert!(matches!(
        call.output_owned(0, (), isize::MAX as usize + 1),
        Err(Error::OutputBytes)
    ));
    let output = call.output_owned(0, (), 7).unwrap();
    assert_eq!(call.usage().memory, 7);
    assert_eq!(call.usage().outputs, 7);
    drop(output);
    assert_eq!(call.usage().memory, 0);
    assert_eq!(call.usage().outputs, 0);
}

#[test]
fn owned_output_drop_failure_and_unwind_restore_only_unfinished_charges() {
    let call = Call::new(Limits {
        work: 7,
        memory: 12,
        outputs: 12,
    });
    call.work(7).unwrap();
    call.output_owned(4, 0u8, 4)
        .unwrap()
        .finish(Ok::<_, ()>)
        .unwrap();
    let baseline = call.usage();
    drop(call.output_owned(8, 0u8, 8).unwrap());
    assert_eq!(call.usage(), baseline);
    let output = call.output_owned(8, 0u8, 8).unwrap();
    assert_eq!(
        output.finish(|_| Err::<(), _>("freeze failure")),
        Err("freeze failure")
    );
    assert_eq!(call.usage(), baseline);
    for during_freeze in [false, true] {
        assert!(
            std::panic::catch_unwind(AssertUnwindSafe(|| {
                let mut output = call.output_owned(8, 0u8, 8).unwrap();
                if during_freeze {
                    let _: Result<(), ()> = output.finish(|data| {
                        assert_eq!(call.usage().memory, 12);
                        assert_eq!(data.len(), 8);
                        panic!("freeze unwind");
                    });
                } else {
                    output.as_mut_slice()[0] = 1;
                    panic!("computation unwind");
                }
            }))
            .is_err()
        );
        assert_eq!(call.usage(), baseline);
    }
    call.output_owned(8, 0u8, 8)
        .unwrap()
        .finish(Ok::<_, ()>)
        .unwrap();
    assert_eq!(
        call.usage(),
        Usage {
            work: 7,
            memory: 12,
            outputs: 12
        }
    );
}

#[test]
fn owned_output_keeps_its_charge_through_element_destruction() {
    use std::cell::Cell;
    #[derive(Clone)]
    struct ObservedDrop<'a> {
        call: &'a Call,
        charged_drops: &'a Cell<usize>,
        expected: Usage,
    }
    impl Drop for ObservedDrop<'_> {
        fn drop(&mut self) {
            if self.call.usage() == self.expected {
                self.charged_drops.set(self.charged_drops.get() + 1);
            }
        }
    }
    let payload = payload_bytes::<ObservedDrop<'_>>(2).unwrap();
    let call = Call::new(Limits {
        work: 0,
        memory: payload,
        outputs: payload,
    });
    let baseline = call.usage();
    for mode in 0..3 {
        let charged_drops = Cell::new(0);
        let output = call
            .output_owned(
                2,
                ObservedDrop {
                    call: &call,
                    charged_drops: &charged_drops,
                    expected: Usage {
                        work: 0,
                        memory: payload,
                        outputs: payload,
                    },
                },
                payload,
            )
            .unwrap();
        match mode {
            0 => drop(output),
            1 => assert_eq!(
                output.finish(|_| Err::<(), _>("freeze failure")),
                Err("freeze failure")
            ),
            _ => assert!(
                std::panic::catch_unwind(AssertUnwindSafe(|| {
                    let _: Result<(), ()> = output.finish(|_| panic!("freeze unwind"));
                }))
                .is_err()
            ),
        }
        assert_eq!(charged_drops.get(), 2);
        assert_eq!(call.usage(), baseline);
    }
}

#[test]
fn output_initialization_unwind_releases_payload_and_reservations() {
    use std::{cell::Cell, rc::Rc};
    struct CloneFailure {
        live: Rc<Cell<usize>>,
        clones: Rc<Cell<usize>>,
    }
    impl Clone for CloneFailure {
        fn clone(&self) -> Self {
            let clones = self.clones.get() + 1;
            self.clones.set(clones);
            assert!(clones < 2, "initialization unwind");
            self.live.set(self.live.get() + 1);
            Self {
                live: self.live.clone(),
                clones: self.clones.clone(),
            }
        }
    }
    impl Drop for CloneFailure {
        fn drop(&mut self) {
            self.live.set(self.live.get() - 1);
        }
    }
    let payload = payload_bytes::<CloneFailure>(4).unwrap();
    let call = Call::new(Limits {
        work: 0,
        memory: 2 * payload,
        outputs: payload,
    });
    for owned in [false, true] {
        let live = Rc::new(Cell::new(1));
        let clones = Rc::new(Cell::new(0));
        assert!(
            std::panic::catch_unwind(AssertUnwindSafe(|| {
                let initial = CloneFailure {
                    live: live.clone(),
                    clones: clones.clone(),
                };
                if owned {
                    let _ = call.output_owned(4, initial, payload);
                } else {
                    let _ = call.output(4, initial, payload);
                }
            }))
            .is_err()
        );
        assert_eq!(clones.get(), 2);
        assert_eq!(live.get(), 0);
        assert_eq!(call.usage().memory, 0);
        assert_eq!(call.usage().outputs, 0);
    }
}

#[test]
fn work_and_storage_have_distinct_lifetimes() {
    let call = Call::new(Limits {
        work: 7,
        memory: 12,
        outputs: 8,
    });
    call.work_items(2, 3, 1).unwrap();
    assert_eq!(call.work(1), Err(Error::Work));
    assert_eq!(call.work_items(2, u64::MAX, 0), Err(Error::Work));
    assert_eq!(call.usage().work, 7);
    {
        let scratch = call.scratch(4, 0u8).unwrap();
        let output = call.output(4, 0u8, 4).unwrap();
        assert_eq!(call.usage().memory, 12);
        assert!(matches!(call.scratch(1, 0u8), Err(Error::Memory)));
        let value = output
            .finish(|value| {
                // Staging and retained storage overlap during the freeze.
                assert_eq!(call.usage().memory, 12);
                Ok::<_, ()>(value.into_boxed_slice())
            })
            .unwrap();
        assert_eq!(call.usage().memory, 8);
        drop(value);
        drop(scratch);
    }
    // Finished results stay charged, even when their returned value is dropped.
    assert_eq!(call.usage().memory, 4);
    assert_eq!(call.usage().outputs, 4);
    let output = call.output(4, 0u8, 4).unwrap();
    assert!(output.finish(|_| Err::<(), _>("freeze failure")).is_err());
    assert_eq!(call.usage().memory, 4);
    assert_eq!(call.usage().outputs, 4);
    assert!(
        std::panic::catch_unwind(AssertUnwindSafe(|| {
            let output = call.output(4, 0u8, 4).unwrap();
            let _: Result<(), ()> = output.finish(|_| panic!("freeze unwind"));
        }))
        .is_err()
    );
    assert_eq!(call.usage().memory, 4);
    assert_eq!(call.usage().outputs, 4);
    assert_eq!(call.usage().work, 7);
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
