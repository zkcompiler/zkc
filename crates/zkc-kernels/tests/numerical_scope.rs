//! Independent payload accounting, publication and unwind boundaries.
use std::panic::AssertUnwindSafe;
use zkc_kernels::numerical::Call;
use zkc_kernels::numerical::Error;
use zkc_kernels::numerical::Limits;
use zkc_kernels::numerical::RowMajor;

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
