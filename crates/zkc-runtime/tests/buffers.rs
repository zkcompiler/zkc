use zkc_runtime::{
    Error,
    buffer::{BufferStore, PackedBuffers, SegmentedBuffers},
};

fn publication<S: BufferStore<u8>>(mut store: S, other: S) {
    assert_eq!(
        store.publish(&[2]).err(),
        Some(Error("buffer-capacity-violation"))
    );
    store.reserve(4, 3).unwrap();
    let before = store.usage();
    let a = store.publish(&[1, 2, 3]).unwrap();
    let b = store.publish(&[4]).unwrap();
    let empty = store.publish(&[]).unwrap();
    assert_eq!(store.usage().reserved_bytes, before.reserved_bytes);
    assert_eq!(store.read(&a).unwrap(), &[1, 2, 3]);
    assert_eq!(store.read(&b).unwrap(), &[4]);
    assert!(store.read(&empty).unwrap().is_empty());
    assert_eq!(other.read(&a), Err(Error("foreign-handle")));
    assert_eq!(
        store.publish(&[5]).err(),
        Some(Error("buffer-capacity-violation"))
    );
    assert_eq!(store.read(&a).unwrap(), &[1, 2, 3]);
    // A failed reservation cannot invalidate or mutate existing buffers.
    assert_eq!(
        store.reserve(usize::MAX, usize::MAX),
        Err(Error("capacity-overflow"))
    );
    assert_eq!(store.read(&b).unwrap(), &[4]);
    store.reserve(1000, 1).unwrap();
    let after_reservation = store.usage().reserved_bytes;
    let c = store.publish(&[6; 1000]).unwrap();
    assert_eq!(store.read(&a).unwrap(), &[1, 2, 3]);
    assert_eq!(store.read(&c).unwrap(), &[6; 1000]);
    assert_eq!(store.usage().reserved_bytes, after_reservation);
    assert_eq!(
        store.required_bytes(0, 0).unwrap(),
        store.usage().reserved_bytes
    );
}
#[test]
fn packed_publication_and_alias_custody() {
    publication(PackedBuffers::new().unwrap(), PackedBuffers::new().unwrap());
}
#[test]
fn segmented_publication_and_alias_custody() {
    publication(
        SegmentedBuffers::new().unwrap(),
        SegmentedBuffers::new().unwrap(),
    );
}
#[test]
fn segmented_reservation_counts_stranded_capacity() {
    let mut store = SegmentedBuffers::<u32>::new().unwrap();
    store.reserve(10, 1).unwrap();
    let a = store.publish(&[1]).unwrap();
    let pointer = store.read(&a).unwrap().as_ptr();
    let old = store.usage().reserved_bytes;
    let required = store.required_bytes(20, 1).unwrap();
    assert!(required >= old + 20 * std::mem::size_of::<u32>());
    store.reserve(20, 1).unwrap();
    let before_publish = store.usage().reserved_bytes;
    let b = store.publish(&[2; 20]).unwrap();
    assert_eq!(store.read(&a).unwrap().as_ptr(), pointer);
    assert_eq!(store.read(&a).unwrap(), &[1]);
    assert_eq!(store.read(&b).unwrap(), &[2; 20]);
    assert_eq!(store.usage().reserved_bytes, before_publish);
    assert!(store.required_bytes(0, 0).unwrap() >= old + 80);
}
#[test]
fn capture_is_an_owned_copy_not_a_borrow() {
    for segmented in [false, true] {
        fn check<S: BufferStore<u8>>(mut store: S) {
            store.reserve(3, 1).unwrap();
            let mut source = [1, 2, 3];
            let reference = store.publish(&source).unwrap();
            source[0] = 6;
            assert_eq!(source, [6, 2, 3]);
            assert_eq!(store.read(&reference).unwrap(), &[1, 2, 3]);
        }
        if segmented {
            check(SegmentedBuffers::new().unwrap());
        } else {
            check(PackedBuffers::new().unwrap());
        }
    }
}

#[test]
fn zero_sized_elements_still_have_checked_logical_lengths() {
    fn check<S: BufferStore<()>>(mut store: S) {
        store.reserve(1, 1).unwrap();
        let a = store.publish(&[()]).unwrap();
        assert_eq!(store.read(&a).unwrap().len(), 1);
        assert_eq!(
            store.reserve(usize::MAX, 0),
            Err(Error("capacity-overflow"))
        );
        assert!(store.usage().reserved_bytes > 0); // reference metadata
        assert_eq!(store.read(&a).unwrap().len(), 1);
    }
    check(PackedBuffers::new().unwrap());
    check(SegmentedBuffers::new().unwrap());
}

#[test]
fn repeated_reservations_guarantee_spare_not_cumulative_capacity() {
    fn check<S: BufferStore<u8>>(mut store: S) {
        store.reserve(4, 2).unwrap();
        let before = store.usage().reserved_bytes;
        store.reserve(4, 2).unwrap();
        assert_eq!(store.usage().reserved_bytes, before);
        let reference = store.publish(&[1, 2, 3, 4]).unwrap();
        assert_eq!(store.read(&reference).unwrap(), &[1, 2, 3, 4]);
        // Do not assert exact allocator capacity: reserve promises a minimum.
    }
    check(PackedBuffers::new().unwrap());
    check(SegmentedBuffers::new().unwrap());
}

#[test]
fn unrepresentable_vec_capacity_preserves_existing_buffers() {
    fn check<S: BufferStore<u8>>(mut store: S) {
        store.reserve(2, 1).unwrap();
        let old = store.publish(&[3, 6]).unwrap();
        // Vec rejects a payload larger than isize::MAX before asking the OS.
        // Arithmetic still fits usize; this exercises the fallible Vec path.
        assert_eq!(
            store.reserve(isize::MAX as usize + 1, 1),
            Err(Error("reservation-failed"))
        );
        assert_eq!(store.read(&old).unwrap(), &[3, 6]);
    }
    check(PackedBuffers::new().unwrap());
    check(SegmentedBuffers::new().unwrap());
}
