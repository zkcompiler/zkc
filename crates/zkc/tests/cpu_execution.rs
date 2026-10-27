use zkc::execution::CpuExecution;

#[test]
fn cpu_execution_rejects_invalid_counts_and_owns_fresh_defaults() {
    fn send_sync<T: Send + Sync>() {}
    send_sync::<CpuExecution>();
    for count in [0, 257, usize::MAX] {
        assert_eq!(
            CpuExecution::new(count).unwrap_err().to_string(),
            "cpu-worker-count"
        );
    }
    let first = CpuExecution::serial().unwrap();
    let second = CpuExecution::serial().unwrap();
    assert_eq!(first.workers(), 1);
    #[cfg(feature = "parallel")]
    assert_ne!(
        first.execute(|| std::thread::current().id()),
        second.execute(|| std::thread::current().id())
    );
    let clone = first.clone();
    let worker = first.execute(|| std::thread::current().id());
    #[allow(clippy::drop_non_drop)] // Serial builds have no owned pool to release.
    drop(first);
    assert_eq!(clone.execute(|| std::thread::current().id()), worker);
    #[cfg(feature = "parallel")]
    assert_eq!(CpuExecution::new(2).unwrap().clone().workers(), 2);
    #[cfg(not(feature = "parallel"))]
    {
        assert!(CpuExecution::new(2).is_err());
        assert_eq!(
            second.execute(|| std::thread::current().id()),
            std::thread::current().id()
        );
    }
    assert_eq!(clone.workers(), 1);
}
