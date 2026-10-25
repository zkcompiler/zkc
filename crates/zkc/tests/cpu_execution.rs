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
    assert_ne!(
        first.execute(|| std::thread::current().id()),
        second.execute(|| std::thread::current().id())
    );
    let clone = first.clone();
    let worker = first.execute(|| std::thread::current().id());
    drop(first);
    assert_eq!(clone.execute(|| std::thread::current().id()), worker);
    let explicit = CpuExecution::new(2).unwrap();
    assert_eq!(explicit.clone().workers(), 2);
    assert_eq!(clone.workers(), 1);
}
