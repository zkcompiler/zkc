//! Application-owned CPU execution for typed numerical phases.
//!
//! A context bounds its Rayon workers. Caller validation, other contexts and
//! foreign threads are outside that bound. Entering a context leaves the caller
//! on its own thread; only explicitly installed numerical work moves to workers.
use rayon::{ThreadPool, ThreadPoolBuilder};
use std::{cell::RefCell, sync::Arc};

/// Immutable execution policy and shared worker lifetime.
#[derive(Clone)]
pub struct CpuExecution(Arc<ThreadPool>);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    WorkerCount,
    PoolCreation,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::WorkerCount => "cpu-worker-count",
            Self::PoolCreation => "cpu-pool-creation",
        })
    }
}
impl std::error::Error for Error {}
impl std::fmt::Debug for CpuExecution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CpuExecution")
            .field("workers", &self.workers())
            .finish()
    }
}

thread_local! {
    // Lexically supplied by the Host/Native owner, never a process-wide setting.
    static CURRENT: RefCell<Option<CpuExecution>> = const { RefCell::new(None) };
}

impl CpuExecution {
    /// Create one finite pool. Clones and concurrent callers share its workers.
    pub fn new(workers: usize) -> Result<Self, Error> {
        if !(1..=256).contains(&workers) {
            return Err(Error::WorkerCount);
        }
        let pool = ThreadPoolBuilder::new()
            .num_threads(workers)
            .thread_name(|index| format!("zkc-cpu-{index}"))
            .build()
            .map_err(|_| Error::PoolCreation)?;
        // Construction includes readiness of every worker. Admission and timed
        // numerical phases do not inherit deferred thread startup.
        pool.broadcast(|_| ());
        Ok(Self(Arc::new(pool)))
    }

    /// Create an explicitly owned one-worker context. No environment variable
    /// changes this policy. Dropping the last clone requests worker shutdown;
    /// it does not provide a join receipt for worker thread termination.
    pub fn serial() -> Result<Self, Error> {
        Self::new(1)
    }

    pub fn workers(&self) -> usize {
        self.0.current_num_threads()
    }

    /// Supply a context on the calling thread, restoring the outer context on
    /// return or unwind. This alone neither moves work nor spawns a task.
    pub fn enter<R>(&self, action: impl FnOnce() -> R) -> R {
        struct Restore(Option<CpuExecution>);
        impl Drop for Restore {
            fn drop(&mut self) {
                CURRENT.with(|slot| {
                    slot.replace(self.0.take());
                });
            }
        }
        let _restore = Restore(CURRENT.with(|slot| slot.replace(Some(self.clone()))));
        action()
    }

    /// Execute a typed numerical phase. Nested Rayon work uses the same pool.
    /// Do not capture VM custody, partial effects or caller accounting scopes.
    pub fn execute<R: Send>(&self, action: impl FnOnce() -> R + Send) -> R {
        self.0.install(|| self.enter(action))
    }
}

/// Contain an upstream parallel-capable numerical phase when a caller supplied
/// a context. Standalone typed kernels retain the caller's upstream policy.
pub(crate) fn install<R: Send>(action: impl FnOnce() -> R + Send) -> R {
    let context = CURRENT.with(|slot| slot.borrow().clone());
    match context {
        Some(context) => context.execute(action),
        None => action(),
    }
}

/// Split a total element-wise phase using only its public shape. Small work
/// stays on the caller and does not pay a pool hop. No fallible task race occurs.
pub(crate) fn chunks_mut<T: Send>(
    values: &mut [T],
    grain: usize,
    action: impl Fn(usize, &mut [T]) + Send + Sync,
) {
    let context = CURRENT.with(|slot| slot.borrow().clone());
    if let Some(context) = context.filter(|cpu| cpu.workers() > 1 && values.len() / grain >= 2) {
        context.execute(|| {
            use rayon::prelude::*;
            values
                .par_chunks_mut(grain)
                .enumerate()
                .for_each(|(i, chunk)| context.enter(|| action(i * grain, chunk)));
        });
    } else {
        for (i, chunk) in values.chunks_mut(grain).enumerate() {
            action(i * grain, chunk);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn counts_and_nesting_are_explicit() {
        assert!(matches!(CpuExecution::new(0), Err(Error::WorkerCount)));
        assert!(matches!(CpuExecution::new(257), Err(Error::WorkerCount)));
        let outer = CpuExecution::new(2).unwrap();
        let inner = CpuExecution::new(1).unwrap();
        outer.enter(|| {
            assert_eq!(install(rayon::current_num_threads), 2);
            inner.enter(|| assert_eq!(install(rayon::current_num_threads), 1));
            assert_eq!(install(rayon::current_num_threads), 2);
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    || inner.enter(|| panic!("test"))
                ))
                .is_err()
            );
            assert_eq!(install(rayon::current_num_threads), 2);
        });
        assert!(CURRENT.with(|slot| slot.borrow().is_none()));
    }
    #[test]
    fn concurrent_clones_share_the_pool() {
        let cpu = CpuExecution::new(2).unwrap();
        let ids = Arc::new(std::sync::Mutex::new(std::collections::HashSet::new()));
        std::thread::scope(|scope| {
            for _ in 0..4 {
                let cpu = cpu.clone();
                let ids = ids.clone();
                scope.spawn(move || {
                    cpu.execute(|| {
                        use rayon::prelude::*;
                        (0..64).into_par_iter().for_each(|_| {
                            ids.lock().unwrap().insert(std::thread::current().id());
                        });
                    })
                });
            }
        });
        assert!((1..=2).contains(&ids.lock().unwrap().len()));
    }

    #[test]
    fn stolen_chunks_retain_nested_execution_context() {
        let cpu = CpuExecution::new(4).unwrap();
        let mut values = vec![0usize; 4096];
        cpu.enter(|| {
            chunks_mut(&mut values, 32, |_, chunk| {
                assert_eq!(
                    CURRENT.with(|slot| slot.borrow().as_ref().unwrap().workers()),
                    4
                );
                assert_eq!(install(rayon::current_num_threads), 4);
                chunks_mut(chunk, 4, |_, inner| inner.fill(1));
            })
        });
        assert!(values.iter().all(|v| *v == 1));
        assert!(CURRENT.with(|slot| slot.borrow().is_none()));
        let inner = CpuExecution::serial().unwrap();
        cpu.execute(|| {
            assert_eq!(inner.execute(rayon::current_num_threads), 1);
            assert_eq!(install(rayon::current_num_threads), 4);
        });
    }
}
