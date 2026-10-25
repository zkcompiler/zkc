//! Build and Linux process observations shared by development benchmark clients.
use serde_json::{Value, json};

pub fn build() -> Value {
    json!({"compiler": env!("BENCH_RUSTC"), "profile": env!("BENCH_PROFILE"),
        "opt_level": env!("BENCH_OPT_LEVEL"), "target": env!("BENCH_TARGET"),
        "target_features": env!("BENCH_CARGO_CFG_TARGET_FEATURE").split(',').filter(|s| !s.is_empty()).collect::<Vec<_>>(),
        "rustflags": env!("BENCH_CARGO_ENCODED_RUSTFLAGS").split('\x1f').filter(|s| !s.is_empty()).collect::<Vec<_>>(),
        "crate_features": env!("BENCH_FEATURES").split(',').filter(|s| !s.is_empty()).collect::<Vec<_>>(),
        "debug_assertions": cfg!(debug_assertions)})
}

// Lifetime high-water mark, including setup, warmups and observations.
pub fn peak_rss() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    value(&status, "VmHWM:")?
        .split_whitespace()
        .next()?
        .parse::<u64>()
        .ok()?
        .checked_mul(1024)
}

fn value<'a>(status: &'a str, key: &str) -> Option<&'a str> {
    status
        .lines()
        .find_map(|line| line.strip_prefix(key).map(str::trim))
}

pub fn process() -> Value {
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let mut errors = Vec::new();
    let mut entries = Vec::new();
    match std::fs::read_dir("/proc/self/task") {
        Err(error) => errors.push(error.to_string()),
        Ok(tasks) => {
            for task in tasks {
                let observed = (|| -> Result<_, String> {
                    let task = task.map_err(|e| e.to_string())?;
                    let tid = task
                        .file_name()
                        .to_string_lossy()
                        .parse::<u64>()
                        .map_err(|e| e.to_string())?;
                    let status = match std::fs::read_to_string(task.path().join("status")) {
                        Ok(status) => status,
                        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                            return Ok(None);
                        }
                        Err(error) => return Err(error.to_string()),
                    };
                    let cpus =
                        value(&status, "Cpus_allowed_list:").ok_or("missing thread affinity")?;
                    Ok(Some((tid, cpus.to_owned())))
                })();
                match observed {
                    Ok(Some(entry)) => entries.push(entry),
                    Ok(None) => (), // The task vanished during the observation.
                    Err(error) => errors.push(error),
                }
            }
        }
    }
    entries.sort();
    let threads: Vec<_> = entries
        .into_iter()
        .map(|(tid, cpus)| json!({"tid":tid,"cpus":cpus}))
        .collect();
    json!({"threads_at_exit": value(&status, "Threads:"),
        "affinity": value(&status, "Cpus_allowed_list:"), "thread_affinities": threads,
        "thread_observation_errors": errors,
        "rayon_num_threads": std::env::var("RAYON_NUM_THREADS").ok()})
}

pub fn timer_floor_ns() -> u128 {
    (0..1000)
        .map(|_| {
            let start = std::time::Instant::now();
            std::hint::black_box(());
            start.elapsed().as_nanos()
        })
        .min()
        .unwrap()
}
