//! Count successful task creation over a child test's entire lifetime.
use std::{path::Path, process::Command};

/// Trace one exact test in the current executable, retaining output and syscalls.
/// Requires strace and ptrace permission; callers select their own task budget.
pub fn test(directory: &Path, name: &str, environment: &[(&str, String)]) -> usize {
    let trace = directory.join("tasks.strace");
    let output = Command::new("strace")
        .args(["-f", "-qq", "-e", "trace=clone,clone3,fork,vfork", "-o"])
        .arg(&trace)
        .arg(std::env::current_exe().unwrap())
        .args([
            "--exact",
            name,
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .envs(environment.iter().map(|(key, value)| (key, value)))
        .output()
        .expect("install strace to run the Linux thread-creation gate");
    std::fs::write(directory.join("stdout"), &output.stdout).unwrap();
    std::fs::write(directory.join("stderr"), &output.stderr).unwrap();
    assert!(
        output.status.success(),
        "traced child failed; inspect {}",
        directory.display()
    );
    let log = std::fs::read_to_string(&trace).unwrap();
    let tasks = log.lines().filter(|line| successful_creation(line)).count();
    assert!(tasks > 0, "no task events captured in {}", trace.display());
    tasks
}

fn successful_creation(line: &str) -> bool {
    // Failed clone3 attempts may precede a successful clone fallback. Concurrent
    // syscalls may instead return their task ID on an unfinished/resumed pair.
    ["clone", "clone3", "fork", "vfork"].iter().any(|syscall| {
        line.contains(&format!("{syscall}(")) || line.contains(&format!("<... {syscall} resumed>"))
    }) && line.rsplit_once("= ").is_some_and(|(_, result)| {
        result
            .split_whitespace()
            .next()
            .and_then(|s| s.parse::<u64>().ok())
            .is_some_and(|id| id > 0)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accounting_handles_resumed_and_failed_creation() {
        assert!(successful_creation("123 clone(flags=CLONE_THREAD) = 456"));
        assert!(successful_creation("123 <... clone3 resumed>) = 456"));
        assert!(!successful_creation("123 clone3({}, 88) = -1 ENOSYS"));
        assert!(!successful_creation(
            "123 clone(flags=CLONE_THREAD <unfinished ...>"
        ));
        assert!(!successful_creation("123 +++ exited with 0 +++"));
    }
}
