//! Shared native-test fixtures, bounded probe transport, and retained evidence.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// The repository root, from this crate's place in it.
pub fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the repository root is where this crate's manifest says it is")
}

fn checkout_path(value: impl AsRef<Path>) -> PathBuf {
    let path = value.as_ref();
    if path.is_absolute() {
        path.to_owned()
    } else {
        root().join(path)
    }
}

/// Immutable conformance fixtures owned by this crate.
pub fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures")
}

/// One source from that corpus, by name.
pub fn source(name: &str) -> PathBuf {
    let path = corpus().join(name);
    assert!(
        path.exists(),
        "{name} is not in the corpus at {}",
        corpus().display()
    );
    path
}

/// The directory the running test writes its inputs and reports to.
///
/// The name is the test's own: the harness names each test's thread after it,
/// which is also what keeps two tests in one binary -- they run in parallel --
/// from clearing each other's evidence. `fallback` is for a run with one thread,
/// where every test is on `main`.
///
/// One directory per test, so a test that builds two subjects has to say so
/// with `nested`: twice here a second subject wrote `source.json` over the
/// first's, and the first was then checked against the second's source.
///
/// It starts empty, and it is not removed: the evidence of a run that failed is
/// exactly what is worth reading, and a temporary directory deleted on the way
/// out throws it away precisely then.
pub fn evidence(fallback: &str) -> Evidence {
    let thread = std::thread::current();
    let named = thread
        .name()
        .filter(|name| *name != "main" && !name.is_empty());
    Evidence(records(&named.unwrap_or(fallback).replace("::", "/")))
}

/// A directory a test writes to, which outlives the test.
///
/// `path()` exposes the evidence directory; files remain available after the run.
#[derive(Clone, Debug)]
pub struct Evidence(PathBuf);

impl Evidence {
    pub fn path(&self) -> &Path {
        &self.0
    }

    /// A directory of its own inside this one.
    ///
    /// A test that builds two subjects needs somewhere to put each: they are
    /// one test, so they share a directory, and two sources written to the same
    /// name would leave the first subject checked against the second's.
    pub fn nested(&self, name: &str) -> Evidence {
        let path = self.0.join(name);
        std::fs::create_dir_all(&path).expect("a directory for this subject");
        Evidence(path)
    }
}

impl AsRef<Path> for Evidence {
    fn as_ref(&self) -> &Path {
        &self.0
    }
}

/// The same, for a helper that has worked out a name of its own.
pub fn records(test: &str) -> PathBuf {
    let base = match std::env::var_os("ZKC_REPORTS_DIR") {
        Some(value) => checkout_path(PathBuf::from(value)),
        _ => root().join("build/reports"),
    }
    .join("tests");
    // Reserve once, atomically: PID reuse and competing binaries can never
    // claim an existing run. Case lookup only creates missing directories;
    // looking up a parent after its child must retain the child's evidence.
    static PROCESS_ROOT: OnceLock<PathBuf> = OnceLock::new();
    let process_root = PROCESS_ROOT.get_or_init(|| {
        allocate_process_root(&base.join("rust"), std::process::id())
            .expect("an exclusive directory for this process's evidence")
    });
    let path = process_root.join(test);
    std::fs::create_dir_all(&path).expect("a directory to write this test's evidence to");
    path
}

fn allocate_process_root(base: &Path, pid: u32) -> std::io::Result<PathBuf> {
    std::fs::create_dir_all(base)?;
    for attempt in 0_u64.. {
        let path = base.join(format!("run-{pid}-{attempt}"));
        match std::fs::create_dir(&path) {
            Ok(()) => return Ok(path),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(std::io::Error::other("exhausted process report names"))
}

/// Wire bytes as the lowercase hexadecimal these tests read and write.
///
/// Four test files wrote this same function and four wrote its inverse. The
/// product has its own, which is not this one: `zkc_tools::proof::hex`
/// is what a tool prints, and a test that compared against it would be checking
/// that one expression equals itself.
pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// The inverse, for a test reading bytes a tool printed.
///
/// It panics on anything that is not hexadecimal, because a test that meant to
/// decode a tool's output and met something else has already failed.
pub fn unhex(text: &str) -> Vec<u8> {
    assert!(
        text.len().is_multiple_of(2),
        "hexadecimal has two digits to the byte, and this has {}",
        text.len()
    );
    (0..text.len())
        .step_by(2)
        .map(|at| {
            u8::from_str_radix(&text[at..at + 2], 16)
                .unwrap_or_else(|_| panic!("{:?} is not a hexadecimal byte", &text[at..at + 2]))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relative_project_paths_are_rooted_in_the_checkout() {
        assert_eq!(checkout_path("build/custom"), root().join("build/custom"));
    }

    #[test]
    fn the_corpus_is_one_directory_and_holds_what_tests_ask_for() {
        assert!(source("variants/descriptors.json").exists());
        assert!(source("external-transcript/monero-hash-vectors.json").exists());
    }

    #[test]
    fn evidence_goes_somewhere_that_survives_the_run() {
        let directory = records("support-self-check");
        std::fs::write(directory.join("kept.json"), "{}").unwrap();
        assert!(directory.join("kept.json").exists());
        // Where it should be, rather than "here or wherever the variable says":
        // CI sets that variable, so the second half of such a disjunction is
        // what would be true there and the location would go unchecked.
        let expected = match std::env::var_os("ZKC_REPORTS_DIR") {
            Some(value) => checkout_path(PathBuf::from(value)),
            _ => root().join("build/reports"),
        }
        .join("tests");
        assert!(directory.starts_with(&expected), "{}", directory.display());
    }

    #[test]
    fn wire_bytes_round_trip_through_the_spelling_tools_print() {
        assert_eq!(hex(&[0x00, 0x0f, 0xff]), "000fff");
        assert_eq!(unhex("000fff"), vec![0x00, 0x0f, 0xff]);
        assert_eq!(unhex(&hex(b"zkc")), b"zkc");
        assert_eq!(hex(&[]), "");
    }

    #[test]
    fn evidence_is_named_after_the_test_that_asks_for_it() {
        // The harness names this thread after this function, so two tests in
        // one binary cannot clear each other's evidence.
        let directory = evidence("unnamed");
        assert!(
            directory
                .path()
                .ends_with("tests/evidence_is_named_after_the_test_that_asks_for_it"),
            "{}",
            directory.path().display()
        );
    }

    #[test]
    fn reused_pid_and_competing_allocations_preserve_old_evidence() {
        let base = records("allocation-regression");
        let old = allocate_process_root(&base, 42).unwrap();
        std::fs::write(old.join("retained"), "old run").unwrap();
        let barrier = std::sync::Arc::new(std::sync::Barrier::new(8));
        let handles: Vec<_> = (0..8)
            .map(|_| {
                let base = base.clone();
                let barrier = barrier.clone();
                std::thread::spawn(move || {
                    barrier.wait();
                    allocate_process_root(&base, 42).unwrap()
                })
            })
            .collect();
        let mut paths = vec![old.clone()];
        paths.extend(handles.into_iter().map(|handle| handle.join().unwrap()));
        paths.sort();
        paths.dedup();
        assert_eq!(paths.len(), 9);
        assert_eq!(
            std::fs::read_to_string(old.join("retained")).unwrap(),
            "old run"
        );
    }

    #[test]
    fn repeated_parent_and_child_lookups_retain_both_cases() {
        let child = records("nested-regression/child");
        std::fs::write(child.join("child.json"), "child").unwrap();
        let parent = records("nested-regression");
        std::fs::write(parent.join("parent.json"), "parent").unwrap();
        assert_eq!(records("nested-regression/child"), child);
        assert_eq!(records("nested-regression"), parent);
        assert_eq!(
            std::fs::read_to_string(child.join("child.json")).unwrap(),
            "child"
        );
        assert_eq!(
            std::fs::read_to_string(parent.join("parent.json")).unwrap(),
            "parent"
        );
        let nested = Evidence(parent).nested("child");
        assert_eq!(nested.path(), child);
        assert!(nested.path().join("child.json").is_file());
    }

    #[test]
    fn concurrent_processes_do_not_clear_each_others_evidence() {
        const PARENT: &str = "ZKC_EVIDENCE_TEST_PARENT";
        let directory = records("concurrent-evidence");
        if let Some(parent) = std::env::var_os(PARENT) {
            let parent = PathBuf::from(parent);
            assert_ne!(directory, parent);
            assert!(parent.join("in-use.json").exists());
            return;
        }
        std::fs::write(directory.join("in-use.json"), "{}").unwrap();
        let child = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "tests::concurrent_processes_do_not_clear_each_others_evidence",
            ])
            .env(PARENT, &directory)
            .output()
            .unwrap();
        assert!(
            child.status.success(),
            "{}{}",
            String::from_utf8_lossy(&child.stdout),
            String::from_utf8_lossy(&child.stderr)
        );
        assert!(directory.join("in-use.json").exists());
    }
}

/// Hand-built portable local-sum fixtures.
pub mod variants;

/// Bounded transport for independent conformance probes.
pub mod json_lines;
