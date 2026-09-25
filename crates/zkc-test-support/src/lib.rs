//! Where the tools a test drives are, and where it leaves what it did.
//!
//! A test that crosses a build runs tools from three separate builds as
//! processes and compares what they do. It never receives an executable path
//! from its caller and never reaches into another build's directory by hand: it
//! names the tool it needs and this finds it.
//!
//! A tool that is not there is a failure naming the directory searched and the
//! command that builds it. It is not a reason to skip the test. Fifty-one tests
//! here used to carry `#[ignore]` for that reason, in three wordings, which
//! meant a plain `cargo test` reported them as ignored and a reader counted
//! them as fine. A skip reads as a pass, and these are the tests that compare
//! the compiler against the runtime against the formal reference -- the ones
//! whose silence is worth the least.
//!
//! Directory overrides have the same meaning as in the Python harness. Nix
//! checks supply installed directories; native commands use checkout defaults.
//! An invalid explicit directory never falls back to the checkout or PATH.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// The three builds, each with its own output directory and its own command.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Build {
    /// CMake: the compiler and its tools.
    Compiler,
    /// Cargo: the runtime, the host tools and their examples.
    Native,
    /// Lake: the formal library and its executable checkers.
    Formal,
}

impl Build {
    /// The variable naming this build's output directory, and its default.
    const fn directory(self) -> (&'static str, &'static str) {
        match self {
            Build::Compiler => ("ZKC_COMPILER_BIN", "build/compiler"),
            Build::Native => ("ZKC_NATIVE_BIN", "target/release"),
            Build::Formal => ("ZKC_LEAN_BIN", "formal/.lake/build/bin"),
        }
    }

    /// What builds it, for a failure to name.
    const fn command(self) -> &'static str {
        match self {
            Build::Compiler => "just build-compiler",
            Build::Native => "just build-rust",
            Build::Formal => "just build-lean",
        }
    }
}

/// The repository root, from this crate's place in it.
pub fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the repository root is where this crate's manifest says it is")
}

/// Removed aliases cannot silently select a different compiler in another suite.
const REMOVED: &[(&str, &str)] = &[
    ("ZKC_COMPILER", "ZKC_COMPILER_BIN"),
    ("ZKC_OPTIMIZER", "ZKC_COMPILER_BIN"),
    ("ZKC_SOURCE_BENCH", "ZKC_COMPILER_BIN"),
    ("ZKC_SERVICE_COMPILER", "ZKC_COMPILER_BIN"),
    ("ZKC_SERVICE_OPTIMIZER", "ZKC_COMPILER_BIN"),
    ("ZKC_REQUIREMENTS_TEST", "ZKC_COMPILER_BIN"),
    ("ZKC_LEAN", "ZKC_LEAN_BIN"),
    ("ZKC_PHYSICAL_CHECKER", "ZKC_LEAN_BIN"),
    ("ZKC_TEST_RECORDS", "ZKC_REPORTS_DIR (without /tests)"),
    ("ZKC_COMPILER_BUILD", "a CMake preset and ZKC_COMPILER_BIN"),
    (
        "ZKC_BUILD_PRESET",
        "a profile argument, e.g. just build-compiler dev",
    ),
    ("ZKC_JOBS", "the native tool's parallelism setting"),
];

fn checkout_path(value: impl AsRef<Path>) -> PathBuf {
    let path = value.as_ref();
    if path.is_absolute() {
        path.to_owned()
    } else {
        root().join(path)
    }
}

fn validate_environment(
    lookup: &impl Fn(&str) -> Option<std::ffi::OsString>,
) -> Result<(), String> {
    for (old, replacement) in REMOVED {
        if lookup(old).is_some() {
            return Err(format!("{old} was removed; use {replacement}"));
        }
    }
    for name in [
        "ZKC_COMPILER_BIN",
        "ZKC_NATIVE_BIN",
        "ZKC_LEAN_BIN",
        "ZKC_REPORTS_DIR",
    ] {
        if let Some(value) = lookup(name)
            && value.to_string_lossy().trim().is_empty()
        {
            return Err(format!(
                "{name} must be a nonempty path; unset it to use the default"
            ));
        }
    }
    Ok(())
}

fn resolve_tool(
    build: Build,
    name: &str,
    lookup: impl Fn(&str) -> Option<std::ffi::OsString>,
) -> Result<PathBuf, String> {
    validate_environment(&lookup)?;
    let (variable, fallback) = build.directory();
    let directory = match lookup(variable) {
        Some(value) => checkout_path(PathBuf::from(value)),
        _ if build == Build::Native => match lookup("CARGO_TARGET_DIR") {
            Some(target) if !target.is_empty() => {
                let path = PathBuf::from(target);
                let path = if path.is_absolute() {
                    path
                } else {
                    std::env::current_dir()
                        .map_err(|error| error.to_string())?
                        .join(path)
                };
                path.join("release")
            }
            _ => root().join(fallback),
        },
        _ => root().join(fallback),
    };
    locate(build, name, &directory, variable)
}

/// Resolve by name within the selected build directory, never by legacy alias or PATH.
pub fn tool(build: Build, name: &str) -> PathBuf {
    resolve_tool(build, name, |key| std::env::var_os(key))
        .unwrap_or_else(|reason| panic!("{reason}"))
}

fn executable(path: &Path) -> bool {
    let Ok(metadata) = path.metadata() else {
        return false;
    };
    if !metadata.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

/// The same, with the directory decided, so what a failure says can be tested
/// without a test having to change the environment its neighbours read.
fn locate(build: Build, name: &str, directory: &Path, variable: &str) -> Result<PathBuf, String> {
    let path = directory.join(name);
    if executable(&path) {
        return Ok(path);
    }
    Err(format!(
        "{name} is not in {}\n  \
         {variable} names it or this build writes there, and it is neither\n  \
         build it with: {}\n  \
         present there: {}",
        directory.display(),
        build.command(),
        present(directory).join(", ")
    ))
}

/// The executables a build has actually produced, for a failure to name.
///
/// Lake writes a digest, a response file and a trace beside each binary; an
/// extension is what separates those from the executable itself.
fn present(directory: &Path) -> Vec<String> {
    let Ok(entries) = std::fs::read_dir(directory) else {
        return vec!["nothing".into()];
    };
    let mut names: Vec<String> = entries
        .flatten()
        .filter(|entry| entry.path().is_file() && entry.path().extension().is_none())
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    if names.is_empty() {
        names.push("nothing".into());
    }
    names
}

/// The compiler, which reads sources and writes plans.
pub fn compiler() -> PathBuf {
    tool(Build::Compiler, "zkc-compile")
}

/// The optimizer, which runs the compiler's passes over MLIR.
pub fn optimizer() -> PathBuf {
    tool(Build::Compiler, "zkc-opt")
}

/// A compiled Lean reference, by its executable name.
///
/// The references are not interchangeable: a source consumer refuses an
/// artifact descriptor and an artifact reference refuses a table plan. Passing
/// the wrong one produces a plausible refusal rather than an obvious error, so
/// the name belongs to the test.
pub fn checker(name: &str) -> PathBuf {
    tool(Build::Formal, name)
}

/// The sources every build's tests read.
pub fn corpus() -> PathBuf {
    root().join("tests/fixtures")
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

/// The directory the running test writes its sources, plans and reports to.
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
/// It answers `path()` the way a temporary directory does, because that is what
/// these tests used to hold and the difference worth having is at the end of
/// the run rather than at the call site.
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
    validate_environment(&|key| std::env::var_os(key)).unwrap_or_else(|reason| panic!("{reason}"));
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

/// Run one compiler subcommand over one file and return what it printed.
///
/// Twelve places across two crates wrote this: spawn the compiler, assert the
/// status, and show stderr when it is not what was wanted. A test that is
/// judging the refusal rather than requiring the success wants `Command` and
/// its own assertions; this is for the step that has to have worked before the
/// test can begin.
pub fn compile(subcommand: &str, input: impl AsRef<Path>) -> Vec<u8> {
    let input = input.as_ref();
    let result = std::process::Command::new(compiler())
        .arg(subcommand)
        .arg(input)
        .output()
        .unwrap_or_else(|error| panic!("could not run the compiler: {error}"));
    assert!(
        result.status.success(),
        "{subcommand} {} failed: {}",
        input.display(),
        String::from_utf8_lossy(&result.stderr)
    );
    result.stdout
}

/// Wire bytes as the lowercase hexadecimal these tests read and write.
///
/// Four test files wrote this same function and four wrote its inverse. The
/// product has its own, which is not this one: `zkc_tools::artifact::io::hex`
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
    fn a_tool_this_build_produced_is_found_by_name() {
        let directory =
            std::env::temp_dir().join(format!("zkc-tool-resolution-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let binary = directory.join("zkc-compile");
        std::fs::write(&binary, "#!/bin/sh\nexit 0\n").unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&binary, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        let found = resolve_tool(Build::Compiler, "zkc-compile", |name| {
            (name == "ZKC_COMPILER_BIN").then(|| directory.as_os_str().to_owned())
        })
        .unwrap();
        assert_eq!(found, binary);
        assert!(
            resolve_tool(Build::Compiler, "absent", |name| {
                (name == "ZKC_COMPILER_BIN").then(|| directory.as_os_str().to_owned())
            })
            .is_err()
        );
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn old_aliases_and_empty_directories_are_rejected_before_lookup() {
        for (old, replacement) in REMOVED {
            let error = resolve_tool(Build::Compiler, "zkc-compile", |name| {
                (name == *old).then(|| "/some/old/path".into())
            })
            .unwrap_err();
            assert!(
                error.contains(old) && error.contains(replacement),
                "{error}"
            );
        }
        let error = resolve_tool(Build::Formal, "checker", |name| {
            (name == "ZKC_LEAN_BIN").then(|| "".into())
        })
        .unwrap_err();
        assert!(error.contains("nonempty"));
    }

    #[test]
    fn relative_project_paths_are_rooted_in_the_checkout() {
        assert_eq!(checkout_path("build/custom"), root().join("build/custom"));
    }

    #[test]
    fn the_corpus_is_one_directory_and_holds_what_tests_ask_for() {
        assert!(source("generic-operations.pir").exists());
        assert!(source("air/lookup.json").exists());
    }

    #[test]
    fn a_missing_tool_names_the_directory_searched_and_what_builds_it() {
        let message = locate(
            Build::Formal,
            "no-such-reference",
            Path::new("/nowhere-this-build-writes"),
            "ZKC_LEAN_BIN",
        )
        .expect_err("a tool that is not there is a failure, not a skip");
        assert!(message.contains("/nowhere-this-build-writes"), "{message}");
        assert!(message.contains("just build-lean"), "{message}");
        assert!(message.contains("ZKC_LEAN_BIN"), "{message}");
        assert!(message.contains("present there: nothing"), "{message}");
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
