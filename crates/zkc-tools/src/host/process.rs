//! Bounded one-shot child execution. The guard kills and reaps the direct child
//! on timeout, output overflow or I/O failure. Descendant isolation belongs to
//! the application host; this is not a sandbox or a process-tree supervisor.
use std::{
    io,
    path::Path,
    process::{Child, Command, ExitStatus, Stdio},
    time::{Duration, Instant},
};

#[derive(Debug)]
pub(crate) enum Error {
    Process(io::Error),
    Io(io::Error),
    Timeout,
    OutputLimit,
}
struct Running(Child);
impl Drop for Running {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Own captured files and the direct child until the consumer finishes reading.
/// Consumers choose streams and map bounded-read failures themselves, preserving
/// their status/error precedence. No output is interpreted by this module.
pub(crate) struct Captured {
    pub(crate) status: ExitStatus,
    pub(crate) stdout: tempfile::NamedTempFile,
    pub(crate) stderr: Option<tempfile::NamedTempFile>,
    _child: Running,
}

/// The caller retains its deadline comparison as well as response interpretation.
pub(crate) fn capture(
    command: &mut Command,
    directory: &Path,
    timed_out: impl Fn(Duration) -> bool,
    limit: usize,
    capture_stderr: bool,
) -> Result<Captured, Error> {
    let stdout = tempfile::NamedTempFile::new_in(directory).map_err(Error::Io)?;
    let stderr = if capture_stderr {
        Some(tempfile::NamedTempFile::new_in(directory).map_err(Error::Io)?)
    } else {
        None
    };
    command
        .stdin(Stdio::null())
        .stdout(stdout.reopen().map_err(Error::Io)?)
        .stderr(match &stderr {
            Some(file) => Stdio::from(file.reopen().map_err(Error::Io)?),
            None => Stdio::null(),
        });
    let mut child = Running(command.spawn().map_err(Error::Process)?);
    let start = Instant::now();
    let status = loop {
        for file in std::iter::once(&stdout).chain(stderr.iter()) {
            if file.as_file().metadata().map_err(Error::Io)?.len() > limit as u64 {
                return Err(Error::OutputLimit);
            }
        }
        if let Some(status) = child.0.try_wait().map_err(Error::Process)? {
            break status;
        }
        if timed_out(start.elapsed()) {
            return Err(Error::Timeout);
        }
        std::thread::sleep(Duration::from_millis(2));
    };
    Ok(Captured {
        status,
        stdout,
        stderr,
        _child: child,
    })
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use crate::host::io::{ReadError, read_bounded};
    use std::process::Output;
    fn run(script: &str, limit: usize, stderr: bool) -> Result<Output, Error> {
        let dir = tempfile::tempdir().unwrap();
        let captured = capture(
            Command::new("sh").args(["-c", script]),
            dir.path(),
            |elapsed| elapsed >= Duration::from_secs(1),
            limit,
            stderr,
        )?;
        let read = |path: &Path| {
            read_bounded(path, limit).map_err(|error| match error {
                ReadError::Io(e) => Error::Io(e),
                ReadError::Limit => Error::OutputLimit,
            })
        };
        Ok(Output {
            status: captured.status,
            stdout: read(captured.stdout.path())?,
            stderr: captured
                .stderr
                .as_ref()
                .map(|file| read(file.path()))
                .transpose()?
                .unwrap_or_default(),
        })
    }
    #[test]
    fn preserves_failure_status_and_each_bounded_stream() {
        let output = run("printf ok; printf bad >&2; exit 7", 3, true).unwrap();
        assert_eq!(output.status.code(), Some(7));
        assert_eq!(output.stdout, b"ok");
        assert_eq!(output.stderr, b"bad");
    }
    #[test]
    fn rejects_overflow_even_when_the_writer_exits_immediately() {
        assert!(matches!(
            run("printf abcde", 4, true),
            Err(Error::OutputLimit)
        ));
        assert!(matches!(
            run("printf abcde >&2", 4, true),
            Err(Error::OutputLimit)
        ));
        assert!(run("printf abcde >&2", 4, false).unwrap().status.success());
    }
    #[test]
    fn timeout_reaps_the_owned_child() {
        let dir = tempfile::tempdir().unwrap();
        let pid_file = dir.path().join("pid");
        let mut command = Command::new("sh");
        command
            .args(["-c", r#"echo $$ > "$1"; exec sleep 30"#, "checker"])
            .arg(&pid_file);
        assert!(matches!(
            capture(
                &mut command,
                dir.path(),
                |elapsed| elapsed >= Duration::from_millis(100),
                4096,
                false
            ),
            Err(Error::Timeout)
        ));
        let pid = std::fs::read_to_string(pid_file).unwrap();
        assert!(
            !Command::new("kill")
                .args(["-0", pid.trim()])
                .stderr(Stdio::null())
                .status()
                .unwrap()
                .success()
        );
    }
}
