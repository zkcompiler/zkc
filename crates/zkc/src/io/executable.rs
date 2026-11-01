//! Immutable executable bytes for pinned EVM tools. Interpreters and shared
//! libraries remain part of the trusted host toolchain.
use super::ReadError;
#[cfg(target_os = "linux")]
use sha2::{Digest, Sha256};
use std::{ffi::OsStr, io, path::Path, process::Command, time::Duration};
#[cfg(target_os = "linux")]
use std::{fs::File, os::fd::AsRawFd, sync::Arc};

#[derive(Clone, Debug)]
pub(crate) struct Executable {
    #[cfg(target_os = "linux")]
    file: Arc<File>,
    sha256: String,
    #[cfg(target_os = "linux")]
    limit: usize,
}

impl Executable {
    pub(crate) fn capture(path: &Path, limit: usize) -> Result<Self, ReadError> {
        #[cfg(target_os = "linux")]
        {
            use rustix::fs::{MemfdFlags, Mode, SealFlags};
            let input = open(path, limit)?;
            let mut file = File::from(
                rustix::fs::memfd_create(
                    "zkc-executable",
                    MemfdFlags::CLOEXEC | MemfdFlags::ALLOW_SEALING | MemfdFlags::EXEC,
                )
                .map_err(io::Error::from)
                .map_err(ReadError::Io)?,
            );
            // Each buffer is both copied and hashed, even if the input is being
            // edited. The digest describes exactly the image we seal and execute.
            let sha256 = transfer(input, &mut file, limit)?;
            rustix::fs::fchmod(&file, Mode::RUSR | Mode::XUSR)
                .map_err(io::Error::from)
                .map_err(ReadError::Io)?;
            rustix::fs::fcntl_add_seals(
                &file,
                SealFlags::WRITE | SealFlags::GROW | SealFlags::SHRINK | SealFlags::SEAL,
            )
            .map_err(io::Error::from)
            .map_err(ReadError::Io)?;
            Ok(Self {
                file: Arc::new(file),
                sha256,
                limit,
            })
        }
        #[cfg(not(target_os = "linux"))]
        {
            let _ = (path, limit);
            Err(ReadError::Io(unsupported()))
        }
    }

    pub(crate) fn sha256(&self) -> &str {
        &self.sha256
    }

    /// Retain the live installed-path check without ever executing that path.
    pub(crate) fn matches_path(&self, path: &Path) -> Result<bool, ReadError> {
        #[cfg(target_os = "linux")]
        {
            Ok(transfer(open(path, self.limit)?, io::sink(), self.limit)? == self.sha256)
        }
        #[cfg(not(target_os = "linux"))]
        {
            let _ = path;
            Err(ReadError::Io(unsupported()))
        }
    }

    pub(crate) fn command(&self, argv0: &Path) -> io::Result<ExecutableCommand<'_>> {
        #[cfg(target_os = "linux")]
        {
            use std::os::unix::process::CommandExt;
            // The child and a script interpreter reopen the parent's descriptor.
            // CLOEXEC stays set: no executable descriptor is inherited by exec.
            let mut command = Command::new(format!(
                "/proc/{}/fd/{}",
                std::process::id(),
                self.file.as_raw_fd()
            ));
            command.arg0(argv0);
            Ok(ExecutableCommand {
                command,
                _image: self,
            })
        }
        #[cfg(not(target_os = "linux"))]
        {
            let _ = argv0;
            Err(unsupported())
        }
    }
}

/// A command cannot escape its image borrow or expose an unowned std Command.
/// Capture reaps the direct child, including failure paths, before releasing it.
pub(crate) struct ExecutableCommand<'a> {
    command: Command,
    _image: &'a Executable,
}
impl ExecutableCommand<'_> {
    pub(crate) fn env(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) -> &mut Self {
        self.command.env(key, value);
        self
    }

    pub(crate) fn args(
        &mut self,
        arguments: impl IntoIterator<Item = impl AsRef<OsStr>>,
    ) -> &mut Self {
        self.command.args(arguments);
        self
    }

    pub(crate) fn capture(
        &mut self,
        directory: &Path,
        timeout: Duration,
        limit: usize,
        input: Option<&[u8]>,
    ) -> Result<super::process::Captured, super::process::Error> {
        super::process::capture_input(
            &mut self.command,
            directory,
            |elapsed| elapsed >= timeout,
            limit,
            true,
            input,
        )
    }
}

#[cfg(not(target_os = "linux"))]
fn unsupported() -> io::Error {
    io::Error::new(
        io::ErrorKind::Unsupported,
        "immutable executable snapshots require Linux",
    )
}

#[cfg(target_os = "linux")]
fn open(path: &Path, limit: usize) -> Result<File, ReadError> {
    let file = super::open_regular(path)?;
    if file.metadata().map_err(ReadError::Io)?.len() > limit as u64 {
        return Err(ReadError::Limit);
    }
    // Ask the kernel about the opened inode, including effective credentials,
    // ACLs and noexec mounts. Mode bits alone cannot establish executability.
    rustix::fs::accessat(
        rustix::fs::CWD,
        format!("/proc/self/fd/{}", file.as_raw_fd()),
        rustix::fs::Access::EXEC_OK,
        rustix::fs::AtFlags::EACCESS,
    )
    .map_err(io::Error::from)
    .map_err(ReadError::Io)?;
    Ok(file)
}

#[cfg(target_os = "linux")]
fn transfer(
    mut input: impl io::Read,
    mut output: impl io::Write,
    limit: usize,
) -> Result<String, ReadError> {
    let mut hash = Sha256::new();
    let mut buffer = [0; 65536];
    let mut remaining = limit;
    loop {
        let capacity = buffer.len().min(remaining.saturating_add(1));
        let size = input.read(&mut buffer[..capacity]).map_err(ReadError::Io)?;
        if size == 0 {
            return Ok(super::bytes::hex(&hash.finalize()));
        }
        remaining = remaining.checked_sub(size).ok_or(ReadError::Limit)?;
        output.write_all(&buffer[..size]).map_err(ReadError::Io)?;
        hash.update(&buffer[..size]);
    }
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;
    use std::{
        io::{Read, Write},
        os::unix::fs::{FileExt, PermissionsExt},
    };

    const ORIGINAL: &[u8] = b"#!/bin/sh\nprintf original\n";
    const REPLACEMENT: &[u8] = b"#!/bin/sh\nprintf replaced\n";

    fn script(path: &Path, bytes: &[u8]) {
        std::fs::write(path, bytes).unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).unwrap();
    }

    fn run(executable: &Executable, path: &Path) {
        let output = execute(executable, path, &[]);
        assert!(output.status.success(), "{output:?}");
        assert_eq!(output.stdout, b"original");
        assert_eq!(
            executable.sha256(),
            super::super::bytes::hex(&Sha256::digest(ORIGINAL))
        );
    }

    fn execute(executable: &Executable, path: &Path, arguments: &[&str]) -> std::process::Output {
        let directory = tempfile::tempdir().unwrap();
        let captured = executable
            .command(path)
            .unwrap()
            .args(arguments)
            .capture(directory.path(), Duration::from_secs(5), 1024, None)
            .unwrap();
        std::process::Output {
            status: captured.status,
            stdout: super::super::read_regular(captured.stdout.path(), 1024).unwrap(),
            stderr: super::super::read_regular(captured.stderr.as_ref().unwrap().path(), 1024)
                .unwrap(),
        }
    }

    #[test]
    fn atomic_path_replacement_cannot_change_executed_bytes() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("tool");
        script(&path, ORIGINAL);
        let executable = Executable::capture(&path, 1024).unwrap();
        assert!(executable.matches_path(&path).unwrap());
        let replacement = directory.path().join("replacement");
        script(&replacement, REPLACEMENT);
        std::fs::rename(replacement, &path).unwrap();
        run(&executable, &path);
        assert!(!executable.matches_path(&path).unwrap());
    }

    #[test]
    fn in_place_modification_cannot_change_executed_bytes() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("tool");
        script(&path, ORIGINAL);
        let executable = Executable::capture(&path, 1024).unwrap();
        script(&path, REPLACEMENT);
        run(&executable, &path);
        assert!(!executable.matches_path(&path).unwrap());
    }

    #[test]
    fn kernel_seals_refuse_writes_truncation_growth_and_additional_seals() {
        use rustix::fs::SealFlags;
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("tool");
        script(&path, ORIGINAL);
        let executable = Executable::capture(&path, 1024).unwrap();
        assert_eq!(
            rustix::fs::fcntl_get_seals(&*executable.file).unwrap(),
            SealFlags::WRITE | SealFlags::GROW | SealFlags::SHRINK | SealFlags::SEAL,
        );
        for offset in [0, ORIGINAL.len() as u64] {
            assert_eq!(
                executable
                    .file
                    .write_at(b"x", offset)
                    .unwrap_err()
                    .raw_os_error(),
                Some(libc::EPERM)
            );
        }
        for length in [0, ORIGINAL.len() as u64 + 1] {
            assert_eq!(
                executable.file.set_len(length).unwrap_err().raw_os_error(),
                Some(libc::EPERM)
            );
        }
        assert_eq!(
            rustix::fs::fcntl_add_seals(&*executable.file, SealFlags::FUTURE_WRITE),
            Err(rustix::io::Errno::PERM),
        );
        run(&executable, &path);
    }

    #[test]
    fn script_interpreter_reopens_the_parent_image_with_cloexec_set() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("tool");
        let bytes = b"#!/bin/sh\nprintf '%s\\n' \"$0\"\ncat \"$0\"\n";
        script(&path, bytes);
        let executable = Executable::capture(&path, 1024).unwrap();
        std::fs::remove_file(&path).unwrap();
        let parent_path = format!(
            "/proc/{}/fd/{}",
            std::process::id(),
            executable.file.as_raw_fd()
        );
        assert!(
            rustix::io::fcntl_getfd(&*executable.file)
                .unwrap()
                .contains(rustix::io::FdFlags::CLOEXEC)
        );
        let output = execute(&executable, &path, &[]);
        assert!(output.status.success(), "{output:?}");
        assert_eq!(
            output.stdout,
            [parent_path.as_bytes(), b"\n", bytes].concat()
        );
        assert!(
            rustix::io::fcntl_getfd(&*executable.file)
                .unwrap()
                .contains(rustix::io::FdFlags::CLOEXEC)
        );
    }

    #[test]
    fn bounded_copy_and_hash_agree_even_when_the_input_changes_between_reads() {
        struct Changing {
            file: File,
            edit: File,
            changed: bool,
        }
        impl Read for Changing {
            fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
                let size = self.file.read(buffer)?;
                if !self.changed {
                    self.edit.write_at(&[b'b'; 65536], 65536)?;
                    self.changed = true;
                }
                Ok(size)
            }
        }
        let mut input = tempfile::tempfile().unwrap();
        input.write_all(&[b'a'; 2 * 65536]).unwrap();
        use std::io::Seek;
        input.rewind().unwrap();
        let edit = input.try_clone().unwrap();
        let mut copied = Vec::new();
        let sha256 = transfer(
            Changing {
                file: input,
                edit,
                changed: false,
            },
            &mut copied,
            2 * 65536,
        )
        .unwrap();
        assert_eq!(copied[..65536], [b'a'; 65536]);
        assert_eq!(copied[65536..], [b'b'; 65536]);
        assert_eq!(sha256, super::super::bytes::hex(&Sha256::digest(&copied)));
    }

    #[test]
    fn input_bounds_cover_metadata_and_stream_growth_without_unbounded_reads() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("tool");
        script(&path, ORIGINAL);
        assert!(Executable::capture(&path, ORIGINAL.len()).is_ok());
        assert!(matches!(
            Executable::capture(&path, ORIGINAL.len() - 1),
            Err(ReadError::Limit)
        ));
        let mut input = io::Cursor::new(b"abcde");
        assert!(matches!(
            transfer(&mut input, io::sink(), 4),
            Err(ReadError::Limit)
        ));
        assert_eq!(input.position(), 5);
        assert!(transfer(&b"abcd"[..], io::sink(), 4).is_ok());
        assert!(transfer(io::empty(), io::sink(), 0).is_ok());
        assert!(matches!(
            transfer(&b"x"[..], io::sink(), 0),
            Err(ReadError::Limit)
        ));
    }

    #[test]
    fn kernel_execution_permission_is_required_before_snapshotting() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("tool");
        std::fs::write(&path, ORIGINAL).unwrap();
        assert!(
            matches!(Executable::capture(&path, 1024), Err(ReadError::Io(error)) if error.kind() == io::ErrorKind::PermissionDenied)
        );
        assert!(Executable::capture(directory.path(), 1024).is_err());
        assert!(Executable::capture(&directory.path().join("missing"), 1024).is_err());
    }

    #[test]
    fn elf_snapshot_preserves_the_requested_argv0() {
        assert_eq!(&std::fs::read("/bin/sh").unwrap()[..4], b"\x7fELF");
        let executable = Executable::capture(Path::new("/bin/sh"), 16 * 1024 * 1024).unwrap();
        let output = execute(
            &executable,
            Path::new("/original/installed/tool"),
            &["-c", "printf '%s' \"$0\""],
        );
        assert!(output.status.success());
        assert_eq!(output.stdout, b"/original/installed/tool");
    }

    #[test]
    fn elf_exec_does_not_inherit_the_image_descriptor() {
        let executable = Executable::capture(Path::new("/bin/sh"), 16 * 1024 * 1024).unwrap();
        let fd = executable.file.as_raw_fd().to_string();
        let output = execute(
            &executable,
            Path::new("/original/installed/tool"),
            &[
                "-c",
                "readlink /proc/$$/fd/\"$1\"; printf done",
                "tool",
                &fd,
            ],
        );
        assert!(output.status.success());
        assert_eq!(output.stdout, b"done", "{output:?}");
        assert!(
            rustix::io::fcntl_getfd(&*executable.file)
                .unwrap()
                .contains(rustix::io::FdFlags::CLOEXEC)
        );
    }

    #[test]
    fn elf_bytes_survive_path_replacement_and_in_place_edit() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("tool");
        let original = std::fs::read("/bin/sh").unwrap();
        let replacement = std::fs::read("/bin/false").unwrap();
        assert_eq!(&original[..4], b"\x7fELF");
        assert_eq!(&replacement[..4], b"\x7fELF");
        for replace_inode in [true, false] {
            script(&path, &original);
            let executable = Executable::capture(&path, 16 * 1024 * 1024).unwrap();
            assert!(executable.matches_path(&path).unwrap());
            if replace_inode {
                let other = directory.path().join("replacement");
                script(&other, &replacement);
                std::fs::rename(other, &path).unwrap();
            } else {
                script(&path, &replacement);
            }
            let output = execute(&executable, &path, &["-c", "printf original"]);
            assert!(output.status.success(), "{output:?}");
            assert_eq!(output.stdout, b"original");
            assert_eq!(
                executable.sha256(),
                super::super::bytes::hex(&Sha256::digest(&original))
            );
            assert!(!executable.matches_path(&path).unwrap());
            script(&path, &original);
            assert!(executable.matches_path(&path).unwrap());
        }
    }
}
