"""Shared measurement I/O; callers own workload semantics and timing policy."""
import argparse
from contextlib import contextmanager
from contextvars import ContextVar
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shlex
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
from processes import run  # noqa: E402

class MeasurementError(Exception):
    pass


class MeasurementBusy(MeasurementError):
    """Another cooperating session owns the host's measurement slot."""


MEASUREMENT_LOCK = Path('/tmp/zkc-benchmark-execution.lock')
_measurement_fd = ContextVar('measurement_fd', default=None)


@contextmanager
def measurement_slot(evidence):
    """Hold one advisory lock across preparation, workers and validation.

    Children are managed by the owning scheduler and must not reacquire this
    lock. The stable lock file is never removed, including on failure.
    """
    if evidence.parent.exists():
        raise FileExistsError(evidence.parent)
    record = {'path': str(MEASUREMENT_LOCK), 'pid': os.getpid(),
              'attempted_utc': datetime.now(timezone.utc).isoformat()}
    with MEASUREMENT_LOCK.open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise MeasurementBusy(f'measurement slot busy: {MEASUREMENT_LOCK}') from error
        record['acquired_utc'] = datetime.now(timezone.utc).isoformat()
        token = _measurement_fd.set(lock.fileno())
        try:
            yield record
        finally:
            _measurement_fd.reset(token)
            record['finished_utc'] = datetime.now(timezone.utc).isoformat()
            if evidence.parent.is_dir():
                write_json(evidence, record)


def require(condition, message):
    if not condition:
        raise MeasurementError(message)


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def identity(path):
    return {'path': str(path), 'sha256': digest(path), 'bytes': path.stat().st_size,
            'mtime_ns': path.stat().st_mtime_ns}


def performance_environment():
    # A fixed allowlist avoids collecting unrelated credentials and user secrets.
    names = ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'MALLOC_ARENA_MAX', 'MALLOC_CONF', 'GLIBC_TUNABLES',
             'MALLOC_MMAP_THRESHOLD_', 'MALLOC_TRIM_THRESHOLD_', 'MALLOC_TOP_PAD_', 'MALLOC_CHECK_',
             'RAYON_NUM_THREADS', 'OMP_NUM_THREADS', 'OMP_PROC_BIND', 'OMP_PLACES',
             'RUST_LOG', 'RUST_BACKTRACE')
    return {name: os.environ[name] for name in names if name in os.environ}


def command_environment():
    # Explicit inputs to child tools; do not inherit ambient tracing, feature
    # switches, Python injection paths, or unrelated credentials.
    names = ('PATH', 'HOME', 'TMPDIR', 'TMP', 'TEMP', 'SYSTEMROOT', 'NIX_LD', 'NIX_LD_LIBRARY_PATH')
    return ({name: os.environ[name] for name in names if name in os.environ}
            | performance_environment()
            | {'LC_ALL': 'C', 'PYTHONHASHSEED': '0', 'PYTHONDONTWRITEBYTECODE': '1'})


class Journal:
    """Retain each process invocation, including failures, timeouts and interrupts."""

    def __init__(self, directory, timeout):
        self.directory, self.timeout = directory, timeout
        self.directory.mkdir(parents=True, exist_ok=True)
        self.sequence = 0

    def command(self, argv, *, cwd, stdout=None, expected=0):
        argv = list(map(str, argv))
        number = self.sequence
        self.sequence += 1
        stdout = stdout or self.directory / f'{number:04d}.stdout'
        stderr = self.directory / f'{number:04d}.stderr'
        environment = command_environment()
        record = {'argv': argv, 'shell': shlex.join(argv), 'cwd': str(cwd),
                  'environment': environment, 'timeout_seconds': self.timeout,
                  'performance_environment': performance_environment(),
                  'stdout': str(stdout), 'stderr': str(stderr),
                  'started_utc': datetime.now(timezone.utc).isoformat(), 'returncode': None}
        out = err = b''
        start = time.perf_counter()
        try:
            # Pipe capture wakes on EOF. File-backed subprocess.wait(timeout=...)
            # polls and can dominate these short runs with its sleep intervals.
            result = run(argv, cwd=cwd, env=environment, capture_output=True,
                         timeout=self.timeout, pass_fds=(() if _measurement_fd.get() is None else (_measurement_fd.get(),)))
            out, err = result.stdout, result.stderr
            record['returncode'] = result.returncode
        except BaseException as error:
            out, err = getattr(error, 'stdout', None) or b'', getattr(error, 'stderr', None) or b''
            record['error'] = f'{type(error).__name__}: {error}'
            raise
        finally:
            record['wall_seconds'] = time.perf_counter() - start
            record['finished_utc'] = datetime.now(timezone.utc).isoformat()
            stdout.write_bytes(out)
            stderr.write_bytes(err)
            with (self.directory / 'commands.jsonl').open('a') as stream:
                stream.write(json.dumps(record) + '\n')
        if expected is not None:
            require(result.returncode == expected,
                    f'command exited {result.returncode}; see {stderr} and {stdout}')
        return record

    def report(self, argv, *, cwd, status, refused=False):
        record = self.command(argv, cwd=cwd, expected=None)
        report = json.loads(Path(record['stdout']).read_text())
        code = record['returncode']
        require((code > 0 if refused else code == 0) and report.get('status') == status,
                f'expected {status}, exit={code}; see {record["stdout"]}')
        return report, record


def executable(value):
    path = Path(value).expanduser().resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise argparse.ArgumentTypeError(f'explicit executable does not exist: {path}')
    return path


def positive_integer(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError('expected a positive integer')
    return number
