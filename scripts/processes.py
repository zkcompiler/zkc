"""Run commands with owned process groups and bounded cancellation cleanup.

This is a lifecycle primitive, not a timeout policy or a shell. Callers select
their own budgets and interpret domain exit codes. POSIX descendants that stay
in the command's group are terminated together; detached daemons and supervisor
SIGKILL are outside this contract. Non-POSIX cleanup covers the direct child.
"""

from contextlib import contextmanager
import locale
import math
import os
import signal
import subprocess
import sys
import threading
import time

GRACE = 1.0
# Signals that end a run from outside: SIGTERM, and SIGHUP where the platform
# has it, which a closed terminal or a dropped SSH session sends. Children run
# in sessions of their own, so neither reaches them unless it is forwarded.
TERMINATION = tuple(getattr(signal, name) for name in ("SIGTERM", "SIGHUP")
                    if hasattr(signal, name))


class Interrupted(KeyboardInterrupt):
    """Cancellation, with captured diagnostics and the initiating signal."""

    def __init__(self, signum=signal.SIGINT):
        super().__init__(f"interrupted by signal {signum}")
        self.signum = signum
        self.stdout = self.stderr = None


def positive_timeout(value):
    seconds = float(value)
    if not math.isfinite(seconds) or seconds <= 0:
        raise ValueError("timeout must be a finite positive number of seconds")
    return seconds


@contextmanager
def termination_handler():
    # Python permits signal handlers only in the main thread. Do not override
    # an ignored signal (as under nohup); callers retain their deliberate
    # signal policy.
    previous = {}

    def interrupt(signum, frame):
        raise Interrupted(signum)

    if threading.current_thread() is threading.main_thread():
        for signum in TERMINATION:
            if signal.getsignal(signum) != signal.SIG_IGN:
                previous[signum] = signal.signal(signum, interrupt)
    try:
        yield
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def _signal(process, signum):
    try:
        if os.name == "posix":
            os.killpg(process.pid, signum)
        elif process.poll() is None:
            process.kill()
    except ProcessLookupError:
        pass


def _group_exists(process):
    if os.name != "posix":
        return process.poll() is None
    try:
        os.killpg(process.pid, 0)
    except ProcessLookupError:
        return False
    return True


def _stop(process, grace, initial=signal.SIGTERM):
    # Give pytest and nested runners their initiating signal so they can write
    # summaries and clean their own groups. Timeouts and caller aborts use TERM.
    stages = [initial] + ([signal.SIGTERM] if initial != signal.SIGTERM else [])
    try:
        for signum in stages:
            _signal(process, signum)
            deadline = time.monotonic() + grace
            try:
                output = process.communicate(timeout=grace)
            except subprocess.TimeoutExpired:
                continue
            # A descendant may close its pipes but remain alive after the leader
            # exits. Give it the same grace, then escalate the whole group.
            while _group_exists(process) and time.monotonic() < deadline:
                time.sleep(0.01)
            if not _group_exists(process):
                return output
    finally:
        _signal(process, getattr(signal, "SIGKILL", signal.SIGTERM))
    try:
        return process.communicate(timeout=GRACE)
    except subprocess.TimeoutExpired as error:
        # A detached process can retain an inherited pipe. Do not wait forever
        # for its EOF; retain the bytes already collected, then close our ends.
        return error.stdout, error.stderr
    finally:
        process.wait()


@contextmanager
def cleanup_signals():
    """A second Ctrl-C must not abandon children halfway through cleanup."""
    previous = {}
    if threading.current_thread() is threading.main_thread():
        for signum in (signal.SIGINT, *TERMINATION):
            previous[signum] = signal.signal(signum, signal.SIG_IGN)
    try:
        yield
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def run(arguments, *, input=None, text=False, capture_output=False, stdout=None,
        stderr=None, timeout=None, cwd=None, env=None, check=False, cleanup_grace=GRACE):
    """The subprocess.run subset used by repository tools, with group cleanup."""
    if timeout is not None:
        timeout = positive_timeout(timeout)
    cleanup_grace = positive_timeout(cleanup_grace)
    if capture_output:
        if stdout is not None or stderr is not None:
            raise ValueError("capture_output cannot be combined with stdout/stderr")
        stdout = stderr = subprocess.PIPE
    arguments = list(map(str, arguments))
    encoding = "utf-8" if sys.flags.utf8_mode else locale.getencoding()
    if text and input is not None:
        input = input.replace("\n", os.linesep).encode(encoding)
    with termination_handler():
        # Transport bytes until the process is reaped. Decoding during timeout
        # cleanup could replace the timeout with an unrelated Unicode error.
        process = subprocess.Popen(arguments, stdin=subprocess.PIPE if input is not None else None,
                                   stdout=stdout, stderr=stderr, cwd=cwd, env=env,
                                   start_new_session=(os.name == "posix"))
        try:
            out, err = process.communicate(input, timeout=timeout)
        except BaseException as error:
            with cleanup_signals():
                initial = (getattr(error, "signum", signal.SIGINT)
                           if isinstance(error, KeyboardInterrupt) else signal.SIGTERM)
                out, err = _stop(process, cleanup_grace, initial)
            if isinstance(error, subprocess.TimeoutExpired):
                # Match subprocess's bytes contract for TimeoutExpired.
                error.output, error.stderr = out, err
            elif isinstance(error, KeyboardInterrupt):
                interrupted = error if isinstance(error, Interrupted) else Interrupted()
                interrupted.stdout, interrupted.stderr = out, err
                if interrupted is error:
                    raise
                raise interrupted from error
            else:
                # pytest-timeout and other caller aborts need the same retained
                # output, without being relabeled as user cancellation.
                error.stdout, error.stderr = out, err
            raise
        finally:
            for stream in (process.stdin, process.stdout, process.stderr):
                if stream is not None:
                    stream.close()
        if text:
            try:
                def decode(value):
                    return None if value is None else value.decode(encoding).replace("\r\n", "\n").replace("\r", "\n")
                decoded_out, decoded_err = decode(out), decode(err)
            except UnicodeError as error:
                error.stdout, error.stderr = out, err
                raise
            out, err = decoded_out, decoded_err
        result = subprocess.CompletedProcess(arguments, process.returncode, out, err)
        if check:
            result.check_returncode()
        return result
