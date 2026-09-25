"""Exercise cancellation against real processes, including grandchildren."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

import pytest

from journal import Journal
from processes import TERMINATION, run

ROOT = Path(__file__).resolve().parents[2]


def command(code):
    return [sys.executable, "-c", code]


def alive(pid):
    # An orphan zombie has stopped executing; only its new parent can reap it.
    status = Path(f"/proc/{pid}/stat")
    if status.exists():
        return status.read_text().split(") ", 1)[1].split()[0] != "Z"
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True


def wait_for(predicate, seconds=5):
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.01)
    assert predicate(), "controlled process did not reach the expected state"


def tree_script(tmp_path, *, leave=False):
    """A child holding inherited pipes, even after its parent exits."""
    path = tmp_path / "tree.py"
    pidfile = tmp_path / "grandchild.pid"
    path.write_text(f'''import os, signal, subprocess, sys, time
from pathlib import Path
signal.signal(signal.SIGINT, lambda *_: sys.exit(0))
child = subprocess.Popen([sys.executable, "-c", "import signal,time; signal.signal(signal.SIGINT, signal.SIG_IGN); signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(60)"])
print("partial stdout", flush=True)
print("partial stderr", file=sys.stderr, flush=True)
Path({str(pidfile)!r}).write_text(str(child.pid))
{"sys.exit(0)" if leave else "time.sleep(60)"}
''')
    return path, pidfile


@pytest.mark.skipif(os.name != "posix", reason="POSIX process-group contract")
@pytest.mark.parametrize("leave", [False, True])
def test_timeout_stops_grandchild_even_after_leader_exit(tmp_path, leave):
    script, pidfile = tree_script(tmp_path, leave=leave)
    started = time.monotonic()
    try:
        with pytest.raises(subprocess.TimeoutExpired) as caught:
            Journal(tmp_path / "report").attempt([sys.executable, script], timeout=0.5)
        assert caught.value.stdout == b"partial stdout\n"
        assert caught.value.stderr == b"partial stderr\n"
        wait_for(lambda: not alive(int(pidfile.read_text())))
        assert time.monotonic() - started < 5
        record = json.loads((tmp_path / "report/commands.jsonl").read_text())
        assert record["returncode"] == "timeout"
        assert Path(record["output"]).read_text() == "partial stdout\n"
    finally:
        if pidfile.exists() and alive(int(pidfile.read_text())):
            os.kill(int(pidfile.read_text()), signal.SIGKILL)


@pytest.mark.skipif(os.name != "posix", reason="POSIX process-group contract")
@pytest.mark.parametrize("signum", [signal.SIGINT, signal.SIGTERM, getattr(signal, "SIGHUP", None)])
def test_interrupt_preserves_output_and_cleans_nested_groups(tmp_path, signum):
    script, pidfile = tree_script(tmp_path)
    leaf = tmp_path / "leaf.py"
    leaf.write_text(f'''import sys
sys.path.insert(0, {str(ROOT / "tests/support")!r})
from journal import Journal
Journal({str(tmp_path / "journal")!r}).attempt([sys.executable, {str(script)!r}])
''')
    middle = tmp_path / "middle.py"
    middle.write_text(f'''import sys
sys.path.insert(0, {str(ROOT / "tests/support")!r})
from journal import Journal
Journal({str(tmp_path / "middle-journal")!r}).attempt([sys.executable, {str(leaf)!r}], cleanup_grace=3)
''')
    supervisor = command(f'''import sys
sys.path.insert(0, {str(ROOT / "scripts")!r})
from processes import run, Interrupted
try:
    run([sys.executable, {str(middle)!r}], cleanup_grace=5, check=True)
except Interrupted as error:
    sys.exit(128 + error.signum)
''')
    process = subprocess.Popen(supervisor, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               start_new_session=True)
    try:
        wait_for(pidfile.exists)
        process.send_signal(signum)
        process.communicate(timeout=20)
        assert process.returncode == 128 + signum
        wait_for(lambda: not alive(int(pidfile.read_text())))
        saved = json.loads((tmp_path / "journal/commands.jsonl").read_text())
        assert saved["returncode"] == "interrupted"
        assert saved["signal"] == signum
        assert saved["stderr"] == "partial stderr\n"
        assert Path(saved["output"]).read_text() == "partial stdout\n"
    finally:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate(timeout=5)
        if pidfile.exists() and alive(int(pidfile.read_text())):
            os.kill(int(pidfile.read_text()), signal.SIGKILL)


def test_process_api_preserves_streams_cwd_environment_and_status(tmp_path):
    result = run(command("import os,sys; print(os.getcwd()); print(os.environ['SELECTED']); "
                         "print(sys.stdin.read(), file=sys.stderr); sys.exit(7)"),
                 input="payload", text=True, capture_output=True, cwd=tmp_path,
                 env={**os.environ, "SELECTED": "literal $(no-shell)"})
    assert result.returncode == 7
    assert result.stdout == f"{tmp_path}\nliteral $(no-shell)\n"
    assert result.stderr == "payload\n"
    with (tmp_path / "output").open("w") as stream:
        run(command("print('streamed')"), stdout=stream, check=True)
    assert (tmp_path / "output").read_text() == "streamed\n"
    with pytest.raises(subprocess.CalledProcessError) as caught:
        run(command("print('bad'); raise SystemExit(9)"), capture_output=True, check=True)
    assert caught.value.returncode == 9 and caught.value.stdout == b"bad\n"


@pytest.mark.parametrize("timeout", [0, -1, float("inf"), float("nan")])
def test_invalid_timeout_does_not_spawn(tmp_path, timeout):
    marker = tmp_path / "must-not-exist"
    with pytest.raises(ValueError, match="finite positive"):
        run(command(f"from pathlib import Path; Path({str(marker)!r}).touch()"), timeout=timeout)
    assert not marker.exists()


def test_signal_handler_restored_on_success_spawn_failure_and_timeout(tmp_path):
    original = {signum: signal.getsignal(signum) for signum in TERMINATION}
    for arguments, timeout, expected in [(command("pass"), 2, None),
                                          ([tmp_path / "missing"], 2, OSError),
                                          (command("import time; time.sleep(60)"), 0.1,
                                           subprocess.TimeoutExpired)]:
        if expected:
            with pytest.raises(expected):
                run(arguments, timeout=timeout)
        else:
            run(arguments, timeout=timeout)
        assert {signum: signal.getsignal(signum) for signum in TERMINATION} == original


@pytest.mark.skipif(not hasattr(signal, "setitimer"), reason="POSIX timer control")
def test_caller_abort_is_recorded_and_reaps_the_direct_child(tmp_path):
    def abort(signum, frame):
        raise RuntimeError("caller stopped the case")
    old = signal.signal(signal.SIGALRM, abort)
    try:
        signal.setitimer(signal.ITIMER_REAL, 0.2)
        with pytest.raises(RuntimeError, match="caller stopped"):
            Journal(tmp_path).attempt(command("import os,time; print(os.getpid(), flush=True); time.sleep(60)"))
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old)
    record = json.loads((tmp_path / "commands.jsonl").read_text())
    assert record["returncode"] == "aborted"
    pid = int(Path(record["output"]).read_text())
    with pytest.raises(ChildProcessError):
        os.waitpid(pid, os.WNOHANG)
    assert not alive(pid)


@pytest.mark.parametrize("sleep", [False, True])
def test_invalid_text_cannot_replace_timeout_or_erase_raw_output(tmp_path, sleep):
    program = "import sys,time; sys.stdout.buffer.write(b'\\xff'); sys.stdout.flush(); "
    program += "time.sleep(60)" if sleep else "pass"
    with pytest.raises(subprocess.TimeoutExpired if sleep else UnicodeError) as caught:
        Journal(tmp_path).attempt(command(program), timeout=0.2)
    assert caught.value.stdout == b"\xff"
    record = json.loads((tmp_path / "commands.jsonl").read_text())
    assert record["returncode"] == ("timeout" if sleep else "aborted")
    assert Path(record["output"]).read_text() == "\ufffd"


@pytest.mark.skipif(os.name != "posix", reason="POSIX signal forwarding")
def test_actual_pytest_cancellation_writes_junit_and_summary(tmp_path, monkeypatch):
    import xml.etree.ElementTree as ET

    suite = tmp_path / "tiny-suite"
    suite.mkdir()
    ready = suite / "ready"
    (suite / "pytest.ini").write_text("[pytest]\n")
    (suite / "test_interrupt.py").write_text(f'''import os, sys, time
from pathlib import Path

def test_completed():
    assert 1 + 1 == 2

def test_interrupted():
    sys.stdout.buffer.write(b"raw-before-interrupt:\\xff\\n")
    sys.stdout.flush()
    sys.stderr.buffer.write(b"raw-error:\\xfe\\n")
    sys.stderr.flush()
    Path({str(ready)!r}).write_text(str(os.getpid()))
    time.sleep(60)
''')
    # Keep the driver's real lifecycle and JUnit argv; replace only uv's suite
    # selection with a tiny real pytest invocation in the prepared interpreter.
    uv = tmp_path / "uv"
    uv.write_text(f'''#!{sys.executable}
import os, sys
report = next(arg for arg in sys.argv if arg.startswith("--junit-xml="))
os.execv(sys.executable, [sys.executable, "-m", "pytest", "-q", "-s", "-c",
                         {str(suite / "pytest.ini")!r}, {str(suite)!r}, report])
''')
    uv.chmod(0o755)
    monkeypatch.setenv("PATH", f"{tmp_path}{os.pathsep}{os.environ['PATH']}")
    monkeypatch.setenv("ZKC_REPORTS_DIR", str(tmp_path / "reports"))
    monkeypatch.setenv("PYTEST_DISABLE_PLUGIN_AUTOLOAD", "1")
    monkeypatch.delenv("PYTEST_ADDOPTS", raising=False)
    process = subprocess.Popen([sys.executable, str(ROOT / "tests/run.py"), "harness"],
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               start_new_session=True)
    try:
        wait_for(ready.exists, seconds=10)
        process.send_signal(signal.SIGINT)
        out, err = process.communicate(timeout=15)
        assert process.returncode == 130, (out, err)
        assert b"KeyboardInterrupt" in out and b"1 passed" in out
        assert b"raw-before-interrupt:\xff\n" in out
        assert b"raw-error:\xfe\n" in err
        report, = (tmp_path / "reports/runs").glob("*/harness.xml")
        junit = ET.parse(report)
        # pytest may emit an unnamed, unfinished testcase on interruption.
        assert junit.find("testsuite").attrib["tests"] == "1"
        assert [case.attrib["name"] for case in junit.findall(".//testcase[@name]")] == ["test_completed"]
        assert not junit.findall(".//failure") and not junit.findall(".//error")
        manifest = json.loads((report.parent / "run.json").read_text())
        assert manifest["status"] == "interrupted"
        wait_for(lambda: not alive(int(ready.read_text())))
    finally:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate(timeout=5)
        if ready.exists() and alive(int(ready.read_text())):
            os.killpg(int(ready.read_text()), signal.SIGKILL)


@pytest.mark.skipif(os.name != "posix", reason="POSIX signal escalation")
@pytest.mark.parametrize("cancel", [False, True])
def test_signal_escalation_retains_raw_captured_bytes(tmp_path, cancel):
    ready = tmp_path / "ready"
    received = tmp_path / "signals"
    child = tmp_path / "child.py"
    child.write_text(f'''import os, signal, sys, time
from pathlib import Path

def record(signum, frame):
    with Path({str(received)!r}).open("a") as stream:
        stream.write(str(signum) + "\\n")

signal.signal(signal.SIGINT, record)
signal.signal(signal.SIGTERM, record)
sys.stdout.buffer.write(b"partial:\\xff\\n")
sys.stdout.flush()
sys.stderr.buffer.write(b"error:\\xfe\\n")
sys.stderr.flush()
Path({str(ready)!r}).write_text(str(os.getpid()))
while True:
    time.sleep(1)
''')
    supervisor = command(f'''import subprocess, sys
from pathlib import Path
sys.path.insert(0, {str(ROOT / "scripts")!r})
from processes import run, Interrupted
try:
    run([sys.executable, {str(child)!r}], capture_output=True,
        timeout={None if cancel else 0.5!r}, cleanup_grace=0.2)
except (Interrupted, subprocess.TimeoutExpired) as error:
    Path({str(tmp_path / "stdout")!r}).write_bytes(error.stdout)
    Path({str(tmp_path / "stderr")!r}).write_bytes(error.stderr)
    sys.exit(130 if isinstance(error, Interrupted) else 124)
''')
    process = subprocess.Popen(supervisor, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               start_new_session=True)
    try:
        wait_for(ready.exists)
        if cancel:
            process.send_signal(signal.SIGINT)
        out, err = process.communicate(timeout=5)
        assert process.returncode == (130 if cancel else 124), (out, err)
        assert list(map(int, received.read_text().splitlines())) == (
            [signal.SIGINT, signal.SIGTERM] if cancel else [signal.SIGTERM])
        assert (tmp_path / "stdout").read_bytes() == b"partial:\xff\n"
        assert (tmp_path / "stderr").read_bytes() == b"error:\xfe\n"
        wait_for(lambda: not alive(int(ready.read_text())))
    finally:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate(timeout=5)
        if ready.exists() and alive(int(ready.read_text())):
            os.killpg(int(ready.read_text()), signal.SIGKILL)
