"""Python transport checks; native behavior is covered by Entry integration."""

import os
import sys

import pytest

from zkc import Client, ExecutionError, ToolError


def executable(tmp_path, body):
    path = tmp_path / "zkc-adapter-test"
    path.write_text(f"#!{sys.executable}\n" + body)
    path.chmod(0o700)
    return path


def test_source_return_and_failure_keep_the_native_report(tmp_path):
    tool = executable(tmp_path, '''import json, pathlib, sys
assert sys.argv[1:3] == ["--json", "run"]
inputs = pathlib.Path(next(x.split("=", 1)[1] for x in sys.argv if x.startswith("--input=")))
outputs = pathlib.Path(next(x.split("=", 1)[1] for x in sys.argv if x.startswith("--results=")))
arguments = json.loads(inputs.read_text())
if arguments["success"]:
    outputs.write_text(json.dumps({"format":"zkc.entry-outputs/0", "value":arguments["value"]}))
    print(json.dumps({"status":"executed", "execution":{"calls":[{"kind":"numeric"}]}}))
else:
    print(json.dumps({"status":"refused", "code":"runtime-stop", "execution":{"calls":[{"kind":"numeric"}]}}))
    sys.exit(1)
''')
    client = Client(executable=tool)
    value = {"alternative": "Rejected", "fields": {}}
    result = client.run({"success": True, "value": value}, entry="Choose")
    assert result.require_success().value == value
    assert result.report["execution"]["calls"] == [{"kind": "numeric"}]
    result = client.run({"success": False}, entry="Choose")
    assert not result.ok and result.value is None
    with pytest.raises(ExecutionError) as caught:
        result.require_success()
    assert caught.value.execution is result


def test_direct_proof_bytes_and_public_statement_are_passed_unchanged(tmp_path):
    candidate = bytes(range(256))
    tool = executable(tmp_path, '''import json, pathlib, sys
command = sys.argv[2]
public = pathlib.Path(next(x.split("=", 1)[1] for x in sys.argv if x.startswith("--public=")))
assert json.loads(public.read_text()) == {"claim":"17"}
if command == "prove":
    output = pathlib.Path(next(x.split("=", 1)[1] for x in sys.argv if x.startswith("--output=")))
    output.write_bytes(bytes(range(256)))
    print(json.dumps({"status":"produced"}))
else:
    proof = pathlib.Path(next(x.split("=", 1)[1] for x in sys.argv if x.startswith("--proof=")))
    assert proof.read_bytes() == bytes(range(256))
    assert not any(x.startswith("--witness=") for x in sys.argv)
    print(json.dumps({"status":"accepted"}))
''')
    client = Client(executable=tool)
    result = client.prove({"claim": "17"}, {"secret": "8"}, entry="Core")
    assert result.require_success().proof == candidate
    assert client.verify({"claim": "17"}, result.proof, entry="Core").ok


@pytest.mark.parametrize("body", [
    'print("not json")',
    'print("[]")',
    'print(\'{"status":"refused","code":"failure"}\')',
    'import sys; print(\'{"status":"executed"}\'); sys.exit(1)',
])
def test_broken_process_reports_are_not_source_results(tmp_path, body):
    with pytest.raises(ToolError):
        Client(executable=executable(tmp_path, body)).inspect()


def test_package_pin_and_source_options_are_exclusive(tmp_path):
    with pytest.raises(ValueError):
        Client(package=tmp_path / "artifact", sha256="f" * 64, project=tmp_path)
    with pytest.raises(ValueError):
        Client(package=tmp_path / "artifact", sha256="x" * 64)
    with pytest.raises(ValueError):
        Client(sha256="0" * 64)
    tool = executable(tmp_path, '''import json, sys
assert len([x for x in sys.argv if x.startswith("--package=")]) == 1
assert "--sha256=" + "0" * 64 in sys.argv
print(json.dumps({"status":"inspected", "interface":{"entry":"app::Run"}}))
''')
    client = Client(package=tmp_path / "artifact", sha256="0" * 64, executable=tool)
    assert client.inspect().require_success().value == {"entry": "app::Run"}


@pytest.mark.skipif(os.name != "posix", reason="process group cancellation is POSIX")
def test_timeout_cancels_the_owned_tool_process(tmp_path):
    tool = executable(tmp_path, "import time; time.sleep(30)")
    with pytest.raises(ToolError, match="TimeoutExpired"):
        Client(executable=tool, timeout=0.05).inspect()


@pytest.mark.parametrize("status", ["produced", "accepted", "inspected"])
def test_run_refuses_success_reports_from_other_operations(tmp_path, status):
    tool = executable(tmp_path, f"import json; print(json.dumps({{'status': {status!r}}}))")
    with pytest.raises(ToolError, match="different command"):
        Client(executable=tool).run({})


@pytest.mark.skipif(os.name != "posix", reason="process group cancellation is POSIX")
def test_timeout_kills_children_even_when_the_group_leader_exits(tmp_path):
    import time
    from pathlib import Path

    pid_file = tmp_path / "child.pid"
    tool = executable(tmp_path, f"""import pathlib, subprocess, sys, time
child = subprocess.Popen([sys.executable, '-c', 'import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(30)'])
pathlib.Path({str(pid_file)!r}).write_text(str(child.pid))
time.sleep(30)
""")
    with pytest.raises(ToolError, match="TimeoutExpired"):
        Client(executable=tool, timeout=0.15).inspect()
    pid = int(pid_file.read_text())
    # A reparented zombie may remain until the environment's init reaps it.
    for _ in range(50):
        status = Path(f"/proc/{pid}/status")
        if not status.exists() or "State:\tZ" in status.read_text():
            break
        time.sleep(0.01)
    else:
        pytest.fail("owned child survived process-group cancellation")


def test_output_limit_cancels_the_process_before_report_decoding(tmp_path, monkeypatch):
    import zkc.client as adapter

    monkeypatch.setattr(adapter, "_MAX_BYTES", 4096)
    tool = executable(tmp_path, "import sys,time; sys.stderr.write('x'*8192); sys.stderr.flush(); time.sleep(30)")
    with pytest.raises(ToolError, match="output exceeds"):
        Client(executable=tool, timeout=2).inspect()
