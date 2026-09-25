"""Actual artifact entry points retain failed commands before a suite finishes."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]

DRIVERS = {
    "host": ("crates/zkc-tools/tests/artifact_host.py",
             "zkc fixture-exporter compiler lean output-dir"),
    "identity": ("crates/zkc-tools/tests/artifact_identity.py",
                 "zkc compiler output-dir"),
    "limits": ("crates/zkc-tools/tests/artifact_limits.py",
               "zkc compiler lean primitive output"),
    "profile": ("crates/zkc-tools/tests/artifact_profile.py",
                "native compiler lean-checker lean-reference output"),
    "reference": ("crates/zkc-tools/tests/artifact_reference.py",
                  "zkc compiler lean fixture-exporter reference-driver reference primitive output-dir"),
    "baseline": ("tests/artifact/artifact_baseline.py",
                 "baseline fixtures output host compiler participant-checker lean primitive"),
    "differential": ("tests/artifact/artifact_differential.py",
                     "native compiler lean-checker lean-reference primitive fixtures output"),
}


def invocation(name, tmp_path, program):
    fake = tmp_path / "tool"
    fake.write_text(f"#!{sys.executable}\n" + program + "\n")
    fake.chmod(0o755)
    fixture = tmp_path / "fixtures"
    # Only enough input to reach the first tool invocation. No protocol oracle
    # or native compiler is being replaced by this lifecycle control.
    for protocol in ("dleq", "committed-two-factor"):
        path = fixture / protocol
        path.mkdir(parents=True)
        (path / "producer").mkdir()
        (path / "validator").mkdir()
        source = ["zkc.protocol/2", [], [], [], [["test", "test", "test", [["size", "1"]]]]]
        for filename, data in [("source.json", source), ("descriptor.json", []),
                               ("producer/inputs.json", []), ("validator/inputs.json", [])]:
            (path / filename).write_text(json.dumps(data))
        (path / "proof.bin").write_bytes(b"x" * 40)
    script, flags = DRIVERS[name]
    output = tmp_path / "output"
    arguments = [sys.executable, str(ROOT / script)]
    for flag in flags.split():
        value = output if flag.startswith("output") else fixture if flag == "fixtures" else fake
        arguments.extend(["--" + flag, str(value)])
    if name == "identity":
        arguments.append("--inspection-only")
    return arguments, output


@pytest.mark.parametrize("name", DRIVERS)
def test_each_artifact_driver_keeps_timeout_evidence(name, tmp_path):
    arguments, output = invocation(name, tmp_path,
        "import sys,time; print('partial', flush=True); "
        "print('diagnostic', file=sys.stderr, flush=True); time.sleep(60)")
    result = subprocess.run([*arguments, "--timeout", "0.2"],
                            capture_output=True, timeout=10)
    assert result.returncode > 0
    saved = json.loads((output / "commands/commands.jsonl").read_text())
    assert saved["returncode"] == "timeout", result.stderr.decode()
    assert "diagnostic" in saved["stderr"]
    assert Path(saved["output"]).read_text() == "partial\n"
    assert saved["timeout_seconds"] == 0.2
    # A rerun must not truncate the failed run or mix new results into it.
    before = (output / "commands/commands.jsonl").read_bytes()
    again = subprocess.run(arguments, capture_output=True, timeout=10)
    assert again.returncode > 0 and b"FileExistsError" in again.stderr
    assert (output / "commands/commands.jsonl").read_bytes() == before


@pytest.mark.skipif(os.name != "posix", reason="POSIX signal exit status")
def test_differential_driver_refuses_valid_json_followed_by_signal(tmp_path):
    arguments, output = invocation("differential", tmp_path,
        "import os,signal; print('{}', flush=True); os.kill(os.getpid(),signal.SIGTERM)")
    result = subprocess.run(arguments, capture_output=True, text=True, timeout=10)
    saved = json.loads((output / "commands/commands.jsonl").read_text())
    assert saved["returncode"] == -signal.SIGTERM
    assert result.returncode > 0 and f"AssertionError: ({-signal.SIGTERM}," in result.stderr
    assert not (output / "dleq-work/reference").exists()
