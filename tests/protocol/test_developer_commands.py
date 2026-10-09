"""Exercise user-facing commands and the actual published first-run instructions."""

import hashlib
import json
import os
from pathlib import Path
import re
import sys

import pytest
from processes import run as run_process

ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.parametrize("tool", ["runtime", "compiler", "optimizer"])
def test_discovery_without_protocol_inputs(toolchain, directory, tool):
    binary = getattr(toolchain, tool)
    for flag in ("--help", "--version"):
        result = run_process([binary, flag], cwd=directory, capture_output=True,
                                text=True, timeout=15)
        assert result.returncode == 0, result.stderr
        assert binary.name in result.stdout
        assert not result.stderr
        if flag == "--version":
            assert re.search(rf"{binary.name} \d+\.\d+", result.stdout)
    assert not list(directory.iterdir()), "discovery should not create input or report files"


@pytest.mark.parametrize("command", ["run-bundle", "prove-bundle", "verify-bundle",
                                    "compile", "run", "prove", "verify", "bindings"])
def test_runtime_command_help(toolchain, directory, command):
    result = run_process([toolchain.runtime, command, "--help"], cwd=directory,
                            capture_output=True, text=True, timeout=15)
    assert result.returncode == 0, result.stderr
    assert command in result.stdout and "Usage:" in result.stdout


def test_usage_and_execution_failures_remain_distinct(toolchain, directory):
    def invoke(*args):
        return run_process([toolchain.runtime, *args], cwd=directory,
                              capture_output=True, text=True, timeout=15)

    result = invoke()
    assert result.returncode == 2 and "Usage:" in result.stderr and not result.stdout
    for args in [("invalid-command",), ("invalid-command", "--help"),
                 ("invalid-command", "a", "b", "c", "d")]:
        result = invoke(*args)
        assert result.returncode == 2 and "Unknown command" in result.stderr
        assert not result.stdout
    # A real execution command still reports the existing machine-readable refusal.
    result = invoke("run", "missing.entry", "0" * 64, "inputs.json")
    assert result.returncode == 1
    report = json.loads(result.stdout)
    assert report["status"] == "refused" and report["code"]


def test_demo_entry_point(toolchain, directory, journal):
    result = journal.attempt([sys.executable, ROOT / "tests/run.py", "demo"], env={
        **os.environ,
        "ZKC_COMPILER_BIN": str(toolchain.directories["compiler"]),
        "ZKC_NATIVE_BIN": str(toolchain.directories["native"]),
        "ZKC_REPORTS_DIR": str(directory / "reports"),
    })
    assert result.returncode == 0, result.stdout + result.stderr
    assert "Proof accepted:" in result.stdout


@pytest.mark.parametrize("marker", ["native-bundle", "native-proof"])
def test_published_mathematical_walkthrough(marker, toolchain, directory, journal):
    document = (ROOT / "docs/runtime/bundles.md").read_text()
    match = re.search(rf"<!-- executable: {marker} -->\s*```sh\n(.*?)\n```", document, re.S)
    assert match, f"the maintained executable walkthrough is missing: {marker}"
    env = dict(os.environ, TMPDIR=str(directory),
               ZKC_COMPILER_BIN=str(toolchain.directories["compiler"]),
               ZKC_NATIVE_BIN=str(toolchain.directories["native"]))
    result = run_process(["bash", "-euo", "pipefail", "-c", match[1]], cwd=ROOT,
                         env=env, capture_output=True, text=True, timeout=120)
    (directory / "walkthrough.stdout").write_text(result.stdout)
    (directory / "walkthrough.stderr").write_text(result.stderr)
    assert result.returncode == 0, result.stdout + result.stderr
    if marker == "native-bundle":
        report = json.loads(result.stdout)
        assert report["status"] == "executed" and report["outcome"] == ["completed"]
        assert report["acceptance"] is None
        assert report["roles"][1]["outputs"] == [["wire", "bool@native.bool/1", "5a4b4356010500"]]
        return
    output = Path(result.stdout.rsplit("Proof files: ", 1)[1].strip())
    assert output.parent == directory
    assert json.loads((output / "producer.json").read_text())["status"] == "produced"
    assert json.loads((output / "validator.json").read_text())["status"] == "accepted"
    deployment = output / "deployment.json"
    pin = hashlib.sha256(deployment.read_bytes()).hexdigest()
    proof = (output / "proof.bin").read_bytes()
    for data, code, expected in [(proof[:-1], "proof-truncated", pin),
                                 (proof + b"x", "proof-trailing", pin),
                                 (proof, "native-proof-deployment-binding", "00" * 32)]:
        candidate = output / "invalid.bin"
        candidate.write_bytes(data)
        journal.json([toolchain.runtime, "verify-bundle", deployment, expected,
                      output / "validator-inputs.json", candidate, "--allow-header-only"], refuses=code)
