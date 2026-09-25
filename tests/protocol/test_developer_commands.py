"""Exercise user-facing commands and the actual published first-run instructions."""

import json
import os
from pathlib import Path
import re
import sys

import pytest
from processes import run as run_process

ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.parametrize("page", ["docs/language/reference.md",
                                  "docs/language/values.md"])
def test_documented_source_forms(page, toolchain, directory):
    document = (ROOT / page).read_text()
    match = re.search(r"<!-- executable: (source|module-body) -->\s*```text\n(.*?)\n```",
                      document, re.S)
    assert match, f"the maintained source example is missing: {page}"
    source = match[2] if match[1] == "source" else "module {\n" + match[2] + "\n}"
    path = directory / "example.pir"
    path.write_text(source)
    result = run_process([toolchain.compiler, "protocol-source", path],
                            capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stderr
    assert isinstance(json.loads(result.stdout), list)


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


@pytest.mark.parametrize("command", ["run-protocol", "produce-artifact", "validate-artifact",
                                    "inspect-artifact-identity", "run", "run-physical"])
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
    for args in [("unknown",), ("unknown", "--help"), ("unknown", "a", "b", "c", "d")]:
        result = invoke(*args)
        assert result.returncode == 2 and "Unknown command" in result.stderr
        assert not result.stdout
    # A real execution command still reports the existing machine-readable refusal.
    result = invoke("run-protocol", "missing.json", "plan.json", "inputs.json", "checker")
    assert result.returncode == 1
    report = json.loads(result.stdout)
    assert report["status"] == "refused" and report["code"]


def test_demo_entry_point(toolchain, directory, journal):
    result = journal.attempt([sys.executable, ROOT / "tests/run.py", "demo"], env={
        **os.environ,
        "ZKC_COMPILER_BIN": str(toolchain.directories["compiler"]),
        "ZKC_NATIVE_BIN": str(toolchain.directories["native"]),
        "ZKC_LEAN_BIN": str(toolchain.directories["lean"]),
        "ZKC_REPORTS_DIR": str(directory / "reports"),
    })
    assert result.returncode == 0, result.stdout + result.stderr
    assert "Proof accepted: 1514 bytes." in result.stdout


@pytest.mark.parametrize("source,code", [
    ('module { bundle Bad(F) = (Field("koala-bear")); }', "source-bundle-term"),
    ("module { bundle Bad(F) = (Field(G)); }", "source-name-unresolved"),
])
def test_documented_data_refusals(source, code, toolchain, journal):
    journal.run([toolchain.compiler, "protocol-source", "-"], stdin=source, refuses=code)


def test_published_walkthrough_and_invalid_proofs(toolchain, directory, journal):
    document = (ROOT / "docs/getting-started.md").read_text()
    match = re.search(r"<!-- executable: committed-proof -->\s*```sh\n(.*?)\n```", document, re.S)
    assert match, "the maintained executable walkthrough is missing"
    # Exercise Cargo's documented target-directory fallback, including spaces.
    cargo_target = directory / "cargo target"
    cargo_target.mkdir()
    (cargo_target / "release").symlink_to(toolchain.directories["native"], target_is_directory=True)
    env = dict(os.environ, TMPDIR=str(directory), CARGO_TARGET_DIR=str(cargo_target),
               ZKC_COMPILER_BIN=str(toolchain.directories["compiler"]),
               ZKC_LEAN_BIN=str(toolchain.directories["lean"]))
    env.pop("ZKC_NATIVE_BIN", None)
    result = run_process(["bash", "-euo", "pipefail", "-c", match[1]], cwd=ROOT,
                            env=env, capture_output=True, text=True, timeout=120)
    (directory / "walkthrough.stdout").write_text(result.stdout)
    (directory / "walkthrough.stderr").write_text(result.stderr)
    assert result.returncode == 0, result.stdout + result.stderr
    output = Path(result.stdout.rsplit("Demo files: ", 1)[1].strip())
    assert output.parent == directory
    producer = json.loads((output / "producer.json").read_text())
    validator = json.loads((output / "validator.json").read_text())
    assert producer["status"] == "produced" and validator["status"] == "accepted"
    proof = (output / "proof.bin").read_bytes()
    assert len(proof) == producer["proof_bytes"] == validator["proof_bytes"] == 1514
    assert json.loads((output / "inputs/committed-two-factor.validator.json").read_text())[3] == []

    def validate(candidate, inputs):
        result = journal.attempt([toolchain.runtime, "validate-artifact",
                                  output / "source.json", output / "descriptor.json",
                                  output / "construction.json", output / "participants.json",
                                  inputs, toolchain.compiler, toolchain.checker("interactive-protocol"),
                                  candidate, "10000", "--trace=none"])
        assert result.returncode == 1, result.stdout
        report = json.loads(result.stdout)
        assert report["status"] == "refused"
        return report

    truncated = output / "truncated.bin"
    truncated.write_bytes(proof[:-1])
    report = validate(truncated, output / "inputs/committed-two-factor.validator.json")
    assert report["code"] == "proof-truncated"
    # Keep encodings valid but change the application's selected commitment.
    inputs = json.loads((output / "inputs/committed-two-factor.validator.json").read_text())
    inputs[2][1][2], inputs[2][2][2] = inputs[2][2][2], inputs[2][1][2]
    wrong_statement = output / "wrong-statement.json"
    wrong_statement.write_text(json.dumps(inputs))
    report = validate(output / "proof.bin", wrong_statement)
    assert report["code"] == "proof-header"
