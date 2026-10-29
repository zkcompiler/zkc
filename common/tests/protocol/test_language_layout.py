"""Layout source executes through the ordinary compiler and Rust Host."""

import hashlib
import json
from pathlib import Path

import pytest

from entry import joint_package
from input_files import invocation_file

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / "compiler/test/fixtures/layout/schnorr.zkc"
PUBLIC = ROOT / "examples/projects/schnorr/inputs/example.Proof/public.json"


def compile_layout(toolchain, journal, directory, text=None, flags=()):
    source = directory / "schnorr.zkc"
    source.write_text(SOURCE.read_text() if text is None else text)
    package = directory / "schnorr.zkpkg"
    encoded = journal.run([
        toolchain.compiler, "language-package", "--source-format=zkc-layout",
        "--entry=schnorr::Run", f"--module=schnorr={source}", *flags,
    ])
    package.write_text(encoded)
    return package, hashlib.sha256(package.read_bytes()).hexdigest()


def run_layout(toolchain, journal, directory, package, pin, scalar="3", flags=(), refuses=None):
    public = json.loads(PUBLIC.read_text())
    inputs = directory / "inputs.json"
    inputs.write_text(json.dumps({"inputs": {
        "P": {**public, "scalar": scalar}, "V": public,
    }}))
    outputs = directory / "outputs.json"
    report = journal.json([
        toolchain.runtime, "--json", "run", f"--package={package}",
        f"--sha256={pin}", f"--input={inputs}", f"--results={outputs}", *flags,
    ], refuses=refuses)
    return report, None if refuses else json.loads(outputs.read_text())["value"]


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_spec_free_schnorr_executes_without_lean(toolchain, journal, directory, flags):
    package, pin = compile_layout(toolchain, journal, directory, flags=flags)
    child = joint_package(json.loads(package.read_text()))
    assert child["original"].count('"protocol.query"') == 2
    assert child["original"].count('"protocol.exchange"') == 3
    report, values = run_layout(toolchain, journal, directory, package, pin)
    assert report["status"] == "executed"
    assert values == {"P": {}, "V": {"result": True}}
    report, values = run_layout(toolchain, journal, directory, package, pin, scalar="4")
    assert report["status"] == "executed"
    assert values["V"]["result"] is False


def test_unused_random_action_survives_compilation(toolchain, journal, directory):
    package, pin = compile_layout(toolchain, journal, directory)
    before = joint_package(json.loads(package.read_text()))
    binding = invocation_file(journal, "before.invocations.json", package,
                              role_services={"P": {"nonces": 1}})
    run_layout(toolchain, journal, directory, package, pin, flags=(binding,))
    changed = SOURCE.read_text().replace(
        "    nonce <- nonces.draw()",
        "    discarded <- nonces.draw()\n    nonce <- nonces.draw()",
    )
    package, pin = compile_layout(toolchain, journal, directory, changed)
    after = joint_package(json.loads(package.read_text()))
    assert before["original"] != after["original"]
    assert after["original"].count('"protocol.query"') == 3
    binding = invocation_file(journal, "after.invocations.json", package,
                              role_services={"P": {"nonces": 1}})
    run_layout(toolchain, journal, directory, package, pin, flags=(binding,),
               refuses="entry-host-run-failed")


def test_guard_is_a_reached_refusal(toolchain, journal, directory):
    changed = SOURCE.read_text().replace("    return accepted", "    guard @V accepted\n    return accepted")
    package, pin = compile_layout(toolchain, journal, directory, changed)
    child = joint_package(json.loads(package.read_text()))
    assert child["original"].count('"protocol.guard"') == 1
    run_layout(toolchain, journal, directory, package, pin)
    run_layout(toolchain, journal, directory, package, pin, scalar="4",
               refuses="entry-host-run-failed")


def test_native_execution_retains_unavailable_formal_requests(toolchain, journal, directory):
    changed = SOURCE.read_text() + """
spec for Schnorr:
    target statement: DiscreteLog(base, point, scalar)
    security: ProofOfKnowledge(target.statement)
"""
    package, pin = compile_layout(toolchain, journal, directory, changed)
    run_layout(toolchain, journal, directory, package, pin)
    source = directory / "schnorr.zkc"
    command = [toolchain.compiler, "language-check", "--source-format=zkc-layout",
               f"--module=schnorr={source}"]
    checked = journal.json(command + ["--source-ast"])
    assert checked["status"] == "checked"
    assert checked["assurance"]["status"] == "unavailable"
    spec, = checked["assurance"]["specifications"]
    assert spec["protocol"] == "schnorr::Schnorr"
    assert spec["owner"] is True
    assert spec["name"] is None
    nodes = [node for owner in checked["source_ast"]["declarations"] for node in owner["nodes"]]
    assert any(node["kind"] == "formal_syntax" for node in nodes)
    journal.run(command + ["--subject=schnorr::Schnorr<schnorr::Curve>", "--source-claims"],
                refuses="source.assurance-unavailable")


def test_unused_communication_is_observable(toolchain, journal, directory):
    changed = SOURCE.read_text().replace(
        "    #[site(commitment)]",
        "    extra <- send base from P to V\n    #[site(commitment)]",
    )
    package, pin = compile_layout(toolchain, journal, directory, changed)
    child = joint_package(json.loads(package.read_text()))
    assert child["original"].count('"protocol.exchange"') == 4
    run_layout(toolchain, journal, directory, package, pin)
