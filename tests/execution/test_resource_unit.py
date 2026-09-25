"""Closed zero-payload ports: independent C++/MLIR/Rust/Lean and execution."""
import json
from pathlib import Path
import subprocess

import pytest
from journal import names

SOURCE = Path(__file__).resolve().parents[2] / "tests/fixtures/resource-unit.json"


def invoke(command, payload=None):
    return subprocess.run([str(x) for x in command], input=payload, text=True,
                          capture_output=True, timeout=60)


def good(command, payload=None):
    result = invoke(command, payload)
    assert result.returncode == 0, (command, result.stdout, result.stderr)
    return result.stdout


def write(directory, name, value):
    path = directory / name
    path.write_text(json.dumps(value))
    return path


def test_resource_unit_execution(toolchain, directory):
    source = json.loads(SOURCE.read_text())
    checker = toolchain.checker("interactive-protocol")
    source_path = write(directory, "source.json", source)
    physical = json.loads(good([toolchain.compiler, "protocol-compile", source_path]))
    candidate = write(directory, "physical.json", physical)
    logical = json.loads(good([toolchain.compiler, "protocol-project", source_path]))
    good([checker, "--check", source_path, write(directory, "logical.json", logical)])
    good([checker, "--check", source_path, candidate])
    for command in ("protocol-import", "protocol-physical-ir"):
        ir = good([toolchain.compiler, command, source_path])
        optimized = good([toolchain.optimizer, "--verify-each", "--canonicalize", "--cse"], ir)
        assert "resource_unit" in optimized
        assert "consume" in optimized  # no-result operation must remain
        exported = json.loads(good([toolchain.compiler, "protocol-export", "-"], optimized))
        if command == "protocol-physical-ir":
            good([checker, "--check", source_path, write(directory, "roundtrip.json", exported)])
    reference_inputs = write(directory, "reference-inputs.json",
                             ["zkc.reference-inputs/1", "main", "session", [["P", []]], [], [], []])
    native_inputs = write(directory, "native-inputs.json",
                          ["zkc.run/2", "main", "session", [], [["P", [], [], []]], []])
    reference = json.loads(good([checker, "--reference", source_path, reference_inputs]))
    assert reference[3] == ["returned", []]
    assert [e[1][2] for e in reference[4] if e[0] == "request"] == [
        "resource_unit.create", "resource_unit.pass", "resource_unit.consume"]
    assert reference[5] == []  # consumed permission removed
    native = json.loads(good([toolchain.runtime, "run-protocol", source_path, candidate, native_inputs, checker]))
    assert native["outcome"] == ["returned", {"P": []}]
    assert native["wire"]["messages"] == native["wire"]["payload_bytes"] == 0
    assert native["usage"]["P"]["instructions"] == 8
    # Explicit storage release retains the same unit-return calls and effect order.
    released = json.loads(good([toolchain.compiler, "protocol-compile", source_path, "--release-storage"]))
    native = json.loads(good([toolchain.runtime, "run-protocol", source_path,
        write(directory, "released.json", released), native_inputs, checker]))
    assert native["outcome"] == ["returned", {"P": []}]


@pytest.mark.parametrize("ending", ["returned", "stopped"])
def test_unconsumed_unit_is_retired_when_the_protocol_ends(toolchain, directory, ending):
    """The participant's own frame disposes of units as a local frame does.

    A unit made by a local function and handed back to the protocol body is
    never consumed. When the protocol returns without it, or stops, both
    implementations must end with no unit live. Later failure after another
    participant returns is covered separately by test_participant_lifecycle.py
    and crates/zkc-tools/tests/participant_frames.rs.
    """
    source = json.loads(SOURCE.read_text())
    body = [["local", "make", "P", "Make", [], ["x"]], ["return", []]]
    if ending == "stopped":
        source[1] += [["constant", "field.constant", ["bls12-381.fr"], ""],
                      ["equal", "field.equal", ["bls12-381.fr"], ""],
                      ["require", "control.require", [], ""]]
        source[2].append(["function", "Refuse", [], [], [
            ["op", "zero", "constant", ["0"], [], ["zero"]],
            ["op", "one", "constant", ["1"], [], ["one"]],
            ["op", "equal", "equal", [], ["zero", "one"], ["ok"]],
            ["op", "guard", "require", [], ["ok"], []],
            ["return", []]], ["Refuse", []]])
        body.insert(1, ["local", "refuse", "P", "Refuse", [], []])
    source[3][0][7] = body
    path = write(directory, "source.json", source)
    candidate = write(directory, "physical.json",
                      json.loads(good([toolchain.compiler, "protocol-compile", path])))
    checker = toolchain.checker("interactive-protocol")
    reference = json.loads(good([checker, "--reference", path, write(
        directory, "reference-inputs.json",
        ["zkc.reference-inputs/1", "main", "session", [["P", []]], [], [], []])]))
    native = json.loads(good([toolchain.runtime, "run-protocol", path, candidate, write(
        directory, "native-inputs.json",
        ["zkc.run/2", "main", "session", [], [["P", [], [], []]], []]), checker]))
    if ending == "returned":
        assert reference[3] == ["returned", []], reference
        assert native["outcome"] == ["returned", {"P": []}], native
    else:
        assert reference[3][0] == "reject", reference
        assert native["outcome"][0] == "stopped", native
    assert [r for r in reference[5] if r[-1] == "resource_unit"] == [], reference[5]
    assert native["usage"]["P"]["live_resource_units"] == 0, native["usage"]


@pytest.mark.parametrize("mutation,cpp_code,lean_code", [
    ("reuse", "interactive-resource-reuse", "interactive-resource-reuse"),
    ("duplicate-result", "interactive-resource-reuse", "interactive-resource-reuse"),
    ("domain", "binding-operation-signature", "binding-operation-signature"),
    ("slot", "binding-resource-unit-domain", "binding-resource-unit-domain"),
    ("implementation", "binding-implementation", "binding-implementation"),
    ("attributes", "interactive-kernel-parameters", "interactive-kernel-parameters"),
])
def test_resource_unit_independent_refusals(toolchain, directory, mutation, cpp_code, lean_code):
    source = json.loads(SOURCE.read_text())
    if mutation == "reuse":
        source[2][1][4].insert(1, ["op", "again", "consume", [], ["x"], []])
    elif mutation == "duplicate-result":
        source[2][0][3] *= 2
        source[2][0][4][-1] = ["return", ["x", "x"]]
    elif mutation == "domain":
        source[1][1][2] = ["Slot.B"]
    elif mutation == "slot":
        source[1][0][2] = ["0invalid"]
    elif mutation == "implementation":
        source[1][0][3] = "arkworks/resource_unit.create"
    elif mutation == "attributes":
        source[2][0][4][0][3] = ["payload"]
    path = write(directory, "malformed-source.json", source)
    compiler = invoke([toolchain.compiler, "protocol-compile", path])
    assert compiler.returncode > 0 and names(compiler.stderr, cpp_code), compiler.stderr
    lean = invoke([toolchain.checker("interactive-protocol"), "--admit", path])
    assert lean.returncode > 0 and names(lean.stdout, lean_code), lean.stdout


def test_resource_unit_unit_return_guard_survives(toolchain, directory):
    source = json.loads(SOURCE.read_text())
    source[1] += [["constant", "field.constant", ["bls12-381.fr"], ""],
                  ["equal", "field.equal", ["bls12-381.fr"], ""],
                  ["require", "control.require", [], ""]]
    source[2][1][4][-1:-1] = [
        ["op", "zero", "constant", ["0"], [], ["zero"]],
        ["op", "one", "constant", ["1"], [], ["one"]],
        ["op", "equal", "equal", [], ["zero", "one"], ["ok"]],
        ["op", "guard", "require", [], ["ok"], []]]
    path = write(directory, "guard-source.json", source)
    candidate = write(directory, "guard-physical.json", json.loads(good([
        toolchain.compiler, "protocol-compile", path, "--release-storage"])))
    checker = toolchain.checker("interactive-protocol")
    ref_inputs = write(directory, "ref.json", ["zkc.reference-inputs/1", "main", "session", [["P", []]], [], [], []])
    ref = json.loads(good([checker, "--reference", path, ref_inputs]))
    assert ref[3][0] == "reject", ref
    assert [e[1][2] for e in ref[4] if e[0] == "request"][-1] == "control.require"
    inputs = write(directory, "native.json", ["zkc.run/2", "main", "session", [], [["P", [], [], []]], []])
    result = invoke([toolchain.runtime, "run-protocol", path, candidate, inputs, checker])
    native = json.loads(result.stdout)
    assert native["outcome"][0] == "stopped", native
    assert "reject" in json.dumps(native["stop"])


@pytest.mark.parametrize("stage", ["logical", "physical"])
def test_resource_unit_candidate_duplication(toolchain, directory, stage):
    candidate = json.loads(good([toolchain.compiler,
        "protocol-compile" if stage == "physical" else "protocol-project", SOURCE]))
    body = candidate[3][1][4]
    # Copy the pass input after its first consuming use. The source stays valid.
    body.insert(1, ["op", "forged", "consume", [], body[0][4], []])
    path = write(directory, "forged.json", candidate)
    lean = invoke([toolchain.checker("interactive-protocol"), "--check", SOURCE, path])
    expected = "interactive-resource-reuse" if stage == "physical" else "source-local-unmatched"
    assert lean.returncode > 0 and names(lean.stdout, expected), lean.stdout
    cpp = invoke([toolchain.compiler, "protocol-import", path])
    assert cpp.returncode > 0 and names(cpp.stderr, "interactive-resource-reuse"), cpp.stderr


def test_resource_unit_returned_permission_has_no_wire(toolchain, directory):
    source = json.loads(SOURCE.read_text())
    source[3][0][5] = [["P", "resource_unit:Slot.A"]]
    source[3][0][7] = [["local", "make", "P", "Make", [], ["x"]], ["return", ["x"]]]
    path = write(directory, "returned-source.json", source)
    candidate = write(directory, "returned-physical.json", json.loads(good([
        toolchain.compiler, "protocol-compile", path])))
    inputs = write(directory, "native.json", ["zkc.run/2", "main", "session", [], [["P", [], [], []]], []])
    native = json.loads(good([toolchain.runtime, "run-protocol", path, candidate, inputs,
                             toolchain.checker("interactive-protocol")]))
    assert native["outcome"] == ["returned", {"P": [["private", "resource_unit:Slot.A"]]}]
    assert native["wire"]["payload_bytes"] == 0


@pytest.mark.parametrize("exit_kind", ["drop", "pass-and-drop", "create-and-drop", "stop"])
def test_resource_unit_implicit_frame_disposal(toolchain, directory, exit_kind):
    source = json.loads(SOURCE.read_text())
    body = []
    if exit_kind in ("pass-and-drop", "stop"):
        body.append(["op", "pass", "pass", [], ["x"], ["y"]])
    if exit_kind == "create-and-drop":
        body.append(["op", "extra", "create", [], [], ["extra"]])
    if exit_kind == "stop":
        source[1] += [
            ["constant", "field.constant", ["bls12-381.fr"], ""],
            ["equal", "field.equal", ["bls12-381.fr"], ""],
            ["require", "control.require", [], ""],
        ]
        body += [
            ["op", "zero", "constant", ["0"], [], ["zero"]],
            ["op", "one", "constant", ["1"], [], ["one"]],
            ["op", "equal", "equal", [], ["zero", "one"], ["ok"]],
            ["op", "guard", "require", [], ["ok"], []],
        ]
    body.append(["return", []])
    source[2][1][4] = body
    path = write(directory, "source.json", source)
    candidate = write(directory, "physical.json", json.loads(good([
        toolchain.compiler, "protocol-compile", path])))
    checker = toolchain.checker("interactive-protocol")
    reference_inputs = write(directory, "reference.json",
                            ["zkc.reference-inputs/1", "main", "session", [["P", []]], [], [], []])
    native_inputs = write(directory, "native.json",
                         ["zkc.run/2", "main", "session", [], [["P", [], [], []]], []])
    reference = json.loads(good([checker, "--reference", path, reference_inputs]))
    native = json.loads(good([toolchain.runtime, "run-protocol", path, candidate,
                             native_inputs, checker]))
    assert reference[3][0] == ("reject" if exit_kind == "stop" else "returned")
    assert native["outcome"][0] == ("stopped" if exit_kind == "stop" else "returned")
    # No explicit consume is present. Frame disposal must discard inputs and
    # newly created, unreturned permissions on successful and stopped exits.
    assert reference[5] == []
    assert native["resources"] == []
