"""Compare actual inline and outlined bodies with the independent Lean checker."""

import copy
import json
from pathlib import Path

import pytest

from journal import Journal


@pytest.fixture
def pure_subject():
    path = Path(__file__).resolve().parents[1] / "fixtures/mathematical/pure-region.json"
    return json.loads(path.read_text())


def check(toolchain, directory, source, candidate, error=None):
    source_path, candidate_path = directory / "source.json", directory / "candidate.json"
    source_path.write_text(json.dumps(source))
    candidate_path.write_text(json.dumps(candidate))
    journal = Journal(directory)
    return json.loads(journal.run(
        [toolchain.checker("interactive-protocol"), "--check", source_path, candidate_path],
        refuses=error,
    ))


def compile_source(toolchain, directory, source, mode="protocol-compile"):
    return json.loads(Journal(directory).run([toolchain.compiler, mode, "-"], json.dumps(source)))


@pytest.mark.parametrize("mode", ["protocol-project", "protocol-compile"])
def test_actual_pure_correspondence(toolchain, directory, pure_subject, mode):
    candidate = compile_source(toolchain, directory, pure_subject, mode)
    assert check(toolchain, directory, pure_subject, candidate)[:2] == [
        "checked", "generic-structural-correspondence"
    ]


@pytest.mark.parametrize("mutation", ["operator", "operand", "result", "origin", "call", "extra"])
def test_outlined_body_tampering(toolchain, directory, pure_subject, mutation):
    candidate = compile_source(toolchain, directory, pure_subject)
    first = candidate[3][0]
    if mutation == "operator":
        add = first[4][0][2]
        next(binding for binding in candidate[1] if binding[0] == add)[1] = "field.mul"
    elif mutation == "operand":
        second = candidate[3][1]
        # Both operands have the right field type; the fresh receive must still
        # participate in the verifier computation.
        second[4][1][4][0] = second[4][1][4][1]
    elif mutation == "result":
        first[4][-1][1] = [first[2][0][0]]
    elif mutation == "origin":
        first[5][0] = "unrelated"
    elif mutation == "call":
        bob = next(p for p in candidate[4] if p[3] == "Bob")
        bob[7][1][2] = first[1]
    else:
        extra = copy.deepcopy(first)
        extra[1] = "unrelated"
        extra[5][0] = "unrelated"
        candidate[3].append(extra)
    response = check(toolchain, directory, pure_subject, candidate, True)
    assert response[0] == "refused"


@pytest.mark.parametrize("mutation", ["owner", "capture", "ordered", "partial", "hidden_call"])
def test_independent_pure_admission(toolchain, directory, pure_subject, mutation):
    candidate = compile_source(toolchain, directory, pure_subject, "protocol-project")
    region = pure_subject[3][0][7][0]
    if mutation == "owner":
        region[2] = "Bob"
    elif mutation == "capture":
        region[3] = []
    elif mutation == "ordered":
        region[4][0] = ["op", "constant_value", "constant", ["1"], [], ["twice"]]
    elif mutation == "partial":
        pure_subject[1].append(["inverse", "field.inverse", ["bls12-381.fr"], ""])
        region[4][0] = ["op", "inverse_value", "inverse", [], ["x"], ["twice"]]
    else:
        region[4][0] = ["local", "hidden", "Alice", "unknown", ["x"], ["twice"]]
    assert check(toolchain, directory, pure_subject, candidate, True)[0] == "refused"


@pytest.mark.parametrize("received", [None, "9", "0"])
def test_pure_reference_uses_actual_reply(toolchain, directory, pure_subject, received):
    source_path, input_path = directory / "source.json", directory / "inputs.json"
    source_path.write_text(json.dumps(pure_subject))
    field, nonzero = "field:bls12-381.fr", "nonzero_field:bls12-381.fr"
    supplied = [["Bob", [["challenge", [nonzero, "5"]]]]]
    replies = []
    command = [toolchain.checker("interactive-protocol"), "--generic-reference", source_path, input_path]
    if received is None:
        supplied.insert(0, ["Alice", [["x", [field, "3"]]]])
        expected = "30"
    else:
        command[1] = "--generic-role"
        command.append("Bob")
        location = ["source-origin/2", "session", "main", "arithmetic", [], "transfer", "Bob", []]
        replies = [[["receive", location, "scalar", "Alice", field], [field, received]]]
        expected = str(int(received) * 5)
    input_path.write_text(json.dumps([
        "zkc.reference-inputs/1", "main", "session", supplied, [], [], replies
    ]))
    response = json.loads(Journal(directory).run(command))
    assert response[3] == ["returned", [[field, expected]]]


def test_reference_rejects_zero_challenge(toolchain, directory, pure_subject):
    source_path, input_path = directory / "source.json", directory / "inputs.json"
    source_path.write_text(json.dumps(pure_subject))
    input_path.write_text(json.dumps([
        "zkc.reference-inputs/1", "main", "session",
        [["Bob", [["challenge", ["nonzero_field:bls12-381.fr", "0"]]]]], [], [], []
    ]))
    response = json.loads(Journal(directory).run([
        toolchain.checker("interactive-protocol"), "--generic-role", source_path, input_path, "Bob"
    ], refuses="nonzero-field-zero"))
    assert response == ["refused", "nonzero-field-zero"]


@pytest.mark.parametrize("long_site", [False, True])
def test_native_pure_execution(toolchain, directory, pure_subject, long_site):
    if long_site:
        # The introduced helper origin is exactly 128 bytes, so its internal
        # correspondence key (including '@') needs the full 129-byte bound.
        pure_subject[3][0][7][0][1] = "s" * 98
    candidate = compile_source(toolchain, directory, pure_subject)
    journal = Journal(directory)
    source_path = journal.write("source.json", pure_subject)
    candidate_path = journal.write("candidate.json", candidate)
    inputs = journal.write("native-inputs.json", [
        "zkc.run/2", "main", "session", [],
        [["Alice", [], [["x", ["field", "3"]]], []],
         ["Bob", [], [["challenge", ["nonzero_field", "5"]]], []]], []
    ])
    result = json.loads(journal.run([
        toolchain.runtime, "run-protocol", source_path, candidate_path, inputs,
        toolchain.checker("interactive-protocol"),
    ]))
    assert result["outcome"] == ["returned", {"Alice": [], "Bob": [["field", "30"]]}]
    assert result["wire"]["messages"] == 1
