"""Preserve scheduled guards across projection, checking and execution."""

import json
from pathlib import Path

import pytest

from journal import Journal


@pytest.fixture
def guard_subject():
    source = json.loads((Path(__file__).resolve().parents[1] /
                         "fixtures/mathematical/pure-region.json").read_text())
    protocol = source[3][0]
    protocol[4].append(["accept", "Bob", "bool"])
    # Bob's rejection must precede Alice's first computation and message.
    protocol[7].insert(0, ["guard", "accept", "Bob", "accept"])
    return source


@pytest.mark.parametrize("accepted", [False, True])
def test_native_guard_precedes_peer_suffix(toolchain, directory, guard_subject, accepted):
    journal = Journal(directory)
    source = journal.write("source.json", guard_subject)
    candidate = json.loads(journal.run([toolchain.compiler, "protocol-compile", source]))
    bob = next(p for p in candidate[4] if p[3] == "Bob")
    assert bob[7][0][0:2] == ["guard", "accept"]
    candidate_path = journal.write("candidate.json", candidate)
    inputs = journal.write("inputs.json", [
        "zkc.run/2", "main", "session", [],
        [["Alice", [], [["x", ["field", "3"]]], []],
         ["Bob", [], [["challenge", ["nonzero_field", "5"]],
                      ["accept", ["bool", accepted]]], []]], []
    ])
    result = json.loads(journal.run([
        toolchain.runtime, "run-protocol", source, candidate_path, inputs,
        toolchain.checker("interactive-protocol"),
    ]))
    if accepted:
        assert result["outcome"] == ["returned", {"Alice": [], "Bob": [["field", "30"]]}]
        assert result["wire"]["messages"] == 1
    else:
        assert result["outcome"] == ["stopped", "Bob", "accept", 'Explicit("reject")']
        assert result["wire"]["messages"] == 0


@pytest.mark.parametrize("accepted", [False, True])
def test_reference_guard_precedes_peer_suffix(toolchain, directory, guard_subject, accepted):
    journal = Journal(directory)
    source = journal.write("source.json", guard_subject)
    inputs = journal.write("inputs.json", [
        "zkc.reference-inputs/1", "main", "session",
        [["Alice", [["x", ["field:bls12-381.fr", "3"]]]],
         ["Bob", [["challenge", ["nonzero_field:bls12-381.fr", "5"]],
                  ["accept", ["bool", "true" if accepted else "false"]]]]], [], [], []
    ])
    result = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--generic-reference", source, inputs
    ]))
    if accepted:
        assert result[3] == ["returned", [["field:bls12-381.fr", "30"]]]
    else:
        assert result[3][:2] == ["reject", "source-guard"]
        assert result[3][2][-3:-1] == ["accept", "Bob"]
        assert result[4] == []


def test_open_role_does_not_learn_foreign_guard(toolchain, directory, guard_subject):
    journal = Journal(directory)
    source = journal.write("source.json", guard_subject)
    # Alice has neither Bob's accept condition nor his challenge.
    inputs = journal.write("inputs.json", [
        "zkc.reference-inputs/1", "main", "session",
        [["Alice", [["x", ["field:bls12-381.fr", "3"]]]]], [], [], []
    ])
    result = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--generic-role", source, inputs, "Alice"
    ]))
    assert result[3] == ["returned", []]
    assert any(event[0] == "send" for event in result[4])


@pytest.mark.parametrize("mutation", ["condition", "deleted", "after_receive"])
def test_checker_rejects_changed_guard(toolchain, directory, guard_subject, mutation):
    journal = Journal(directory)
    source = journal.write("source.json", guard_subject)
    candidate = json.loads(journal.run([toolchain.compiler, "protocol-compile", source]))
    bob = next(p for p in candidate[4] if p[3] == "Bob")
    if mutation == "condition":
        bob[7][0][2] = bob[5][0][0]
    elif mutation == "deleted":
        bob[7].pop(0)
    else:
        bob[7].insert(1, bob[7].pop(0))
    candidate_path = journal.write("candidate.json", candidate)
    result = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--check", source, candidate_path
    ], refuses=True))
    assert result[0] == "refused"
