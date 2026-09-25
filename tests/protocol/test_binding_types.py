"""Leaf binding types are admitted alike by the compiler and Lean.

Agreement on the sort of an identity is not enough: a table over a field no
backend tabulates is a well-sorted pair that no implementation executes. Each
installed kind is paired with each installed identity, as an ordinary port and
as a local variant payload, and the two independent readers must accept and
refuse the same pairs.
"""
import json
import re

import pytest
from journal import Journal

KINDS = ["field", "matrix", "vector", "polynomial", "round", "rng", "nonce", "table", "point",
         "group", "groups", "commitments", "opening_states", "commitment", "proof",
         "opening_state", "prover_key", "verifier_key", "transcript"]
IDENTITIES = ["bn254.fr", "bn254.g1", "bn254.g2", "koala-bear", "koala-bear.ext8-binomial3",
              "bls12-381.fr", "bls12-381.g1", "multilinear.kzg.bls12-381/1",
              "rows.merkle-keccak256.koala-bear/1",
              "rows.merkle-keccak256.koala-bear.ext8-binomial3/1", "ristretto255.scalar",
              "ristretto255.group", "merlin3.ristretto255.scalar64le/1",
              "merlin3.koala-bear.ext8-binomial3.rejection31le/1", "merlin3.bls12-381.fr64be/1",
              "spongefish0.7.4.keccak.bls12-381.fr64be/1"]


def variant(payload):
    """A two-arm local variant whose first arm carries the leaf."""
    nodes, index = [], {}

    def intern(value):
        node = value if isinstance(value, str) else [str(intern(item)) for item in value]
        key = json.dumps(node, separators=(",", ":"))
        if key not in index:
            index[key] = len(nodes)
            nodes.append(node)
        return index[key]

    intern(["tests/leaf", [["A", [payload]], ["B", []]]])
    graph = ["zkc.variant/1", nodes]
    return "variant:" + json.dumps(graph, separators=(",", ":")).encode().hex()


def source(spelling):
    return ["zkc.protocol/1", [],
            [["function", "Inspect", [["v", spelling]], [], [["return", []]], ["Inspect", []]]],
            [["protocol", "Main", ["P"], [], [], [], [], [["return", []]]]],
            [["instance", "concrete", "Main", [], [], [["P", "P"]]]],
            [["entry", "main", "concrete"]]]


@pytest.mark.parametrize("position", ["port", "payload"])
def test_installed_kind_identity_pairs_agree(toolchain, directory, position):
    journal = Journal(directory)
    accepted = {kind: 0 for kind in KINDS}
    refused = {kind: 0 for kind in KINDS}
    for kind in KINDS:
        for number, identity in enumerate(IDENTITIES):
            leaf = f"{kind}:{identity}"
            path = journal.write(f"{kind}-{number}.json",
                                 source(leaf if position == "port" else variant(leaf)))
            native = journal.attempt([toolchain.compiler, "protocol-admit", path])
            reference = json.loads(journal.attempt(
                [toolchain.checker("interactive-protocol"), "--admit", path]).stdout)
            codes = re.findall(r": error: ([a-z0-9-]+):", native.stderr)
            assert (native.returncode == 0) == (reference[0] == "checked"), (leaf, codes, reference)
            if native.returncode == 0:
                accepted[kind] += 1
            else:
                refused[kind] += 1
                assert codes[:1] == ["binding-type"], (leaf, native.stderr)
                assert reference == ["refused", "binding-type"], (leaf, reference)
    # Every installed kind has some identity both readers admit and some they
    # refuse, so the grid can pass neither by refusing nor by admitting all.
    assert all(accepted.values()), accepted
    assert all(refused.values()), refused
    journal.save()
