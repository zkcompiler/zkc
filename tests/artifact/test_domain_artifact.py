#!/usr/bin/env python3
"""Exercise Ristretto artifact challenges using the selected real primitive service.

The service remains trusted. This checks routing and scalar interpretation, not
Merlin security, point arithmetic or a complete application proof.
"""

import hashlib
import json
from pathlib import Path

import pytest

from journal import Journal
from toolchain import Toolchain, records

# The Lean reference that interprets the artifact.
REFERENCE = "artifact-reference"

# Both identity policies the reference accepts. The policy is what the
# descriptor declares, so it is a case of this test rather than a switch that
# leaves one of the two never run.
IDENTITY_POLICIES = ("exact", "normalized")


def main(policy):
    tools = Toolchain()
    journal = Journal(records(case=policy))
    output = journal.directory
    artifact, primitive = tools.checker(REFERENCE), tools.primitive
    pins = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in (artifact, primitive)}
    field = "ristretto255.scalar"
    suite = "merlin3.ristretto255.scalar64le/1"

    source = ["zkc.protocol/1", [["draw", "random.draw", [field], ""], ["eq", "field.equal", [field], ""]],
              [["function", "Draw", [["rng", "rng:" + field]], ["bool", "rng:" + field],
                [["op", "draw", "draw", [], ["rng"], ["x", "next"]],
                 ["op", "compare", "eq", [], ["x", "x"], ["yes"]], ["return", ["yes", "next"]]], ["Draw", []]]],
              [["protocol", "Main", ["P", "V"], [], [["rng", "V", "rng:" + field]], [["V", "bool"]], [],
                [["local", "step", "V", "Draw", ["rng"], ["yes", "next"]], ["return", ["yes"]]]]],
              [["instance", "root", "Main", [], [], [["P", "P"], ["V", "V"]]]], [["entry", "main", "root"]]]
    descriptor = ["zkc.construction/1", "main", "P", "V", [],
                  ["rng", [["Draw", "draw"]]], "0", suite, policy]
    inputs = ["zkc.artifact-inputs/1", "", [], [], ["zkc.public-configuration/1", [], [], []]]
    paths = [journal.write("source.json", source), journal.write("descriptor.json", descriptor), journal.write("inputs.json", inputs)]
    proof = output / "proof.bin"
    proof.write_bytes(b"")
    replies = ["zkc.primitive-replies/1", []]

    def invoke(name):
        """Ask the reference to interpret the artifact as it stands."""
        response = journal.attempt([artifact, "reference", *paths, proof,
                                    journal.write("replies.json", replies)])
        assert response.returncode == 0 and not response.stderr, (response.stdout, response.stderr)
        observed = json.loads(response.stdout)
        journal.write(name, observed)
        return observed

    def answer(request):
        response = journal.attempt([primitive, journal.write("request.json", request)])
        assert response.returncode == 0 and not response.stderr, (response.stdout, response.stderr)
        value = json.loads(response.stdout)
        replies[1].append([request, value])
        return value

    observed = invoke("pending-hash")
    assert observed[1][:2] == ["pending-primitive", "exact-request-missing"]
    request = observed[1][2]
    assert request[:2] == ["zkc.hash/1", "sha256"]
    digest = answer(request)
    assert digest == hashlib.sha256(bytes.fromhex(request[2])).hexdigest()
    proof.write_bytes(b"ZKCPRF01" + bytes.fromhex(digest))
    observed = invoke("pending-challenge")
    assert observed[1][:2] == ["pending-primitive", "exact-request-missing"]
    request = observed[1][2]
    assert request[:3] == ["zkc.transcript-request/3", suite, b"zkc.artifact/1".hex()]
    assert request[3][-1] == ["challenge", b"challenge".hex(), "64"]
    response = answer(request)
    assert response[0] == "ok" and len(bytes.fromhex(response[1])) == 64
    observed = invoke("accepted")
    assert observed[1] == ["accepted", [["bool", "5a4b4356010501"]]]
    assert observed[3] == [pair[0] for pair in replies[1]], "unexpected/legacy primitive request"
    challenges = [event for event in observed[2] if event[0] == "challenge"]
    modulus = 2**252 + 27742317777372353535851937790883648493
    scalar = int.from_bytes(bytes.fromhex(response[1]), "little") % modulus
    wire = (b"ZKCV" + bytes([1, 13]) + scalar.to_bytes(32, "little")).hex()
    assert len(challenges) == 1 and challenges[0][2] == ["field:" + field, wire]
    assert observed[5:7] == ["1", "1"]
    assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == digest for p, digest in pins.items()), "binary changed during smoke test"
    report = {"status": "pass", "requests": 2, "challenge_suite": suite,
              "identity_policy": policy,
              "binaries": pins,
              "scope": "one original-source Ristretto draw with real SHA256/Merlin service; service is trusted; no application/security proof"}
    journal.write("results.json", report)
    print(json.dumps(report))



@pytest.mark.parametrize("policy", IDENTITY_POLICIES)
def test_domain_artifact(policy):
    main(policy)

if __name__ == "__main__":
    for chosen in IDENTITY_POLICIES:
        main(chosen)
