"""Independent primitive oracle for the maintained public-table Sumcheck fixture.

This consumes a real SDK-produced proof; it never produces a proof. Descriptor
origins supply checked names, while this module independently instantiates loop
coordinates, reconstructs the root, decodes proof frames, evaluates round/terminal
checks and runs the existing independent Python Keccak chain.
"""

import argparse
import hashlib
import json
from pathlib import Path

from oracle import chain_trace  # Also locates the independent support modules.
from hash_chain_reference import BLS12_381_R as PRIME, BLS_SUITE, Chain, fr64be
from logical_tree import decode_tree, encode_tree


def scalar(data):
    if len(data) != 38 or data[:6] != b"ZKCV\x00\x01":
        raise ValueError("scalar-frame")
    value = int.from_bytes(data[6:], "little")
    if value >= PRIME:
        raise ValueError("scalar-residue")
    return value


def scalar_wire(value):
    return b"ZKCV\x00\x01" + (value % PRIME).to_bytes(32, "little")


def public_values(fixture):
    values, claim, rounds = map(bytes.fromhex, fixture["public"])
    if values[:6] != b"ZKCV\x00\x42" or len(values) < 10:
        raise ValueError("public-vector")
    count = int.from_bytes(values[6:10], "little")
    if len(values) != 10 + 32 * count:
        raise ValueError("public-vector-length")
    table = [scalar(b"ZKCV\x00\x01" + values[i:i + 32])
             for i in range(10, len(values), 32)]
    if len(rounds) != 14 or rounds[:6] != b"ZKCV\x00\x1f":
        raise ValueError("public-index")
    return table, scalar(claim), int.from_bytes(rounds[6:], "little")


def invocation_root(fixture):
    descriptor = fixture["descriptor"]
    if len(descriptor) != 9 or descriptor[0] != "zkc.native-proof-descriptor/0":
        raise ValueError("descriptor-profile")
    policy = descriptor[1]
    if policy[5] != BLS_SUITE or descriptor[2] != "zkc.native-origin/0":
        raise ValueError("construction-profile")
    ports = descriptor[4]
    expected_ports = [("0", "vector:bls12-381.fr"), ("1", "field:bls12-381.fr"),
                      ("2", "index")]
    if [(port[1], port[2]) for port in ports] != expected_ports:
        raise ValueError("public-port-profile")
    if any(port[0] != policy[3] for port in ports):
        raise ValueError("public-port-role")
    rows = [[port[0], port[1], port[2], wire]
            for port, wire in zip(ports, fixture["public"], strict=True)]
    tree = ["zkc.native-proof-binding/0", "sha256", descriptor[2], fixture["source"],
            policy[1], policy[2], policy[3], descriptor, rows, fixture["context"]]
    root = encode_tree(tree)
    if fixture.get("invocation_tree", tree) != tree or fixture.get("public_rows", rows) != rows:
        raise ValueError("fixture-root-tree")
    if fixture.get("invocation_root", root.hex()) != root.hex():
        raise ValueError("fixture-root-bytes")
    if fixture.get("binding_sha256", hashlib.sha256(root).hexdigest()) != hashlib.sha256(root).hexdigest():
        raise ValueError("fixture-root-digest")
    return root


def origins(descriptor):
    templates = []
    for kind, encoded in descriptor[3]:
        template = decode_tree(bytes.fromhex(encoded))
        if len(template) != 5 or template[0] != "zkc.native-origin-template/0":
            raise ValueError("origin-template")
        if template[1] != descriptor[1][1] or template[4][0] != kind:
            raise ValueError("origin-template-entry")
        templates.append(template)
    # The maintained Reduce sends its pair as two scalar messages, draws once,
    # and delivers that challenge. Reject other programs rather than guessing.
    if len(templates) != 4 or [t[4][0] for t in templates] != ["message", "message", "query", "message"]:
        raise ValueError("sumcheck-occurrences")
    if any(t[2] != templates[0][2] or t[3] != [] for t in templates):
        raise ValueError("sumcheck-occurrence-path")
    if len(templates[0][2]) != 2 or [p[0] for p in templates[0][2]] != ["apply", "repeat"]:
        raise ValueError("sumcheck-repeat-path")
    producer, validator = descriptor[1][2:4]
    for template in templates[:2]:
        if template[4][4:] != [producer, validator]:
            raise ValueError("sumcheck-round-direction")
    if templates[2][4][4:] != ["random.bls12-381.fr/0", "draw", validator]:
        raise ValueError("sumcheck-query")
    if templates[3][4][4:] != [validator, producer]:
        raise ValueError("sumcheck-delivery")

    def occurrence(index, round_number):
        template = templates[index]
        return encode_tree(["zkc.native-origin/0", template[1], template[2],
                            [str(round_number)], template[4]])

    return occurrence


class Stop(Exception):
    pass


def reconstruct(fixture):
    """Return complete expected primitives or the precise executed stop prefix.

    SHA-256 covers the invocation-root precompile; all following events are
    construction Keccak calls, including final challenge delivery observations.
    No backend bytecode, rendered Yul, static opcode count or runner trace is an
    input to this reconstruction.
    """
    if fixture.get("format") != "zkc.evm-native-fixture/0":
        raise ValueError("native-fixture-format")
    root = invocation_root(fixture)
    table, current, rounds = public_values(fixture)
    occurrence = origins(fixture["descriptor"])
    proof = bytes.fromhex(fixture["proof"])
    root_digest = hashlib.sha256(root).digest()
    if proof[:8] != b"ZKCPRF00" or proof[8:40] != root_digest:
        raise ValueError("proof-header")
    chain = Chain(BLS_SUITE, root)
    position, transitions = 40, 0
    budget = fixture["transcript_budget"]
    point = []
    stop = None
    decision = None

    def debit():
        nonlocal transitions
        if transitions >= budget:
            raise Stop("transcript-budget")
        transitions += 1

    def observe(origin, wire):
        debit()
        chain.absorb(b"origin", origin)
        chain.absorb(b"value", wire)

    def message(index, round_number):
        nonlocal position
        if position + 8 > len(proof):
            raise Stop("proof-frame-length")
        length = int.from_bytes(proof[position:position + 8], "little")
        position += 8
        if length != 38 or position + length > len(proof):
            raise Stop("proof-frame")
        wire = proof[position:position + length]
        position += length
        try:
            value = scalar(wire)
        except ValueError as error:
            raise Stop(str(error)) from error
        observe(occurrence(index, round_number), wire)
        return value

    try:
        if rounds > 10:
            raise Stop("loop-count-bound")
        for round_number in range(rounds):
            left = message(0, round_number)
            right = message(1, round_number)
            if current != (left + right) % PRIME:
                raise Stop("source-require")
            debit()
            chain.absorb(b"origin", occurrence(2, round_number))
            challenge = fr64be(chain.request(b"challenge", 64))
            observe(occurrence(3, round_number), scalar_wire(challenge))
            point.append(challenge)
            current = (left + challenge * (right - left)) % PRIME
        # The terminal obligation is over the original public table. No later
        # proof frame can replace it, including in the zero-round case.
        if len(table) != 1 << rounds:
            decision = False
        else:
            for challenge in point:
                half = len(table) // 2
                table = [(left + challenge * (right - left)) % PRIME
                         for left, right in zip(table[:half], table[half:], strict=True)]
            decision = table[0] == current
        if position != len(proof):
            raise Stop("proof-trailing")
    except Stop as error:
        stop = str(error)
        decision = None
    trace = [{"kind": "sha256", "input": root.hex(), "output": root_digest.hex(), "status": "return"}]
    trace += chain_trace(chain)
    return {"format": "zkc.evm-expected-execution/0", "trace": trace,
            "decision": decision, "stop": stop, "transitions": transitions,
            "proof_position": position, "point": [str(r) for r in point],
            "final_state": chain.state.hex()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    fixture = json.loads(args.fixture.read_text())
    result = reconstruct(fixture)
    if result["decision"] != fixture["decision"]:
        raise AssertionError(f"native/reference decision disagreement: {result['decision']} != {fixture['decision']}")
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"decision": result["decision"], "stop": result["stop"],
                      "primitives": len(result["trace"]), "transitions": result["transitions"]}))


if __name__ == "__main__":
    main()
