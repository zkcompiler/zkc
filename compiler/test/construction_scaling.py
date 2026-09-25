#!/usr/bin/env python3
"""Compact dependency storage preserves source demand and bounded refusal.

All sources and candidates are newly generated beside the run's other
evidence; no evaluation receipts or compiler oracle are imported.
"""

import copy
import json
from commands import Commands
from tools import compiler, records
from journal import names


def fixture(length, role="P", private=False):
    body = []
    previous = "x"
    for i in range(length):
        name = f"v{i}"
        operand = "salt" if private and i == length - 1 else "x"
        body.append(["op", f"add{i}", "field.add", [], [previous, operand], [name]])
        previous = name
    fn = [
        "function",
        "Chain",
        [["x", "field:bls12-381.fr"], ["salt", "field:bls12-381.fr"]],
        ["field:bls12-381.fr"],
        body + [["return", [previous]]],
        ["Chain", []],
    ]
    accept = [
        "function",
        "Accept",
        [],
        ["bool"],
        [
            ["op", "zero", "field.constant", ["0"], [], ["z"]],
            ["op", "eq", "field.equal", [], ["z", "z"], ["ok"]],
            ["return", ["ok"]],
        ],
    ]
    accept.append(["Accept", []])
    receiver = "V" if role == "P" else "P"
    protocol = [
        "protocol",
        "Subject",
        ["P", "V"],
        [],
        [["public", role, "field:bls12-381.fr"], ["private", role, "field:bls12-381.fr"], ["coins", "V", "rng:bls12-381.fr"]],
        [["V", "bool"]],
        [],
        [
            ["local", "chain", role, "Chain", ["public", "private"], ["last"]],
            ["message", "last", "field", role, receiver, "last", "received"],
            ["local", "accept", "V", "Accept", [], ["accepted"]],
            ["return", ["accepted"]],
        ],
    ]
    source = [
        "zkc.protocol/1",
        [[op, op, ["bls12-381.fr"], ""] for op in
         ("field.add", "field.constant", "field.equal")],
        [fn, accept],
        [protocol],
        [["instance", "subject", "Subject", [], [], [["P", "P"], ["V", "V"]]]],
        [["entry", "main", "subject"]],
    ]
    descriptor = [
        "zkc.construction/1",
        "main",
        "P",
        "V",
        [["public", [[role, "public"]]]],
        ["coins", []],
        "0",
        "merlin3.bls12-381.fr64be/1",
        "exact",
    ]
    return source, descriptor


def main():
    work = records()
    commands = Commands(work)

    def run(source, descriptor, error=None, candidate=None):
        src, desc = work / "source.json", work / "descriptor.json"
        src.write_text(json.dumps(source, separators=(",", ":")))
        desc.write_text(json.dumps(descriptor))
        command = [compiler, "protocol-construct", str(src), str(desc)]
        if candidate is not None:
            path = work / "candidate.json"
            path.write_text(json.dumps(candidate, separators=(",", ":")))
            command[1] = "protocol-check-construction"
            command.append(str(path))
        result = commands.attempt(command)
        assert result.returncode == (1 if error else 0), (
            result.returncode,
            result.stderr,
        )
        if error:
            assert names(result.stderr, error), result.stderr
            return None
        if candidate is not None:
            assert result.stdout.strip() == "construction-checked"
            return None
        return json.loads(result.stdout)

    # This retained 1600-operation chain formerly exhausted string-set work.
    # The producer call is preserved: all operations and their order survive.
    source, descriptor = fixture(1600)
    result = run(source, descriptor)
    bodies = [fn[2:5] for fn in result[2][2] if fn[1] != "Chain"]
    assert source[2][0][2:5] in bodies
    rows = [row for row in result[4] if row[4] == "Chain"]
    assert [row[5] for row in rows] == [f"add{i}" for i in range(1600)]
    run(source, descriptor, candidate=result)
    changed = copy.deepcopy(result)
    changed[4][-1][5] = "wrong_source_site"
    run(source, descriptor, "construction-candidate-mismatch", changed)

    # Final-position private dependencies must still reach the root through
    # the entire chain, including when both operands duplicate a prefix.
    source, descriptor = fixture(1600, role="V", private=True)
    run(source, descriptor, "construction-private-demand:private")
    # Same chain without the dependency has a different, output-size refusal.
    # This is the only place the output ceiling is reached: protocol
    # construction built the same 1600-operation chain for the same refusal.
    source, descriptor = fixture(1600, role="V")
    run(source, descriptor, "construction-output:source-limit:module")

    # Bitmaps still have bounded copy/traversal costs, not unlimited work.
    source, descriptor = fixture(6000)
    run(source, descriptor, "construction-analysis-limit")
    # Demand through joins/copies on both sides of bitmap word boundaries.
    for length in [1, 63, 64, 65, 127, 128, 129]:
        source, descriptor = fixture(length, role="V")
        run(source, descriptor)
        source, descriptor = fixture(length, role="V", private=True)
        run(source, descriptor, "construction-private-demand:private")
    print(f"construction scaling: {commands.save()} checks passed")


if __name__ == "__main__":
    main()
