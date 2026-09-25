#!/usr/bin/env python3
"""SSA rewrites must preserve explicit capture meaning, not capture spelling."""

import json
from source import envelope
from cases import case
from commands import Commands
from lowering import imported, planned
from tools import records

FIELD = ["scalar", "f7"]
FIELD_IR = '!algebra.field<"f7">'


commands = Commands(records())


def context(inputs):
    return [
        "trace",
        [[name, ty, ["shared"], "argument"] for name, ty in inputs],
        FIELD,
        [["table-protocol", "1"]],
    ]


directory = commands.directory
source = directory / "source.json"


def export(text, pipeline="lower-pir-to-plan"):
    """The body of the plan those passes produce from this MLIR."""
    return planned(commands, text, directory, pipeline)[9]

# Actual CSE changes values captured by a branch, loop, and nested branch.
for tail, expected_tail in [
    (
        ["if", 3, ["return", 0], ["return", 1]],
        ["if", 2, ["return", 0], ["return", 0]],
    ),
    (
        [
            "repeat",
            2,
            FIELD,
            0,
            ["apply", ["add", "f7"], [0, 2], ["return", 0]],
            ["return", 0],
        ],
        [
            "repeat",
            2,
            FIELD,
            0,
            ["apply", ["add", "f7"], [0, 1], ["return", 0]],
            ["return", 0],
        ],
    ),
    (
        [
            "repeat",
            2,
            FIELD,
            0,
            ["if", 4, ["return", 1], ["return", 2]],
            ["return", 0],
        ],
        [
            "repeat",
            2,
            FIELD,
            0,
            ["if", 3, ["return", 1], ["return", 1]],
            ["return", 0],
        ],
    ),
]:
    body = ["apply", ["add", "f7"], [0, 0], ["apply", ["add", "f7"], [1, 1], tail]]
    source.write_text(
        json.dumps(envelope(context([("x", FIELD), ("flag", ["bool"])]), body))
    )
    text = imported(commands, source)
    assert export(text) == body
    assert export(text, "cse,lower-pir-to-plan") == [
        "apply",
        ["add", "f7"],
        [0, 0],
        expected_tail,
    ]

# A carrier may select/reorder/alias captures. Explicit operands bind each
# block argument, while exported source references retain the outer context.
ctx = json.dumps(
    context([("x", FIELD), ("y", FIELD), ("flag", ["bool"])]), separators=(",", ":")
)
ctx_attr = '"' + ctx.replace('"', "\\22") + '"'
for captures, yes, no, expected in [
    (["%y", "%x"], 1, 0, ["if", 2, ["return", 0], ["return", 1]]),
    (["%x", "%x"], 0, 1, ["if", 2, ["return", 0], ["return", 0]]),
    (["%x"], 0, 0, ["if", 2, ["return", 0], ["return", 0]]),
    (["%y"], 0, 0, ["if", 2, ["return", 1], ["return", 1]]),
]:
    with case(f"captures {captures} on a choice"):
        arguments = ", ".join(f"%c{i}: {FIELD_IR}" for i in range(len(captures)))
        types = ", ".join(["!pir.flow", "i1"] + [FIELD_IR] * len(captures))
        text = f"""module {{
  "pir.program"() <{{context = {ctx_attr}, resultType = {FIELD_IR}}}> ({{
  ^bb0(%flow: !pir.flow, %x: {FIELD_IR}, %y: {FIELD_IR}, %flag: i1):
    "pir.choose"(%flow, %flag, {", ".join(captures)}) ({{
    ^bb0(%f: !pir.flow, {arguments}):
      "pir.return"(%f, %c{yes}) : (!pir.flow, {FIELD_IR}) -> ()
    }}, {{
    ^bb0(%f: !pir.flow, {arguments}):
      "pir.return"(%f, %c{no}) : (!pir.flow, {FIELD_IR}) -> ()
    }}) : ({types}) -> ()
  }}) : () -> ()
}}"""
        assert export(text) == expected

print(f"source captures: {commands.save()} checks; three CSE scope cases and four explicit capture mappings")
