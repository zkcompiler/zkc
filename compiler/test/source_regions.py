#!/usr/bin/env python3
"""Compact region verification, capture remapping, and profile separation."""

import json
from source import envelope

from cases import case
from commands import Commands
from lowering import exported, imported, lowered, planned, refused
from tools import records

FIELD = ["scalar", "f7"]
FIELD_IR = '!algebra.field<"f7">'


commands = Commands(records())


directory = commands.directory
context = [
    "trace",
    [[n, FIELD, ["shared"], "argument"] for n in ("x", "y")],
    FIELD,
    [["table-protocol", "1"]],
]
body = [
    "bind",
    FIELD,
    ["apply", ["add", "f7"], [0, 1], ["return", 0]],
    ["return", 0],
]
source = directory / "source.json"
source.write_text(
    json.dumps(envelope(context, body, "region-source-1"))
)
text = imported(commands, source)
plan_ir = lowered(commands, text, directory)
assert '"table.plan.bind"' in plan_ir
assert exported(commands, plan_ir, directory)[9] == body
for label, invalid, code in [
    (
        "unsupported-profile",
        text.replace(
            'sourceFormat = "region-source-1"', 'sourceFormat = "unknown"'
        ),
        "unsupported-source-format",
    ),
    (
        "old-profile",
        text.replace(', sourceFormat = "region-source-1"', ""),
        "unsupported-source-format",
    ),
    (
        "stale-flow",
        text.replace('"table.source.return"(%after, %value)', '"table.source.return"(%arg0, %value)'),
        "invalid-return",
    ),
    (
        # MLIR's own type consistency rejects this at the operation whose
        # result type no longer matches, before any pass of ours runs, so what
        # is named is our operation rather than a diagnostic of ours.
        "wrong-result",
        text.replace('-> (!table.flow, !algebra.field<"f7">)', "-> (!table.flow, i1)"),
        "table.source.return",
    ),
    (
        "extra-attribute",
        text.replace("}) :", "}) {extra = true} :", 1),
        "unsupported-attribute",
    ),
    (
        # The dialect declares the region isolated, and that is the constraint
        # the verifier names when a body reaches a value defined outside it.
        "implicit-capture",
        text.replace('"table.field_add"(%arg4, %arg5)', '"table.field_add"(%arg1, %arg5)'),
        "region isolation",
    ),
]:
    with case(label):
        assert invalid != text, label
        assert code in refused(commands, invalid, directory, label), (label, code)

# A region may select, reorder or alias captures. It has no implicit initial value.
ctx = json.dumps(context, separators=(",", ":")).replace('"', "\\22")
for captures, returned, index in [
    (["%y", "%x"], 0, 1),
    (["%x", "%x"], 1, 0),
    (["%y"], 0, 1),
]:
    with case(f"captures {captures}, returning operand {returned}"):
        params = ", ".join(f"%c{i}: {FIELD_IR}" for i in range(len(captures)))
        types = ", ".join(["!table.flow"] + [FIELD_IR] * len(captures))
        mapping = f'''
  "table.source.program"() <{{context = "{ctx}", resultType = {FIELD_IR}, sourceFormat = "region-source-1"}}> ({{
  ^bb0(%flow: !table.flow, %x: {FIELD_IR}, %y: {FIELD_IR}):
    %after, %value = "table.source.bind"(%flow, {", ".join(captures)}) ({{
    ^bb0(%f: !table.flow, {params}):
      "table.source.return"(%f, %c{returned}) : (!table.flow, {FIELD_IR}) -> ()
    }}) : ({types}) -> (!table.flow, {FIELD_IR})
    "table.source.return"(%after, %value) : (!table.flow, {FIELD_IR}) -> ()
  }}) : () -> ()
'''
        assert planned(commands, mapping, directory)[9] == [
            "bind",
            FIELD,
            ["return", index],
            ["return", 0],
        ]

print(f"compact regions: {commands.save()} checks; roundtrip, six malformed "
      "controls, three capture mappings")
