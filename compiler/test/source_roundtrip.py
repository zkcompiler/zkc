#!/usr/bin/env python3
"""Tool-level checks: actual structured lowering and malformed-child rejection."""

import json
from source import envelope

from commands import Commands
from lowering import imported, planned, refused
from tools import records

commands = Commands(records())
directory = commands.directory
context = [
    "trace",
    [["x", ["scalar", "f7"], ["shared"], "argument"]],
    ["scalar", "f7"],
    [["table-protocol", "1"]],
]
body = ["apply", ["add", "f7"], [0, 0], ["return", 0]]
source = directory / "source.json"
source.write_text(
    json.dumps(envelope(context, body))
)
text = imported(commands, source)
assert planned(commands, text, directory)[9] == body

# A child of the applied operation, broken one way at a time. Each is refused
# by the verifier rather than carried into a plan.
for label, invalid in {
    "bad-child-type": text.replace('"f7"', '"unknown"', 1),
    "unknown-child": text.replace('"algebra.add"', '"algebra.unknown"'),
    "extra-control-attribute": text.replace(
        '"pir.return"(%arg0, %0)', '"pir.return"(%arg0, %0) {extra = true}'
    ),
    "child-wrong-arity": text.replace(
        '"algebra.add"(%arg1, %arg1)', '"algebra.add"(%arg1)'
    ).replace(
        '(!algebra.field<"f7">, !algebra.field<"f7">)', '(!algebra.field<"f7">)'
    ),
}.items():
    assert invalid != text, label
    refused(commands, invalid, directory, label)
print(f"source roundtrip: {commands.save()} checks, including four malformed-IR controls")
