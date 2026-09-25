#!/usr/bin/env python3
"""Closed library selection, independent types, and actual operation identity."""

import copy
import json
from source import envelope
from pathlib import Path

from commands import Commands
from tools import compiler, records, service_compiler, service_optimizer
from journal import names


commands = Commands(records())


call = commands.attempted


temporary = records()
root = Path(temporary)
source, ir = root / "source.json", root / "source.mlir"
context = [
    "client",
    [["n", ["count"], ["shared"], "argument"]],
    ["predicate"],
    [["vector-service", "1"]],
]
body = ["apply", ["send"], [0], ["if", 0, ["return", 0], ["stop", "reject"]]]
request = envelope(context, body)
source.write_text(json.dumps(request))
imported = call(service_compiler, "import", source)
assert imported.returncode == 0, imported.stderr
assert "!service.predicate" in imported.stdout
assert '"service.send"' in imported.stdout
ir.write_text(imported.stdout)
lowered = call(
    service_optimizer, ir, "--pass-pipeline=builtin.module(cse,lower-pir-to-plan)"
)
assert lowered.returncode == 0, lowered.stderr
ir.write_text(lowered.stdout)
exported = call(service_compiler, "export", ir)
assert exported.returncode == 0, exported.stderr
assert json.loads(exported.stdout)[9] == body
for tool_args, code in [
    ((compiler, "import", source), "unresolved-dependency"),
    ((service_compiler, "--ambiguous-family", "import", source), "ambiguous-library"),
    ((service_compiler, "--ambiguous-family", "export", ir), "ambiguous-library"),
]:
    result = call(*tool_args)
    assert result.returncode == 1 and names(result.stderr, code), result
for deps, code in [
    ([], "unresolved-dependency"),
    ([["vector-service", "2"]], "unresolved-dependency"),
    ([["vector-service", "1"], ["vector-service", "1"]], "invalid-dependency"),
    ([["", "1"]], "invalid-dependency"),
    ([["vector-service", ""]], "invalid-dependency"),
    ([["vector-service"]], "invalid-dependency"),
    ([["vector-service", "1"], ["unknown", "1"]], "unresolved-dependency"),
]:
    invalid = copy.deepcopy(request)
    invalid[3][3] = deps
    source.write_text(json.dumps(invalid))
    result = call(service_compiler, "import", source)
    assert result.returncode == 1 and names(result.stderr, code), (deps, result)
for text, code in [
    (
        imported.stdout.replace('"service.send"', '"service.foreign_send"'),
        "operation-family-mismatch",
    ),
    (
        imported.stdout.replace(
            '"service.send"(%arg0, %arg1)',
            '"service.send"(%arg0, %arg1) {extra = true}',
        ),
        "unsupported-attribute",
    ),
]:
    assert text != imported.stdout
    ir.write_text(text)
    result = call(service_optimizer, ir)
    assert result.returncode == 1 and names(result.stderr, code), result
# AnyType in the control op does not permit using a count as a condition.
invalid = copy.deepcopy(request)
invalid[5][3][1] = 1
source.write_text(json.dumps(invalid))
result = call(service_compiler, "import", source)
assert result.returncode == 1 and names(result.stderr, "invalid-operand"), result

# Large declaration contexts must not be parsed afresh for every operation.
# The shared timeout bounds the regression without asserting a machine-specific
# speedup or replacing the recorded scaling measurement.
def branch(depth, offset):
    if depth:
        child = branch(depth - 1, offset + 1)
        return ["apply", ["send"], [offset], ["if", 0, child, child]]
    result = ["return", 0]
    for index in reversed(range(150)):
        result = ["apply", ["send"], [offset + index], result]
    return result

large = copy.deepcopy(request)
large[3][1] = [[f"i{i}", ["count"], ["shared"], "argument"] for i in range(3000)]
large[5] = branch(4, 0)
source.write_text(json.dumps(large))
result = call(service_compiler, "compile", source)
assert result.returncode == 0, result.stderr
assert json.loads(result.stdout)[9] == large[5]
print(f"source libraries: {commands.save()} checks; independent library, 13 refusal controls, large-context compilation")
