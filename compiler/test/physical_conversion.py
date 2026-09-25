#!/usr/bin/env python3
"""Physical type conversion, actual export, compact control and malformed IR."""

import copy
import json
from source import envelope
from commands import Commands
from tools import compiler, optimizer, records
from journal import names



commands = Commands(records())


call = commands.attempted


directory = records()
source, ir, target = (
    directory / name for name in ("source.json", "source.mlir", "target.mlir")
)
field = ["scalar", "f7"]
context = [
    "trace",
    [
        ["v", ["residual", "f7", 1], ["shared"], "argument"],
        ["p", ["point", "f7"], ["shared"], "argument"],
        ["flag", ["bool"], ["shared"], "capture"],
    ],
    field,
    [["table-protocol", "1"]],
]
evaluate = ["apply", ["evaluate", "f7", 1], [0, 1], ["return", 0]]
body = [
    "bind",
    field,
    ["if", 2, evaluate, evaluate],
    [
        "repeat",
        4,
        field,
        0,
        ["apply", ["add", "f7"], [0, 1], ["return", 0]],
        ["return", 0],
    ],
]
request = envelope(context, body, "region-source-1")
source.write_text(json.dumps(request))
imported = call(compiler, "import", str(source))
assert imported.returncode == 0, imported.stderr
ir.write_text(imported.stdout)
for mode in ("lazy", "materialized"):
    lowered = call(
        optimizer,
        str(ir),
        "--pass-pipeline=builtin.module(lower-pir-to-plan,lower-plan-to-physical{mode="
        + mode
        + "})",
    )
    assert lowered.returncode == 0, lowered.stderr
    text = lowered.stdout
    for expected in (
        '!plan.scalar<"f7">',
        '"plan.prepare"',
        '"plan.invoke"',
        '"plan.bind"',
        '"plan.repeat"',
        '"plan.choose"',
    ):
        assert expected in text, (expected, text)
    for excluded in (
        "!algebra.field",
        '"poly.evaluate"',
        "unrealized_conversion_cast",
    ):
        assert excluded not in text, (excluded, text)
    target.write_text(text)
    exported = call(compiler, "export", str(target))
    compiled = call(compiler, "compile", str(source), "--physical=" + mode)
    assert exported.returncode == compiled.returncode == 0, (
        exported.stderr,
        compiled.stderr,
    )
    assert json.loads(exported.stdout) == json.loads(compiled.stdout)
    plan = json.loads(exported.stdout)
    assert plan[:3] == ["zkc-table-physical-plan", 1, context]
    assert plan[3][0] == "bind" and plan[3][3][0] == "repeat"
    # Rewrite the actual physical IR, rather than changing a producer flag.
    mixed = text.replace(
        'mode = "' + mode + '"',
        'mode = "' + ("materialized" if mode == "lazy" else "lazy") + '"',
        1,
    )
    assert mixed != text
    target.write_text(mixed)
    changed = call(compiler, "export", str(target))
    assert changed.returncode == 0 and json.loads(changed.stdout) != plan
    for label, invalid, code in [
        (
            "mode",
            text.replace('mode = "' + mode + '"', 'mode = "unknown"'),
            "unsupported-preparation-mode",
        ),
        (
            "domain",
            text.replace('!plan.scalar<"f7">', '!plan.scalar<"f2">'),
            "invalid-program-region",
        ),
        (
            "realization",
            text.replace(
                'realization = "table-physical-plan"', 'realization = "unknown"'
            ),
            "missing-physical-context",
        ),
        (
            # What the operation definition says it accepts, which is where
            # the reason for this refusal is written.
            "logical-type",
            text.replace('!plan.scalar<"f7">', '!algebra.field<"f7">'),
            "immutable prepared scalar reference",
        ),
        (
            "extra-attribute",
            text.replace(
                'mode = "' + mode + '"}>', 'mode = "' + mode + '"}> {extra = true}'
            ),
            "invalid-physical-operation",
        ),
        (
            "unknown-descriptor",
            text.replace("add", "unknown_kernel"),
            "unknown-operation",
        ),
    ]:
        assert invalid != text, label
        target.write_text(invalid)
        refused = call(compiler, "export", str(target))
        assert refused.returncode > 0 and "Stack dump" not in refused.stderr, (
            label,
            refused.stderr,
        )
        assert names(refused.stderr, code), (label, code, refused.stderr)
    # A huge static loop remains one loop; conversion cannot enumerate it.
    huge = copy.deepcopy(request)
    huge[5][3][1] = 10**80
    source.write_text(json.dumps(huge))
    large = call(compiler, "compile", str(source), "--physical=" + mode)
    assert large.returncode == 0, large.stderr
    assert json.loads(large.stdout)[3][3][1] == 10**80
    assert len(large.stdout) < 2000
    source.write_text(json.dumps(request))
for mode in ("", "unknown"):
    refused = call(compiler, "compile", str(source), "--physical=" + mode)
    assert (
        refused.returncode == 1 and names(refused.stderr, "unsupported-preparation-mode")
    )
print(f"physical conversion: {commands.save()} checks; type conversion, actual "
      "export, compact control and refusals")
