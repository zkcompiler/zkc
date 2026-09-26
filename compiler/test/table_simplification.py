#!/usr/bin/env python3
"""Exact logical rewrites, retained control/failures, and opt-in CLI refusal."""

from collections import Counter
import json
from source import envelope
import re
from commands import Commands
from tools import compiler, optimizer, records, service_compiler, service_optimizer
from journal import names

FIELD = ["scalar", "f7"]
CONTEXT = [
    "trace",
    [
        [name, ty, ["shared"], "argument"]
        for name, ty in [
            ("a", FIELD),
            ("r", FIELD),
            ("b", FIELD),
            ("flag", ["bool"]),
            ("view", ["residual", "f7", 1]),
            ("point", ["point", "f7"]),
            ("table", ["table", "f7", 1]),
        ]
    ],
    FIELD,
    [["table-protocol", "1"]],
]


commands = Commands(records())


call = commands.attempted


def ok(*args):
    result = call(*args)
    assert result.returncode == 0, (args, result.stderr)
    return result.stdout


def refused(code, *args):
    result = call(*args)
    assert result.returncode > 0 and names(result.stderr, code), (args, result)
    assert not result.stdout and "Stack dump" not in result.stderr, result


def ret(index):
    return ["return", index]


def apply(descriptor, operands, tail):
    return ["apply", descriptor, operands, tail]


def linear(operands, tail):
    return apply(["linear"], operands, tail)


def operations(text):
    return Counter(re.findall(r'"([a-z]+\.[a-z_]+)"\(', text))


# Expected source-index trees are explicit, not computed by a second copy of
# the simplification algorithm. All are checked on PIR and Plan inputs.
cases = [
    ("simple", linear([0, 0, 1], ret(0)), ret(0)),
    ("unused-linear", linear([0, 0, 1], ret(2)), ret(1)),
    (
        "alias-chain",
        linear([0, 0, 1], linear([0, 1, 2], linear([0, 1, 2], ret(0)))),
        ret(0),
    ),
    (
        "if-arms",
        ["if", 3, linear([0, 0, 1], ret(0)), linear([2, 2, 1], ret(0))],
        ["if", 3, ret(0), ret(2)],
    ),
    (
        "nested-capture-aliases",
        linear(
            [0, 0, 1],
            [
                "if",
                4,
                ["if", 4, linear([0, 1, 2], ret(0)), linear([1, 0, 2], ret(0))],
                linear([0, 1, 2], ret(0)),
            ],
        ),
        ["if", 3, ["if", 3, ret(0), ret(0)], ret(0)],
    ),
    (
        "loop-captures-and-accumulator",
        linear(
            [0, 0, 1],
            [
                "repeat",
                4,
                FIELD,
                0,
                linear(
                    [1, 2, 3],
                    linear([1, 1, 4], apply(["add", "f7"], [0, 1], ret(0))),
                ),
                linear([0, 0, 3], ret(0)),
            ],
        ),
        ["repeat", 4, FIELD, 0, apply(["add", "f7"], [0, 1], ret(0)), ret(0)],
    ),
    (
        "loop-accumulator-is-not-initial-capture",
        ["repeat", 4, FIELD, 0, linear([0, 1, 2], ret(0)), ret(0)],
        ["repeat", 4, FIELD, 0, linear([0, 1, 2], ret(0)), ret(0)],
    ),
    (
        "bind-shared-suffix",
        linear(
            [0, 0, 1],
            [
                "bind",
                FIELD,
                ["if", 4, linear([0, 1, 2], ret(0)), linear([1, 0, 2], ret(0))],
                linear([0, 0, 3], apply(["record", "f7"], [0], ret(1))),
            ],
        ),
        [
            "bind",
            FIELD,
            ["if", 3, ret(0), ret(0)],
            apply(["record", "f7"], [0], ret(1)),
        ],
    ),
    (
        "dead-query-point-is-still-evaluated",
        apply(["evaluate", "f7", 1], [4, 5], linear([1, 1, 0], ret(0))),
        apply(["evaluate", "f7", 1], [4, 5], ret(1)),
    ),
    (
        "dead-guards-failed-call-and-pure-operations",
        apply(
            ["view", "f7", 1],
            [6],
            apply(
                ["restrict", "f7", 1],
                [0, 2],
                apply(
                    ["evaluate", "f7", 1],
                    [0, 7],
                    apply(
                        ["add", "f7"],
                        [3, 4],
                        linear(
                            [4, 4, 5],
                            apply(
                                ["abort_write", "f7"],
                                [0],
                                ["if", 9, ret(1), ["stop", "reject"]],
                            ),
                        ),
                    ),
                ),
            ),
        ),
        apply(
            ["view", "f7", 1],
            [6],
            apply(
                ["restrict", "f7", 1],
                [0, 2],
                apply(
                    ["evaluate", "f7", 1],
                    [0, 7],
                    apply(
                        ["add", "f7"],
                        [3, 4],
                        apply(
                            ["abort_write", "f7"],
                            [4],
                            ["if", 8, ret(5), ["stop", "reject"]],
                        ),
                    ),
                ),
            ),
        ),
    ),
]
for count in (0, 10**80):
    cases.append(
        (
            f"retained-loop-{count}",
            ["repeat", count, FIELD, 0, linear([0, 0, 2], ret(0)), ret(1)],
            ["repeat", count, FIELD, 0, ret(0), ret(1)],
        )
    )
for endpoints in ([0, 2, 1], [0, 1, 0], [0, 1, 1]):
    body = linear(endpoints, ret(0))
    cases.append((f"distinct-endpoints-{endpoints}", body, body))
body = apply(
    ["add", "f7"],
    [0, 0],
    apply(["add", "f7"], [1, 1], linear([0, 1, 3], ret(0))),
)
cases.append(("same-computation-distinct-ssa", body, body))


directory = records()
source, ir, target = (
    directory / name for name in ("source.json", "in.mlir", "out.mlir")
)

def optimize(text, pipeline):
    ir.write_text(text)
    return ok(optimizer, ir, f"--pass-pipeline=builtin.module({pipeline})")

def export(text):
    target.write_text(text)
    return json.loads(ok(compiler, "export", target))

for label, body, expected in cases:
    request = envelope(CONTEXT, body, "region-source-1")
    original = json.dumps(request)
    source.write_text(original)
    imported = ok(compiler, "import", source)
    direct_ir = optimize(imported, "lower-pir-to-plan")
    direct = export(direct_ir)
    assert direct[9] == body, label
    assert json.loads(ok(compiler, "compile", source)) == direct, label
    for logical_ir, suffix in ((imported, ",lower-pir-to-plan"), (direct_ir, "")):
        simplified = optimize(logical_ir, "simplify-table-regions")
        before, after = operations(logical_ir), operations(simplified)
        assert after["poly.linear"] <= before["poly.linear"], label
        if expected != body:
            assert after["poly.linear"] < before["poly.linear"], label
        del before["poly.linear"], after["poly.linear"]
        assert before == after, (label, before, after)
        # Region argument lists, captures, and all block/control shapes stay
        # in place. Only SSA operand names and linear definitions may change.
        assert re.findall(r"\^bb\d+\([^\n]*", logical_ir) == re.findall(
            r"\^bb\d+\([^\n]*", simplified
        ), label
        assert optimize(simplified, "simplify-table-regions") == simplified, label
        lowered = optimize(logical_ir, "simplify-table-regions" + suffix)
        candidate = export(lowered)
        assert candidate[:9] == direct[:9], label
        assert candidate[9] == expected, (label, candidate[9], expected)
    for mode in ("lazy", "materialized"):
        physical_pass = f"lower-plan-to-physical{{mode={mode}}}"
        physical_ir = optimize(lowered, physical_pass)
        physical = export(physical_ir)
        assert physical[:3] == ["zkc-table-physical-plan", 1, CONTEXT], label
        for flags in (
            ("--simplify", f"--physical={mode}"),
            (f"--physical={mode}", "--simplify"),
        ):
            assert (
                json.loads(ok(compiler, "compile", source, *flags)) == physical
            ), label
        old_physical = export(optimize(direct_ir, physical_pass))
        assert (
            json.loads(ok(compiler, "compile", source, f"--physical={mode}"))
            == old_physical
        ), label
        if expected != body:
            assert physical != old_physical, label
        ir.write_text(physical_ir)
        refused(
            "expected-logical-program",
            optimizer,
            ir,
            "--pass-pipeline=builtin.module(simplify-table-regions)",
        )
    # The opt-in CLI operates on its imported candidate, leaving retained
    # source bytes and a later ordinary compile/import exactly as before.
    assert source.read_text() == original, label
    assert ok(compiler, "import", source) == imported, label
    assert json.loads(ok(compiler, "compile", source)) == direct, label

# The original finite profile remains usable through both pass and CLI.
source.write_text(
    json.dumps(envelope(CONTEXT, cases[0][1]))
)
imported = ok(compiler, "import", source)
simplified = export(optimize(imported, "simplify-table-regions,lower-pir-to-plan"))
assert simplified[2] == "finite-source-1" and simplified[9] == ret(0)
assert json.loads(ok(compiler, "compile", source, "--physical=lazy", "--simplify"))[
    3
] == ret(0)

malformed = [
    (("--simplify",), "simplification-requires-physical"),
    (("--simplify", "--simplify"), "duplicate-option"),
    (("--physical=lazy", "--physical=lazy"), "duplicate-option"),
    (("--physical=lazy", "--physical=materialized"), "duplicate-option"),
    (("--physical=lazy", "--simplify", "--simplify"), "duplicate-option"),
    (
        ("--simplify", "--physical=lazy", "--physical=materialized"),
        "duplicate-option",
    ),
    (("--simplify", "--physical="), "unsupported-preparation-mode"),
    (("--physical=unknown", "--simplify"), "unsupported-preparation-mode"),
    (("--simplify=true", "--physical=lazy"), "unsupported-option"),
    (("--unknown",), "unsupported-option"),
    (("--physical=lazy", "--simplify", "--unknown"), "unsupported-option"),
    (("--simplify", "--physical", "lazy"), "unsupported-option"),
    (("--physical=lazy", "extra"), "unsupported-option"),
]
for flags, code in malformed:
    refused(code, compiler, "compile", source, *flags)
for command in ("import", "export"):
    for flags in (
        ("--simplify",),
        ("--physical=lazy",),
        ("--simplify", "--physical=lazy"),
    ):
        refused("unsupported-option", compiler, command, source, *flags)
for args in ((), ("compile",)):
    result = call(compiler, *args)
    assert result.returncode == 2 and "usage:" in result.stderr, result
refused("unknown-command", compiler, "unknown", source)

# The pass is registered for consumer tools too, but cannot interpret their
# independent library as table-protocol merely because a pass was loaded.
service_context = [
    "client",
    [["n", ["count"], ["shared"], "argument"]],
    ["predicate"],
    [["vector-service", "1"]],
]
service_body = apply(["send"], [0], ret(0))
source.write_text(
    json.dumps(
        envelope(service_context, service_body)
    )
)
ir.write_text(ok(service_compiler, "import", source))
for pipeline in (
    "simplify-table-regions",
    "lower-pir-to-plan,simplify-table-regions",
):
    refused(
        "unsupported-simplification-library",
        service_optimizer,
        ir,
        f"--pass-pipeline=builtin.module({pipeline})",
    )
refused(
    "unsupported-simplification-library",
    service_compiler,
    "compile",
    source,
    "--simplify",
    "--physical=lazy",
)
assert commands.last.stderr == "error: unsupported-simplification-library\n", commands.last.stderr
for text in ("module {}", "module { module {} }"):
    ir.write_text(text)
    refused(
        "expected-logical-program",
        optimizer,
        ir,
        "--pass-pipeline=builtin.module(simplify-table-regions)",
    )

print(
    f"table simplification: {commands.save()} checks over {len(cases)} exact "
    "rewrite/preservation cases on PIR and Plan; both physical modes and CLI "
    "option orders; finite profile; library/physical/CLI refusals"
)
