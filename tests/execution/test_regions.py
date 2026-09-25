#!/usr/bin/env python3
"""Compact region execution through actual MLIR, Lean checking, and Rust.

Includes independent arithmetic expectations, stopped effect prefixes, dormant
malformation, profile separation, changed actual candidates, and measured size.
"""

import hashlib
import json

import pytest
from pathlib import Path
import random

from conftest import STORAGE_LAYOUTS
from journal import Journal, names
from toolchain import Toolchain, records

from source import (
    BOOL,
    DIGEST,
    apply,
    executed,
    invocation,
    pair,
    point,
    request,
    residual,
    ret,
    scalar,
    stop,
    stopped,
    table,
)

FIELD = scalar("f7")

# The Lean reference these cases are compared against. It is part of what this
# test is, not of how it is invoked: another reference would refuse this source
# rather than disagree with it.
CHECKER = "table-protocol"


def bind(ty, body, next):
    return ["bind", ty, body, next]


def chain(n, offset=0, domain="f7"):
    if n == 0:
        return ret(0)
    return bind(
        scalar(domain),
        [
            "if",
            offset + 2,
            apply(["add", domain], [0, offset + 1], ret(0)),
            apply(["add", domain], [0, 0], ret(0)),
        ],
        chain(n - 1, offset + 1, domain),
    )


def tree(n, offset=0, domain="f7"):
    if n == 0:
        return ret(0)
    return [
        "if",
        offset + 2,
        apply(["add", domain], [0, offset + 1], tree(n - 1, offset + 1, domain)),
        apply(["add", domain], [0, 0], tree(n - 1, offset + 1, domain)),
    ]


def node_count(body):
    match body:
        case ["apply", _, _, next]:
            return 1 + node_count(next)
        case ["if", _, yes, no] | ["bind", _, yes, no]:
            return 1 + node_count(yes) + node_count(no)
        case ["repeat", _, _, _, body, next]:
            return 1 + node_count(body) + node_count(next)
        case _:
            return 1


def main(tools=None, layout=None):
    """Run every case. A layout names which table storage the runtime uses.

    The suite does not arrange that: it is handed a toolchain whose runtime
    already has, so what it compares is the same either way.
    """
    tools = tools or Toolchain()
    compiler, optimizer, runtime = tools.compiler, tools.optimizer, tools.runtime
    checker = tools.checker(CHECKER)
    output = records(case=layout)
    journal = Journal(output)
    sizes = []

    def prepare(name, inputs, ty, body, state=None, profile="region-source-1"):
        directory = output / name
        directory.mkdir(exist_ok=True)
        src, plan, inp = (
            directory / f for f in ("source.json", "plan.json", "inputs.json")
        )
        req = request(inputs, ty, body)
        req[2] = profile
        src.write_text(json.dumps(req))
        inp.write_text(json.dumps(invocation(inputs, state)))
        return directory, src, plan, inp

    def run(name, inputs, ty, body, expected, state=None, profile="region-source-1"):
        directory, src, plan, inp = prepare(name, inputs, ty, body, state, profile)
        compiled = journal.attempt([compiler, "compile", src])
        journal.check(name + "/compile", compiled.returncode == 0, compiled.stderr or None)
        if compiled.returncode:
            return directory
        plan.write_text(compiled.stdout)
        candidate = json.loads(compiled.stdout)
        journal.check(name + "/actual-body", candidate[2] == profile and candidate[9] == body)
        native = journal.attempt([runtime, "run", src, plan, inp, checker])
        lean = journal.attempt([checker, "run", src, plan, inp])
        (directory / "native.json").write_text(native.stdout)
        (directory / "lean.json").write_text(lean.stdout)
        actual, reference = json.loads(native.stdout), json.loads(lean.stdout)
        journal.check(
            name + "/differential",
            native.returncode == lean.returncode == 0 and actual == reference,
            {"native": actual, "lean": reference} if actual != reference else None,
        )
        journal.check(
            name + "/expected",
            actual == expected,
            actual if actual != expected else None,
        )
        return directory

    # A new result type absent from the inputs requires no invented initial value.
    inputs = [("x", FIELD, 3, False), ("y", FIELD, 4, False)]
    bool_body = bind(BOOL, apply(["equal"], [0, 1], ret(0)), ["if", 0, ret(1), ret(2)])
    base = run("new-result-type", inputs, FIELD, bool_body, executed(4))
    run(
        "nested-binding",
        inputs,
        FIELD,
        bind(
            BOOL,
            bind(
                FIELD,
                apply(["add", "f7"], [0, 1], ret(0)),
                apply(["equal"], [0, 1], ret(0)),
            ),
            ["if", 0, ret(1), ret(2)],
        ),
        executed(4),
    )

    # Every terminal reason retains the body's writes and suppresses the suffix.
    for reason in ("reject", "abort", "exhausted", "incomplete", "refused"):
        run(
            "stop-" + reason,
            inputs,
            BOOL,
            bind(
                BOOL,
                apply(["record", "f7"], [0], stop(reason)),
                apply(["record", "f7"], [2], ret(0)),
            ),
            stopped(reason, [0, 3, 1, [], []], [["write", "f7", 3]]),
        )
    run(
        "operation-stops",
        inputs,
        BOOL,
        bind(
            BOOL,
            apply(["abort_write", "f7"], [0], ret(0)),
            apply(["record", "f7"], [2], ret(0)),
        ),
        stopped("abort", [0, 3, 1, [], []], [["write", "f7", 3]]),
    )
    run(
        "suffix-stops",
        inputs,
        BOOL,
        bind(
            BOOL,
            apply(["record", "f7"], [0], ret(0)),
            apply(["abort_write", "f7"], [2], ret(0)),
        ),
        stopped("abort", [0, 4, 2, [], []], [["write", "f7", 3], ["write", "f7", 4]]),
    )
    run(
        "draw-exhaustion",
        inputs,
        BOOL,
        bind(FIELD, apply(["draw"], [], ret(0)), apply(["record", "f7"], [0], ret(0))),
        stopped("exhausted"),
    )
    run(
        "draw-return",
        inputs,
        BOOL,
        bind(FIELD, apply(["draw"], [], ret(0)), apply(["record", "f7"], [0], ret(0))),
        executed(True, [0, 5, 1, [], []], [["drawn", 5], ["write", "f7", 5]]),
        [0, 0, 0, [], [5]],
    )
    # A stopped third iteration leaves two complete writes and the exact consumed tape.
    loop_body = bind(
        FIELD, apply(["draw"], [], ret(0)), apply(["record", "f7"], [0], ret(1))
    )
    for count in (0, 2, 3):
        expected = (
            executed(3, [0, 0, 0, [], [2, 5]])
            if count == 0
            else executed(
                5,
                [0, 5, 2, [], []],
                [["drawn", 2], ["write", "f7", 2], ["drawn", 5], ["write", "f7", 5]],
            )
        )
        if count == 3:
            expected["outcome"] = ["stopped", "exhausted"]
        run(
            f"binding-in-loop-{count}",
            inputs,
            FIELD,
            ["repeat", count, FIELD, 0, loop_body, ret(0)],
            expected,
            [0, 0, 0, [], [2, 5]],
        )
    # A residual is an immutable value with the original root, not a new table.
    views = [
        ("table", table("f7", 2), [11, [0, 1, 2, 4]], True),
        ("r", FIELD, 2, False),
        ("suffix", point("f7"), [3], False),
    ]
    run(
        "bound-residual",
        views,
        FIELD,
        bind(
            residual("f7", 2),
            apply(["view", "f7", 2], [0], apply(["restrict", "f7", 2], [0, 2], ret(0))),
            apply(["evaluate", "f7", 2], [0, 3], ret(0)),
        ),
        executed(6),
    )
    run(
        "original-root",
        views,
        residual("f7", 2),
        bind(
            residual("f7", 2),
            apply(["view", "f7", 2], [0], ret(0)),
            bind(
                residual("f7", 2), apply(["restrict", "f7", 2], [0, 2], ret(0)), ret(1)
            ),
        ),
        executed([11, [0, 1, 2, 4], []]),
    )

    # A maintained Sumcheck trace returns into a real shared effectful suffix.
    example = Path(__file__).resolve().parents[2] / "examples/tables/source.json"
    sum_body = json.loads(example.read_text())[5]
    for claim, tape, label in [
        (0, [3, 6], "success"),
        (1, [3], "reject"),
        (0, [], "exhausted"),
    ]:
        ins = [
            ("table", table("f7", 1), [20, [2, 5]], True),
            ("claim", FIELD, claim, False),
        ]
        expected = (
            stopped("reject", [0, 0, 0, [[2, 5]], tape], [["sent", 2, 5]])
            if claim
            else stopped("exhausted", [0, 0, 0, [[2, 5]], []], [["sent", 2, 5]])
            if not tape
            else executed(
                True,
                [0, 0, 1, [[2, 5]], [6]],
                [["sent", 2, 5], ["drawn", 3], ["write", "f7", 0]],
            )
        )
        run(
            "sumcheck-region-" + label,
            ins,
            BOOL,
            bind(BOOL, sum_body, apply(["record", "f7"], [2], ret(1))),
            expected,
            [0, 0, 0, [], tape],
        )
    # Ordered commitment preparation: the second level is shared after orientation choice.
    for flag in (True, False):
        ins = [
            ("leaf", DIGEST, 2, False),
            ("sibling0", DIGEST, 5, True),
            ("sibling1", DIGEST, 9, True),
            ("root", DIGEST, pair(pair(2, 5), 9), False),
            ("left", BOOL, flag, False),
        ]
        body = bind(
            DIGEST,
            [
                "if",
                4,
                apply(["parent", False], [0, 1], ret(0)),
                apply(["parent", True], [0, 1], ret(0)),
            ],
            apply(["parent", False], [0, 3], apply(["digest_equal"], [0, 5], ret(0))),
        )
        run(f"merkle-region-{flag}", ins, BOOL, body, executed(flag))

    rng = random.Random(71823)
    for i in range(50):
        domain, modulus = ("f2", 2) if i % 2 else ("f7", 7)
        x, y, flag, n = (
            rng.randrange(modulus),
            rng.randrange(modulus),
            bool(rng.randrange(2)),
            rng.randrange(20),
        )
        ins = [
            ("x", scalar(domain), x, False),
            ("y", scalar(domain), y, False),
            ("flag", BOOL, flag, False),
        ]
        result = (x + n * y if flag else x * 2**n) % modulus
        run(
            f"random-{i}",
            ins,
            scalar(domain),
            chain(n, domain=domain),
            executed(result),
        )
        if i < 8:
            small = n % 5
            result = (x + small * y if flag else x * 2**small) % modulus
            run(
                f"tree-{i}",
                ins,
                scalar(domain),
                tree(small, domain=domain),
                executed(result),
                profile="finite-source-1",
            )

    # Measure source control nodes separately from textual captures in actual MLIR.
    for n in (0, 4, 8, 14, 32, 64):
        ins = inputs + [("flag", BOOL, True, False)]
        directory = run(f"size-{n}", ins, FIELD, chain(n), executed((3 + 4 * n) % 7))
        imported = journal.attempt([compiler, "import", directory / "source.json"])
        (directory / "source.mlir").write_text(imported.stdout)
        journal.check(f"size-{n}/import", imported.returncode == 0, imported.stderr or None)
        journal.check(
            f"size-{n}/one-bind-per-decision", imported.stdout.count('"pir.bind"') == n
        )
        sizes.append(
            {
                "decisions": n,
                "region_nodes": node_count(chain(n)),
                "tree_nodes": 4 * 2**n - 3,
                "source_bytes": (directory / "source.json").stat().st_size,
                "plan_bytes": (directory / "plan.json").stat().st_size,
                "mlir_bytes": len(imported.stdout.encode()),
            }
        )

    # The independently supplied source is retained; malformed dormant code is rejected.
    for name, bad, profile in [
        ("old-profile-bind", bool_body, "finite-source-1"),
        ("unknown-profile", bool_body, "unknown"),
        ("wrong-result", bind(BOOL, ret(0), ret(1)), "region-source-1"),
        ("dead-suffix", bind(BOOL, stop("abort"), ret(0)), "region-source-1"),
        (
            "bad-capture",
            bind(BOOL, apply(["equal"], [0, 99], ret(0)), ret(1)),
            "region-source-1",
        ),
        ("bad-bind-arity", ["bind", BOOL, ret(0)], "region-source-1"),
        (
            "dormant-branch",
            bind(BOOL, apply(["equal"], [0, 1], ["if", 0, ret(0), ret(99)]), ret(1)),
            "region-source-1",
        ),
    ]:
        _, src, plan, inp = prepare(name, inputs, FIELD, bad, profile=profile)
        original = json.loads((base / "plan.json").read_text())
        original[2], original[9] = profile, bad
        plan.write_text(json.dumps(original))
        for tool, command in [
            ("compiler", [compiler, "compile", src]),
            ("lean", [checker, "check", src, plan]),
            ("runtime", [runtime, "run", src, plan, inp, checker]),
        ]:
            result = journal.attempt(command)
            codes = {
                "old-profile-bind": (
                    "unsupported-source-format",
                    "invalid-shape",
                    "invalid-shape",
                ),
                "unknown-profile": (
                    "invalid-request",
                    "invalid-shape",
                    "invalid-shape",
                ),
                "bad-bind-arity": ("invalid-shape", "invalid-shape", "invalid-shape"),
            }.get(name, ("invalid-operand", "malformed-source", "invalid-operand"))
            expected_code = codes[("compiler", "lean", "runtime").index(tool)]
            diagnostic = (
                names(result.stderr, expected_code)
                if tool == "compiler"
                else json.loads(result.stdout)
                == {"status": "refused", "code": expected_code}
            )
            journal.check(
                name + "/" + tool,
                result.returncode == 1
                and diagnostic
                and "Stack dump" not in result.stderr,
                {"stdout": result.stdout, "stderr": result.stderr},
            )

    for name, change in [
        ("profile-mismatch", lambda p: p.__setitem__(2, "finite-source-1")),
        ("extra-requirement", lambda p: p.__setitem__(8, [["extra", "1"]])),
        ("changed-suffix", lambda p: p[9].__setitem__(3, ret(1))),
    ]:
        p = json.loads((base / "plan.json").read_text())
        change(p)
        path = output / (name + ".json")
        path.write_text(json.dumps(p))
        result = journal.attempt([checker, "check", base / "source.json", path])
        lean_code, native_code = {
            "profile-mismatch": ("unsupported-semantics-version",) * 2,
            "extra-requirement": ("unapproved-requirement",) * 2,
            "changed-suffix": ("unchecked-plan", "unchecked-plan"),
        }[name]
        native = journal.attempt([
            runtime,
            "run",
            base / "source.json",
            path,
            base / "inputs.json",
            checker,
        ])
        journal.check(
            name,
            result.returncode == native.returncode == 1
            and json.loads(result.stdout) == {"status": "refused", "code": lean_code}
            and json.loads(native.stdout) == {"status": "refused", "code": native_code},
            {"lean": result.stdout, "native": native.stdout},
        )

    # Actual generic CSE under bind can export a well-formed changed candidate,
    # but it does not receive direct-source certification against the original.
    cse_body = bind(
        FIELD,
        apply(["add", "f7"], [0, 1], apply(["add", "f7"], [1, 2], ret(0))),
        ret(0),
    )
    directory = run("cse", inputs, FIELD, cse_body, executed(0))
    ir = journal.attempt([compiler, "import", directory / "source.json"])
    (directory / "source.mlir").write_text(ir.stdout)
    optimized = journal.attempt([
        optimizer,
        directory / "source.mlir",
        "--pass-pipeline=builtin.module(cse,lower-pir-to-plan)",
    ])
    (directory / "optimized.mlir").write_text(optimized.stdout)
    journal.check(
        "cse/structural-lowering", optimized.returncode == 0, optimized.stderr or None
    )
    candidate = journal.attempt([compiler, "export", directory / "optimized.mlir"])
    journal.check("cse/actual-export", candidate.returncode == 0, candidate.stderr or None)
    if candidate.returncode == 0:
        (directory / "changed.json").write_text(candidate.stdout)
        journal.check("cse/body-changed", json.loads(candidate.stdout)[9] != cse_body)
        rejected = journal.attempt([
            checker, "check", directory / "source.json", directory / "changed.json"
        ])
        journal.check(
            "cse/no-unproved-admission",
            rejected.returncode > 0 and names(rejected.stdout, "unchecked-plan"),
            rejected.stdout,
        )

    result = {
        "status": "fail" if journal.failures else "pass",
        "seed": 71823,
        "checks": journal.checks,
        "sizes": sizes,
        "commands": journal.commands,
        "artifacts_sha256": {
            str(p.relative_to(output)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(output.rglob("*"))
            if p.is_file() and p.name != "validation.json"
        },
        "scope": "Finite table interpretation and compact structured control; not native verification, a general CFG, or certified CSE.",
    }
    (output / "validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps({"status": result["status"], "checks": len(journal.checks), "sizes": sizes})
    )
    return 0 if result["status"] == "pass" else 1



@pytest.mark.parametrize("layout", STORAGE_LAYOUTS)
def test_regions(storage, layout):
    assert main(storage(layout), layout) == 0

if __name__ == "__main__":
    raise SystemExit(main())
