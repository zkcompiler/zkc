#!/usr/bin/env python3
"""Consumer-selected phase admission through actual MLIR, Lean and Rust.

Both wire carriers retain source/candidate/evidence. Full execution comparisons
include independent expected results, exhausted tapes and failed-write prefixes.
This finite trace discipline does not establish protocol security or projection.
"""

import copy
import hashlib
import json

import pytest
from pathlib import Path
import random

from conftest import STORAGE_LAYOUTS
from journal import Journal
from lowering import lowered_plan
from toolchain import Toolchain, records

from source import (
    BOOL,
    TERMINAL,
    apply,
    certificate,
    executed,
    invocation,
    request,
    ret,
    scalar,
    stop,
    stopped,
)

F = scalar("f7")
PROFILE = "table-round/1"


# The Lean reference these cases are compared against. It is part of what this
# test is, not of how it is invoked: another reference refuses this source
# rather than disagreeing with it.
CHECKER = "table-protocol"


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

    def prepare(name, source, inputs, evidence=None):
        folder = output / name
        folder.mkdir(exist_ok=True)
        s = journal.write(folder / "source.json", source)
        i = journal.write(folder / "inputs.json", inputs)
        c = journal.write(
            folder / "certificate.json",
            certificate(source[5]) if evidence is None else evidence,
        )
        p = lowered_plan(journal, compiler, optimizer, s, folder)
        return s, p, i, c

    def compare(name, source, inputs, expected, evidence=None):
        s, p, i, c = prepare(name, source, inputs, evidence)
        admitted = journal.attempt([checker, "admit", s, p, PROFILE, c])
        lean = journal.attempt([checker, "run-admitted", s, p, i, PROFILE, c])
        native = journal.attempt([runtime, "run", s, p, i, checker, "--phase", PROFILE, c])
        journal.check(
            name + "-admission",
            admitted.returncode == 0
            and json.loads(admitted.stdout).get("phase-profile") == PROFILE,
        )
        journal.check(
            name + "-complete-execution",
            lean.returncode == native.returncode == 0
            and json.loads(lean.stdout) == json.loads(native.stdout) == expected,
        )
        return s, p, i, c

    inputs = [("a", F, 2, False), ("b", F, 5, True)]
    state = [0, 0, 0, [], [3, 6]]
    body = apply(["send"], [0, 1], apply(["draw"], [], ret(0)))
    compact = [
        "bind",
        BOOL,
        apply(["send"], [0, 1], ret(0)),
        apply(["draw"], [], ret(0)),
    ]
    expected = executed(3, [0, 0, 0, [[2, 5]], [6]], [["sent", 2, 5], ["drawn", 3]])
    source = request(inputs, F, ["bind", F, stop("abort"), apply(["draw"], [], ret(0))])
    source[2] = "region-source-1"
    compare(
        "stopped-shared-body",
        source,
        invocation(inputs, state),
        stopped("abort", state),
    )
    for profile, round_body in [
        ("finite-source-1", body),
        ("region-source-1", compact),
    ]:
        source = request(inputs, F, round_body)
        source[2] = profile
        compare(profile, source, invocation(inputs, state), expected)
        compare(
            profile + "-residual-state",
            source,
            invocation(inputs, [0, 0, 0, [[2, 5]], [3, 6]]),
            executed(
                3,
                [0, 0, 0, [[2, 5], [2, 5]], [6]],
                [["sent", 2, 5], ["drawn", 3]],
            ),
        )
        compare(
            profile + "-exhausted",
            source,
            invocation(inputs),
            stopped("exhausted", [0, 0, 0, [[2, 5]], []], [["sent", 2, 5]]),
        )
        source[5] = apply(["send"], [0, 1], stop("reject"))
        compare(
            profile + "-stop-after-send",
            source,
            invocation(inputs, state),
            stopped("reject", [0, 0, 0, [[2, 5]], [3, 6]], [["sent", 2, 5]]),
        )
        failing = apply(
            ["send"],
            [0, 1],
            apply(["abort_write", "f7"], [1], apply(["draw"], [], ret(0))),
        )
        source[5] = failing
        compare(
            profile + "-failed-write",
            source,
            invocation(inputs, state),
            stopped(
                "abort",
                [0, 2, 1, [[2, 5]], [3, 6]],
                [["sent", 2, 5], ["write", "f7", 2]],
            ),
        )

    # Complete existing table/evaluation example, independently expected output.
    source = json.loads(
        (
            Path(__file__).resolve().parents[2] / "examples/tables/source.json"
        ).read_text()
    )
    values = json.loads(
        (
            Path(__file__).resolve().parents[2] / "examples/tables/inputs.json"
        ).read_text()
    )
    compare(
        "table-round",
        source,
        values,
        executed(True, [0, 0, 0, [[2, 5]], []], [["sent", 2, 5], ["drawn", 3]]),
    )

    # Generated bounded loops exercise a shared admission invariant and arbitrary
    # tape exhaustion, with a separate expected state/event calculation.
    rng = random.Random(71329)
    for n in range(30):
        count = rng.randrange(7)
        tape = [rng.randrange(7) for _ in range(rng.randrange(9))]
        a, b = rng.randrange(7), rng.randrange(7)
        values = [("a", F, a, False), ("b", F, b, True)]
        loop_body = apply(["send"], [0, 2], apply(["draw"], [], ret(0)))
        source = request(values, F, ["repeat", count, F, 0, loop_body, ret(0)])
        source[2] = "region-source-1" if n % 2 else "finite-source-1"
        sent, events, acc = [], [], a
        for index in range(count):
            sent.append([acc, b])
            events.append(["sent", acc, b])
            if index == len(tape):
                expected = stopped("exhausted", [0, 0, 0, sent, []], events)
                break
            acc = tape[index]
            events.append(["drawn", acc])
        else:
            expected = executed(acc, [0, 0, 0, sent, tape[count:]], events)
        compare(f"loop-{n}", source, invocation(values, [0, 0, 0, [], tape]), expected)

    def refused(name, body, result=F, extra_inputs=None, evidence=None):
        values = inputs if extra_inputs is None else extra_inputs
        source = request(values, result, body)
        source[2] = "region-source-1"
        s, p, i, c = prepare(name, source, invocation(values, state), evidence)
        direct = journal.attempt([checker, "check", s, p])
        lean = journal.attempt([checker, "admit", s, p, PROFILE, c])
        native = journal.attempt([runtime, "run", s, p, i, checker, "--phase", PROFILE, c])
        journal.check(name + "-preservation-is-insufficient", direct.returncode == 0)
        journal.check(
            name + "-phase-refusal",
            lean.returncode == native.returncode == 1
            and json.loads(lean.stdout)["code"]
            == json.loads(native.stdout)["code"]
            == "phase-not-admitted",
        )
        return s, p, i, c

    s, p, i, _ = refused("draw-first", apply(["draw"], [], ret(0)))
    direct = journal.attempt([runtime, "run", s, p, i, checker])
    journal.check(
        "preservation-only-execution",
        direct.returncode == 0
        and json.loads(direct.stdout)
        == executed(3, [0, 0, 0, [], [6]], [["drawn", 3]]),
    )
    refused("unfinished-send", apply(["send"], [0, 1], ret(0)), BOOL)
    refused(
        "double-send", apply(["send"], [0, 1], apply(["send"], [1, 2], ret(0))), BOOL
    )
    refused(
        "dormant-branch",
        ["if", 2, body, apply(["draw"], [], ret(0))],
        extra_inputs=inputs + [("flag", BOOL, True, False)],
    )
    refused(
        "wrong-shared-certificate",
        compact,
        evidence=["bind", TERMINAL, ["next", TERMINAL]],
    )
    refused(
        "zero-loop-illegal-body",
        ["repeat", 0, F, 0, apply(["draw"], [], ret(0)), ret(0)],
    )
    loop_body = apply(["send"], [0, 2], apply(["draw"], [], ret(0)))
    for name, invariant in [
        ("empty-invariant", []),
        ("missing-entry", ["sent"]),
        ("overwide-invariant", ["ready", "sent"]),
    ]:
        refused(
            name,
            ["repeat", 2, F, 0, loop_body, ret(0)],
            evidence=["loop", invariant, certificate(loop_body), TERMINAL],
        )

    source = request(inputs, F, compact)
    source[2] = "region-source-1"
    s, p, i, c = prepare("mutations", source, invocation(inputs, state))
    for label, profile in [
        ("wrong-policy", "another-profile/1"),
        ("policy-trailing-space", PROFILE + " "),
    ]:
        response = journal.attempt([runtime, "run", s, p, i, checker, "--phase", profile, c])
        journal.check(
            label,
            response.returncode == 1
            and json.loads(response.stdout)["code"] == "unsupported-check-policy",
        )
    for label, evidence in [
        ("unknown-phase", ["loop", ["foreign"], TERMINAL, TERMINAL]),
        ("extra-field", ["terminal", "ready"]),
        ("depth-limit", ["next"]),
        ("wrong-arity", ["bind", TERMINAL]),
    ]:
        if label == "depth-limit":
            evidence = TERMINAL
            for _ in range(260):
                evidence = ["next", evidence]
        bad = journal.write(c.parent / (label + ".json"), evidence)
        response = journal.attempt([
            runtime, "run", s, p, i, checker, "--phase", PROFILE, bad
        ])
        lean = journal.attempt([checker, "admit", s, p, PROFILE, bad])
        journal.check(
            label,
            lean.returncode == response.returncode == 1
            and json.loads(lean.stdout)["code"]
            == ("depth-limit" if label == "depth-limit" else "invalid-shape")
            and json.loads(response.stdout)["code"] == "check-not-established",
        )
    conditional = copy.deepcopy(json.loads(p.read_text()))
    conditional[8] = [["extra", "1"]]
    bad = journal.write(p.parent / "unapproved-requirement.json", conditional)
    lean = journal.attempt([checker, "check", s, bad])
    native = journal.attempt([runtime, "run", s, bad, i, checker])
    journal.check(
        "conditional-requirement-boundary",
        lean.returncode == native.returncode == 1
        and json.loads(lean.stdout)["code"] == "unapproved-requirement"
        and json.loads(native.stdout)["code"] == "unapproved-requirement",
    )
    changed = copy.deepcopy(json.loads(p.read_text()))
    changed[9][3] = ret(1)
    bad = journal.write(p.parent / "changed-plan.json", changed)
    response = journal.attempt([runtime, "run", s, bad, i, checker, "--phase", PROFILE, c])
    journal.check(
        "actual-candidate-bound",
        response.returncode == 1
        and json.loads(response.stdout)["code"] == "unchecked-plan",
    )
    source[3][0] = "other-role"
    s, p, i, c = prepare("wrong-role", source, invocation(inputs, state))
    response = journal.attempt([runtime, "run", s, p, i, checker, "--phase", PROFILE, c])
    journal.check(
        "consumer-role-fixed",
        response.returncode == 1
        and json.loads(response.stdout)["code"] == "unsupported-check-policy",
    )

    result = {
        "status": "fail" if journal.failures else "pass",
        "checks": journal.checks,
        "commands": journal.commands,
        "binaries": {
            str(p): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in (compiler, optimizer, runtime, checker)
        },
        "scope": "Bounded table trace phase admission and complete native/reference execution; not protocol security or native formal verification.",
    }
    (output / "validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "checks": len(journal.checks)}))
    return int(result["status"] != "pass")



@pytest.mark.parametrize("layout", STORAGE_LAYOUTS)
def test_phase_admission(storage, layout):
    assert main(storage(layout), layout) == 0

if __name__ == "__main__":
    raise SystemExit(main())
