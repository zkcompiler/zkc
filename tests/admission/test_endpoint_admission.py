#!/usr/bin/env python3
"""Stateful endpoint admission through actual MLIR, Lean and native execution.

Expected results are calculated separately, including residual phase and stopped
call effects. In-process Rust tests additionally check custody, stale receipts
and host failures that cannot be represented as logical Lean outcomes.
"""

import copy
import hashlib
import json

import pytest
import random

from conftest import STORAGE_LAYOUTS
from journal import Journal
from lowering import lowered_plan
from toolchain import Toolchain, records

from source import (
    BOOL,
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
PROFILE = "table-endpoint/1"


def endpoint_source(values, result, body, carrier="region-source-1"):
    source = request(values, result, body)
    source[2] = carrier
    source[3][0] = "prover"
    # Include a private argument and a shared capture in the actual source.
    source[3][1][0][2] = ["private", "prover"]
    return source


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
    programs = 0

    def prepare(name, source, inputs, phase="ready", evidence=None):
        nonlocal programs
        programs += 1
        folder = output / name
        folder.mkdir(exist_ok=True)
        s = journal.write(folder / "source.json", source)
        i = journal.write(folder / "inputs.json", inputs)
        c = journal.write(
            folder / "certificate.json",
            certificate(source[5]) if evidence is None else evidence,
        )
        e = journal.write(folder / "entry.json", ["prover", phase])
        p = lowered_plan(journal, compiler, optimizer, s, folder)
        return s, p, i, c, e

    def native(files, profile=PROFILE):
        s, p, i, c, _ = files
        return journal.attempt([runtime, "run", s, p, i, checker, "--endpoint", profile, c])

    def reference(files):
        s, p, i, c, e = files
        return journal.attempt([checker, "run-entry", s, p, i, PROFILE, c, e])

    def compare(name, source, inputs, expected, phase="ready", evidence=None):
        files = prepare(name, source, inputs, phase, evidence)
        s, p, _, c, e = files
        admission = journal.attempt([checker, "admit-entry", s, p, PROFILE, c, e])
        journal.check(
            name + "-entry-acknowledged",
            admission.returncode == 0
            and json.loads(admission.stdout)
            == {
                "claim": "complete-logical-execution",
                "realization": "direct-logical-plan",
                "status": "checked",
                "phase-profile": PROFILE,
                "entry": ["prover", phase],
            },
        )
        lean, rust = reference(files), native(files)
        journal.check(
            name + "-complete-execution",
            lean.returncode == rust.returncode == 0
            and json.loads(lean.stdout) == json.loads(rust.stdout) == expected,
        )
        return files

    values = [("a", F, 2, False), ("b", F, 5, True)]
    state = [0, 0, 0, [], [3, 6]]
    round_body = apply(["send"], [0, 1], apply(["draw"], [], ret(0)))
    for carrier in ("finite-source-1", "region-source-1"):

        def src(body, result=F):
            return endpoint_source(values, result, body, carrier)

        compare(
            carrier + "-round",
            src(round_body),
            invocation(values, ["prover", "ready", state]),
            executed(
                3,
                ["prover", "ready", [0, 0, 0, [[2, 5]], [6]]],
                [["sent", 2, 5], ["drawn", 3]],
            ),
        )
        compare(
            carrier + "-send-stop",
            src(apply(["send"], [0, 1], stop("abort"))),
            invocation(values, ["prover", "ready", state]),
            stopped(
                "abort",
                ["prover", "sent", [0, 0, 0, [[2, 5]], [3, 6]]],
                [["sent", 2, 5]],
            ),
        )
        compare(
            carrier + "-follow-on-draw",
            src(apply(["draw"], [], ret(0))),
            invocation(values, ["prover", "sent", [0, 0, 0, [[2, 5]], [3, 6]]]),
            executed(3, ["prover", "ready", [0, 0, 0, [[2, 5]], [6]]], [["drawn", 3]]),
            "sent",
        )
        compare(
            carrier + "-exhaustion",
            src(round_body),
            invocation(values, ["prover", "ready", [0, 0, 0, [], []]]),
            stopped(
                "exhausted",
                ["prover", "sent", [0, 0, 0, [[2, 5]], []]],
                [["sent", 2, 5]],
            ),
        )
        compare(
            carrier + "-failed-write",
            src(
                apply(
                    ["send"],
                    [0, 1],
                    apply(["abort_write", "f7"], [1], apply(["draw"], [], ret(0))),
                )
            ),
            invocation(values, ["prover", "ready", state]),
            stopped(
                "abort",
                ["prover", "sent", [0, 2, 1, [[2, 5]], [3, 6]]],
                [["sent", 2, 5], ["write", "f7", 2]],
            ),
        )
        compare(
            carrier + "-already-sent-stop",
            src(stop("reject")),
            invocation(values, ["prover", "sent", state]),
            stopped("reject", ["prover", "sent", state]),
            "sent",
        )
        # State labels are explicit deployment premises; old message count cannot determine phase.
        compare(
            carrier + "-history-not-phase",
            src(round_body),
            invocation(values, ["prover", "ready", [0, 0, 0, [[1, 1]], [3, 6]]]),
            executed(
                3,
                ["prover", "ready", [0, 0, 0, [[1, 1], [2, 5]], [6]]],
                [["sent", 2, 5], ["drawn", 3]],
            ),
        )

    # Independent expected state, events and phase for arbitrary loop/tape boundaries.
    rng = random.Random(91013)
    for n in range(30):
        count = rng.randrange(8)
        tape = [rng.randrange(7) for _ in range(rng.randrange(10))]
        a, b = rng.randrange(7), rng.randrange(7)
        vals = [("a", F, a, False), ("b", F, b, True)]
        loop = apply(["send"], [0, 2], apply(["draw"], [], ret(0)))
        source = endpoint_source(
            vals,
            F,
            ["repeat", count, F, 0, loop, ret(0)],
            "region-source-1" if n % 2 else "finite-source-1",
        )
        acc, sent, events = a, [], []
        for index in range(count):
            sent.append([acc, b])
            events.append(["sent", acc, b])
            if index == len(tape):
                expected = stopped(
                    "exhausted", ["prover", "sent", [0, 0, 0, sent, []]], events
                )
                break
            acc = tape[index]
            events.append(["drawn", acc])
        else:
            expected = executed(
                acc, ["prover", "ready", [0, 0, 0, sent, tape[count:]]], events
            )
        compare(
            f"loop-{n}",
            source,
            invocation(vals, ["prover", "ready", [0, 0, 0, [], tape]]),
            expected,
        )

    shared = [
        "bind",
        BOOL,
        apply(["send"], [0, 1], ret(0)),
        apply(["draw"], [], ret(0)),
    ]
    files = compare(
        "shared-continuation",
        endpoint_source(values, F, shared),
        invocation(values, ["prover", "ready", state]),
        executed(
            3,
            ["prover", "ready", [0, 0, 0, [[2, 5]], [6]]],
            [["sent", 2, 5], ["drawn", 3]],
        ),
    )
    s, p, i, c, e = files
    stale = journal.write(
        i.parent / "stale-inputs.json",
        ["malformed private inputs", ["prover", "sent", state]],
    )
    result = reference((s, p, stale, c, e))
    journal.check(
        "reference-entry-before-private-inputs",
        result.returncode == 1
        and json.loads(result.stdout)["code"] == "endpoint-entry-mismatch",
    )
    # CLI derives the requested phase from actual supplied state, and thus refuses this source from sent.
    stale = journal.write(
        i.parent / "sent-inputs.json", invocation(values, ["prover", "sent", state])
    )
    result = native((s, p, stale, c, e))
    journal.check(
        "native-no-ready-reset",
        result.returncode == 1
        and json.loads(result.stdout)["code"] == "phase-not-admitted",
    )
    for label, policy in [
        ("wrong-policy", "foreign/1"),
        ("trace-downgrade", "table-round/1"),
    ]:
        result = native(files, policy)
        journal.check(
            label,
            result.returncode == 1
            and json.loads(result.stdout)["code"] == "unsupported-check-policy",
        )
    wrong = journal.write(e.parent / "wrong-entry.json", ["verifier", "ready"])
    result = journal.attempt([checker, "admit-entry", s, p, PROFILE, c, wrong])
    journal.check(
        "reference-role-fixed",
        result.returncode == 1
        and json.loads(result.stdout)["code"] == "endpoint-role-mismatch",
    )
    wrong = journal.write(
        i.parent / "wrong-role-inputs.json",
        invocation(values, ["verifier", "ready", state]),
    )
    result = native((s, p, wrong, c, e))
    journal.check(
        "native-role-fixed",
        result.returncode == 1
        and json.loads(result.stdout)["code"] == "endpoint-role-mismatch",
    )
    wrong = copy.deepcopy(json.loads(p.read_text()))
    wrong[9][3] = ret(1)
    bad_plan = journal.write(p.parent / "changed-plan.json", wrong)
    result = native((s, bad_plan, i, c, e))
    journal.check(
        "entry-does-not-bypass-preservation",
        result.returncode == 1
        and json.loads(result.stdout)["code"] == "unchecked-plan",
    )
    result = journal.attempt([checker, "admit", s, p, PROFILE, c])
    journal.check(
        "missing-entry-not-a-trace",
        result.returncode == 1
        and json.loads(result.stdout)["code"] == "unsupported-phase-profile",
    )
    for label, phase in [("host-unknown", "unknown"), ("invalid-phase", "foreign")]:
        wrong = journal.write(
            i.parent / (label + ".json"), invocation(values, ["prover", phase, state])
        )
        result = native((s, p, wrong, c, e))
        journal.check(
            label,
            result.returncode == 1
            and json.loads(result.stdout)["code"]
            == (
                "check-not-established"
                if phase == "unknown"
                else "invalid-endpoint-phase"
            ),
        )
    unknown_entry = journal.write(e.parent / "unknown-entry.json", ["prover", "unknown"])
    response = journal.attempt([checker, "admit-entry", s, p, PROFILE, c, unknown_entry])
    journal.check(
        "lean-unknown-not-a-phase",
        response.returncode == 1
        and json.loads(response.stdout)["code"] == "invalid-endpoint-phase",
    )
    unknown_state = journal.write(
        i.parent / "unknown-state.json",
        invocation(values, ["prover", "unknown", state]),
    )
    response = reference((s, p, unknown_state, c, e))
    journal.check(
        "lean-unknown-not-an-invocation",
        response.returncode == 1
        and json.loads(response.stdout)["code"] == "invalid-endpoint-phase",
    )
    # Legacy mode cannot consume the endpoint state envelope by accident.
    result = journal.attempt([runtime, "run", s, p, i, checker])
    journal.check(
        "state-envelope-not-silently-erased",
        result.returncode == 1 and json.loads(result.stdout)["code"] == "invalid-shape",
    )

    def refused(name, body, result=F, phase="ready", vals=values, evidence=None):
        files = prepare(
            name,
            endpoint_source(vals, result, body),
            invocation(vals, ["prover", phase, state]),
            phase,
            evidence,
        )
        s, p, _, c, e = files
        direct = journal.attempt([checker, "check", s, p])
        lean = journal.attempt([checker, "admit-entry", s, p, PROFILE, c, e])
        rust = native(files)
        journal.check(name + "-preservation-insufficient", direct.returncode == 0)
        journal.check(
            name + "-phase-refusal",
            lean.returncode == rust.returncode == 1
            and json.loads(lean.stdout)["code"]
            == json.loads(rust.stdout)["code"]
            == "phase-not-admitted",
        )

    refused("draw-from-ready", apply(["draw"], [], ret(0)))
    refused("send-from-sent", round_body, phase="sent")
    refused("return-from-sent", ret(0), phase="sent")
    refused("unfinished-send", apply(["send"], [0, 1], ret(0)), BOOL)
    refused(
        "dormant-illegal-branch",
        ["if", 2, round_body, apply(["draw"], [], ret(0))],
        vals=values + [("flag", BOOL, True, False)],
    )
    refused(
        "zero-loop-illegal-body",
        ["repeat", 0, F, 0, apply(["draw"], [], ret(0)), ret(0)],
    )
    refused(
        "shared-wrong-certificate",
        shared,
        evidence=["bind", ["terminal"], ["next", ["terminal"]]],
    )
    # Generic roles are strings; the installed policy, not an ASCII prefilter,
    # rejects a source and entry naming another participant.
    source = endpoint_source(values, F, round_body)
    source[3][0] = "증명자"
    source[3][1][0][2] = ["private", "증명자"]
    unicode_files = prepare(
        "unicode-role", source, invocation(values, ["증명자", "ready", state])
    )
    s, p, i, c, e = unicode_files
    journal.write(e, ["증명자", "ready"])
    response = reference(unicode_files)
    journal.check(
        "unicode-role-policy-refusal",
        response.returncode == 1
        and json.loads(response.stdout)["code"] == "endpoint-role-mismatch",
    )
    response = native(unicode_files)
    journal.check(
        "unicode-role-native-policy-refusal",
        response.returncode == 1
        and json.loads(response.stdout)["code"] == "check-not-established",
    )
    report = {
        "status": "fail" if journal.failures else "pass",
        "programs": programs,
        "checks": journal.checks,
        "commands": journal.commands,
        "binaries": {
            str(p): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in (compiler, optimizer, runtime, checker)
        },
        "scope": "Bounded local table endpoint phase and complete executions; no projection, security or native formal verification claim.",
    }
    (output / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {k: report[k] for k in ("status", "programs")} | {"checks": len(journal.checks)}
        )
    )
    return int(report["status"] != "pass")



@pytest.mark.parametrize("layout", STORAGE_LAYOUTS)
def test_endpoint_admission(storage, layout):
    assert main(storage(layout), layout) == 0

if __name__ == "__main__":
    raise SystemExit(main())
