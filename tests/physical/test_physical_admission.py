#!/usr/bin/env python3
"""Phase and endpoint admission of actual MLIR physical plans.

Compare logical Lean, physical Lean and both native stores, with independent
outcome/state/event and table-evaluation expectations. Host faults and receipt
custody are exercised separately by the in-process Rust tests.

One case is one pytest case, so a failure is one case failing and a change to
one of them can be re-run by name rather than by running all of them.
"""

import copy
import json
from pathlib import Path
import random

import pytest

from source import BOOL, apply, certificate, executed, invocation, point, request
from source import residual, ret, scalar, stop, stopped
from region_cases import cases

F = scalar("f7")
PROFILES = {"trace": "table-round/1", "prover": "table-endpoint/1"}


def protocol_cases():
    values = [
        ("view", residual("f7", 1), [37, [1, 3], []], True),
        ("point", point("f7"), [2], False),
        ("initial", F, 4, False),
        ("flag", BOOL, True, True),
    ]
    evaluate = ["evaluate", "f7", 1]
    body = apply(
        evaluate,
        [0, 1],
        ["bind", BOOL, apply(["send"], [0, 0], ret(0)), apply(["draw"], [], ret(2))],
    )
    yield (
        "prepared-shared-round",
        values,
        F,
        body,
        executed(5, [0, 0, 0, [[5, 5]], []], [["sent", 5, 5], ["drawn", 3]]),
        (3, 1),
        [0, 0, 0, [], [3]],
        "ready",
        "ready",
    )
    # A valid admitted continuation can stop in sent before it reaches draw.
    bad = copy.deepcopy(values)
    bad[1] = ("point", point("f7"), [], False)
    after_send = apply(
        ["send"],
        [2, 2],
        apply(evaluate, [1, 2], apply(["draw"], [], ret(0))),
    )
    yield (
        "guard-after-send",
        bad,
        F,
        after_send,
        stopped("refused", [0, 0, 0, [[4, 4]], [3]], [["sent", 4, 4]]),
        (0, 0),
        [0, 0, 0, [], [3]],
        "ready",
        "sent",
    )
    yield (
        "guard-before-send",
        bad,
        F,
        body,
        stopped("refused"),
        (0, 0),
        None,
        "ready",
        "ready",
    )
    for flag in (False, True):
        vals = values[:-1] + [("flag", BOOL, flag, True)]
        yield (
            f"branch-stop-{flag}",
            vals,
            F,
            ["if", 3, body, stop("reject")],
            (
                executed(5, [0, 0, 0, [[5, 5]], []], [["sent", 5, 5], ["drawn", 3]])
                if flag
                else stopped("reject", [0, 0, 0, [], [3]])
            ),
            (3, 1) if flag else (0, 0),
            [0, 0, 0, [], [3]],
            "ready",
            "ready",
        )
    for tape in ([], [6]):
        yield (
            "sent-entry-" + str(len(tape)),
            values,
            F,
            apply(evaluate, [0, 1], apply(["draw"], [], ret(1))),
            (executed(5, events=[["drawn", 6]]) if tape else stopped("exhausted")),
            (1, 1) if tape else (0, 1),
            [0, 0, 0, [], tape],
            "sent",
            "ready" if tape else "sent",
        )
    rng = random.Random(91326)
    for index in range(30):
        count = rng.randrange(8)
        tape = [rng.randrange(7) for _ in range(rng.randrange(9))]
        cells = [rng.randrange(7), rng.randrange(7)]
        x = rng.randrange(7)
        vals = copy.deepcopy(values)
        vals[0] = ("view", residual("f7", 1), [37, cells, []], True)
        vals[1] = ("point", point("f7"), [x], False)
        value = ((1 - x) * cells[0] + x * cells[1]) % 7
        loop = apply(
            evaluate,
            [1, 2],
            apply(
                ["send"],
                [0, 1],
                apply(["draw"], [], apply(["add", "f7"], [0, 2], ret(0))),
            ),
        )
        body = ["repeat", count, F, 2, loop, ret(0)]
        messages, events, accumulator = [], [], 4
        completed = min(count, len(tape))
        attempts = min(count, len(tape) + 1)
        for iteration in range(attempts):
            messages.append([value, accumulator])
            events.append(["sent", value, accumulator])
            if iteration < completed:
                events.append(["drawn", tape[iteration]])
                accumulator = (tape[iteration] + value) % 7
        state = [0, 0, 0, messages, tape[completed:]]
        exhausted = count > len(tape)
        expected = (
            stopped("exhausted", state, events)
            if exhausted
            else executed(accumulator, state, events)
        )
        yield (
            f"loop-{index}",
            vals,
            F,
            body,
            expected,
            (attempts + completed, attempts),
            [0, 0, 0, [], tape],
            "ready",
            "sent" if exhausted else "ready",
        )




# The two Lean references these cases are compared against. Which reference a
# test uses is part of what the test is, not of how it is invoked: the physical
# reference refuses a logical plan rather than disagreeing with it.
CHECKER = "table-protocol"
PHYSICAL = "table-physical-reference"

# The case the refusals are stated over. A refusal is about a candidate that
# was admitted first.
ADMITTED = "prepared-shared-round"


def tools(toolchain):
    return (toolchain.compiler, toolchain.runtime,
            toolchain.checker(CHECKER), toolchain.checker(PHYSICAL))


def native(journal, runtime, physical_reference, folder, candidate, actor,
           layout="packed", checker=None, profile=None, inputs=None):
    """Run a physical candidate on the host, as one actor under one layout."""
    return journal.attempt([
        runtime,
        "run-physical",
        folder / "source.json",
        candidate,
        inputs or folder / "inputs.json",
        checker or physical_reference,
        "--phase" if actor == "trace" else "--endpoint",
        profile or PROFILES[actor],
        folder / "certificate.json",
        "--storage",
        layout,
    ])



def staged(journal, original, inputs, actor, start):
    """The four files one actor of a case is admitted from.

    Both the comparison and the test that changes an admitted candidate need
    these, and they have to be written the same way or the second would be
    judging something the first never produced.
    """
    folder = journal.directory / actor
    folder.mkdir(parents=True, exist_ok=True)
    source = copy.deepcopy(original)
    source[2] = "region-source-1"
    source[3][0] = actor
    for descriptor in source[3][1]:
        if descriptor[2][0] == "private":
            descriptor[2][1] = actor
    data = copy.deepcopy(inputs)
    if actor == "prover":
        data[1] = [actor, start, data[1]]
    return (folder,
            journal.write(folder / "source.json", source),
            journal.write(folder / "inputs.json", data),
            journal.write(folder / "certificate.json", certificate(source[5])),
            journal.write(folder / "entry.json", [actor, start]))


def compare(journal, toolchain, name, original, inputs, expected, costs,
            start="ready", final="ready"):
    """One case as every actor it is admitted for, against both references."""
    compiler, runtime, logical_reference, physical_reference = tools(toolchain)
    for actor, profile in PROFILES.items():
        if start != "ready" and actor == "trace":
            continue
        folder, s, i, c, e = staged(journal, original, inputs, actor, start)
        outcome = copy.deepcopy(expected)
        if actor == "prover":
            outcome["state"] = [actor, final, outcome["state"]]
        extra = [profile, c] + ([e] if actor == "prover" else [])
        direct = journal.attempt([compiler, "compile", s])
        plan = folder / "direct.json"
        plan.write_text(direct.stdout)
        logical = journal.attempt([
            logical_reference,
            "run-entry" if actor == "prover" else "run-admitted",
            s,
            plan,
            i,
            *extra,
        ])
        journal.check(
            "logical",
            direct.returncode == logical.returncode == 0
            and journal.parse(logical) == outcome,
            journal.parse(logical),
        )
        for mode, count in zip(("lazy", "materialized"), costs, strict=True):
            produced = journal.attempt([compiler, "compile", s, "--physical=" + mode])
            p = folder / (mode + ".json")
            p.write_text(produced.stdout)
            acknowledgement = journal.attempt([
                physical_reference,
                "admit-entry" if actor == "prover" else "admit",
                s,
                p,
                *extra,
            ])
            ack = {
                "status": "checked",
                "claim": "complete-logical-execution",
                "realization": "table-physical-plan",
                "phase-profile": profile,
            }
            if actor == "prover":
                ack["entry"] = [actor, start]
            journal.check(
                "admit-" + mode,
                produced.returncode == acknowledgement.returncode == 0
                and journal.parse(acknowledgement) == ack,
                journal.parse(acknowledgement),
            )
            reference = journal.attempt([
                physical_reference,
                "run-entry" if actor == "prover" else "run-admitted",
                s,
                p,
                i,
                *extra,
            ])
            expected_physical = journal.parse(reference)
            journal.check(
                "reference-" + mode,
                reference.returncode == 0
                and expected_physical.get("execution") == outcome
                and expected_physical.get("table-evaluations") == count,
                expected_physical,
            )
            journal.write(folder / (mode + "-lean.json"), expected_physical)
            for layout in ("packed", "segmented"):
                result = native(journal, runtime, physical_reference, folder, p, actor, layout)
                journal.write(folder / (mode + "-" + layout + ".json"), journal.parse(result))
                journal.check(
                    "native-" + mode + "-" + layout,
                    result.returncode == reference.returncode == 0
                    and journal.parse(result) == expected_physical,
                    journal.parse(result),
                )


def corpus():
    """Every case, from the shared region corpus, this file's own protocol
    cases and one complete table round, in the order `compare` takes them."""
    rows = []
    for name, values, result, body, expected, costs, state in cases(40):
        if name in ("exhausted-after-prepare", "draw-state"):
            continue  # Their draw from ready is tested as a refusal below.
        if name == "send-then-abort":
            # The fixture stops, but the contract also permits a typed reply.
            # Complete that reply's phase path instead of assuming it is dead.
            body[3][3][3] = apply(["draw"], [], ret(1))
        rows.append((
            name,
            request(values, result, body),
            invocation(values, state),
            expected,
            costs,
            "ready",
            "sent" if name == "send-then-abort" else "ready",
        ))
    for (
        name,
        values,
        result,
        body,
        expected,
        costs,
        state,
        start,
        final,
    ) in protocol_cases():
        rows.append((
            name,
            request(values, result, body),
            invocation(values, state),
            expected,
            costs,
            start,
            final,
        ))
    rows.append((
        "table-round",
        json.loads(Path("examples/tables/source.json").read_text()),
        json.loads(Path("examples/tables/inputs.json").read_text()),
        executed(True, [0, 0, 0, [[2, 5]], []], [["sent", 2, 5], ["drawn", 3]]),
        (7, 3),
        "ready",
        "ready",
    ))
    return rows


CASES = corpus()


def admitted(journal, toolchain):
    """The case the refusals are stated over, taken as far as being admitted.

    It runs the same steps `compare` runs and makes none of its judgments: this
    test is about what happens to a candidate afterwards, and repeating another
    test's checks here would report them twice.
    """
    compiler, runtime, logical_reference, physical_reference = tools(toolchain)
    _, original, inputs, _, _, start, _ = next(
        one for one in CASES if one[0] == ADMITTED)
    for actor in PROFILES:
        folder, s, _, _, _ = staged(journal, original, inputs, actor, start)
        journal.run([compiler, "compile", s, "--physical=lazy"],
                    keep=folder / "lazy.json")
    return journal.directory


@pytest.mark.parametrize("case", CASES, ids=[one[0] for one in CASES])
def test_a_phase_case_agrees(journal, toolchain, case):
    """One case, admitted and run as every actor it is admitted for."""
    compare(journal, toolchain, *case)
    journal.save()
    assert not journal.failures, journal.failures


def test_an_admitted_candidate_may_not_be_changed(journal, toolchain):
    """What a candidate has to stay, stated over one that was admitted."""
    compiler, runtime, logical_reference, physical_reference = tools(toolchain)
    prepared = admitted(journal, toolchain)
    base = prepared / "prover"
    s, p, c, e = [
        base / (name + ".json") for name in ("source", "lazy", "certificate", "entry")
    ]
    good = json.loads(p.read_text())
    for name, mutate in (
        ("context", lambda x: x[2].__setitem__(0, "other")),
        ("changed-point", lambda x: x[3].__setitem__(2, [0, 0])),
        ("changed-return", lambda x: x[3][3][3][3].__setitem__(1, 0)),
        ("reference-only", lambda x: x.__setitem__(0, "zkc-table-physical-reference")),
    ):
        changed = copy.deepcopy(good)
        mutate(changed)
        candidate = journal.write(base / (name + ".json"), changed)
        result = native(journal, runtime, physical_reference, base, candidate, "prover")
        journal.check(
            name + ":native-refused",
            result.returncode == 1 and journal.parse(result).get("status") == "refused",
            journal.parse(result),
        )
    reference_only = journal.attempt([
        physical_reference,
        "admit-entry",
        s,
        base / "reference-only.json",
        PROFILES["prover"],
        c,
        e,
    ])
    journal.check(
        "reference-profile-cannot-gain-phase",
        reference_only.returncode == 1
        and journal.parse(reference_only).get("code") == "unsupported-physical-phase",
        journal.parse(reference_only),
    )
    for actor in PROFILES:
        folder = prepared / actor
        result = native(journal, runtime, physical_reference, folder, folder / "lazy.json", actor, profile="foreign/1")
        journal.check(
            actor + ":unknown-policy",
            result.returncode == 1
            and journal.parse(result).get("code") == "unsupported-check-policy",
            journal.parse(result),
        )
        result = native(journal, runtime, physical_reference, folder, folder / "lazy.json", actor, checker=logical_reference)
        journal.check(
            actor + ":wrong-checker",
            result.returncode == 1 and journal.parse(result).get("status") == "refused",
            journal.parse(result),
        )
    for name, entry, code in (
        ("foreign-entry", ["verifier", "ready"], "endpoint-role-mismatch"),
        ("unknown-entry", ["prover", "unknown"], "invalid-endpoint-phase"),
        ("sent-entry", ["prover", "sent"], "phase-not-admitted"),
    ):
        wrong = journal.write(base / (name + ".json"), entry)
        result = journal.attempt([physical_reference, "admit-entry", s, p, PROFILES["prover"], c, wrong])
        journal.check(
            name,
            result.returncode == 1 and journal.parse(result).get("code") == code,
            journal.parse(result),
        )
    wrong_inputs = journal.write(
        base / "stale-inputs.json", [[], ["prover", "sent", [0, 0, 0, [], []]]]
    )
    result = journal.attempt([
        physical_reference, "run-entry", s, p, wrong_inputs, PROFILES["prover"], c, e
    ])
    journal.check(
        "entry-before-private-inputs",
        result.returncode == 1
        and journal.parse(result).get("code") == "endpoint-entry-mismatch",
        journal.parse(result),
    )
    result = journal.attempt([physical_reference, "admit", s, p, PROFILES["prover"], c])
    journal.check(
        "missing-entry",
        result.returncode == 1
        and journal.parse(result).get("code") == "unsupported-phase-profile",
        journal.parse(result),
    )
    journal.save()
    assert not journal.failures, journal.failures


def test_a_preserving_candidate_may_still_violate_the_phase(journal, toolchain):
    """Dormant bodies and paths after a false reply are still phase relevant."""
    compiler, runtime, logical_reference, physical_reference = tools(toolchain)
    # discipline. Dormant bodies and paths after false replies remain relevant.
    vals = [("x", F, 2, True), ("flag", BOOL, True, True)]
    for name, body in (
        ("draw-from-ready", apply(["draw"], [], ret(0))),
        ("unfinished-send", apply(["send"], [0, 0], ret(1))),
        (
            "fixture-stop-is-not-a-law",
            apply(["send"], [0, 0], apply(["abort_write", "f7"], [1], ret(2))),
        ),
        ("dormant-draw", ["if", 1, ret(0), apply(["draw"], [], ret(0))]),
        ("zero-loop-draw", ["repeat", 0, F, 0, apply(["draw"], [], ret(0)), ret(0)]),
    ):
        folder = journal.directory / name
        folder.mkdir(parents=True, exist_ok=True)
        source = request(vals, F, body)
        source[2], source[3][0] = "region-source-1", "prover"
        s = journal.write(folder / "source.json", source)
        journal.write(
            folder / "inputs.json",
            invocation(vals, ["prover", "ready", [0, 0, 0, [], [3]]]),
        )
        c = journal.write(folder / "certificate.json", certificate(body))
        e = journal.write(folder / "entry.json", ["prover", "ready"])
        produced = journal.attempt([compiler, "compile", s, "--physical=lazy"])
        p = folder / "lazy.json"
        p.write_text(produced.stdout)
        ordinary = journal.attempt([physical_reference, "check", s, p])
        admitted = journal.attempt([physical_reference, "admit-entry", s, p, PROFILES["prover"], c, e])
        result = native(journal, runtime, physical_reference, folder, p, "prover")
        journal.check(
            name + ":preservation-only", produced.returncode == ordinary.returncode == 0
        )
        journal.check(
            name + ":phase-refusal",
            admitted.returncode == result.returncode == 1
            and journal.parse(admitted).get("code")
            == journal.parse(result).get("code")
            == "phase-not-admitted",
            [journal.parse(admitted), journal.parse(result)],
        )

    journal.save()
    assert not journal.failures, journal.failures
