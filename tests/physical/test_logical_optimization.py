#!/usr/bin/env python3
"""Changed MLIR candidates checked against original sources, then run on both stores.

Expectations use independent field arithmetic and explicit failure traces. The
source certificate remains unchanged when the optimized body has fewer nodes.

One case is one pytest case, so a failure is one case failing and a change to
one of them can be re-run by name rather than by running all of them.
"""

import copy

import pytest

from journal import names
from source import (
    BOOL,
    apply,
    certificate,
    executed,
    invocation,
    point,
    request,
    residual,
    ret,
    scalar,
    stopped,
)

F = scalar("f7")
LINEAR = ["linear"]


def cases():
    for a in range(7):
        for r in range(7):
            values = [("a", F, a, True), ("r", F, r, False)]
            body = apply(LINEAR, [0, 0, 1], apply(LINEAR, [0, 1, 2], ret(0)))
            yield f"field-{a}-{r}", values, body, executed(a), None, "ready", 2
    values = [("a", F, 4, True), ("r", F, 2, False)]
    for flag in (False, True):
        args = values + [("flag", BOOL, flag, True)]
        body = [
            "if",
            2,
            apply(LINEAR, [0, 0, 1], ret(0)),
            apply(LINEAR, [1, 1, 0], ret(0)),
        ]
        yield f"branch-{flag}", args, body, executed(4 if flag else 2), None, "ready", 2
    for count in (0, 1, 4):
        body = ["repeat", count, F, 0, apply(LINEAR, [0, 0, 2], ret(0)), ret(0)]
        yield f"loop-{count}", values, body, executed(4), None, "ready", 1
    body = [
        "bind",
        F,
        apply(LINEAR, [0, 0, 1], ret(0)),
        apply(LINEAR, [0, 0, 2], ret(0)),
    ]
    yield "shared-suffix", values, body, executed(4), None, "ready", 2
    # The outer fold aliases distinct captures of the explicit shared region.
    body = apply(
        LINEAR, [0, 0, 1], ["bind", F, apply(LINEAR, [0, 1, 2], ret(0)), ret(0)]
    )
    yield "capture-alias", values, body, executed(4), None, "ready", 2
    for valid in (False, True):
        args = values + [
            ("view", residual("f7", 1), [19, [1, 3], []], True),
            ("point", point("f7"), [2] if valid else [], False),
        ]
        body = apply(LINEAR, [0, 0, 1], apply(["evaluate", "f7", 1], [3, 4], ret(1)))
        expected = executed(4) if valid else stopped("refused")
        yield f"dead-guard-{valid}", args, body, expected, None, "ready", 1
        body = apply(["evaluate", "f7", 1], [2, 3], apply(LINEAR, [0, 0, 2], ret(0)))
        expected = executed(5) if valid else stopped("refused")
        yield f"prepared-alias-{valid}", args, body, expected, None, "ready", 1
    for tape in ([], [3]):
        body = apply(
            LINEAR, [0, 0, 1], apply(["send"], [0, 0], apply(["draw"], [], ret(2)))
        )
        expected = (
            executed(4, [0, 0, 0, [[4, 4]], []], [["sent", 4, 4], ["drawn", 3]])
            if tape
            else stopped("exhausted", [0, 0, 0, [[4, 4]], []], [["sent", 4, 4]])
        )
        yield (
            f"round-{len(tape)}",
            values,
            body,
            expected,
            [0, 0, 0, [], tape],
            "ready" if tape else "sent",
            1,
        )
    body = apply(LINEAR, [0, 0, 1], apply(["abort_write", "f7"], [0], ret(1)))
    yield (
        "failed-write",
        values,
        body,
        stopped("abort", [0, 4, 1, [], []], [["write", "f7", 4]]),
        None,
        "ready",
        1,
    )
    body = apply(
        ["send"],
        [0, 0],
        apply(
            LINEAR,
            [1, 1, 2],
            apply(["abort_write", "f7"], [0], apply(["draw"], [], ret(2))),
        ),
    )
    yield (
        "sent-failed-write",
        values,
        body,
        stopped(
            "abort", [0, 4, 1, [[4, 4]], [3]], [["sent", 4, 4], ["write", "f7", 4]]
        ),
        [0, 0, 0, [], [3]],
        "sent",
        1,
    )


def count_linear(body, physical=False):
    match body:
        case ["apply", op, _, tail]:
            return int(
                op == (["invoke", LINEAR] if physical else LINEAR)
            ) + count_linear(tail, physical)
        case ["if", _, yes, no] | ["bind", _, yes, no]:
            return count_linear(yes, physical) + count_linear(no, physical)
        case ["repeat", _, _, _, inner, tail]:
            return count_linear(inner, physical) + count_linear(tail, physical)
        case _:
            return 0


# The two Lean references these cases are compared against. Which reference a
# test uses is part of what the test is, not of how it is invoked: the physical
# reference refuses a logical plan rather than disagreeing with it.
CHECKER = "table-protocol"
PHYSICAL = "table-physical-reference"



CASES = list(cases())


def tools(toolchain):
    return (toolchain.compiler, toolchain.runtime,
            toolchain.checker(CHECKER), toolchain.checker(PHYSICAL))


# The one case whose demand reduction is stated in numbers. The claim belongs
# to that case rather than to a pass over every case's costs afterwards.
MEASURED = "prepared-alias-True"


@pytest.mark.parametrize("case", CASES, ids=[one[0] for one in CASES])
def test_an_optimized_candidate_agrees(journal, toolchain, case):
    """One case, as both actors, changed and then checked against its source."""
    name, values, body, expected, state, final, removed = case
    compiler, runtime, checker, physical_reference = tools(toolchain)
    costs = []
    for actor in ("trace", "prover"):
        folder = journal.directory / actor
        folder.mkdir(parents=True, exist_ok=True)
        original = request(values, F, body)
        # Both existing source grammars enter the same compact checker.
        original[2] = (
            "finite-source-1" if name.startswith("field-") else "region-source-1"
        )
        original[3][0] = actor
        data, expected = invocation(values, state), copy.deepcopy(expected)
        if actor == "prover":
            data[1] = [actor, "ready", data[1]]
            expected["state"] = [actor, final, expected["state"]]
        source = journal.write(folder / "source.json", original)
        source_bytes = source.read_bytes()
        inputs = journal.write(folder / "inputs.json", data)
        cert = journal.write(folder / "certificate.json", certificate(body))
        profile = "table-round/1" if actor == "trace" else "table-endpoint/1"
        extra = [profile, cert]
        if actor == "prover":
            extra.append(journal.write(folder / "entry.json", [actor, "ready"]))
        direct = journal.attempt([compiler, "compile", source])
        direct_path = folder / "direct.json"
        direct_path.write_text(direct.stdout)
        logical = journal.attempt([
            checker,
            "run-admitted" if actor == "trace" else "run-entry",
            source,
            direct_path,
            inputs,
            *extra,
        ])
        journal.check(
            folder.name + ":logical",
            direct.returncode == logical.returncode == 0
            and journal.parse(logical) == expected,
            journal.parse(logical),
        )
        for mode in ("lazy", "materialized"):
            baseline = journal.attempt([compiler, "compile", source, "--physical=" + mode])
            baseline_path = folder / (mode + "-baseline.json")
            baseline_path.write_text(baseline.stdout)
            produced = journal.attempt([
                compiler, "compile", source, "--simplify", "--physical=" + mode
            ])
            path = folder / (mode + ".json")
            path.write_text(produced.stdout)
            candidate, old = journal.parse(produced), journal.parse(baseline)
            valid = produced.returncode == baseline.returncode == 0
            journal.check(
                folder.name + ":changed-" + mode,
                valid
                and candidate != old
                and count_linear(old[3], True) - count_linear(candidate[3], True)
                == removed,
                candidate,
            )
            reference = journal.attempt([
                physical_reference,
                "run-admitted" if actor == "trace" else "run-entry",
                source,
                path,
                inputs,
                *extra,
            ])
            observed = journal.parse(reference)
            journal.check(
                folder.name + ":reference-" + mode,
                reference.returncode == 0 and observed.get("execution") == expected,
                observed,
            )
            baseline_run = journal.attempt([
                physical_reference,
                "run-admitted" if actor == "trace" else "run-entry",
                source,
                baseline_path,
                inputs,
                *extra,
            ])
            old_observed = journal.parse(baseline_run)
            journal.check(
                folder.name + ":baseline-" + mode,
                baseline_run.returncode == 0
                and old_observed.get("execution") == expected,
                old_observed,
            )
            costs.append(
                {
                    "case": name + "-" + actor,
                    "mode": mode,
                    "before": old_observed.get("table-evaluations"),
                    "after": observed.get("table-evaluations"),
                }
            )
            for layout in ("packed", "segmented"):
                native = journal.attempt([
                    runtime,
                    "run-physical",
                    source,
                    path,
                    inputs,
                    physical_reference,
                    "--phase" if actor == "trace" else "--endpoint",
                    profile,
                    cert,
                    "--storage",
                    layout,
                ])
                journal.check(
                    folder.name + ":native-" + mode + "-" + layout,
                    native.returncode == 0 and journal.parse(native) == observed,
                    journal.parse(native),
                )
            if valid:
                # Shortened-candidate evidence cannot stand in for source journal.
                wrong_cert = journal.write(
                    folder / (mode + "-candidate-certificate.json"),
                    certificate(candidate[3]),
                )
                bad = journal.attempt([
                    physical_reference,
                    "admit" if actor == "trace" else "admit-entry",
                    source,
                    path,
                    profile,
                    wrong_cert,
                    *extra[2:],
                ])
                journal.check(
                    folder.name + ":source-certificate-" + mode,
                    bad.returncode > 0,
                    journal.parse(bad),
                )
        journal.check(
            folder.name + ":original-retained", source.read_bytes() == source_bytes
        )

    journal.write("costs.json", costs)
    if name == MEASURED:
        selected = [row for row in costs if row["case"] == "prepared-alias-True-trace"]
        journal.check(
            "lazy-demand-reduction",
            any(
                row["mode"] == "lazy" and row["before"] == 2 and row["after"] == 1
                for row in selected
            ),
            selected,
        )
        journal.check(
            "materialized-cost-retained",
            any(
                row["mode"] == "materialized" and row["before"] == row["after"] == 1
                for row in selected
            ),
            selected,
        )
    journal.save()
    assert not journal.failures, journal.failures


def test_a_changed_candidate_is_refused(journal, toolchain):
    """Well typed changes that look right under one input are still refused."""
    compiler, runtime, checker, physical_reference = tools(toolchain)
    # Well-typed changed candidates that look right under a selected input or a
    # dormant path are still refused against the original source.
    values = [
        ("a", F, 4, True),
        ("b", F, 4, True),
        ("r", F, 2, False),
        ("flag", BOOL, True, True),
        ("view", residual("f7", 1), [19, [1, 3], []], True),
        ("point", point("f7"), [], False),
    ]
    negatives = [
        ("distinct-endpoints-same-input", apply(LINEAR, [0, 1, 2], ret(0)), ret(0)),
        (
            "deleted-guard",
            apply(["evaluate", "f7", 1], [4, 5], apply(LINEAR, [1, 1, 3], ret(0))),
            ret(0),
        ),
        ("deleted-failed-call", apply(["abort_write", "f7"], [0], ret(1)), ret(0)),
        ("deleted-draw", apply(["draw"], [], ret(1)), ret(0)),
        (
            "dormant-branch",
            ["if", 3, ret(0), apply(LINEAR, [0, 1, 2], ret(0))],
            ["if", 3, ret(0), ret(0)],
        ),
        (
            "stale-loop-alias",
            ["repeat", 0, F, 0, apply(LINEAR, [0, 1, 3], ret(0)), ret(0)],
            ["repeat", 0, F, 0, ret(0), ret(0)],
        ),
    ]
    for name, body, wrong in negatives:
        folder = journal.directory / name
        folder.mkdir(parents=True, exist_ok=True)
        original = request(values, F, body)
        original[2] = "region-source-1"
        source = journal.write(folder / "source.json", original)
        surrogate = copy.deepcopy(original)
        surrogate[5] = wrong
        surrogate_path = journal.write(folder / "surrogate.json", surrogate)
        inputs = journal.write(folder / "inputs.json", invocation(values))
        for mode in ("lazy", "materialized"):
            produced = journal.attempt([
                compiler, "compile", surrogate_path, "--physical=" + mode
            ])
            path = folder / (mode + ".json")
            path.write_text(produced.stdout)
            rejected = journal.attempt([physical_reference, "check", source, path])
            journal.check(
                name + ":refused-" + mode,
                produced.returncode == 0
                and rejected.returncode > 0
                and names(rejected.stdout, "physical-source-mismatch"),
                journal.parse(rejected),
            )
            for layout in ("packed", "segmented"):
                result = journal.attempt([
                    runtime,
                    "run-physical",
                    source,
                    path,
                    inputs,
                    physical_reference,
                    "--storage",
                    layout,
                ])
                journal.check(
                    name + ":native-refused-" + mode + "-" + layout,
                    result.returncode > 0 and names(result.stdout, "check-not-established"),
                    journal.parse(result),
                )

    journal.save()
    assert not journal.failures, journal.failures
