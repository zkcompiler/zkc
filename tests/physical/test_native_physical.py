#!/usr/bin/env python3
"""Actual MLIR physical plans against Lean, independent algebra and both Rust stores.

What this does not claim: native formal verification, an unbounded resource
guarantee, phase or endpoint coverage — `physical_admission` is that suite —
protocol security, or a speedup.

One case is one pytest case, so a failure is one case failing and a change to
one of them can be re-run by name rather than by running all of them.
"""

import copy
import json
from pathlib import Path

import pytest

from source import (
    BOOL,
    DIGEST,
    apply,
    executed,
    mle,
    point,
    residual,
    ret,
    scalar,
    stopped,
)
from region_cases import cases, written


# The two Lean references these cases are compared against. Which reference a
# test uses is part of what the test is, not of how it is invoked: the physical
# reference refuses a logical plan rather than disagreeing with it.
CHECKER = "table-protocol"
PHYSICAL = "table-physical-reference"

# Generated cases beyond the written ones, shared with the Lean-produced run.
RANDOM_CASES = 120

# The written cases the refusals and the capacity limit are stated over. A
# refusal is about a candidate that was well formed first.
BASELINE = "old-alias"
GUARDED = ("unused", "invalid-unused")
LOOPING = "loop-preparation"


def tools(toolchain):
    return (toolchain.compiler, toolchain.runtime,
            toolchain.checker(CHECKER), toolchain.checker(PHYSICAL))


def corpus():
    """The shared region cases, and the ones only this comparison asks for."""
    all_cases = list(cases(RANDOM_CASES))
    # A stopped path has no return value. It must not add a hypothetical lazy
    # rank (or maximal digest size) to the bound of a returning loop branch.
    for ty, operation, iterations, label in (
        (scalar("f7"), ["add", "f7"], 12, "scalar"),
        (["digest"], ["ordered_pair"], 3, "digest"),
    ):
        for count in (0, iterations):
            value = 1
            for _ in range(count):
                value = (
                    (value + 2) % 7
                    if label == "scalar"
                    else (4 + value if value < 2 else value * value + value + 2)
                )
            for flag in (False, True):
                all_cases.append(
                    (
                        f"stopped-branch-{label}-{count}-{flag}",
                        [
                            ("initial", ty, 1, True),
                            ("step", ty, 2, True),
                            ("flag", BOOL, flag, True),
                        ],
                        ty,
                        [
                            "repeat",
                            count,
                            ty,
                            0,
                            [
                                "if",
                                3,
                                ["stop", "reject"],
                                apply(operation, [0, 2], ret(0)),
                            ],
                            ret(0),
                        ],
                        stopped("reject") if flag and count else executed(value),
                        (0, 0),
                        None,
                    )
                )
    # Scalar-only entry/result coverage must not require a preparation cell.
    all_cases.append(
        (
            "scalar-input",
            [("x", scalar("f7"), 6, True)],
            scalar("f7"),
            ret(0),
            {
                "status": "executed",
                "outcome": ["returned", 6],
                "state": [0, 0, 0, [], []],
                "events": [],
            },
            (0, 0),
            None,
        )
    )
    for rank in (8, 10, 12):
        cells = [(3 * i + i // 7) % 7 for i in range(2**rank)]
        coordinates = [(2 * i + 1) % 7 for i in range(rank)]
        inputs = [
            ("view", residual("f7", rank), [93, cells, []], True),
            ("point", point("f7"), coordinates, False),
        ]
        value = mle(cells, coordinates, 7)
        all_cases.append(
            (
                f"rank-{rank}",
                inputs,
                scalar("f7"),
                apply(["evaluate", "f7", rank], [0, 1], ret(0)),
                executed(value),
                (1, 1),
                None,
            )
        )
    # A prepared scalar must remain usable by consumers besides add/record.
    all_cases.append(
        (
            "prepared-restriction",
            [
                ("view", residual("f7", 2), [31, [1, 2, 3, 4], []], True),
                ("point", point("f7"), [2, 1], False),
            ],
            scalar("f7"),
            apply(
                ["evaluate", "f7", 2],
                [0, 1],
                apply(
                    ["restrict", "f7", 2],
                    [1, 0],
                    apply(
                        ["endpoint_point", False],
                        [],
                        apply(["evaluate", "f7", 2], [1, 0], ret(0)),
                    ),
                ),
            ),
            executed(6),
            (2, 2),
            None,
        )
    )
    all_cases.append(
        (
            "prepared-point",
            [
                ("view", residual("f7", 1), [32, [1, 3], []], True),
                ("point", point("f7"), [2], False),
            ],
            scalar("f7"),
            apply(
                ["evaluate", "f7", 1],
                [0, 1],
                apply(["point"], [0], apply(["evaluate", "f7", 1], [2, 0], ret(0))),
            ),
            executed(4),
            (2, 2),
            None,
        )
    )
    all_cases.append(
        (
            "prepared-pack",
            [
                ("binary", residual("f2", 1), [33, [0, 1], []], True),
                ("binary-point", point("f2"), [1], False),
                ("prime", residual("f7", 1), [34, [1, 3], []], True),
                ("prime-point", point("f7"), [2], False),
                ("digest", DIGEST, 9, False),
            ],
            ["summary"],
            apply(
                ["evaluate", "f2", 1],
                [0, 1],
                apply(
                    ["evaluate", "f7", 1], [3, 4], apply(["pack"], [1, 0, 6], ret(0))
                ),
            ),
            executed([1, 5, 9]),
            (2, 2),
            None,
        )
    )
    return all_cases


CASES = corpus()


def native(journal, runtime, physical_reference, directory, candidate, layout,
           source=None, inputs=None, checker=None, *extra):
    """Run a physical candidate on the host, under one table storage layout."""
    return journal.attempt([
        runtime,
        "run-physical",
        source or directory / "source.json",
        candidate,
        inputs or directory / "inputs.json",
        checker or physical_reference,
        "--storage",
        layout,
        *extra,
    ])


def prepare(journal, compiler, wanted):
    """One written case as far as a lazy candidate the compiler produced, for a
    test that judges what the host refuses rather than what it computes."""
    case = next(one for one in CASES if one[0] == wanted)
    folder = journal.directory / wanted
    source, _ = written(journal, case, folder)
    journal.run([compiler, "compile", source, "--physical=lazy"],
                keep=folder / "lazy.json")
    return folder


@pytest.mark.parametrize("case", CASES, ids=[one[0] for one in CASES])
def test_a_native_physical_case_agrees(journal, toolchain, case):
    """One case, through MLIR, the physical reference and both table stores."""
    name, inputs, result, body, expected, costs, state = case
    compiler, runtime, checker, physical_reference = tools(toolchain)
    directory = journal.directory
    source, inputs_file = written(journal, case)
    direct = journal.attempt([compiler, "compile", source])
    direct_file = directory / "direct.json"
    direct_file.write_text(direct.stdout)
    reference = journal.attempt([checker, "run", source, direct_file, inputs_file])
    journal.check(
        "logical-oracle",
        direct.returncode == reference.returncode == 0
        and journal.parse(reference) == expected,
        journal.parse(reference),
    )
    for mode, count in zip(("lazy", "materialized"), costs, strict=True):
        produced = journal.attempt([compiler, "compile", source, "--physical=" + mode])
        candidate = directory / (mode + ".json")
        candidate.write_text(produced.stdout)
        journal.check("mlir-" + mode, produced.returncode == 0, produced.stderr)
        accepted = journal.attempt([physical_reference, "check", source, candidate])
        journal.check(
            "checked-" + mode,
            accepted.returncode == 0
            and journal.parse(accepted)
            == {
                "status": "checked",
                "claim": "complete-logical-execution",
                "realization": "table-physical-plan",
            },
            journal.parse(accepted),
        )
        physical = journal.attempt([physical_reference, "run", source, candidate, inputs_file])
        physical_json = journal.parse(physical)
        journal.write(directory / (mode + "-lean.json"), physical_json)
        journal.check(
            "physical-oracle-" + mode,
            physical.returncode == 0
            and physical_json.get("execution") == expected
            and physical_json.get("table-evaluations") == count,
            physical_json,
        )
        for layout in ("packed", "segmented"):
            actual = native(journal, runtime, physical_reference, directory, candidate, layout)
            report = journal.parse(actual)
            journal.write(directory / (mode + "-" + layout + ".json"), report)
            journal.check(
                "native-" + mode + "-" + layout,
                actual.returncode == 0 and report == physical_json,
                report,
            )
    journal.save()
    assert not journal.failures, journal.failures


def test_a_complete_table_round(journal, toolchain):
    """Send, draw, point construction, two endpoints and returned acceptance."""
    compiler, runtime, checker, physical_reference = tools(toolchain)
    directory = journal.directory
    # A complete selected table round exercises send, draw, point construction,
    # two endpoints and returned acceptance, beyond isolated evaluation cases.
    for name in ("source", "inputs"):
        journal.write(
            directory / (name + ".json"),
            json.loads(Path("examples/tables", name + ".json").read_text()),
        )
    for mode in ("lazy", "materialized"):
        candidate = directory / (mode + ".json")
        out = journal.attempt([
            compiler, "compile", directory / "source.json", "--physical=" + mode
        ])
        candidate.write_text(out.stdout)
        reference = journal.attempt([
            physical_reference,
            "run",
            directory / "source.json",
            candidate,
            directory / "inputs.json",
        ])
        journal.check(
            "table-round:" + mode,
            out.returncode == reference.returncode == 0
            and journal.parse(reference).get("execution", {}).get("outcome")
            == ["returned", True],
            journal.parse(reference),
        )
        for layout in ("packed", "segmented"):
            actual = native(journal, runtime, physical_reference, directory, candidate, layout)
            journal.write(directory / (mode + "-" + layout + ".json"), journal.parse(actual))
            journal.check(
                "table-round:" + mode + "-" + layout,
                actual.returncode == 0 and journal.parse(actual) == journal.parse(reference),
                journal.parse(actual),
            )

    journal.save()
    assert not journal.failures, journal.failures


def test_the_host_refuses(journal, toolchain):
    """What a candidate has to be, stated over cases that already are ones."""
    compiler, runtime, checker, physical_reference = tools(toolchain)
    base = prepare(journal, compiler, BASELINE)
    good = json.loads((base / "lazy.json").read_text())
    for label in ("mixed", "eager"):
        changed = copy.deepcopy(good)
        if label == "mixed":
            changed[3][3][1][1] = "materialized"
        else:
            changed[3][1] = ["invoke", ["evaluate", "f7", 1]]
            changed[3][3][1] = ["invoke", ["evaluate", "f7", 1]]
        candidate = journal.write(base / (label + ".json"), changed)
        reference = journal.attempt([
            physical_reference, "run", base / "source.json", candidate, base / "inputs.json"
        ])
        for layout in ("packed", "segmented"):
            actual = native(journal, runtime, physical_reference, base, candidate, layout)
            journal.check(
                label + ":" + layout,
                reference.returncode == actual.returncode == 0
                and journal.parse(actual) == journal.parse(reference),
                journal.parse(actual),
            )
    mutants = {}
    for label, alter in [
        ("changed-result", lambda p: p[3][3].__setitem__(3, ret(0))),
        ("changed-point", lambda p: p[3].__setitem__(2, [0, 2])),
        ("unknown-mode", lambda p: p[3][1].__setitem__(1, "unknown")),
        ("context-role", lambda p: p[2].__setitem__(0, "other")),
        ("uninstalled-library", lambda p: p[2].__setitem__(3, [["uninstalled", "1"]])),
        ("cross-domain", lambda p: p[3][1].__setitem__(2, "f2")),
        ("unknown-version", lambda p: p.__setitem__(1, 2)),
        ("reference-only", lambda p: p.__setitem__(0, "zkc-table-physical-reference")),
    ]:
        p = copy.deepcopy(good)
        alter(p)
        mutants[label] = journal.write(base / (label + ".json"), p)
    for label, candidate in mutants.items():
        for layout in ("packed", "segmented"):
            refused = native(journal, runtime, physical_reference, base, candidate, layout)
            report = journal.parse(refused)
            journal.check(
                label + ":" + layout,
                refused.returncode > 0 and report.get("status") == "refused",
                report,
            )
    for label in GUARDED:
        directory = prepare(journal, compiler, label)
        candidate = json.loads((directory / "lazy.json").read_text())
        candidate[3] = ret(2)
        path = journal.write(directory / "deleted-guard.json", candidate)
        refused = native(journal, runtime, physical_reference, directory, path, "packed")
        journal.check(label + ":deleted-guard", refused.returncode > 0, journal.parse(refused))
    # A direct checker cannot acknowledge the physical execution claim.
    refused = native(journal, runtime, physical_reference, base, base / "lazy.json", "packed", checker=checker)
    journal.check("wrong-checker", refused.returncode > 0, journal.parse(refused))
    # Phase and endpoint admission have their own maintained physical_admission.py suite.
    journal.save()
    assert not journal.failures, journal.failures


def test_the_host_keeps_its_own_capacity(journal, toolchain):
    """An accepted reference execution is not the host's finite capacity."""
    compiler, runtime, checker, physical_reference = tools(toolchain)
    looping = prepare(journal, compiler, LOOPING)
    # Accepted-reference execution is distinct from the host's finite capacity.
    directory = journal.directory / "capacity"
    directory.mkdir(parents=True, exist_ok=True)
    source_json = json.loads((looping / "source.json").read_text())
    source_json[5][3][1] = 10**80
    source = journal.write(directory / "source.json", source_json)
    inputs_file = journal.write(
        directory / "inputs.json",
        json.loads((looping / "inputs.json").read_text()),
    )
    candidate = directory / "plan.json"
    produced = journal.attempt([compiler, "compile", source, "--physical=materialized"])
    candidate.write_text(produced.stdout)
    accepted = journal.attempt([physical_reference, "check", source, candidate])
    journal.check(
        "capacity:mathematical-check",
        produced.returncode == accepted.returncode == 0,
        journal.parse(accepted),
    )
    for layout in ("packed", "segmented"):
        refused = native(journal, runtime, physical_reference, directory, candidate, layout, inputs=inputs_file)
        report = journal.parse(refused)
        execution = report.get("execution", {})
        journal.check(
            "capacity:host-refusal-" + layout,
            execution.get("status") == "start-failed"
            and execution.get("code") == "capacity-limit"
            and execution.get("events") == []
            and execution.get("state") == [0, 0, 0, [], []]
            and report.get("scalar-cells") == report.get("table-evaluations") == 0,
            report,
        )
    # Changing a dormant loop body must be checked, even though it never executes.
    directory = journal.directory / "dormant"
    directory.mkdir(parents=True, exist_ok=True)
    source_json[5][3][1] = 0
    source = journal.write(directory / "source.json", source_json)
    journal.write(directory / "inputs.json", json.loads(inputs_file.read_text()))
    out = journal.attempt([compiler, "compile", source, "--physical=lazy"])
    target = journal.parse(out)
    target[3][3][4] = ["return", 0]
    candidate = journal.write(directory / "changed-body.json", target)
    refused = native(journal, runtime, physical_reference, directory, candidate, "packed")
    journal.check("dormant:changed-body", refused.returncode > 0, journal.parse(refused))
    journal.save()
    assert not journal.failures, journal.failures
