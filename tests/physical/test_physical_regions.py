#!/usr/bin/env python3
"""Compare checked physical Lean regions with logical Lean and a Rust baseline.

The physical candidate producer is Lean in this unit. MLIR exports the direct
baseline only. Complete outcomes, residual provider state and ordered events are
compared; the table oracle independently sums the Boolean basis.

What this does not claim: native physical lowering or execution, a native memory
or cost theorem, a speedup, phase transport, protocol security, or an
independent kernel or provider implementation.

One region case is one pytest case, so a failure is one case failing and a
change to one of them can be re-run by name in a second rather than by running
all of them.
"""

import copy
import json

import pytest

from source import executed, invocation, request, ret

from region_cases import cases


# The two Lean references these cases are compared against. Which reference a
# test uses is part of what the test is, not of how it is invoked: the physical
# reference refuses a logical plan rather than disagreeing with it.
CHECKER = "table-protocol"
PHYSICAL = "table-physical-reference"

# Generated cases beyond the written ones. The written cases state a property;
# these look for a disagreement the written ones did not think to ask for.
RANDOM_CASES = 120

CASES = list(cases(RANDOM_CASES))

# The written case the refusals are stated over. A refusal is about a candidate
# that was well formed first.
BASELINE = "old-alias"


def tools(toolchain):
    return (toolchain.compiler, toolchain.runtime,
            toolchain.checker(CHECKER), toolchain.checker(PHYSICAL))


def prepare(journal, compiler, physical_reference, wanted):
    """One written case as far as a well formed lazy candidate, for a test that
    judges what the reference refuses rather than what it computes."""
    name, inputs, result, body, _, _, state = next(c for c in CASES if c[0] == wanted)
    folder = journal.directory / name
    source_value = request(inputs, result, body)
    source_value[2] = "region-source-1"
    source = journal.write(folder / "source.json", source_value)
    journal.write(folder / "inputs.json", invocation(inputs, state))
    journal.run([compiler, "compile", source], keep=folder / "direct.json")
    journal.run([physical_reference, "lower", "lazy", source],
                keep=folder / "lazy.json")
    return folder, source


@pytest.mark.parametrize("case", CASES, ids=[one[0] for one in CASES])
def test_a_region_case_agrees(journal, toolchain, case):
    """One case, through MLIR, the logical reference and the physical one."""
    name, inputs, result, body, expected, expected_costs, state = case
    compiler, runtime, checker, physical_reference = tools(toolchain)
    costs = []
    directory = journal.directory
    source_value = request(inputs, result, body)
    source_value[2] = "region-source-1"
    source = journal.write(directory / "source.json", source_value)
    invocation_file = journal.write(directory / "inputs.json", invocation(inputs, state))
    direct = journal.attempt([compiler, "compile", source])
    (directory / "direct.json").write_text(direct.stdout)
    journal.check("mlir-direct", direct.returncode == 0, direct.stderr)
    logical = journal.attempt(
        [checker, "run", source, directory / "direct.json", invocation_file]
    )
    reference = journal.parse(logical)
    journal.write(directory / "logical.json", reference)
    journal.check(
        "independent-algebra",
        logical.returncode == 0 and reference == expected,
        reference,
    )
    for mode, expected_cost in zip(
        ("lazy", "materialized"), expected_costs, strict=True
    ):
        candidate = directory / (mode + ".json")
        produced = journal.attempt([physical_reference, "lower", mode, source])
        candidate.write_text(produced.stdout)
        journal.check("produce-" + mode, produced.returncode == 0, produced.stderr)
        accepted = journal.attempt([physical_reference, "check", source, candidate])
        journal.check("check-" + mode, accepted.returncode == 0, accepted.stdout)
        executed_result = journal.attempt(
            [physical_reference, "run", source, candidate, invocation_file]
        )
        physical = journal.parse(executed_result)
        journal.write(directory / (mode + "-execution.json"), physical)
        journal.check(
            "execution-" + mode,
            executed_result.returncode == 0
            and physical.get("execution") == reference,
            physical,
        )
        journal.check(
            "cost-" + mode,
            physical.get("table-evaluations") == expected_cost,
            physical,
        )
        costs.append(
            {
                "case": name,
                "mode": mode,
                "evaluations": physical.get("table-evaluations"),
                "cells": physical.get("scalar-cells"),
            }
        )
    if not name.startswith("generated-"):
        for storage in ("packed", "segmented"):
            native = journal.attempt(
                [
                    runtime,
                    "run",
                    source,
                    directory / "direct.json",
                    invocation_file,
                    checker,
                    "--storage",
                    storage,
                ]
            )
            report = journal.parse(native)
            journal.write(directory / (storage + ".json"), report)
            journal.check(
                "rust-direct-" + storage,
                native.returncode == 0 and report == reference,
                report,
            )

    journal.write("costs.json", costs)
    journal.save()
    assert not journal.failures, journal.failures


def test_the_physical_reference_refuses(journal, toolchain):
    """What a candidate has to be, stated over cases that already are ones."""
    compiler, runtime, checker, physical_reference = tools(toolchain)
    base, source = prepare(journal, compiler, physical_reference, BASELINE)
    good = json.loads((base / "lazy.json").read_text())
    # Different preparation sites may make independent choices.
    mixed = copy.deepcopy(good)
    mixed[3][3][1][1] = "materialized"
    mixed_file = journal.write(base / "mixed.json", mixed)
    mixed_run = journal.attempt([physical_reference, "run", source, mixed_file, base / "inputs.json"])
    mixed_result = journal.parse(mixed_run)
    journal.check(
        "mixed-site-choice",
        mixed_run.returncode == 0
        and mixed_result.get("execution") == executed(5)
        and mixed_result.get("table-evaluations") == 2,
        mixed_result,
    )
    eager = copy.deepcopy(good)
    eager[3][1] = ["invoke", ["evaluate", "f7", 1]]
    eager[3][3][1] = ["invoke", ["evaluate", "f7", 1]]
    eager_file = journal.write(base / "eager.json", eager)
    eager_run = journal.attempt([physical_reference, "run", source, eager_file, base / "inputs.json"])
    eager_result = journal.parse(eager_run)
    journal.check(
        "ordinary-eager-invocation",
        eager_run.returncode == 0
        and eager_result.get("execution") == executed(5)
        and eager_result.get("table-evaluations") == 2
        and eager_result.get("scalar-cells") == 0,
        eager_result,
    )
    mutants = {}
    changed = copy.deepcopy(good)
    changed[3][3][3] = ret(0)
    mutants["changed-result"] = changed
    changed = copy.deepcopy(good)
    changed[3][1][1] = "unknown"
    mutants["unknown-mode"] = changed
    changed = copy.deepcopy(good)
    changed[3][2] = [0, 2]
    mutants["changed-point"] = changed
    changed = copy.deepcopy(good)
    changed[3][1][2] = "f2"
    mutants["cross-domain"] = changed
    changed = copy.deepcopy(good)
    changed[2][0] = "other-role"
    mutants["context-role"] = changed
    changed = copy.deepcopy(good)
    changed[2][3] = [["unknown", "1"]]
    mutants["context-library"] = changed
    changed = copy.deepcopy(good)
    changed[1] = 2
    mutants["profile-version"] = changed
    changed = copy.deepcopy(good)
    changed.append("extra")
    mutants["extra-field"] = changed
    expected_codes = {
        "changed-result": "physical-source-mismatch",
        "unknown-mode": "unknown-operation",
        "changed-point": "physical-source-mismatch",
        "cross-domain": "malformed-physical-region",
        "context-role": "context-mismatch",
        "context-library": "context-mismatch",
        "profile-version": "invalid-shape",
        "extra-field": "invalid-shape",
    }
    for name, mutant in mutants.items():
        path = journal.write(name + ".json", mutant)
        refused = journal.attempt([physical_reference, "check", source, path])
        journal.check(
            name + ":refused",
            refused.returncode == 1
            and journal.parse(refused) == {"status": "refused", "code": expected_codes[name]},
            journal.parse(refused),
        )
    for case, replacement in [("unused", ret(2)), ("invalid-unused", ret(2))]:
        directory, _ = prepare(journal, compiler, physical_reference, case)
        changed = json.loads((directory / "lazy.json").read_text())
        changed[3] = replacement
        path = journal.write(directory / "deleted-guard.json", changed)
        refused = journal.attempt([physical_reference, "check", directory / "source.json", path])
        journal.check(
            case + ":deleted-guard-refused",
            refused.returncode == 1
            and journal.parse(refused).get("code") == "physical-source-mismatch",
            journal.parse(refused),
        )
    # Both source grammars bind the same actual logical context.
    finite = json.loads(source.read_text())
    finite[2] = "finite-source-1"
    finite_file = journal.write(base / "finite-source.json", finite)
    finite_run = journal.attempt(
        [physical_reference, "run", finite_file, base / "lazy.json", base / "inputs.json"]
    )
    journal.check(
        "finite-source-bridge",
        finite_run.returncode == 0
        and journal.parse(finite_run).get("execution") == executed(5),
        journal.parse(finite_run),
    )
    unknown = copy.deepcopy(finite)
    unknown[3][3] = [["uninstalled", "1"]]
    unknown_file = journal.write(base / "unknown-source.json", unknown)
    unknown_run = journal.attempt([physical_reference, "lower", "lazy", unknown_file])
    journal.check(
        "uninstalled-source-library",
        unknown_run.returncode == 1
        and journal.parse(unknown_run).get("code") == "unresolved-dependency",
        journal.parse(unknown_run),
    )
    wrong_mode = journal.attempt([physical_reference, "lower", "automatic", source])
    journal.check(
        "unknown-producer-mode",
        wrong_mode.returncode == 1
        and journal.parse(wrong_mode).get("code") == "unsupported-preparation-mode",
        journal.parse(wrong_mode),
    )
    missing = json.loads((base / "inputs.json").read_text())
    missing[0] = missing[0][:-1]
    missing_file = journal.write(base / "missing-input.json", missing)
    missing_run = journal.attempt([physical_reference, "run", source, base / "lazy.json", missing_file])
    journal.check(
        "missing-input",
        missing_run.returncode == 1
        and journal.parse(missing_run).get("code") == "missing-input",
        journal.parse(missing_run),
    )
    # Profile separation in both directions: direct receipts never grant physical execution.
    direct_to_physical = journal.attempt([physical_reference, "check", source, base / "direct.json"])
    physical_to_direct = journal.attempt(
        [
            runtime,
            "run",
            source,
            base / "lazy.json",
            base / "inputs.json",
            checker,
        ]
    )
    journal.check(
        "direct-profile-refused",
        direct_to_physical.returncode == 1,
        journal.parse(direct_to_physical),
    )
    journal.check(
        "physical-profile-not-native",
        physical_to_direct.returncode > 0,
        journal.parse(physical_to_direct),
    )
    journal.save()
    assert not journal.failures, journal.failures
