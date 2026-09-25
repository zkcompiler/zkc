"""Direct-plan metadata refusals agree between the Lean checker and the runtime.

docs/spec/profiles/compiler/direct-plan.md decodes a request and its candidate,
then applies ten ordered tests and names the first that fails. Each case below
changes one field of a compiled plan or of its request, or two where the order
between them is the point, and both readers must refuse with the same code.
"""

import copy
import json

import pytest

from source import invocation, request, ret, scalar

F = scalar("f7")
INPUTS = [("x", F, 3, False), ("y", F, 4, False)]
REQUIREMENT = ["extra", "1"]


def plan(index, value):
    return lambda source, candidate: candidate.__setitem__(index, value)


def asked(index, value):
    return lambda source, candidate: source.__setitem__(index, value)


def shared_context(change):
    """Change the request's context and give the candidate the same one."""
    def apply(source, candidate):
        change(source[3])
        candidate[7] = copy.deepcopy(source[3])
    return apply


def permitted(source, candidate):
    source[4] = [REQUIREMENT]
    candidate[8] = [REQUIREMENT]


def mismatched_with_requirement(source, candidate):
    candidate[7][0] = "other"
    candidate[8] = [REQUIREMENT]


CASES = {
    "plan-tag": (plan(0, "zkc-plan-2"), "invalid-shape"),
    "plan-format": (plan(1, 2), "unsupported-format-version"),
    "plan-format-text": (plan(1, "1"), "expected-natural"),
    "plan-semantics": (plan(2, "region-source-1"), "unsupported-semantics-version"),
    "capability": (plan(3, ["tables"]), "unsupported-capability"),
    "realization": (plan(4, "other"), "unsupported-realization"),
    "rule": (plan(5, "other"), "unsupported-rule"),
    "claim": (plan(6, ["equality", "outcome", "all-inputs-and-handlers"]), "unsupported-claim"),
    "context": (lambda source, candidate: candidate[7].__setitem__(0, "other"),
                "context-mismatch"),
    "duplicate-input": (shared_context(lambda c: c[1][1].__setitem__(0, c[1][0][0])),
                        "invalid-context"),
    "input-of-another-role": (shared_context(lambda c: c[1][0].__setitem__(2, ["private", "other"])),
                              "invalid-context"),
    "empty-role": (shared_context(lambda c: c.__setitem__(0, "")), "invalid-context"),
    "unapproved-requirement": (plan(8, [REQUIREMENT]), "unapproved-requirement"),
    "permitted-requirement": (permitted, "unsupported-requirement"),
    "context-before-requirement": (mismatched_with_requirement, "context-mismatch"),
    "request-tag": (asked(0, "zkc-request-2"), "invalid-shape"),
    "request-version": (asked(1, 2), "invalid-shape"),
    "request-version-text": (asked(1, "1"), "expected-natural"),
    "request-semantics-type": (asked(2, 7), "expected-string"),
    "request-semantics": (asked(2, "future-source-1"), "invalid-shape"),
    "input-kind": (shared_context(lambda c: c[1][0].__setitem__(3, "other")), "invalid-shape"),
    "candidate-input-type": (lambda s, c: c[7][1][0].__setitem__(1, ["nonsense"]), "unknown-type"),
    "candidate-result-type": (lambda s, c: c[7].__setitem__(2, ["nonsense"]), "unknown-type"),
    "request-input-type": (lambda s, c: s[3][1][0].__setitem__(1, ["nonsense"]), "unknown-type"),
    "request-result-type": (lambda s, c: s[3].__setitem__(2, ["nonsense"]), "unknown-type"),
}


@pytest.mark.parametrize("name", CASES)
def test_the_first_failing_metadata_test_names_the_refusal(toolchain, journal, directory, name):
    change, code = CASES[name]
    source = request(INPUTS, F, ret(0))
    compiled = json.loads(journal.run([toolchain.compiler, "compile",
                                       journal.write(directory / "source.json", source)]))
    changed_source, candidate = copy.deepcopy(source), copy.deepcopy(compiled)
    change(changed_source, candidate)
    s = journal.write(directory / "changed-source.json", changed_source)
    p = journal.write(directory / "changed-plan.json", candidate)
    i = journal.write(directory / "inputs.json", invocation(INPUTS))
    checker = toolchain.checker("table-protocol")
    for command in ([checker, "check", s, p], [toolchain.runtime, "run", s, p, i, checker]):
        result = journal.attempt(command)
        assert result.returncode == 1, (command, result.stdout, result.stderr)
        assert json.loads(result.stdout) == {"status": "refused", "code": code}, (command, result.stdout)


def test_the_unchanged_plan_is_accepted(toolchain, journal, directory):
    source = journal.write(directory / "source.json", request(INPUTS, F, ret(0)))
    p = journal.write(directory / "plan.json",
                      json.loads(journal.run([toolchain.compiler, "compile", source])))
    i = journal.write(directory / "inputs.json", invocation(INPUTS))
    checker = toolchain.checker("table-protocol")
    journal.run([checker, "check", source, p])
    journal.run([toolchain.runtime, "run", source, p, i, checker])


@pytest.mark.parametrize("side", ["source", "candidate"])
@pytest.mark.parametrize("position", ["input", "result"])
def test_physical_context_types_are_decoded_before_comparison(toolchain, journal, side, position):
    source = request(INPUTS, F, ret(0))
    s = journal.write("source.json", source)
    candidate = json.loads(journal.run([toolchain.compiler, "compile", s, "--physical=lazy"]))
    context = source[3] if side == "source" else candidate[2]
    if position == "input":
        context[1][0][1] = ["nonsense"]
    else:
        context[2] = ["nonsense"]
    s = journal.write("changed-source.json", source)
    p = journal.write("changed-plan.json", candidate)
    i = journal.write("inputs.json", invocation(INPUTS))
    checker = toolchain.checker("table-physical-reference")
    for command in ([checker, "check", s, p], [toolchain.runtime, "run-physical", s, p, i, checker]):
        result = journal.attempt(command)
        assert result.returncode == 1, (command, result.stdout, result.stderr)
        assert json.loads(result.stdout) == {"status": "refused", "code": "unknown-type"}
