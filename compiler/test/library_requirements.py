"""Native requirement derivations against every finite model of each
enumerable problem.

The largest problem has a hundred and twenty-eight terms; the engine answers
it, but its partitions cannot be enumerated, so only that it is answered at
all is checked here.

What the independent Lean checker makes of the certificates the engine derives
is a separate test, tests/protocol/test_library_requirements_reference.py, because
it needs another build. The problems both of them answer are generated in one
place, tests/support/requirement_problems.py.
"""

import copy
import json
from requirement_problems import principal, problems
from commands import Commands
from tools import records, requirements_test


commands = Commands(records())


def run(program, value, success=True):
    """The answer read as JSON, or what the refusal itself said."""
    printed = commands.run([program], stdin=json.dumps(value) + "\n",
                           refuses=None if success else True)
    return json.loads(printed) if success else commands.last


def partitions(size):
    """Every partition of a finite identity universe, in restricted-growth order."""
    if size == 0:
        yield ()
        return

    def extend(prefix):
        if len(prefix) == size:
            yield tuple(prefix)
        else:
            for value in range(max(prefix) + 2):
                yield from extend([*prefix, value])

    yield from extend([0])


def model_answers(problem):
    _, terms, assumptions, rules, goals = problem
    answers = [True] * len(goals)
    models = 0
    for identity in partitions(len(terms)):
        # Associated members are actual functions of identity in each model.
        members = {}
        for child, term in enumerate(terms):
            if len(term) == 3:
                _, name, arguments = term
                key = "apply", name, tuple(identity[a] for a in arguments)
            elif term[0] is not None:
                parent, name = term
                key = "project", identity[parent], name
            else:
                continue
            if key in members and members[key] != identity[child]:
                break
            members[key] = identity[child]
        else:
            if any(name == "=" and identity[args[0]] != identity[args[1]]
                   for name, args in assumptions):
                continue
            facts = {(name, tuple(identity[a] for a in args))
                     for name, args in assumptions if name != "="}
            # Least relational model for positive unary implications. This
            # search ranges over all identity partitions, not requirements_test closure.
            while True:
                added = {(b, args) for a, b in rules for name, args in facts
                         if name == a and len(args) == 1}
                if added <= facts:
                    break
                facts |= added
            models += 1
            for i, (name, args) in enumerate(goals):
                value = (identity[args[0]] == identity[args[1]] if name == "="
                         else (name, tuple(identity[a] for a in args)) in facts)
                answers[i] &= value
    assert models, "uninterpreted positive requirements have a model"
    return answers, models


def main():
    count = models = 0

    for problem, enumerable in problems():
        result = run(requirements_test, problem)
        version = problem[0].rsplit("/", 1)[1]
        assert result[0] == f"zkc.requirements-certificate/{version}"
        answers = [proof is not None for proof in result[2]]
        if enumerable:
            expected, samples = model_answers(problem)
            assert answers == expected, (problem, answers, expected)
            models += samples
        count += 1
        if count == 1:
            assert answers == [True, True, False, True, False, True, True], answers

    # A declaration that is not one is refused rather than answered.
    for section, invalid in [
        (1, [[0, "Self"]]), (1, [[None, "T"], [None, "T"]]),
        (1, [[None, ""]]), (2, [["=", [0]]]), (2, [["=", [0, 100]]]),
        (3, [["", "Field"]]), (3, [["A", "="]]), (3, [["=", "A"]]),
    ]:
        bad = copy.deepcopy(principal())
        bad[section] = invalid
        run(requirements_test, bad, False)

    print(f"library requirements: {count} problems decided against {models} "
          "enumerated identity models")


if __name__ == "__main__":
    main()
