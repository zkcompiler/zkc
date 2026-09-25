"""A refusal is an ordinary exit with a nonzero status, never a signal.

The shared runners (`tests/support/journal.py`, `tests/support/differential.py`)
already treat a child killed by a signal as a failure of the test, not as the
refusal it asserted. An assertion written directly against an exit status must
say the same: `returncode > 0` for a refusal, `returncode == 0` or
`not returncode` for success. `returncode != 0` and a bare `returncode` used as
a truth value also accept a crash, whose status is negative.
"""

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TREES = ("tests", "compiler/test", "crates", "formal/checks", "formal/consumers")


def status(node):
    return isinstance(node, ast.Attribute) and node.attr == "returncode"


def zero(node):
    return isinstance(node, ast.Constant) and node.value == 0 and not isinstance(node.value, bool)


def loose(test):
    """Each part of an assertion that also accepts a signal death."""
    found = []
    # A bare status is loose where its truth value is the assertion: the whole
    # test, or an operand of `and`/`or`. Under `not` it asserts success.
    for node in [test] + [value for n in ast.walk(test) if isinstance(n, ast.BoolOp)
                          for value in n.values]:
        if status(node):
            found.append(node)
    for node in ast.walk(test):
        if isinstance(node, ast.Compare):
            sides = [node.left, *node.comparators]
            for op, left, right in zip(node.ops, sides, sides[1:]):
                if isinstance(op, ast.NotEq) and ((status(left) and zero(right))
                                                  or (zero(left) and status(right))):
                    found.append(node)
    return found


def sources():
    for tree in TREES:
        for path in sorted((ROOT / tree).rglob("*.py")):
            if "target" not in path.relative_to(ROOT).parts:
                yield path


def test_refusal_assertions_require_an_ordinary_exit():
    violations = []
    for path in sources():
        tree = ast.parse(path.read_text(), str(path))
        # A comparison with zero is loose wherever it decides an outcome, as in
        # a journal check; a bare status only where an assertion rests on it.
        parts = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Assert):
                parts += [part for part in loose(node.test) if status(part)]
            elif isinstance(node, ast.Compare):
                parts += loose(node)
        violations += sorted({f"{path.relative_to(ROOT)}:{part.lineno}" for part in parts})
    assert not violations, (
        "assert a refusal as `returncode > 0`; these also accept a signal death:\n"
        + "\n".join(violations))


def test_the_rule_distinguishes_refusal_from_crash():
    def parts(text):
        return len(loose(ast.parse(text).body[0].test))

    assert parts("assert result.returncode != 0") == 1
    assert parts("assert 0 != result.returncode") == 1
    assert parts("assert result.returncode") == 1
    assert parts("assert result.returncode and 'x' in result.stderr") == 1
    assert parts("assert result.returncode > 0 and 'x' in result.stderr") == 0
    assert parts("assert not result.returncode, result.stderr") == 0
    assert parts("assert result.returncode == 0") == 0
    assert parts("assert result.returncode in (0, 1)") == 0
