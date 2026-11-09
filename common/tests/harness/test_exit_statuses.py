"""A refusal is an ordinary exit with a nonzero status, never a signal.

The shared journal (`common/tests/support/journal.py`)
already treats a child killed by a signal as a failure of the test, not as the
refusal it asserted. An assertion written directly against an exit status must
say the same: `returncode > 0` for a refusal, `returncode == 0` or
`not returncode` for success. `returncode != 0` and a bare `returncode` used as
a truth value also accept a crash, whose status is negative.
"""

import ast
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
TREES = ("common/tests", "compiler/test", "crates", "lean/checks", "lean/consumers")


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


def refusal_assertions(tree):
    # Returning the identical subprocess result propagates a signal as failure;
    # it does not turn that signal into an asserted ordinary refusal.
    propagated = set()
    for node in ast.walk(tree):
        if (isinstance(node, ast.If) and isinstance(node.test, ast.Compare)
                and len(node.test.ops) == 1 and isinstance(node.test.ops[0], ast.NotEq)
                and len(node.body) == 1 and isinstance(node.body[0], ast.Return)
                and not node.orelse):
            left, right = node.test.left, node.test.comparators[0]
            candidate = left if status(left) and zero(right) else right if status(right) and zero(left) else None
            returned = node.body[0].value
            if candidate is not None and returned is not None and ast.dump(candidate.value) == ast.dump(returned):
                propagated.add(node.test)
    parts = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Assert):
            parts += [part for part in loose(node.test) if status(part)]
        elif isinstance(node, ast.Compare) and node not in propagated:
            parts += loose(node)
    return parts


def test_refusal_assertions_require_an_ordinary_exit():
    violations = []
    for path in sources():
        tree = ast.parse(path.read_text(), str(path))
        # A comparison with zero is loose wherever it decides an outcome, as in
        # a journal check; a bare status only where an assertion rests on it.
        parts = refusal_assertions(tree)
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


@pytest.mark.parametrize("body,expected", [
    ("if result.returncode != 0:\n return result", 0),
    ("if 0 != result.returncode:\n return result", 0),
    ("if result.returncode != 0:\n return other", 1),
    ("if result.returncode != 0:\n return 0", 1),
    ("if result.returncode != 0:\n return result\nelse:\n accept()", 1),
    ("if result.returncode != 0:\n accept()", 1),
    ("assert result.returncode != 0", 1),
    ("journal.check(result.returncode != 0)", 1),
])
def test_only_exact_result_propagation_is_exempt(body, expected):
    assert len(refusal_assertions(ast.parse("def run():\n " + body.replace("\n", "\n ")))) == expected
