"""The region cases three tests state their comparisons over.

Written cases each state a property. The generated ones beyond them look for a
disagreement the written ones did not think to ask for, from a fixed seed so
that the same sample is compared from run to run.

They live here because three tests use them. A test that imported them from
another test would make its own result depend on that test's shape.
"""

import copy
import random

from source import (BOOL, apply, executed, invocation, mle, point, request,
                    residual, ret, scalar, stopped)


# Every test that states a comparison over these cases starts by writing the
# same two files. The profile string is part of what a region case is, so it is
# set here rather than remembered separately by each test that forgets it once.
PROFILE = "region-source-1"


def written(journal, case, folder=None):
    """A case's source and its input, beside the rest of a test's evidence."""
    _, inputs, result, body, _, _, state = case
    folder = journal.directory if folder is None else folder
    source = request(inputs, result, body)
    source[2] = PROFILE
    return (journal.write(folder / "source.json", source),
            journal.write(folder / "inputs.json", invocation(inputs, state)))


def cases(random_cases):
    domain = "f7"
    inputs = [
        ("view", residual(domain, 1), [37, [1, 3], []], False),
        ("point", point(domain), [2], False),
        ("flag", BOOL, True, True),
    ]
    evaluate = ["evaluate", domain, 1]
    yield (
        "repeated-read",
        inputs,
        scalar(domain),
        apply(
            evaluate,
            [0, 1],
            apply(["add", domain], [0, 0], apply(["record", domain], [1], ret(2))),
        ),
        executed(5, [0, 5, 1, [], []], [["write", domain, 5]]),
        (4, 1),
        None,
    )
    yield (
        "unused",
        inputs,
        BOOL,
        apply(evaluate, [0, 1], ret(3)),
        executed(True),
        (0, 1),
        None,
    )
    invalid = copy.deepcopy(inputs)
    invalid[1] = ("point", point(domain), [], False)
    yield (
        "invalid-unused",
        invalid,
        BOOL,
        apply(evaluate, [0, 1], ret(3)),
        stopped("refused"),
        (0, 0),
        None,
    )
    yield (
        "failed-write",
        inputs,
        BOOL,
        apply(evaluate, [0, 1], apply(["abort_write", domain], [0], ret(0))),
        stopped("abort", [0, 5, 1, [], []], [["write", domain, 5]]),
        (1, 1),
        None,
    )
    yield (
        "exhausted-after-prepare",
        inputs,
        scalar(domain),
        apply(evaluate, [0, 1], apply(["draw"], [], ret(0))),
        stopped("exhausted"),
        (0, 1),
        None,
    )
    yield (
        "draw-state",
        inputs,
        scalar(domain),
        apply(
            evaluate,
            [0, 1],
            apply(["draw"], [], apply(["add", domain], [0, 1], ret(0))),
        ),
        executed(2, [0, 0, 0, [], [6]], [["drawn", 4]]),
        (1, 1),
        [0, 0, 0, [], [4, 6]],
    )
    yield (
        "send-then-abort",
        inputs,
        BOOL,
        apply(
            evaluate,
            [0, 1],
            apply(["send"], [0, 0], apply(["abort_write", domain], [1], ret(0))),
        ),
        stopped(
            "abort", [0, 5, 1, [[5, 5]], []], [["sent", 5, 5], ["write", domain, 5]]
        ),
        (3, 1),
        None,
    )
    two_points = inputs[:2] + [("second", point(domain), [1], True)]
    yield (
        "old-alias",
        two_points,
        scalar(domain),
        apply(evaluate, [0, 1], apply(evaluate, [1, 3], ret(1))),
        executed(5),
        (1, 2),
        None,
    )
    yield (
        "returned-original",
        inputs,
        residual(domain, 1),
        apply(evaluate, [0, 1], ret(1)),
        executed([37, [1, 3], []]),
        (0, 1),
        None,
    )
    # One shared suffix receives the branch's prepared value.
    body = [
        "bind",
        scalar(domain),
        ["if", 2, apply(evaluate, [0, 1], ret(0)), apply(evaluate, [0, 1], ret(0))],
        apply(["add", domain], [0, 0], ret(0)),
    ]
    yield "shared-branch", inputs, scalar(domain), body, executed(3), (2, 1), None
    # The body receives accumulator, outer prepared scalar, view, point, flag.
    body = apply(
        evaluate,
        [0, 1],
        [
            "repeat",
            4,
            scalar(domain),
            0,
            apply(evaluate, [2, 3], apply(["add", domain], [1, 0], ret(0))),
            ret(0),
        ],
    )
    yield "loop-preparation", inputs, scalar(domain), body, executed(4), (5, 5), None
    body = apply(
        evaluate,
        [0, 1],
        [
            "repeat",
            4,
            scalar(domain),
            0,
            apply(["abort_write", domain], [0], ret(1)),
            ret(0),
        ],
    )
    yield (
        "stopped-loop",
        inputs,
        scalar(domain),
        body,
        stopped("abort", [0, 5, 1, [], []], [["write", domain, 5]]),
        (1, 1),
        None,
    )
    rng = random.Random(81937)
    for i in range(random_cases):
        domain, modulus = rng.choice([("f2", 2), ("f7", 7)])
        rank = rng.randrange(6)
        cells = [rng.randrange(modulus) for _ in range(2**rank)]
        prefix_length = rng.randrange(rank + 1)
        prefix = [rng.randrange(modulus) for _ in range(prefix_length)]
        tail = [rng.randrange(modulus) for _ in range(rank - prefix_length)]
        valid = i % 7 != 0
        if not valid:
            tail.append(rng.randrange(modulus))
        inputs = [
            ("original", residual(domain, rank), [i + 100, cells, prefix], bool(i % 2)),
            ("tail", point(domain), tail, False),
            ("flag", BOOL, bool(i % 3), False),
        ]
        body = apply(
            ["evaluate", domain, rank],
            [0, 1],
            ret(3) if i % 4 == 0 else apply(["add", domain], [0, 0], ret(0)),
        )
        result = BOOL if i % 4 == 0 else scalar(domain)
        expected = (
            stopped("refused")
            if not valid
            else executed(
                bool(i % 3)
                if i % 4 == 0
                else 2 * mle(cells, prefix + tail, modulus) % modulus
            )
        )
        costs = (0, 0) if not valid else ((0, 1) if i % 4 == 0 else (2, 1))
        yield f"generated-{i}", inputs, result, body, expected, costs, None
