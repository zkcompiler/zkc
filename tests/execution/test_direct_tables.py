"""Actual MLIR, a checked plan and Rust execution against the Lean reference.

Each case states a source, the values it is invoked with and the complete result
every implementation of it owes. The native path and the independently written
Lean model must agree, and where the answer is also known in closed form the
case states that too, so agreement with a wrong implementation is not mistaken
for correctness.
"""

import copy
import json
import random

import pytest
from differential import Refused
from source import (
    BOOL,
    DIGEST,
    apply,
    executed,
    invocation,
    mle,
    pair,
    point,
    refused,
    request,
    residual,
    ret,
    scalar,
    stop,
    stopped,
    table,
)

DOMAINS = [("f2", 2), ("f7", 7)]


def evaluation(domain, arity, cells, coordinates):
    """A source that views a table and evaluates it at a point."""
    return (
        [
            ("table", table(domain, arity), [17, cells], True),
            ("point", point(domain), coordinates, False),
        ],
        apply(["view", domain, arity], [0],
              apply(["evaluate", domain, arity], [0, 2], ret(0))),
    )


@pytest.mark.parametrize("domain,modulus", DOMAINS)
@pytest.mark.parametrize("arity", range(4))
def test_evaluation_agrees_with_the_boolean_sum(run, domain, modulus, arity):
    cells = [i % modulus for i in range(1 << arity)]
    coordinates = [(i + 2) % modulus for i in range(arity)]
    inputs, body = evaluation(domain, arity, cells, coordinates)
    case = run()
    plan = case.compile(inputs, scalar(domain), body)
    assert plan[9] == body, "the direct candidate must carry the actual source body"
    assert case.both() == executed(mle(cells, coordinates, modulus))


@pytest.mark.parametrize("domain,modulus", DOMAINS)
@pytest.mark.parametrize("arity", range(4))
def test_a_point_of_the_wrong_length_is_refused(run, domain, modulus, arity):
    cells = [i % modulus for i in range(1 << arity)]
    coordinates = [(i + 2) % modulus for i in range(arity)]
    inputs, body = evaluation(domain, arity, cells, coordinates)
    wrong = copy.deepcopy(inputs)
    wrong[1] = ("point", point(domain), coordinates + [0], False)
    case = run()
    case.compile(wrong, scalar(domain), body)
    assert case.both() == stopped("refused")


PREFIX_INPUTS = [
    ("table", table("f7", 2), [11, [0, 1, 2, 4]], True),
    ("coordinate", scalar("f7"), 2, False),
    ("suffix", point("f7"), [], False),
]


def test_a_loop_grows_the_fixed_prefix(run):
    body = apply(["view", "f7", 2], [0], [
        "repeat", 2, residual("f7", 2), 0,
        apply(["restrict", "f7", 2], [0, 3], ret(0)),
        apply(["evaluate", "f7", 2], [0, 4], ret(0)),
    ])
    case = run()
    case.compile(PREFIX_INPUTS, scalar("f7"), body)
    assert case.both() == executed(3)


def test_restriction_leaves_the_original_view_usable(run):
    body = apply(["view", "f7", 2], [0],
                 apply(["restrict", "f7", 2], [0, 2], ret(1)))
    case = run()
    case.compile(PREFIX_INPUTS, residual("f7", 2), body)
    assert case.both() == executed([11, [0, 1, 2, 4], []])


@pytest.mark.parametrize(
    "reason", ["reject", "abort", "exhausted", "incomplete", "refused"])
def test_an_explicit_stop_keeps_its_reason(run, reason):
    case = run()
    case.compile([], BOOL, stop(reason))
    assert case.both() == stopped(reason)


COUNTER_INPUTS = [
    ("initial", scalar("f2"), None, False),
    ("increment", scalar("f2"), 1, True),
]


def counter_inputs(initial):
    inputs = copy.deepcopy(COUNTER_INPUTS)
    inputs[0] = ("initial", scalar("f2"), initial, False)
    return inputs


@pytest.mark.parametrize("initial", [0, 1])
def test_a_loop_records_every_iteration(run, initial):
    body = [
        "repeat", 3, scalar("f2"), 0,
        apply(["record", "f2"], [0], apply(["add", "f2"], [1, 3], ret(0))),
        ret(0),
    ]
    events = [["write", "f2", (initial + i) % 2] for i in range(3)]
    case = run()
    case.compile(counter_inputs(initial), scalar("f2"), body)
    assert case.both() == executed(
        (initial + 3) % 2, [(initial + 2) % 2, 0, 3, [], []], events)


@pytest.mark.parametrize("initial", [0, 1])
def test_a_stopped_loop_keeps_the_prefix_it_reached(run, initial):
    body = [
        "repeat", 3, scalar("f2"), 0,
        apply(["record", "f2"], [0], ["if", 0, ret(1), stop("reject")]),
        apply(["abort_write", "f2"], [0], ret(1)),
    ]
    expected = (
        stopped("reject", [0, 0, 1, [], []], [["write", "f2", 0]]) if initial == 0
        else stopped("abort", [1, 0, 4, [], []], [["write", "f2", 1]] * 4))
    case = run()
    case.compile(counter_inputs(initial), scalar("f2"), body)
    assert case.both() == expected


def test_an_abort_retains_the_write_that_preceded_it(run):
    inputs = [("value", scalar("f7"), 0, False)]
    body = apply(["abort_write", "f7"], [0], apply(["record", "f7"], [1], ret(0)))
    case = run()
    case.compile(inputs, BOOL, body, state=[0, 4, 4, [], []])
    assert case.both() == stopped(
        "abort", [0, 0, 5, [], []], [["write", "f7", 0]])


def test_a_shape_refusal_retains_the_write_that_preceded_it(run):
    inputs = [
        ("view", residual("f7", 2), [3, [0, 1, 2, 4], []], True),
        ("point", point("f7"), [1], False),
        ("value", scalar("f7"), 6, False),
    ]
    body = apply(["record", "f7"], [2],
                 apply(["evaluate", "f7", 2], [1, 2], ret(0)))
    case = run()
    case.compile(inputs, scalar("f7"), body)
    assert case.both() == stopped(
        "refused", [0, 6, 1, [], []], [["write", "f7", 6]])


def _sumcheck():
    """One Sumcheck round: send the two endpoint values, then check the claim.

    Built from the inside out, because the source is a chain of bindings and
    reading it that way is how its shape is checked.
    """
    verify = apply(["equal"], [0, 2], ret(0))
    at_challenge = apply(["evaluate", "f7", 1], [8, 0], verify)
    challenge_point = apply(["point"], [1], at_challenge)
    combined = apply(["linear"], [5, 4, 0], challenge_point)
    drawn = apply(["draw"], [], combined)
    compare = apply(["equal"], [0, 8], ["if", 0, drawn, stop("reject")])
    total = apply(["add", "f7"], [2, 1], compare)
    sent = apply(["send"], [1, 0], total)
    at_one = apply(["evaluate", "f7", 1], [1, 2], sent)
    at_zero = apply(["evaluate", "f7", 1], [0, 2], at_one)
    view = apply(["view", "f7", 1], [2], at_zero)
    return apply(["endpoint_point", False], [],
                 apply(["endpoint_point", True], [], view))


SUMCHECK = _sumcheck()


@pytest.mark.parametrize("claim,tape", [
    pytest.param(0, [3], id="accepted"),
    pytest.param(1, [3], id="rejected"),
    pytest.param(0, [], id="tape-exhausted"),
    pytest.param(0, [3, 6], id="tape-left-over"),
])
def test_one_sumcheck_round(run, claim, tape):
    inputs = [
        ("table", table("f7", 1), [20, [2, 5]], True),
        ("claim", scalar("f7"), claim, False),
    ]
    if claim:
        expected = stopped("reject", [0, 0, 0, [[2, 5]], tape], [["sent", 2, 5]])
    elif not tape:
        expected = stopped("exhausted", [0, 0, 0, [[2, 5]], []], [["sent", 2, 5]])
    else:
        expected = executed(True, [0, 0, 0, [[2, 5]], tape[1:]],
                            [["sent", 2, 5], ["drawn", tape[0]]])
    case = run()
    case.compile(inputs, BOOL, SUMCHECK, state=[0, 0, 0, [], tape])
    assert case.both() == expected


@pytest.mark.parametrize("left", [False, True])
def test_a_merkle_path_checks_its_root(run, left):
    inputs = [
        ("leaf", DIGEST, 2, False),
        ("sibling0", DIGEST, 5, True),
        ("sibling1", DIGEST, 9, True),
        ("root", DIGEST, pair(pair(2, 5), 9), False),
    ]
    body = apply(["parent", left], [0, 1],
                 apply(["parent", False], [0, 3],
                       apply(["digest_equal"], [0, 5], ret(0))))
    case = run()
    case.compile(inputs, BOOL, body)
    assert case.both() == executed(not left)


def test_two_domains_record_separately(run):
    inputs = [
        ("two", scalar("f2"), 1, True),
        ("seven", scalar("f7"), 3, False),
        ("digest", DIGEST, 19, False),
    ]
    body = apply(["record", "f2"], [0],
                 apply(["record", "f7"], [2],
                       apply(["pack"], [2, 3, 4], ret(0))))
    case = run()
    case.compile(inputs, ["summary"], body)
    assert case.both() == executed(
        [1, 3, 19], [1, 3, 2, [], []],
        [["write", "f2", 1], ["write", "f7", 3]])


def test_nested_loops_accumulate(run):
    inputs = [("initial", scalar("f7"), 1, False), ("step", scalar("f7"), 2, True)]
    body = [
        "repeat", 2, scalar("f7"), 0,
        ["repeat", 3, scalar("f7"), 0, apply(["add", "f7"], [0, 3], ret(0)), ret(0)],
        ret(0),
    ]
    case = run()
    case.compile(inputs, scalar("f7"), body)
    assert case.both() == executed(6)


def test_two_tables_with_the_same_label_stay_distinct(run):
    inputs = [
        ("a", table("f7", 0), [9, [2]], True),
        ("b", table("f7", 0), [9, [5]], True),
        ("point", point("f7"), [], False),
    ]
    body = apply(["view", "f7", 0], [0],
                 apply(["evaluate", "f7", 0], [0, 3],
                       apply(["view", "f7", 0], [3],
                             apply(["evaluate", "f7", 0], [0, 5],
                                   apply(["equal"], [0, 2], ret(0))))))
    case = run()
    case.compile(inputs, BOOL, body)
    assert case.both() == executed(False)


def test_a_large_natural_survives_the_round_trip(run):
    huge = 10**900
    inputs = [("a", DIGEST, huge, False), ("b", DIGEST, huge + 7, True)]
    case = run()
    case.compile(inputs, DIGEST, apply(["ordered_pair"], [0, 1], ret(0)))
    assert case.both() == executed(pair(huge, huge + 7))


@pytest.mark.parametrize("body,code", [
    (["repeat", 4, DIGEST, 0, apply(["ordered_pair"], [0, 0], ret(0)), ret(0)],
     "natural-capacity-limit"),
    (["repeat", 10**300, DIGEST, 0, ret(0), ret(0)], "capacity-limit"),
])
def test_capacity_is_refused_before_execution(run, body, code):
    case = run()
    case.compile([("seed", DIGEST, 1, False)], DIGEST, body)
    assert case.native() == refused(code)


@pytest.mark.parametrize("index", range(100))
def test_generated_sources_agree(run, index):
    """A generated source, its residual view and one recorded write.

    The generator varies domain, arity, how much of the point is already fixed,
    whether the remaining coordinates complete it, and whether the write aborts.
    """
    rng = random.Random(72431 + index)
    domain, modulus = rng.choice(DOMAINS)
    arity = rng.randrange(4)
    fixed_count = rng.randrange(arity + 1)
    cells = [rng.randrange(modulus) for _ in range(1 << arity)]
    fixed = [rng.randrange(modulus) for _ in range(fixed_count)]
    tail = [rng.randrange(modulus)
            for _ in range(arity - fixed_count + (1 if rng.randrange(5) == 0 else 0))]
    written = rng.randrange(modulus)
    aborts = rng.randrange(6) == 0
    inputs = [
        ("view", residual(domain, arity), [index, cells, fixed], True),
        ("point", point(domain), tail, False),
        ("write", scalar(domain), written, False),
    ]
    body = apply(["abort_write" if aborts else "record", domain], [2],
                 apply(["evaluate", domain, arity], [1, 2], ret(0)))
    state = [written if domain == "f2" else 0,
             written if domain == "f7" else 0, 1, [], []]
    events = [["write", domain, written]]
    if aborts:
        expected = stopped("abort", state, events)
    elif len(fixed) + len(tail) != arity:
        expected = stopped("refused", state, events)
    else:
        expected = executed(mle(cells, fixed + tail, modulus), state, events)
    case = run()
    case.compile(inputs, scalar(domain), body)
    assert case.both() == expected


@pytest.mark.parametrize("bad", [
    pytest.param(([("flag", BOOL, False, False)], BOOL,
                  ["if", 0, apply(["unknown"], [], ret(0)), ret(0)]),
                 id="unknown-operation-in-a-dormant-branch"),
    pytest.param(([("flag", BOOL, False, False)], BOOL,
                  ["repeat", 0, BOOL, 0, apply(["unknown"], [], ret(0)), ret(0)]),
                 id="unknown-operation-in-a-zero-trip-loop"),
    pytest.param(([("a", scalar("f2"), 1, False), ("b", scalar("f7"), 2, False)],
                  scalar("f7"), apply(["add", "f7"], [0, 1], ret(0))),
                 id="operation-applied-across-domains"),
])
def test_the_compiler_refuses(run, bad):
    case = run()
    with pytest.raises(Refused):
        case.compile(*bad)


def test_a_mutated_plan_is_refused_by_the_checker(run):
    """The exported plan is changed after the fact; its types still fit."""
    inputs = [
        ("leaf", DIGEST, 2, False),
        ("sibling0", DIGEST, 5, True),
        ("sibling1", DIGEST, 9, True),
        ("root", DIGEST, pair(pair(2, 5), 9), False),
    ]
    body = apply(["parent", False], [0, 1],
                 apply(["parent", False], [0, 3],
                       apply(["digest_equal"], [0, 5], ret(0))))
    case = run()
    case.compile(inputs, BOOL, body)
    imported = case.invoke(case.toolchain.compiler, "import", case.source)
    mlir = case.directory / "source.mlir"
    mlir.write_text(imported.stdout)
    lowered = case.invoke(case.toolchain.optimizer, mlir,
                          "--pass-pipeline=builtin.module(lower-pir-to-plan)")
    assert lowered.returncode == 0, lowered.stderr
    changed = case.directory / "changed.mlir"
    changed.write_text(lowered.stdout.replace("left = false", "left = true", 1))
    exported = case.invoke(case.toolchain.compiler, "export", changed)
    assert exported.returncode == 0, exported.stderr
    assert '"parent",true' in exported.stdout, "the mutation must reach the plan"
    candidate = case.directory / "changed-plan.json"
    candidate.write_text(exported.stdout)
    refusal = case.invoke(case.checker, "check", case.source, candidate)
    assert refusal.returncode > 0, refusal.stdout


MINIMAL = request([("flag", BOOL, True, False)], BOOL, ret(0))


def test_canonical_negative_zero_is_a_number(run):
    case = run()
    path = case.directory / "negative-zero.json"
    path.write_text(json.dumps(MINIMAL).replace('["return", 0]', '["return", -0]'))
    compiled = case.invoke(case.toolchain.compiler, "compile", path)
    assert compiled.returncode == 0, compiled.stderr


def test_a_quoted_index_is_not_repaired(run):
    case = run()
    path = case.directory / "quoted-index.json"
    path.write_text(json.dumps(MINIMAL).replace('["return", 0]', '["return", "0"]'))
    assert case.invoke(case.toolchain.compiler, "compile", path).returncode > 0


def test_a_missing_dormant_capture_is_refused(run):
    """A returned value elsewhere does not excuse an input that was not supplied."""
    inputs = [
        ("table", table("f7", 1), [20, [2, 5]], True),
        ("claim", scalar("f7"), 0, False),
    ]
    case = run()
    case.compile(inputs, BOOL, SUMCHECK, state=[0, 0, 0, [], [3]])
    missing = invocation(inputs, [0, 0, 0, [], [3]])
    missing[0] = missing[0][1:]
    path = case.write("missing-capture.json", missing)
    native = case.invoke(case.toolchain.runtime, "run",
                         case.source, case.plan, path, case.checker)
    assert native.returncode > 0, native.stdout
