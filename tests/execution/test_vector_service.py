#!/usr/bin/env python3
"""Dependent replies through an independent MLIR family, Lean, and Rust consumer."""

import hashlib
import json
import random

from journal import Journal
from lowering import lowered_plan
from toolchain import Toolchain, records


def apply(op, args, next):
    return ["apply", [op], args, next]


# This unit runs an independent operation family, so every tool is that family's:
# the compiler's own service example, the Rust consumer example, and the Lean
# consumer built for the same family. The table references refuse these sources.
COMPILER = "zkc-service-compile"
OPTIMIZER = "zkc-service-opt"
CONSUMER = "vector-service"
CHECKER = "vector-service"


def main():
    tools = Toolchain()
    compiler = tools.service(COMPILER)
    optimizer = tools.service(OPTIMIZER)
    runtime = tools.example(CONSUMER)
    checker = tools.checker(CHECKER)
    journal = Journal(records())
    programs = []

    def prepare(
        name,
        body,
        result="vector",
        profile="finite-source-1",
        inputs=None,
        changed=False,
    ):
        programs.append(name)
        directory = journal.directory / name
        directory.mkdir(exist_ok=True)
        source, plan, ir = (
            directory / f for f in ("source.json", "plan.json", "source.mlir")
        )
        context = [
            "client",
            inputs
            if inputs is not None
            else [["n", ["count"], ["shared"], "argument"]],
            [result],
            [["vector-service", "1"]],
        ]
        source.write_text(json.dumps(["zkc-request", 1, profile, context, [], body]))
        # Ordered calls remain; the generic pipeline handles the independent types.
        plan.write_text(lowered_plan(journal, compiler, optimizer, source, directory,
                                     "cse,lower-pir-to-plan").read_text())
        exported = plan
        direct = journal.attempt([compiler, "compile", source])
        journal.check(
            name + "/direct-export",
            direct.returncode == 0
            and (json.loads(direct.stdout) != json.loads(exported.read_text())) == changed,
        )
        checked = journal.attempt([checker, "check", source, plan])
        journal.check(
            name + "/lean-check",
            checked.returncode == (1 if changed else 0),
            checked.stdout,
        )
        if changed:
            journal.check(
                name + "/changed-plan-refused",
                json.loads(checked.stdout)
                == {"status": "refused", "code": "unchecked-plan"},
                checked.stdout,
            )
        return source, plan

    def run(name, paths, n, tape, expected, calls=5, fault=None):
        source, plan = paths
        invocation = source.parent / (name + "-inputs.json")
        invocation.write_text(json.dumps([[["n", ["count"], n]], [calls, tape]]))
        native = journal.attempt([
            runtime,
            source,
            plan,
            invocation,
            checker,
            *([] if fault is None else ["--fault", *fault]),
        ])
        native_value = json.loads(native.stdout)
        journal.check(
            name + "/native",
            native.returncode == 0 and native_value == expected,
            native_value,
        )
        if fault is None:
            lean = journal.attempt([checker, "run", source, plan, invocation])
            lean_value = json.loads(lean.stdout)
            journal.check(
                name + "/lean",
                lean.returncode == 0 and lean_value == expected,
                lean_value,
            )
            journal.check(name + "/differential", native_value == lean_value)

    def executed(value, calls, tape, events, stopped=False):
        return {
            "status": "executed",
            "outcome": ["stopped" if stopped else "returned", value],
            "state": [calls, tape],
            "events": events,
        }

    adaptive = apply(
        "request",
        [0],
        apply("sum", [0], apply("request", [0], apply("send", [1], ["return", 1]))),
    )
    paths = prepare("adaptive", adaptive)
    rng = random.Random(93717)
    # Expectations use n*seed directly, independently of either source evaluator.
    values = [
        (n, [a, b, 4, 6])
        for n in [0, 1, 2, 17, 1024, 1025]
        for a, b in [(0, 0), (1, 6), (2, 3), (6, 1)]
    ]
    values += [
        (rng.randrange(1026), [rng.randrange(7) for _ in range(rng.randrange(5))])
        for _ in range(80)
    ]
    values += [(3, []), (3, [2]), (3, [2, 4]), (3, [2, 4, 5]), (2**100, [2, 4])]
    for i, (n, tape) in enumerate(values):
        events, rest, count, stopped = [], list(tape), 5, None
        if n > 1024:
            stopped = "refused"
            output = []
        else:
            events.append(["request", n])
            count += 1
            if not rest:
                stopped, output = "exhausted", []
            else:
                size = n * rest.pop(0)
                output = []
                if size > 1024:
                    stopped = "refused"
                else:
                    events.append(["request", size])
                    count += 1
                    if not rest:
                        stopped = "exhausted"
                    else:
                        output = [rest.pop(0)] * size
                        events.append(["send", size])
                        count += 1
                        if not rest:
                            stopped = "exhausted"
                        else:
                            rest.pop(0)
        run(
            f"adaptive-{i}",
            paths,
            n,
            tape,
            executed(stopped or output, count, rest, events, stopped is not None),
        )

    # The previous vector reply determines the second request's shape.
    for at, count, events in [
        (1, 6, [["request", 3]]),
        (2, 7, [["request", 3], ["request", 6]]),
    ]:
        for kind, code in [
            ("wrong-length", "invalid-dependent-reply"),
            ("wrong-type", "invalid-value"),
            ("noncanonical", "noncanonical-scalar"),
        ]:
            run(
                f"fault-{kind}-{at}",
                paths,
                3,
                [2, 4, 5, 6],
                {
                    "status": "interrupted",
                    "code": code,
                    "state": [count, [2, 4, 5, 6][at:]],
                    "events": events,
                },
                fault=(kind, at),
            )

    branch = apply(
        "send", [0], ["if", 0, apply("request", [1], ["return", 0]), ["stop", "reject"]]
    )
    branch_paths = prepare("predicate", branch)
    run(
        "predicate-true",
        branch_paths,
        0,
        [2, 4],
        executed([], 7, [], [["send", 0], ["request", 0]]),
    )
    run(
        "predicate-false",
        branch_paths,
        8,
        [2, 4],
        executed("reject", 6, [4], [["send", 8]], True),
    )
    run(
        "predicate-wrong",
        branch_paths,
        8,
        [2, 4],
        {
            "status": "interrupted",
            "code": "invalid-dependent-reply",
            "state": [6, [4]],
            "events": [["send", 8]],
        },
        fault=("wrong-flag", 1),
    )
    run(
        "predicate-wrong-type",
        branch_paths,
        0,
        [2, 4],
        {
            "status": "interrupted",
            "code": "invalid-value",
            "state": [6, [4]],
            "events": [["send", 0]],
        },
        fault=("wrong-type", 1),
    )

    # Structured repeat carries the value and stops before its shared suffix.
    step = apply("request", [0], apply("sum", [0], ["return", 0]))
    repeat = ["repeat", 3, ["count"], 0, step, apply("send", [0], ["return", 1])]
    region = ["bind", ["count"], repeat, ["return", 0]]
    region_paths = prepare("region", region, "count", "region-source-1")
    run(
        "region-return",
        region_paths,
        2,
        [2, 3, 4, 5, 6],
        executed(
            48, 9, [6], [["request", 2], ["request", 4], ["request", 12], ["send", 48]]
        ),
    )
    run(
        "region-stop",
        region_paths,
        2,
        [2],
        executed("exhausted", 7, [], [["request", 2], ["request", 4]], True),
    )
    run(
        "region-bad-reply",
        region_paths,
        2,
        [2, 3, 4, 5],
        {
            "status": "interrupted",
            "code": "invalid-dependent-reply",
            "state": [7, [4, 5]],
            "events": [["request", 2], ["request", 4]],
        },
        fault=("wrong-length", 2),
    )

    # A changed, well-typed candidate must still be refused by the Lean checker.
    source, plan = paths
    bad_plan = json.loads(plan.read_text())
    bad_plan[9] = ["apply", ["request"], [0], ["return", 0]]
    mutated = plan.parent / "changed-plan.json"
    mutated.write_text(json.dumps(bad_plan))
    lean = journal.attempt([checker, "check", source, mutated])
    journal.check(
        "changed-candidate/lean",
        lean.returncode == 1 and json.loads(lean.stdout)["status"] == "refused",
    )
    native = journal.attempt([
        runtime,
        source,
        mutated,
        source.parent / "adaptive-0-inputs.json",
        checker,
    ])
    journal.check(
        "changed-candidate/native",
        native.returncode == 0
        and json.loads(native.stdout)["status"] == "admission-failed",
    )
    # Legal shape/content domain alone cannot establish the selected provider's
    # value law. This mutant passes reply validation but differs from Lean.
    single = prepare("single-request", apply("request", [0], ["return", 0]))
    source, plan = single
    invocation = source.parent / "legal-shape-inputs.json"
    invocation.write_text(json.dumps([[["n", ["count"], 3]], [5, [2, 4]]]))
    native = journal.attempt([
        runtime, source, plan, invocation, checker, "--fault", "wrong-content", 1
    ])
    lean = journal.attempt([checker, "run", source, plan, invocation])
    journal.check(
        "legal-shape/wrong-provider-value",
        native.returncode == 0
        and json.loads(native.stdout) == executed([3, 2, 2], 6, [4], [["request", 3]]),
        native.stdout,
    )
    journal.check(
        "legal-shape/reference-value",
        lean.returncode == 0
        and json.loads(lean.stdout) == executed([2, 2, 2], 6, [4], [["request", 3]]),
        lean.stdout,
    )
    journal.check(
        "legal-shape/differential-detects",
        json.loads(native.stdout) != json.loads(lean.stdout),
    )
    run(
        "empty-wrong-length",
        single,
        0,
        [2, 4],
        {
            "status": "interrupted",
            "code": "invalid-dependent-reply",
            "state": [6, [4]],
            "events": [["request", 0]],
        },
        fault=("wrong-length", 1),
    )
    # Native preflight conservatively checks both branches against its capacity
    # policy. This is a host refusal, not a new stop in the Lean meaning.
    capacity = prepare(
        "capacity",
        [
            "if",
            1,
            apply("sum", [0], ["return", 0]),
            apply("request", [2], apply("sum", [0], ["return", 0])),
        ],
        "count",
        inputs=[
            [name, [ty], ["shared"], "argument"]
            for name, ty in [("xs", "vector"), ("flag", "predicate"), ("n", "count")]
        ],
    )
    source, plan = capacity
    for flag in [True, False]:
        invocation = source.parent / f"capacity-{flag}-inputs.json"
        invocation.write_text(
            json.dumps(
                [
                    [
                        ["xs", ["vector"], [6] * 1025],
                        ["flag", ["predicate"], flag],
                        ["n", ["count"], 2],
                    ],
                    [5, [2, 4]],
                ]
            )
        )
        native = journal.attempt([runtime, source, plan, invocation, checker])
        lean = journal.attempt([checker, "run", source, plan, invocation])
        journal.check(
            f"capacity/{flag}/host-refusal",
            native.returncode == 0
            and json.loads(native.stdout)
            == {
                "status": "start-failed",
                "code": "capacity-limit",
                "state": [5, [2, 4]],
                "events": [],
            },
            native.stdout,
        )
        expected = (
            executed(6150, 5, [2, 4], [])
            if flag
            else executed(4, 6, [4], [["request", 2]])
        )
        journal.check(
            f"capacity/{flag}/logical-execution",
            lean.returncode == 0 and json.loads(lean.stdout) == expected,
            lean.stdout,
        )
    composite = prepare(
        "composite", apply("request_and_send", [0], ["return", 0]), "predicate"
    )
    for n, tape, outcome, calls, rest, events, stopped in [
        (3, [2, 4, 6], False, 7, [6], [["request", 3], ["send", 6]], False),
        (3, [0, 4], True, 7, [], [["request", 3], ["send", 0]], False),
        (0, [2, 4], True, 7, [], [["request", 0], ["send", 0]], False),
        (1025, [2, 4], "refused", 5, [2, 4], [], True),
        (3, [], "exhausted", 6, [], [["request", 3]], True),
        (3, [2], "exhausted", 7, [], [["request", 3], ["send", 6]], True),
    ]:
        run(
            f"composite-{n}-{len(tape)}-{tape[:1]}",
            composite,
            n,
            tape,
            executed(outcome, calls, rest, events, stopped),
        )
    # A post-operation predicate check cannot see the first vector. The
    # provider-boundary check must interrupt before the hidden second call.
    for kind, code, at in [
        ("wrong-length", "invalid-dependent-reply", 1),
        ("noncanonical", "noncanonical-scalar", 1),
        ("wrong-type", "invalid-value", 1),
        ("wrong-flag", "invalid-dependent-reply", 2),
    ]:
        run(
            f"composite-{kind}",
            composite,
            3,
            [2, 4, 6],
            {
                "status": "interrupted",
                "code": code,
                "state": [5 + at, [2, 4, 6][at:]],
                "events": [["request", 3], ["send", 6]][:at],
            },
            fault=(kind, at),
        )
    # An unreached host fault does not change execution or consume a call.
    run(
        "composite-unreached-fault",
        composite,
        3,
        [2, 4, 6],
        executed(False, 7, [6], [["request", 3], ["send", 6]]),
        fault=("wrong-type", 3),
    )
    cse = prepare(
        "cse-changed",
        apply(
            "request",
            [0],
            apply("sum", [0], apply("sum", [1], apply("send", [0], ["return", 0]))),
        ),
        "predicate",
        changed=True,
    )
    source, plan = cse
    invocation = source.parent / "inputs.json"
    invocation.write_text(json.dumps([[["n", ["count"], 3]], [5, [2, 4]]]))
    native = journal.attempt([runtime, source, plan, invocation, checker])
    journal.check(
        "cse-changed/native-refusal",
        native.returncode == 0
        and json.loads(native.stdout)
        == {
            "status": "admission-failed",
            "code": "unchecked-plan",
            "state": [5, [2, 4]],
            "events": [],
        },
        native.stdout,
    )
    # Binding errors retain the supplied initial state and remain distinct from
    # source admission and capacity failure.
    source, plan = single
    invocation = source.parent / "wrong-name-inputs.json"
    invocation.write_text(json.dumps([[["m", ["count"], 3]], [5, [2, 4]]]))
    native = journal.attempt([runtime, source, plan, invocation, checker])
    journal.check(
        "wrong-input/binding-failure",
        native.returncode == 0
        and json.loads(native.stdout)
        == {
            "status": "binding-failed",
            "code": "wrong-input-name",
            "state": [5, [2, 4]],
            "events": [],
        },
        native.stdout,
    )
    mixed = prepare(
        "private-mixed-inputs",
        [
            "if",
            1,
            apply("sum", [0], ["return", 0]),
            apply("request", [2], apply("sum", [0], ["return", 0])),
        ],
        "count",
        inputs=[
            ["xs", ["vector"], ["private", "client"], "argument"],
            ["flag", ["predicate"], ["shared"], "argument"],
            ["n", ["count"], ["shared"], "argument"],
        ],
    )
    source, plan = mixed
    for flag in [True, False]:
        invocation = source.parent / f"inputs-{flag}.json"
        invocation.write_text(
            json.dumps(
                [
                    [
                        ["xs", ["vector"], [1, 3, 6]],
                        ["flag", ["predicate"], flag],
                        ["n", ["count"], 2],
                    ],
                    [5, [2, 4]],
                ]
            )
        )
        expected = (
            executed(10, 5, [2, 4], [])
            if flag
            else executed(4, 6, [4], [["request", 2]])
        )
        native = journal.attempt([runtime, source, plan, invocation, checker])
        lean = journal.attempt([checker, "run", source, plan, invocation])
        journal.check(
            f"private-mixed/{flag}",
            native.returncode == lean.returncode == 0
            and json.loads(native.stdout) == json.loads(lean.stdout) == expected,
            [native.stdout, lean.stdout],
        )
    # Large vectors remain legal values when no bounded sum is requested.
    unrestricted = prepare(
        "large-vector-value",
        ["return", 0],
        inputs=[["xs", ["vector"], ["shared"], "argument"]],
    )
    source, plan = unrestricted
    invocation = source.parent / "inputs.json"
    invocation.write_text(json.dumps([[["xs", ["vector"], [6] * 2000]], [5, [2, 4]]]))
    native = journal.attempt([runtime, source, plan, invocation, checker])
    lean = journal.attempt([checker, "run", source, plan, invocation])
    journal.check(
        "large-vector/sort-unrestricted",
        native.returncode == lean.returncode == 0
        and json.loads(native.stdout)
        == json.loads(lean.stdout)
        == executed([6] * 2000, 5, [2, 4], []),
    )
    summary = {
        "programs": programs,
        "native_invocations": sum(c["argv"][0] == str(runtime) for c in journal.commands),
        "reference_invocations": sum(
            c["argv"][:2] == [str(checker), "run"] for c in journal.commands
        ),
        "checks": len(journal.checks),
        "passed": sum(one["pass"] for one in journal.checks),
        "binaries": {
            key: {
                "path": str(tool),
                "sha256": hashlib.sha256(tool.read_bytes()).hexdigest(),
            }
            for key, tool in (
                ("compiler", compiler),
                ("optimizer", optimizer),
                ("runtime", runtime),
                ("lean", checker),
            )
        },
        "results": journal.checks,
    }
    journal.write("validation.json", summary)
    journal.save()
    print(f"vector service: {summary['passed']}/{summary['checks']} checks passed")
    return 0 if summary["passed"] == summary["checks"] else 1



def test_vector_service():
    assert main() == 0


if __name__ == "__main__":
    raise SystemExit(main())
