#!/usr/bin/env python3
"""Exercise serialized requests and plans through the maintained Lean executable.

Expected behavior is asserted independently of the checker implementation. This
is finite integration evidence, not a proof of Lean's parser or native compiler.
All generated inputs and responses live in a temporary directory; --output
writes a reviewable receipt including hashes of the implementation under test.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_TOOL = ROOT / "formal/.lake/build/bin/source-plan-example"


def run(tool: Path, arguments: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(tool), *arguments], capture_output=True, text=True, timeout=30, check=False
    )


def check(tool: Path) -> dict:
    cases = []
    with tempfile.TemporaryDirectory(prefix="zkc-source-plan-") as temporary:
        directory = Path(temporary)
        request_path, plan_path = directory / "request.json", directory / "plan.json"
        generated = run(tool, ["write", str(request_path), str(plan_path)])
        if generated.returncode != 0 or generated.stderr:
            raise AssertionError(f"fixture generation failed: {generated}")
        base_request = json.loads(request_path.read_text())
        base_plan = json.loads(plan_path.read_text())

        def case(name, request=None, plan=None, *, error=None, invocation=None,
                 output=None, request_bytes=None, plan_bytes=None):
            request_path.write_bytes(request_bytes if request_bytes is not None else
                                     json.dumps(base_request if request is None else request).encode())
            plan_path.write_bytes(plan_bytes if plan_bytes is not None else
                                  json.dumps(base_plan if plan is None else plan).encode())
            arguments = ["check" if invocation is None else "run", str(request_path), str(plan_path)]
            if invocation is not None:
                arguments.extend(invocation)
            result = run(tool, arguments)
            expected_code = 1 if error else 0
            expected = ({"status": "refused", "code": error} if error else output or {
                "status": "checked", "claim": "complete-logical-execution",
                "realization": "direct-logical-plan",
            })
            actual = json.loads(result.stdout)
            if result.returncode != expected_code or actual != expected or result.stderr:
                raise AssertionError(
                    f"{name}: expected ({expected_code}, {expected}); "
                    f"got ({result.returncode}, {actual}), stderr={result.stderr!r}"
                )
            cases.append({"name": name, "status": "pass", "exit_code": result.returncode,
                          "response": actual})

        case("encoded-request-and-plan")
        for name, enabled, counter, outcome, state, events in [
            ("returned-loop", "true", "1", ["returned", [2, 4, 4]], 3, [1, 2, 3]),
            ("failed-call-retains-state", "true", "0", ["stopped", "abort"], 1, [0]),
            ("dormant-loop", "false", "1", ["stopped", "reject"], 0, []),
        ]:
            case(name, invocation=[enabled, counter], output={
                "status": "executed", "outcome": outcome, "state": state, "events": events,
            })

        # Candidate changes are compared with an independently retained request.
        plan = deepcopy(base_plan)
        plan[-1][2] = [3, 2]
        case("same-typed-operand-swap", plan=plan, error="unchecked-plan")
        request = deepcopy(base_request)
        request[-1][2] = [3, 2]
        case("retained-source-changed", request=request, error="unchecked-plan")
        case("different-source-has-its-own-direct-plan", request=request, plan=plan,
             invocation=["true", "1"], output={"status": "executed",
                 "outcome": ["returned", [3, 4, 4]], "state": 3, "events": [1, 2, 3]})

        for name, index, value, error in [
            ("format-version", 1, 2, "unsupported-format-version"),
            ("semantic-version", 2, "future", "unsupported-semantics-version"),
            ("mandatory-capability", 3, ["native-cost"], "unsupported-capability"),
            ("generated-code-relabel", 4, "generated-code", "unsupported-realization"),
            ("unregistered-rule", 5, "unproved-rewrite", "unsupported-rule"),
            ("stronger-observer", 6, ["equality", "native-time", "all-inputs-and-handlers"],
             "unsupported-claim"),
            ("one-secret-execution", 6, ["equality", "logical-outcome-state-events", "one-input"],
             "unsupported-claim"),
            ("extra-requirement", 8, [["extra", "1"]], "unapproved-requirement"),
        ]:
            plan = deepcopy(base_plan)
            plan[index] = value
            case(name, plan=plan, error=error)
        request, plan = deepcopy(base_request), deepcopy(base_plan)
        request[4] = plan[8] = [["extra", "1"]]
        case("permitted-but-unsupported-requirement", request, plan, error="unsupported-requirement")

        for name, mutate in [
            ("wrong-role", lambda ctx: ctx.__setitem__(0, "verifier")),
            ("changed-field-domain", lambda ctx: ctx[1][2].__setitem__(1, "field/7")),
            ("changed-dependency", lambda ctx: ctx[3][0].__setitem__(1, "2")),
            ("reordered-captures", lambda ctx: ctx[1].__setitem__(slice(2, 4), ctx[1][2:4][::-1])),
        ]:
            plan = deepcopy(base_plan)
            mutate(plan[7])
            case(name, plan=plan, error="context-mismatch")

        request, plan = deepcopy(base_request), deepcopy(base_plan)
        request[3][3][0][1] = plan[7][3][0][1] = "2"
        case("unresolved-definition-on-both-sides", request, plan, error="unresolved-dependency")

        for name, mutate in [
            ("duplicate-input-declaration", lambda ctx: ctx[1].append(deepcopy(ctx[1][0]))),
            ("empty-input-name", lambda ctx: ctx[1][0].__setitem__(0, "")),
            ("inaccessible-private-input", lambda ctx: ctx.__setitem__(0, "verifier")),
        ]:
            request, plan = deepcopy(base_request), deepcopy(base_plan)
            mutate(request[3])
            plan[7] = deepcopy(request[3])
            case(name, request, plan, error="invalid-context")

        for name, body in [
            ("cross-field-operand", ["apply", "negate/7", [2], ["stop", "reject"]]),
            ("missing-operand", ["apply", "subtract/5", [2], ["stop", "reject"]]),
            ("extra-operand", ["apply", "negate/7", [4, 4], ["stop", "reject"]]),
            ("out-of-scope-operand", ["return", 99]),
            ("invalid-dormant-branch", ["if", 0, ["stop", "reject"], ["return", 99]]),
        ]:
            request, plan = deepcopy(base_request), deepcopy(base_plan)
            request[-1] = plan[-1] = body
            case(name, request, plan, error="malformed-source")

        # These inputs are well formed; binding must still check dormant slots.
        request, plan = deepcopy(base_request), deepcopy(base_plan)
        request[3][1].append(["unused", "nat", ["private", "prover"], "capture"])
        plan[7] = deepcopy(request[3])
        case("missing-dormant-runtime-input", request, plan, invocation=["false", "1"],
             error="missing-input")
        request, plan = deepcopy(base_request), deepcopy(base_plan)
        request[3][1][1][0] = "renamed-counter"
        plan[7] = deepcopy(request[3])
        case("runtime-input-name", request, plan, invocation=["false", "1"], error="wrong-input-name")
        request, plan = deepcopy(base_request), deepcopy(base_plan)
        request[-1] = plan[-1] = ["stop", "reject"]
        request[3][1][1][1] = "bool"
        plan[7] = deepcopy(request[3])
        case("runtime-input-type", request, plan, invocation=["false", "1"], error="wrong-input-type")
        request[3][1] = request[3][1][:1]
        plan[7] = deepcopy(request[3])
        case("unexpected-runtime-input", request, plan, invocation=["false", "1"],
             error="unexpected-input")

        for reason in ["reject", "abort", "exhausted", "incomplete", "refused"]:
            request, plan = deepcopy(base_request), deepcopy(base_plan)
            request[-1] = plan[-1] = ["stop", reason]
            case(f"stop-{reason}", request, plan, invocation=["true", "1"], output={
                "status": "executed", "outcome": ["stopped", reason], "state": 0, "events": [],
            })

        for name, body, error in [
            ("unknown-syntax", ["callback", "host-function"], "invalid-shape"),
            ("unknown-operation", ["apply", "missing-op", [], ["return", 0]], "unknown-operation"),
            ("unknown-type", ["repeat", 1, "field/11", 2, ["return", 0], ["return", 0]], "unknown-type"),
            ("unknown-stop", ["stop", "success"], "unknown-stop"),
            ("negative-index", ["return", -1], "expected-natural"),
            ("fractional-index", ["return", 0.5], "expected-natural"),
            ("extra-control-field", ["return", 0, "ignored"], "invalid-shape"),
        ]:
            plan = deepcopy(base_plan)
            plan[-1] = body
            case(name, plan=plan, error=error)
        case("invalid-json", plan_bytes=b"[", error="invalid-json")
        case("scientific-number", plan_bytes=b'["zkc-plan",1e1000000000]', error="expected-natural")
        case("oversized-number", plan_bytes=b'["zkc-plan",' + b"1" * 1025 + b']', error="number-limit")
        case("trailing-json", plan_bytes=json.dumps(base_plan).encode() + b"[]", error="invalid-json")
        case("invalid-utf8", plan_bytes=b"\xff", error="invalid-utf8")
        case("oversized-file", plan_bytes=b" " * (1024 * 1024 + 1), error="byte-limit")
        case("object-instead-of-array", plan_bytes=b'{"tag":"zkc-plan","tag":"other"}', error="invalid-shape")
        plan = deepcopy(base_plan)
        plan[2] = 3
        case("non-string-version", plan=plan, error="expected-string")
        plan = deepcopy(base_plan)
        body = ["stop", "reject"]
        for _ in range(256):
            body = ["apply", "increment", [1], body]
        plan[-1] = body
        case("decoder-depth", plan=plan, error="depth-limit")
        request, plan = deepcopy(base_request), deepcopy(base_plan)
        body = ["repeat", 100001, "nat", 1, ["return", 0], ["stop", "reject"]]
        request[-1] = plan[-1] = body
        case("public-loop-execution-limit", request, plan, invocation=["true", "1"],
             error="execution-work-limit")

    sources = sorted(path for directory in ["formal/Zkc", "formal/Tools", "formal/Tests"]
                     for path in (ROOT / directory).rglob("*.lean"))
    return {
        "status": "pass", "cases": len(cases), "results": cases,
        "tool_sha256": hashlib.sha256(tool.read_bytes()).hexdigest(),
        "source_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sources},
        "scope": "finite compiled-checker and logical-interpreter controls; no parser, native-backend or protocol-security theorem",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tool", type=Path, default=DEFAULT_TOOL)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = check(args.tool.resolve())
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "cases": report["cases"]}))


if __name__ == "__main__":
    main()
