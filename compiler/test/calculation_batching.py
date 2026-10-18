"""Calculation batching and the definition schedule of participant mathematics.

The deferred-rounds fixture's verifier computes `a0 * r0` after the first draw
and consumes it only after the second. With batching, the default, the
validator computes every product in one calculation call before the final
comparison. `--no-calculation-batching` computes each needed operation before
the first action that follows it in source order, so the first product is
computed before the second message is received. The compiler's own lowering
check runs on both schedules; a refused schedule would refuse compilation. The
named participant pipeline and the explicit passes agree under the option.
"""
import json

from cases import case
from commands import Commands
from tools import ROOT, compiler, records

OUT = records()
commands = Commands(OUT)
FIXTURE = ROOT / "common/tests/fixtures/projects/deferred-rounds/main.zkc"
options = ["--source-format=zkc", "--entry=example::Proof", f"--module=example={FIXTURE}"]


def validator(*flags):
    """The validator's actions and the program's local functions."""
    deployment = json.loads(commands.run([compiler, "language-bundle", *options, *flags]))
    program = json.loads(deployment[4])
    role = deployment[2][1][3]
    body = next(item for item in program[3] if item[3] == role)[6]
    functions = {item[1]: item for item in program[2]}
    return body, functions


def schedule(body):
    """Receives, transcript calls and calculation calls, in order."""
    kinds = []
    for item in body:
        if item[0] == "local":
            kinds.append("calculation" if item[2].startswith("_calculation") else "transcript")
        else:
            kinds.append(item[0])
    return kinds


def operations(functions, call):
    """The operations a calculation call computes."""
    return [step[2] for step in functions[call[2]][4] if step[0] == "op"]


round_actions = ["receive", "transcript", "transcript", "transcript"]

with case("batching computes every product before the comparison"):
    body, functions = validator()
    assert schedule(body) == [*round_actions, *round_actions, "calculation", "return"], schedule(body)
    calls = [item for item in body if item[0] == "local" and item[2].startswith("_calculation")]
    assert len(operations(functions, calls[0])) == 6

with case("the definition schedule computes the first product after the first round"):
    body, functions = validator("--no-calculation-batching")
    assert schedule(body) == [*round_actions, "calculation", *round_actions, "calculation", "return"], \
        schedule(body)
    calls = [item for item in body if item[0] == "local" and item[2].startswith("_calculation")]
    assert [len(operations(functions, call)) for call in calls] == [1, 5]

with case("checking accepts no schedule option"):
    commands.run([compiler, "language-check", *options, "--no-calculation-batching"], refuses="source.options")

with case("the named pipeline and the explicit passes agree without batching"):
    source = (ROOT / "compiler/test/fixtures/mathematical/local-execution.mlir").read_text()
    named = commands.verified(source, None, "--pass-pipeline=builtin.module(zkc-participant-pipeline"
                              "{calculation-batching=false})")
    explicit = commands.verified(source, None, "--pass-pipeline=builtin.module(zkc-project-protocol,"
                                 "zkc-eliminate-polynomials,zkc-lower-math{calculation-batching=false},"
                                 "zkc-select-physical)")
    assert named == explicit

print(f"calculation batching: {commands.save()} checks")
