#!/usr/bin/env python3
"""Callable expansion against the independently implemented consumer.

A callable is expanded away before a plan exists, so a plan carries no trace of
the calls it came from and correspondence has to be re-established from the
source. The compiler's own test states what it expands and what it refuses.
This one states that a second implementation agrees about which plan belongs to
which source: it accepts the plan compiled from the fixture and from a nested
variant, and refuses a source whose callables call each other, a source that
reuses an affine value, a plan with a guard removed, and a plan compiled from a
body that was changed after the source was read.
"""
import copy
import json
from pathlib import Path

from algorithm_variants import cycle, nested, with_identity
from journal import Journal
from toolchain import Toolchain, records

# The Lean reference these sources and plans are checked against.
CHECKER = "interactive-protocol"

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/fixtures/local-algorithms.pir"


def main():
    tools = Toolchain()
    compiler, checker = tools.compiler, tools.checker(CHECKER)
    journal = Journal(records())

    def native(command, value, *flags):
        text = value if isinstance(value, str) else json.dumps(value)
        return journal.run([compiler, command, "-", *flags], text)

    text = FIXTURE.read_text()
    source = json.loads(native("protocol-source", text))
    plan = json.loads(native("protocol-compile", source))
    nested_source = nested(source)
    nested_plan = json.loads(native("protocol-compile", nested_source))

    # A body changed after the source was read produces a plan that no longer
    # answers to it, even though nothing in the source says so.
    identity_source = with_identity(source)
    changed = native("protocol-import", identity_source).replace("call @Twice",
                                                                 "call @Identity")
    changed_plan = json.loads(native("protocol-compile",
                                     native("protocol-export", changed)))

    # An affine value is spent once; a second call spends it again.
    affine = copy.deepcopy(source)
    affine[2][5][4].insert(1, ["apply", "again", "Commit", [], ["bases", "n"],
                               ["cc", "nn"]])

    # A guard the source states has no instruction answering to it in the plan.
    without_guard = copy.deepcopy(plan)
    guarded = next(f for f in without_guard[3] if f[1] == "Authenticate")
    guarded[4] = [i for i in guarded[4]
                  if not (i[0] == "op" and i[1] == "lc_5_guard")]

    directory = journal.directory
    source_path = Path(directory) / "source.json"
    plan_path = Path(directory) / "plan.json"

    def check(admitted, candidate, error=None):
        source_path.write_text(json.dumps(admitted))
        plan_path.write_text(json.dumps(candidate))
        journal.run([checker, "--check-generic", source_path, plan_path], refuses=error)

    check(source, plan)
    check(nested_source, nested_plan)
    check(cycle(source), plan, error="algorithm-call-cycle-or-symbol")
    check(affine, plan, error="interactive-resource-reuse")
    check(source, without_guard, error="source-local-unmatched")
    check(identity_source, changed_plan, error="source-local-unmatched")

    print(f"{journal.save()} local algorithm reference checks passed")



def test_local_algorithms_reference():
    main()

if __name__ == "__main__":
    main()
