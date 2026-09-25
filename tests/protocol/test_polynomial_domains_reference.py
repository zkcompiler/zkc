#!/usr/bin/env python3
"""The polynomial-domain source against the independently implemented consumer.

The compiler's own test states what it reports about cosets, shifts and sizes.
This one states that a second implementation, which shares no code with it,
accepts the same source against the candidate the compiler produced, and refuses
that source once an algebraic requirement the generic function depends on is
removed from what its caller promises.
"""
import copy
import json
from pathlib import Path

from journal import Journal, names
from toolchain import Toolchain, records

# The Lean reference this generic source is checked against.
CHECKER = "interactive-protocol"

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/fixtures/polynomial-domains.pir"

# The promise the generic function requires, as the admitted source records it.
PROMISE = ["CharacteristicNotTwo", ["F"]]


def main():
    tools = Toolchain()
    compiler, checker = tools.compiler, tools.checker(CHECKER)
    journal = Journal(records())

    def compile(command, text):
        return journal.json([compiler, command, "-"], text)

    text = FIXTURE.read_text()
    plan = compile("protocol-compile", text)
    admitted = compile("protocol-source", text)
    without_promise = copy.deepcopy(admitted)
    without_promise[1][0][3].remove(PROMISE)

    directory = journal.directory
    root = Path(directory)
    plan_path = root / "plan.json"
    plan_path.write_text(json.dumps(plan))
    for source, error in [(admitted, None),
                          (without_promise, "generic-requirement-not-provided")]:
        source_path = root / "source.json"
        source_path.write_text(json.dumps(source))
        result = journal.attempt([checker, "--check-generic", source_path, plan_path])
        if error:
            assert result.returncode > 0, result
            assert names(result.stdout + result.stderr, error), result
        else:
            assert result.returncode == 0, result

    print(f"{journal.save()} polynomial domain reference checks passed")



def test_polynomial_domains_reference():
    main()

if __name__ == "__main__":
    main()
