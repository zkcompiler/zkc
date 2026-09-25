#!/usr/bin/env python3
"""Requirement certificates replayed by the independently implemented checker.

The engine answers a requirement problem and says why: a derivation, step by
step, for every goal it proved. The compiler's own test decides whether the
answers are right by enumerating every finite model. This one states that the
reasons hold up: a second implementation replays each certificate and reaches
the same answers, refuses a certificate whose premise has been damaged in each
of the seven ways a step can be formed, refuses a valid proof offered for the
wrong goal, and refuses input that is not a certificate at all.
"""
import copy
import json

from requirement_problems import applications, problems
from journal import Journal, names
from toolchain import Toolchain, records

# The Lean checker these certificates are replayed by.
CHECKER = "requirement-checker"

# The engine whose derivations are replayed.
ENGINE = "zkc-requirements-test"

# Every way a derivation step is formed. A certificate that reaches a goal
# through any of them must stop being accepted once that step is damaged.
STEPS = {"assumption", "reflexivity", "symmetry", "transitivity",
         "projection", "transport", "implication"}


def main():
    tools = Toolchain()
    engine = tools.native_test(ENGINE)
    checker = tools.checker(CHECKER)
    journal = Journal(records())

    def run(program, value, accepted=True):
        """Send one problem or certificate, and read the answer."""
        result = journal.attempt([program], stdin=json.dumps(value) + "\n", timeout=30)
        assert result.returncode >= 0 and (result.returncode == 0) == accepted, (result.stderr, result.stdout, value)
        return json.loads(result.stdout) if accepted else result

    certificates = 0
    first = None
    for problem, _ in problems():
        derived = run(engine, problem)
        answers = [proof is not None for proof in derived[2]]
        replay = run(checker, [problem, derived])
        assert replay == ["checked", ["proved" if p else "unresolved" for p in answers]]
        certificates += 1
        if first is None:
            first = problem, derived

    problem, derived = first
    seen = set()
    for i, step in enumerate(derived[1]):
        if step[1] in seen:
            continue
        seen.add(step[1])
        damaged = copy.deepcopy(derived)
        if step[1] == "assumption":
            damaged[1][i][3] = 1024
        elif step[1] == "reflexivity":
            damaged[1][i][0] = ["=", [0, 1]]
        else:
            damaged[1][i][2][0] = i  # Self or forward reference.
        run(checker, [problem, damaged], False)
    assert seen == STEPS, seen

    application = next(applications())
    certificate = run(engine, application)
    steps = [i for i, step in enumerate(certificate[1]) if step[1] == "application"]
    assert steps, "application congruence must actually occur in a generated proof"
    for i in steps:
        for premises in ([], [i], [0, 0]):
            damaged = copy.deepcopy(certificate)
            damaged[1][i][2] = premises
            run(checker, [application, damaged], False)

    # A compact DAG must not trigger exponential recursive term equality.
    terms = [[None, "x"]]
    for child in range(30):
        terms.append(["apply", "F", [child, child]])
    large = ["zkc.requirements/1", terms, [], [], [["=", [30, 30]]]]
    proof = ["zkc.requirements-certificate/1",
             [[["=", [30, 30]], "reflexivity", [], 0]], [0]]
    for executable, payload in ((engine, large), (checker, [large, proof])):
        refused = journal.attempt([executable], stdin=json.dumps(payload), timeout=5)
        assert refused.returncode > 0
        assert names(refused.stderr + refused.stdout, "requirements-work-limit")
    bounded = ["zkc.requirements/1", terms[:13], [], [], [["=", [12, 12]]]]
    step = [["=", [12, 12]], "reflexivity", [], 0]
    small = ["zkc.requirements-certificate/1", [step], [0]]
    assert run(checker, [bounded, small]) == ["checked", ["proved"]]
    excessive = ["zkc.requirements-certificate/1", [step] * 17, [0]]
    refused = journal.attempt([checker], stdin=json.dumps([bounded, excessive]), timeout=5)
    assert refused.returncode > 0
    assert names(refused.stderr + refused.stdout, "requirements-work-limit")

    # A proof that holds, offered for a goal it does not reach.
    damaged = copy.deepcopy(derived)
    damaged[2][0] = damaged[2][-1]
    run(checker, [problem, damaged], False)

    # Input that is not a certificate is refused, and says so, rather than
    # exhausting the reader that is trying to make one out of it.
    for text in ["[" * 100000 + "0" + "]" * 100000,
                 "[1e1000000000]", "[0e1000000000]", "[1.0]", "[-1]",
                 "[" + "9" * 10000 + "]", "[true]", "{}"]:
        rejected = journal.attempt([checker], stdin=text, timeout=30)
        assert rejected.returncode == 1, (text[:50], rejected.returncode, rejected.stderr)
        assert json.loads(rejected.stdout)[0] == "refused"

    # Replay the exact bytes the engine was given, without Python normalizing
    # a negative zero on the way through.
    original = '["zkc.requirements/1",[[null,"T"]],[],[],[["=",[-0,0]]]]'
    produced = journal.attempt([engine], stdin=original, timeout=30)
    assert produced.returncode == 0, produced.stderr
    replay = journal.attempt([checker], stdin=f'[{original},{produced.stdout}]', timeout=30)
    assert replay.returncode == 0, replay.stdout
    assert json.loads(replay.stdout) == ["checked", ["proved"]]

    print(json.dumps({"certificates": certificates, "checks": journal.save()}))



def test_library_requirements_reference():
    main()

if __name__ == "__main__":
    main()
