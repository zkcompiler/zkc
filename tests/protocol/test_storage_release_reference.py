#!/usr/bin/env python3
"""Storage-release candidates against the independently implemented consumer.

A release says the participant no longer holds a value. The compiler's own test
states where it places them and which malformed ones it refuses. This one states
that a second implementation agrees: it accepts the candidate the compiler
released storage in and the one it did not, accepts the same source written in
the readable profile, and refuses each of the ten malformed candidates, which
both tests build from one place.
"""
import json
from pathlib import Path

from release_candidates import malformed
from journal import Journal
from toolchain import Toolchain, records

# The Lean reference these candidates are checked against.
CHECKER = "interactive-protocol"

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/fixtures/storage-release.pir"


def main():
    tools = Toolchain()
    compiler, optimizer = tools.compiler, tools.optimizer
    checker = tools.checker(CHECKER)
    journal = Journal(records())

    def compile(command, text, *flags):
        return json.loads(journal.run([compiler, command, "-", *flags], text))

    source = FIXTURE.read_text()
    original = compile("protocol-source", source)
    dense = compile("protocol-compile", source)
    released = compile("protocol-compile", source, "--release-storage")
    projected = json.loads(journal.run(
        [compiler, "protocol-export", "-"],
        journal.run([optimizer, "--zkc-project-participants"],
            journal.run([compiler, "protocol-import", "-"], source))))

    # The same source in the readable profile reaches the identical pass.
    profile = source.replace('module {\n  bind both = bool.and();',
                             'module "arkworks.multilinear.bls12-381/1" {')
    profile = profile.replace('= both(', '= bool.and(')
    profile_source = compile("protocol-source", profile)
    profile_released = compile("protocol-compile", json.dumps(profile_source),
                               "--release-storage")

    directory = journal.directory
    source_path = Path(directory) / "source.json"
    candidate_path = Path(directory) / "candidate.json"

    def check(admitted, candidate, accepted):
        source_path.write_text(json.dumps(admitted))
        candidate_path.write_text(json.dumps(candidate))
        result = journal.attempt([checker, "--check", source_path, candidate_path])
        assert result.returncode >= 0 and (result.returncode == 0) == accepted, (candidate, result.stdout,
                                                      result.stderr)

    check(original, released, True)
    check(original, dense, True)
    for _, candidate in malformed(released, projected):
        check(original, candidate, False)
    check(profile_source, profile_released, True)

    print(f"{journal.save()} storage release reference checks passed")



def test_storage_release_reference():
    main()

if __name__ == "__main__":
    main()
