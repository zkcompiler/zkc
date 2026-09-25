#!/usr/bin/env python3
"""Execute readable sources through the existing compiler, checker and Rust host."""

import argparse
import json
from pathlib import Path

from journal import Journal
from toolchain import Toolchain, records


# The Lean reference these readable sources are executed against.
CHECKER = "interactive-protocol"


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path,
                        help="optional existing artifact baseline fixtures directory")
    args = parser.parse_args(argv)
    tools = Toolchain()
    root = Path(__file__).resolve().parents[2]
    examples = root / "examples/protocols"
    compiler, runtime = tools.compiler, tools.runtime
    checker = tools.checker(CHECKER)
    journal = Journal(records())
    output = journal.directory
    reports = {}

    def call(*command, destination=None, cwd=root):
        """Run a frontend command where the sources are, and read its answer."""
        out = journal.run(command, cwd=cwd)
        if destination:
            destination.write_text(out)
        return json.loads(out)

    def normalize(stem, directory):
        source = directory / "source.json"
        actual = call(compiler, "protocol-source", examples / f"{stem}.pir",
                      destination=source)
        assert actual == json.loads((examples / f"{stem}.json").read_text())
        return source

    for stem in ("group-exchange", "two-factor"):
        directory = output / stem
        directory.mkdir(exist_ok=True)
        source = normalize(stem, directory)
        participants = directory / "participants.json"
        call(compiler, "protocol-compile", examples / f"{stem}.pir", destination=participants)
        report = call(runtime, "run-protocol", source, participants,
                      examples / f"{stem}.inputs.json", checker,
                      destination=directory / "execution.json")
        assert report["outcome"][0] == "returned", report
        assert report["outcome"][1]["V"][0] == ["bool", True], report
        reports[stem] = {"outcome": "accepted", "path": "interactive"}

    if args.fixtures:
        fixtures = args.fixtures.resolve()
        for stem in ("committed-two-factor", "dleq"):
            directory = output / stem
            directory.mkdir(exist_ok=True)
            fixture = fixtures / stem
            source = normalize(stem, directory)
            descriptor = directory / "descriptor.json"
            call(compiler, "protocol-source", examples / f"{stem}.construction.pir",
                 destination=descriptor)
            # The retained keys and inputs belong to these exact source fixtures.
            for actual, expected in ((source, fixture / "source.json"),
                                     (descriptor, fixture / "descriptor.json")):
                assert json.loads(actual.read_text()) == json.loads(expected.read_text())
            construction = directory / "construction.json"
            built = call(compiler, "protocol-construct", examples / f"{stem}.pir",
                         examples / f"{stem}.construction.pir", destination=construction)
            common = directory / "common.json"
            common.write_text(json.dumps(built[2]))
            participants = directory / "participants.json"
            call(compiler, "protocol-compile", common, destination=participants)
            proof = directory / "candidate.proof"
            for command, role in (("produce-artifact", "producer"),
                                  ("validate-artifact", "validator")):
                report = call(runtime, command, source, descriptor, construction,
                              participants, fixture / role / "inputs.json", compiler,
                              checker, proof, "15" if stem == "committed-two-factor" else "10",
                              destination=directory / f"{role}.json", cwd=fixture / role)
                expected = "produced" if role == "producer" else "accepted"
                assert report["status"] == expected, report
            reports[stem] = {"outcome": "accepted", "path": "independent artifacts",
                             "proof_bytes": proof.stat().st_size}

    (output / "summary.json").write_text(json.dumps(reports, indent=2) + "\n")
    print(json.dumps(reports, indent=2))



def test_protocol_frontend():
    main([])

if __name__ == "__main__":
    main()
