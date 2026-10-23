"""Actual policy-selected producer exports and checked pair containers."""
import hashlib
import json
from pathlib import Path
import re

from cases import case, counted
from commands import Commands
from project import project_arguments
from tools import compiler, records

ROOT = Path(__file__).resolve().parents[2]
OUT = records()
commands = Commands(OUT)


def instructions(block):
    for instruction in block:
        yield instruction
        for region in instruction[5]:
            yield from instructions(region[1])


for name, project in [("SmallSumcheck", "examples/projects/sumcheck"),
                      ("TwoSums", "examples/projects/sumcheck/composed")]:
    directory = OUT / name
    directory.mkdir()
    flags = ["--source-format=zkc", "--entry=example::Proof",
             *project_arguments(ROOT / project / "zkc.toml")]
    source = commands.run([compiler, "language-emit", *flags])
    deployment = json.loads(commands.run([compiler, "language-bundle", *flags]))
    policy = deployment[2][1]
    source_path, policy_path, candidate_path = [directory / file for file in
                                                ("source.mlir", "policy.json", "candidate.mlir")]
    source_path.write_text(source)
    policy_path.write_text(json.dumps(policy))
    candidate = commands.run([compiler, "protocol-construct-proof", source_path, policy_path])
    candidate_path.write_text(candidate)
    arguments = [source_path, policy_path, candidate_path]

    with case(f"{name}: actual producer and exact paired export"):
        producer = json.loads(commands.run([compiler, "protocol-constructed-participant", *arguments,
                                            "--role=producer"]))
        validator = json.loads(commands.run([compiler, "protocol-constructed-participant", *arguments]))
        explicit = json.loads(commands.run([compiler, "protocol-constructed-participant", *arguments,
                                            "--role=validator"]))
        pair = json.loads(commands.run([compiler, "protocol-constructed-pair", *arguments]))
        assert validator == explicit
        assert pair == ["zkc.constructed-pair/0", producer, validator]
        assert producer[1:4] == validator[1:4]
        assert producer[1] == "sha256:" + hashlib.sha256(source.encode()).hexdigest()
        assert producer[3] == policy and producer[4] != validator[4]
        producer_names = [op[0] for op in instructions(producer[7])]
        validator_names = [op[0] for op in instructions(validator[7])]
        assert producer_names.count("protocol.send") == (2 if name == "SmallSumcheck" else 4)
        assert "protocol.receive" not in producer_names
        assert "protocol.send" not in validator_names
        assert "crypto.exec.indexed_transcript_challenge" in producer_names
        for role, value in [("producer", producer), ("validator", validator), ("pair", pair)]:
            (directory / f"{role}.json").write_text(json.dumps(value) + "\n")

    with case(f"{name}: export refuses a changed producer arithmetic body"):
        match = next(match for match in re.finditer(r"(algebra.field_add )(%\w+), (%\w+)", candidate)
                     if match[2] != match[3])
        changed = candidate[:match.start()] + match[1] + match[2] + ", " + match[2] + candidate[match.end():]
        candidate_path.write_text(changed)
        try:
            for mode, options in [("protocol-constructed-participant", ["--role=producer"]),
                                  ("protocol-constructed-pair", [])]:
                commands.run([compiler, mode, *arguments, *options], refuses="native-proof-correspondence")
        finally:
            candidate_path.write_text(candidate)

    with case(f"{name}: role dispatch is exact and unambiguous"):
        for options in [["--role=other"], ["--role=producer", "--role=validator"],
                        ["--role=producer", "--role=producer"]]:
            commands.run([compiler, "protocol-constructed-participant", *arguments, *options],
                         refuses="native-proof-options")
        for mode in ["protocol-check-proof", "protocol-constructed-pair", "protocol-construct-proof"]:
            commands.run([compiler, mode, *arguments, "--role=producer"], refuses="native-proof-options")

counted()
