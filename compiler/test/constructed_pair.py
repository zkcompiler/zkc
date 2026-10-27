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
                      ("TwoSums", "examples/projects/sumcheck/composed"),
                      ("Schnorr", "examples/projects/schnorr")]:
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
        assert producer_names.count("protocol.send") == (4 if name == "TwoSums" else 2)
        assert "protocol.receive" not in producer_names
        assert "protocol.send" not in validator_names
        challenges = [op for op in instructions(producer[7])
                      if op[0] == "exec.apply" and op[2]
                      and op[2][0] == "transcript.native.indexed.challenge"]
        assert len(challenges) == (2 if name == "TwoSums" else 1)
        assert all(op[2][1:] == [[policy[5]], ""] for op in challenges)
        assert len(producer) == len(validator) == 11
        assert validator[9] == []
        if name == "Schnorr":
            assert producer[9] == [["service_3", policy[2], "3", "3", "random.bls12-381.fr/0"]]
            query = next(op for op in instructions(producer[7]) if op[0] == "protocol.service_query")
            assert query[3] == [] and len(query) == 7 and query[6][1] == []
            assert query[4] == ['!algebra.field<"bls12-381.fr">']
        else:
            assert producer[9] == []
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

    if name == "Schnorr":
        service = 'service_ports = [["service_3", "random.bls12-381.fr/0", 3]]'
        mutations = [
            ("root input", service, service.replace(', 3]]', ', 2]]')),
            ("nominal domain", service, service.replace('random.bls12-381.fr/0', 'random.other/0')),
            ("owner", f'role = "{policy[2]}"', f'role = "{policy[3]}"'),
            ("source site", 'site = "s0"', 'site = "another-site"'),
            ("unsupported method", 'method = "draw"', 'method = "index"'),
        ]
        for label, before, after in mutations:
            with case(f"Schnorr: refuse changed local service {label}"):
                assert before in candidate
                candidate_path.write_text(candidate.replace(before, after, 1))
                try:
                    commands.run([compiler, "protocol-constructed-pair", *arguments],
                                 refuses="native-proof-candidate")
                finally:
                    candidate_path.write_text(candidate)

counted()
