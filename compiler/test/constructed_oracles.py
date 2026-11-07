"""Retained FRI exports the actual constructed oracle execution on both roles."""
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
flags = ["--source-format=zkc", "--entry=example::Proof",
         *project_arguments(ROOT / "examples/projects/fri/zkc.toml")]
source = commands.run([compiler, "language-emit", *flags])
deployment = json.loads(commands.run([compiler, "language-bundle", *flags]))
policy = deployment[2][1]
source_path, policy_path, candidate_path = [OUT / name for name in
                                            ("source.mlir", "policy.json", "candidate.mlir")]
source_path.write_text(source)
policy_path.write_text(json.dumps(policy))
candidate = commands.run([compiler, "protocol-construct-proof", source_path, policy_path])
candidate_path.write_text(candidate)
arguments = [source_path, policy_path, candidate_path]


def instructions(block):
    for row in block:
        yield row
        for region in row[5]:
            yield from instructions(region[1])


with case("FRI: complete candidate export retains generated computation and ranges"):
    pair = json.loads(commands.run([compiler, "protocol-constructed-pair", *arguments]))
    assert pair[0] == "zkc.constructed-pair/0"
    assert pair[1][4] != pair[2][4]
    for role, child in zip(("producer", "validator"), pair[1:]):
        assert child[0] == "zkc.constructed-participant/0"
        assert child[1] == "sha256:" + hashlib.sha256(source.encode()).hexdigest()
        assert child[1:4] == pair[1][1:4]
        assert re.fullmatch(r"sha256:[0-9a-f]{64}", child[2])
        assert child[3] == policy
        (OUT / f"{role}.json").write_text(json.dumps(child) + "\n")
    body = list(instructions(pair[2][7]))
    ranges = [row for row in body if row[0] == "exec.range"]
    computations = [row for row in body if row[0] == "exec.compute"]
    assert ranges and computations
    assert all(isinstance(row[5][0][3], bool) for row in ranges)
    assert any(row[5][0][3] for row in ranges)
    for row in computations:
        assert len(row[5]) == 1 and len(row[5][0]) == 3
        assert row[5][0][2][0] == "func.return"
        assert len(row[5][0][0]) == len(row[3])
        assert len(row[5][0][2][1]) == len(row[4])
    assert any(row[0] == "data.finite_fold" for row in body)

with case("FRI: same-signature child-position substitution refuses before export"):
    match = re.search(r'callee = @(_oracle_virtual_\w+_position_)0', candidate)
    assert match is not None
    changed = candidate[:match.end() - 1] + "1" + candidate[match.end():]
    candidate_path.write_text(changed)
    try:
        commands.run([compiler, "protocol-constructed-pair", *arguments],
                     refuses="native-proof-correspondence")
    finally:
        candidate_path.write_text(candidate)

counted()
