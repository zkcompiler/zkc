"""Repeat provenance and the exact logical-slot boundary through production APIs."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from component_cases import descriptor_cases, repeat_cases, slot_case
from tools import compiler, records

directory = records()
commands = Commands(directory)
manifest = []
(directory / "descriptor-cases.json").write_text(json.dumps(descriptor_cases()) + "\n")
fixture = Path(__file__).parent / "fixtures/source-claims/components-repeat-values.zkc"


def capture(name, source, refusal=None, slots=None):
    path = directory / (name + ".zkc")
    path.write_text(source)
    flags = ["--source-format=zkc", "--subject=claims::Run", f"--module=claims={path}"]
    emitted = commands.run([compiler, "language-emit", *flags])
    original = directory / (name + ".mlir")
    original.write_text(emitted)
    interface = json.loads(commands.run([compiler, "language-interface", *flags]))
    snapshot = json.loads(commands.run([compiler, "protocol-structured", original,
                                        "--symbol=" + interface["protocol"]]))
    snapshot_path = directory / (name + "-snapshot.json")
    snapshot_path.write_text(json.dumps(snapshot) + "\n")
    result = commands.run([compiler, "language-check", *flags, "--source-claims"], refuses=refusal)
    wire_path = directory / (name + "-claims.json")
    if refusal is None:
        wire = json.loads(result)["source_claims"]
        wire_path.write_text(json.dumps(wire) + "\n")
        if slots is not None:
            assert len(wire["proposals"]) == 1
            assert len(wire["proposals"][0][5]) == slots
        if name.endswith("handoff") or name == "pure-accepting":
            repeats = [row for row in wire["seams"] if row[1][0] == "repeat_result"]
            assert repeats and all(len(row[3]) == 2 for row in repeats)
            inputs = [row for row in wire["seams"] if row[1][0] == "repeat_input"]
            assert inputs and any(row[1][2] == 0 for row in inputs)
            if not name.startswith("pure"):
                assert any(row[2] == "method" for row in repeats)
                assert any(row[2] == "method" for row in inputs)
    manifest.append([name, str(snapshot_path), str(wire_path) if refusal is None else refusal])
    (directory / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")


for name, source, refusal in repeat_cases(fixture.read_text()):
    with case(name):
        capture(name, source, refusal)

for name, parameters, duplicate_residual, duplicate_clause, refusal in [
    ("slots-512", 256, False, False, None),
    ("slots-512-duplicate-clause", 256, False, True, None),
    ("slots-513", 257, True, False, "component-instantiation-limit"),
    ("slots-514", 257, False, False, "component-instantiation-limit"),
]:
    with case(name):
        capture(name, slot_case(parameters, duplicate_residual, duplicate_clause), refusal, 512)

print(f"component boundary controls: {counted()} cases; manifest: {directory / 'manifest.json'}")
