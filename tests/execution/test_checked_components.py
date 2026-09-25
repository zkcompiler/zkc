"""An interface-checked client, two layouts, and independent actual execution."""
import json
from pathlib import Path

from journal import Journal


SOURCE = Path(__file__).resolve().parents[2] / "examples/protocols/checked-components.pir"


def test_checked_components(toolchain, directory):
    journal = Journal(directory)
    source = journal.run([toolchain.compiler, "protocol-source", SOURCE])
    parsed = json.loads(source)
    assert parsed[0] == "zkc.protocol/1"
    assert "resource_unit:" in source and '"bool"' in source
    source_path = journal.write("linked-source.json", parsed)
    checker = toolchain.checker("interactive-protocol")
    physical = json.loads(journal.run([toolchain.compiler, "protocol-compile", source_path]))
    physical_path = journal.write("physical.json", physical)
    journal.run([checker, "--check", source_path, physical_path])

    # This also checks the real frontend -> PIR -> projected -> physical path,
    # rather than running a handcrafted interpretation of the library API.
    for entry in ("empty", "stored"):
        for valid in (True, False):
            label = f"{entry}-{valid}"
            reference_inputs = ["zkc.reference-inputs/1", entry, "components",
                                [["Prover", [["ok", ["bool", str(valid).lower()]]]]],
                                [], [], []]
            encoded = (b"ZKCV\x01\x05" + bytes([valid])).hex()
            native_inputs = ["zkc.run/2", entry, "components", [],
                             [["Prover", [], [["ok", ["wire", encoded]]], []]], []]
            reference = json.loads(journal.run([
                checker, "--reference", source_path,
                journal.write(f"{label}-reference-inputs.json", reference_inputs)]))
            native = json.loads(journal.run([
                toolchain.runtime, "run-protocol", source_path, physical_path,
                journal.write(f"{label}-native-inputs.json", native_inputs), checker]))
            requests = [event[1][2] for event in reference[4] if event[0] == "request"]
            assert requests[0] == "control.require"
            assert native["wire"]["messages"] == native["wire"]["payload_bytes"] == 0
            if valid:
                assert reference[3] == ["returned", [["bool", "true"]]]
                assert native["outcome"] == ["returned", {"Prover": [["bool", True]]}]
                expected = ["control.require"]
                if entry == "empty":
                    expected += ["resource_unit.create", "resource_unit.consume"]
                assert requests == expected
                assert reference[5] == []  # all temporary logical permissions discarded
            else:
                assert reference[3][:2] == ["reject", "require"]
                assert native["outcome"][0] == "stopped"
                assert native["stop"]["detail"] == "rejected:require"
                assert requests == ["control.require"]
                assert reference[5] == []  # a stopped guard never creates a token
            assert native["resources"] == []
    journal.save()
