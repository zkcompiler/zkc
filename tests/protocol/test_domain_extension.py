"""A new nominal type across source, MLIR, Rust execution and Lean meaning.

The expected field result and message bytes are independent arithmetic oracles.
Agreement covers this installed extension, not arbitrary backend refinement.
"""
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
MODULUS = 2**31 - 2**24 + 1


def write(directory, name, value):
    path = directory / name
    path.write_text(json.dumps(value))
    return path


def wire_vector(values):
    return (b"ZKCV\x01\x14" + len(values).to_bytes(4, "little")
            + b"".join(x.to_bytes(4, "little") for x in values)).hex()


@pytest.mark.parametrize("length,left,right", [
    (0, [], []),
    (1, [7], [9]),
    (4, [1, 2, 3, 4], [5, 6, 7, 8]),
    (2, [MODULUS - 1, 2], [2, 3]),
    (257, list(range(257)), list(reversed(range(257)))),
    (4, [1], [5, 6, 7, 8]),
    (4, [1, 2, 3, 4, 5], [5, 6, 7, 8]),
])
def test_fixed_vector_compiles_and_executes(toolchain, directory, journal, length, left, right):
    compiler = toolchain.compiler
    checker = toolchain.checker("interactive-protocol")
    text = (ROOT / "examples/protocols/fixed-vector.pir").read_text().replace(
        "N = 4", f"N = {length}")
    authored = directory / "example.pir"
    authored.write_text(text)
    source_value = journal.json([compiler, "protocol-source", authored])
    source = write(directory, "source.json", source_value)
    common_ir = journal.run([compiler, "protocol-import", source])
    assert f'!algebra.fixed_vector<!algebra.field<"koala-bear">, {length}>' in common_ir
    assert '"algebra.fixed_vector_dot"' in common_ir
    logical = journal.json([compiler, "protocol-export", "-"], common_ir)
    logical_path = write(directory, "logical.json", logical)
    assert all(binding[2] == ["koala-bear", str(length)] for binding in logical[1])
    physical_value = journal.json([compiler, "protocol-compile", source])
    physical = write(directory, "physical.json", physical_value)
    physical_ir = journal.run([compiler, "protocol-physical-ir", source])
    assert f'!algebra.fixed_vector<!algebra.field<"koala-bear">, {length}>' in physical_ir
    assert "plonky3.fixed-vector/1" in physical_ir
    assert journal.json([compiler, "protocol-export", "-"], physical_ir) == physical_value
    assert journal.json([checker, "--admit", source])[0] == "checked"
    assert journal.json([checker, "--check", source, physical])[0] == "checked"
    assert journal.json([checker, "--admit", logical_path])[0] == "checked"

    values = [("left", left), ("right", right)]
    native_inputs = write(directory, "native-inputs.json", [
        "zkc.run/2", "main", "fixed-vector", [],
        [["P", [], [[name, ["wire", wire_vector(value)]] for name, value in values], []],
         ["V", [], [], []]], []])
    reference_inputs = write(directory, "reference-inputs.json", [
        "zkc.reference-inputs/1", "main", "fixed-vector",
        [["P", [[name, ["vector:koala-bear", list(map(str, value))]] for name, value in values]],
         ["V", []]], [], [], []])
    actual = journal.json([toolchain.runtime, "run-protocol", source, physical,
                           native_inputs, checker])
    # A reference refusal is a structured observation with exit status one.
    observed = journal.attempt([checker, "--reference", source, reference_inputs])
    assert observed.returncode in (0, 1), observed.stderr
    reference = json.loads(observed.stdout)
    if len(left) != length or len(right) != length:
        assert actual["stop"]["detail"] == "refused:fixed-vector-length"
        assert reference[3][:2] == ["refused", "fixed-vector-length"]
        assert actual["wire"]["messages"] == 0
    else:
        expected = sum(x * y for x, y in zip(left, right)) % MODULUS
        wire = (b"ZKCV\x01\x13" + expected.to_bytes(4, "little")).hex()
        assert actual["outcome"] == ["returned", {"P": [], "V": [["wire", "field", wire]]}]
        assert reference[3] == ["returned", [["field:koala-bear", str(expected)]]]
        assert actual["wire"]["messages"] == 1
        assert actual["wire"]["payload_bytes"] == 10
        requests = [event[1][2] for event in reference[4] if event[0] == "request"]
        assert requests == ["fixed_vector.from_vector", "fixed_vector.from_vector", "fixed_vector.dot"]
    assert actual["resources"] == reference[5] == []


def test_logical_extension_without_backend(toolchain, directory, journal):
    compiler = toolchain.compiler
    text = (ROOT / "examples/protocols/fixed-vector.pir").read_text().replace("koala-bear", '"bls12-381.fr"')
    authored = directory / "unsupported.pir"
    authored.write_text(text)
    source = write(directory, "source.json", journal.json([compiler, "protocol-source", authored]))
    assert journal.json([toolchain.checker("interactive-protocol"), "--admit", source])[0] == "checked"
    # Logical formation and native lowering are separate judgments.
    result = journal.attempt([compiler, "protocol-compile", source])
    assert result.returncode == 1
    assert "binding-representation" in result.stderr or "binding-implementation" in result.stderr
