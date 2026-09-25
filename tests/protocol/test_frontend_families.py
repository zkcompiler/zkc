"""Whole-protocol source families through independent admission and execution.

These compare concrete selections, not a proof about all instantiations of a
family. The Lean reader checks the emitted common source and participants; the
Rust runtime executes the selected backend contracts.
"""

import json
from pathlib import Path

import pytest
from journal import Journal
from toolchain import Toolchain, records

ROOT = Path(__file__).resolve().parents[2]
EXAMPLES = ROOT / "examples/protocols"


def execute(text, inputs, directory):
    tools = Toolchain()
    journal = Journal(directory)
    source = directory / "source.json"
    participants = directory / "participants.json"
    host_inputs = directory / "inputs.json"
    source.write_text(journal.run([tools.compiler, "protocol-source", "-"], text))
    participants.write_text(journal.run([tools.compiler, "protocol-compile", "-"], text))
    host_inputs.write_text(json.dumps(inputs))
    report = journal.json([
        tools.runtime, "run-protocol", source, participants, host_inputs,
        tools.checker("interactive-protocol"),
    ])
    journal.write(directory / "execution.json", report)
    return report


def polynomial_reference(inputs, domain, directory):
    tools = Toolchain()
    journal = Journal(directory / "reference")
    values = [
        [role, [[name, [value[0] + ":" + domain, value[1]]]
                for name, value in ports]]
        for role, _, ports, _ in inputs[4]
    ]
    path = journal.write("inputs.json", [
        "zkc.reference-inputs/1", inputs[1], inputs[2], values, [], [], [],
    ])
    return journal.json([
        tools.checker("interactive-protocol"), "--generic-reference",
        directory / "source.json", path,
    ])


@pytest.mark.parametrize("domain", ["koala-bear", "bls12-381.fr"])
def test_polynomial_family_execution(domain):
    directory = records(case=f"polynomial-{domain}")
    directory.mkdir(parents=True, exist_ok=True)
    text = (EXAMPLES / "folded-contraction-family.pir").read_text()
    text = text.replace("F = koala-bear", f'F = "{domain}"')
    inputs = json.loads((EXAMPLES / "folded-contraction.inputs.json").read_text())
    report = execute(text, inputs, directory)
    assert report["outcome"][0] == "returned", report
    # Native KoalaBear exposes its canonical field wire; the BLS host retains
    # its decimal presentation. Assert the installed codec, then compare the
    # numeric result with Lean's separately computed field value.
    worker = report["outcome"][1]["Worker"][0]
    if domain == "koala-bear":
        assert worker[:2] == ["wire", "field"]
        wire = bytes.fromhex(worker[2])
        assert wire[:6] == b"ZKCV\x01\x13" and len(wire) == 10
        result = int.from_bytes(wire[6:], "little")
    else:
        assert worker[0] == "field"
        result = int(worker[1])
    reference = polynomial_reference(inputs, domain, directory)
    assert reference[3] == ["returned", [["field:" + domain, str(result)], ["bool", "true"]]]
    assert result == 270
    assert report["outcome"][1]["Checker"] == [["bool", True]], report


@pytest.mark.parametrize("domain", ["bls12-381.g1", "bn254.g1", "bn254.g2"])
def test_group_family_execution(domain):
    directory = records(case=f"group-{domain}")
    directory.mkdir(parents=True, exist_ok=True)
    text = (EXAMPLES / "group-agreement-family.pir").read_text()
    text = text.replace('G = "bls12-381.g1"', f'G = "{domain}"')
    inputs = ["zkc.run/2", "main", "group-family", [], [
        ["Sender", [], [], []], ["Receiver", [], [], []],
    ], []]
    report = execute(text, inputs, directory)
    assert report["outcome"][0] == "returned", report
    assert report["outcome"][1]["Receiver"] == [["bool", True]], report


def test_family_failure_retains_protocol_rejection():
    directory = records(case="polynomial-rejection")
    directory.mkdir(parents=True, exist_ok=True)
    text = (EXAMPLES / "folded-contraction-family.pir").read_text()
    inputs = json.loads((EXAMPLES / "folded-contraction.inputs.json").read_text())
    inputs[4][1][2][1][1] = ["field", "271"]
    report = execute(text, inputs, directory)
    reference = polynomial_reference(inputs, "koala-bear", directory)
    assert reference[3][:2] == ["reject", "require"], reference
    assert report["outcome"][0] == "stopped", report
    assert report["stop"]["role"] == "Checker", report


def test_closed_composition_executes_named_ports():
    directory = records(case="closed-composition")
    directory.mkdir(parents=True, exist_ok=True)
    text = (EXAMPLES / "group-agreement-family.pir").read_text()
    text = text[:text.index("  entry main")] + '''
      protocol RepeatAgreement<G: ScalarAction> {
        roles (Sender, Receiver);
        outputs (Receiver accepted: bool);
        dependencies (child: GroupAgreement::<G=G>());
        invoke child() -> {accepted: first};
        invoke child() -> {accepted: second};
        finish {accepted: second};
      }
      entry main = RepeatAgreement::<G="bls12-381.g1">;
    }'''
    inputs = ["zkc.run/2", "main", "closed-source-composition", [], [
        ["Sender", [], [], []], ["Receiver", [], [], []],
    ], []]
    report = execute(text, inputs, directory)
    assert report["outcome"] == ["returned", {"Receiver": [["bool", True]], "Sender": []}], report
