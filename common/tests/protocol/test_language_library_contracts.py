"""Reusable 4.1 members connect actual protocols, custody and final acceptance."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path

import pytest

from entry import joint_package
from harness import load

ROOT = Path(__file__).resolve().parents[3]
FIXTURES = ROOT / "compiler/test/fixtures/layout/library-contracts"
PUBLIC = ROOT / "examples/projects/schnorr/inputs/example.Proof/public.json"


def sources(directory, client, replacements=()):
    modules = {"group_client": "group.zkc"} if client == "group" else {
        "evaluation": "evaluation.zkc", "sums": "sumcheck.zkc",
    }
    flags = ["--source-format=zkc-layout"]
    for module, filename in modules.items():
        text = (FIXTURES / filename).read_text()
        for selected, before, after in replacements:
            if selected == module:
                assert before in text
                text = text.replace(before, after)
        path = directory / filename
        path.write_text(text)
        flags.append(f"--module={module}={path}")
    return flags, "group_client::Run" if client == "group" else "sums::Run"


def subject(client):
    return ("group_client::Schnorr<group_client::Curve,group_client::Standard>"
            if client == "group" else "sums::Argument<sums::F,sums::Revealed>")


def compile_client(toolchain, journal, directory, client, replacements=(), flags=()):
    capture_directory = directory / f"capture-{len(journal.commands)}"
    capture_directory.mkdir()
    capture, entry = sources(capture_directory, client, replacements)
    checked = journal.json([
        toolchain.compiler, "language-check", *capture, f"--subject={subject(client)}",
        "--source-ast", "--source-correspondence",
    ], keep=f"{client}-check-{len(journal.commands)}.json")
    package = directory / f"{client}.zkpkg"
    package.write_text(journal.run([
        toolchain.compiler, "language-package", *capture, f"--entry={entry}", *flags,
    ], keep=f"{client}-package-{len(journal.commands)}.json"))
    pin = hashlib.sha256(package.read_bytes()).hexdigest()
    return package, pin, checked


def execute(toolchain, journal, directory, package, pin, inputs, *, refuses=None):
    request = directory / "inputs.json"
    request.write_text(json.dumps({"inputs": inputs}))
    output = directory / "outputs.json"
    report = journal.json([
        toolchain.runtime, "--json", "run", f"--package={package}",
        f"--sha256={pin}", f"--input={request}", f"--results={output}",
    ], refuses=refuses)
    if refuses:
        return None
    assert report["status"] == "executed"
    return json.loads(output.read_text())["value"]


def obligations(checked):
    return [item for spec in checked["assurance"]["specifications"]
            for item in spec["obligations"]]


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_sumcheck_hands_actual_residual_to_generic_opening(toolchain, journal, directory, flags):
    package, pin, checked = compile_client(toolchain, journal, directory, "sums", flags=flags)
    inputs = {"P": {"table": ["1", "2", "3", "4"]},
              "V": {"statement": ["1", "2", "3", "4"], "claimed": "10"}}
    assert execute(toolchain, journal, directory, package, pin, inputs) == {
        "P": {}, "V": {"accepted": True},
    }
    # Adding one to every table cell changes every evaluation by one, for every
    # challenge. This negative case does not depend on a lucky random draw.
    inputs["V"]["statement"] = ["2", "3", "4", "5"]
    assert execute(toolchain, journal, directory, package, pin, inputs)["V"]["accepted"] is False
    # A failed round check stops; it is different from the final false result.
    inputs["V"]["claimed"] = "11"
    execute(toolchain, journal, directory, package, pin, inputs,
            refuses="entry-host-run-failed")
    assert checked["assurance"]["status"] == "open"
    assert [item["role"] for item in obligations(checked)] == ["postcondition", "request"]
    assert all(item["status"] == "open" for item in obligations(checked))


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_group_member_preserves_associated_scalar_and_services(toolchain, journal, directory, flags):
    package, pin, checked = compile_client(toolchain, journal, directory, "group", flags=flags)
    public = json.loads(PUBLIC.read_text())
    inputs = {"P": {**public, "secret": "3"}, "V": public}
    assert execute(toolchain, journal, directory, package, pin, inputs) == {
        "P": {}, "V": {"accepted": True},
    }
    inputs["P"]["secret"] = "4"
    assert execute(toolchain, journal, directory, package, pin, inputs)["V"]["accepted"] is False
    child = joint_package(json.loads(package.read_text()))
    assert child["original"].count('"protocol.query"') == 2
    assert child["original"].count('"protocol.exchange"') == 3
    assert checked["assurance"]["status"] == "open"
    rows = obligations(checked)
    assert [item["role"] for item in rows].count("postcondition") == 2
    assert [item["role"] for item in rows].count("request") == 3
    assert len({item["companion"] for item in rows}) == 5
    assert all(item["status"] == "open" for item in rows)


def test_body_edit_retains_lookup_but_changes_actual_subject(toolchain, journal, directory):
    package, _, before = compile_client(toolchain, journal, directory, "group")
    original = joint_package(json.loads(package.read_text()))["original"]
    package, pin, after = compile_client(toolchain, journal, directory, "group", [(
        "group_client", "return base * response == commitment + point * challenge", "return false",
    )])
    changed = joint_package(json.loads(package.read_text()))["original"]
    assert changed != original
    assert [item["companion"] for item in obligations(before)] == [
        item["companion"] for item in obligations(after)
    ]
    assert all(item["status"] == "open" for item in obligations(after))
    public = json.loads(PUBLIC.read_text())
    inputs = {"P": {**public, "secret": "3"}, "V": public}
    assert execute(toolchain, journal, directory, package, pin, inputs)["V"]["accepted"] is False


def test_claim_custody_cannot_replace_final_check_or_be_duplicated(toolchain, journal, directory):
    capture, entry = sources(directory, "sums", [(
        "sums", "accepted <- O::Open<C>(claim, statement) @(P, V)",
        "first <- O::Open<C>(claim, statement) @(P, V)\n    accepted <- O::Open<C>(claim, statement) @(P, V)",
    )])
    journal.run([toolchain.compiler, "language-check", *capture, f"--entry={entry}"],
                refuses="source.move")


@pytest.mark.parametrize("client", ["group", "sums"])
def test_neutral_inventory_reaches_existing_exact_artifact_reader(
        toolchain, journal, directory, client):
    # This transport reader owns address and exact-subject checks, not formal
    # elaboration. Import the existing bridge instead of another frontend reader.
    load("library_contract_inventory", "lean/bridges/pipeline/source_claims.py")
    from bridges.common.lean_render import Refused
    from bridges.pipeline.source_inventory import Inventory

    capture, _ = sources(directory, client)
    flags = [*capture, f"--subject={subject(client)}"]
    checked = journal.json([toolchain.compiler, "language-check", *flags,
                            "--source-correspondence"], keep="checked.json")
    source = journal.run([toolchain.compiler, "language-emit", *flags])
    source_path = directory / "source.mlir"
    source_path.write_text(source)
    interface = journal.run([toolchain.compiler, "language-interface", *flags],
                            keep="interface.json")
    original = journal.run([toolchain.compiler, "protocol-structured", source_path,
                            f'--symbol={json.loads(interface)["protocol"]}'],
                           keep="structured-original.json")
    context = dict(source=source.encode(), interface_text=interface, original_text=original)
    inventory = Inventory(checked["source_correspondence"], **context)
    nodes = list(inventory.nodes.values())
    assert any(node["kind"] == "formal.security" for node in nodes)
    assert any(node["kind"] == "formal.target" and node["decision"] for node in nodes)
    if client == "group":
        assert any(node["kind"] == "formal.site" for node in nodes)
    assert checked["assurance"]["status"] == "open"
    changed = deepcopy(checked["source_correspondence"])
    changed["source_ast"]["capture"] = "0" * 64
    with pytest.raises(Refused, match="mixed source context"):
        Inventory(changed, **context)


@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_generic_protocol_preserves_permuted_distributed_custody(
        toolchain, journal, directory, flags):
    source = FIXTURES / "distributed.zkc"
    capture = ["--source-format=zkc-layout", f"--module=distributed={source}"]
    package = directory / "distributed.zkpkg"
    package.write_text(journal.run([
        toolchain.compiler, "language-package", *capture,
        "--entry=distributed::Run", *flags,
    ]))
    pin = hashlib.sha256(package.read_bytes()).hexdigest()
    assert execute(toolchain, journal, directory, package, pin, {"P": {}, "V": {}}) == {
        "P": {}, "V": {"accepted": True},
    }
