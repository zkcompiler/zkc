"""Source claims and exact references to the admitted structured export."""

import hashlib
import json
from pathlib import Path

from cases import case
from commands import Commands
from tools import compiler, records

commands = Commands(records())
fixtures = Path(__file__).parent / "fixtures" / "source-claims"


def cardinality_domains(value):
    """Read normalized builtin arguments without interpreting their sizes."""
    if isinstance(value, dict):
        if (
            value.get("kind") == "application"
            and value.get("name") == "cardinality"
            and value.get("version") is None
        ):
            assert len(value["arguments"]) == 1
            argument = value["arguments"][0]
            assert argument["label"] is None
            assert argument["value"]["kind"] == "reference"
            yield argument["value"]["name"]
        for child in value.values():
            yield from cardinality_domains(child)
    elif isinstance(value, list):
        for child in value:
            yield from cardinality_domains(child)


for fixture in ("schnorr", "sumcheck", "nested", "guess", "cardinality"):
    with case(fixture):
        arguments = [
            "--source-format=zkc",
            "--entry=claims::Demo",
            f"--module=claims={fixtures / (fixture + '.zkc')}",
        ]
        result = commands.run(
            [compiler, "language-check", *arguments, "--source-claims"]
        )
        claims = json.loads(result)["source_claims"]
        subject_arguments = [arg.replace("--entry=", "--subject=", 1) for arg in arguments]
        selected = json.loads(commands.run(
            [compiler, "language-check", *subject_arguments, "--source-claims"]
        ))
        assert selected["scope"] == "subject" and selected["source_claims"] == claims
        domains = list(cardinality_domains(claims["claims"]))
        assert domains and set(domains) == {"bls12-381.fr"}
        emitted = commands.run([compiler, "language-emit", *arguments])
        reference = claims["admission"]
        digest = "sha256:" + hashlib.sha256(emitted.encode()).hexdigest()
        assert reference["original_sha256"] == digest
        original = records() / (fixture + ".mlir")
        original.write_text(emitted)
        structured = commands.run(
            [
                compiler,
                "protocol-structured",
                original,
                f"--symbol={reference['protocol_symbol']}",
            ]
        )
        unit = json.loads(structured)
        assert unit[2] == digest and unit[3] == reference["protocol_symbol"]
        if fixture == "guess":
            target = claims["claims"][0]["request"]["target"]
            assert target == {
                "protocol": reference["protocol_symbol"],
                "language": {
                    "kind": "application",
                    "name": "languages.guess",
                    "version": 0,
                    "arguments": [],
                },
            }
            # Endpoint.ImportedLanguage checks all contracts in the raw unit.
            assert unit[8] and all(not clauses for _, clauses in unit[8])
        for options in (
            [arg for arg in arguments if not arg.startswith("--entry=")]
            + ["--source-claims"],
            arguments + ["--source-claims", "--source-claims"],
        ):
            commands.run(
                [compiler, "language-check", *options], refuses="source.options"
            )
        commands.run(
            [compiler, "language-emit", *arguments, "--source-claims"],
            refuses="source.options",
        )

with case("closed protocol subject uses exact original and interface"):
    path = records() / "closed-subject.zkc"
    source = (fixtures / "cardinality.zkc").read_text()
    source = source.replace("for Demo", "for Run<Alias>").replace(
        "stage=executable_bytes", "stage=interactive"
    )
    source += "entry fn Wrapper(inputs: Run<Fr>::Inputs) { return Run<Fr>::run(inputs); }"
    path.write_text(source)
    flags = ["--source-format=zkc", f"--module=claims={path}"]
    selected = "--subject=claims::Run<claims::Fr>"
    response = json.loads(commands.run(
        [compiler, "language-check", *flags, selected, "--source-claims"]
    ))
    exported = response["source_claims"]
    assert response["scope"] == "subject" and len(exported["claims"]) == 1
    original = commands.run([compiler, "language-emit", *flags, selected])
    interface = commands.run([compiler, "language-interface", *flags, selected])
    assert exported["entry"] == json.loads(interface)["entry"] == response["entry"]
    assert exported["admission"]["original_sha256"] == "sha256:" + hashlib.sha256(original.encode()).hexdigest()
    assert exported["admission"]["interface_sha256"] == "sha256:" + hashlib.sha256(
        interface.removesuffix("\n").encode()
    ).hexdigest()
    for extra in (["--entry=claims::Demo"], ["--entry-kind=proof"], [selected]):
        commands.run([compiler, "language-emit", *flags, selected, *extra], refuses="source.options")
    for selector in ("--subject=claims::Wrapper", "--subject=claims::Run<index>"):
        commands.run([compiler, "language-interface", *flags, selector],
                     refuses="source.subject" if "Wrapper" in selector else "source.generic")
    commands.run([compiler, "language-check", *flags, "--entry=claims::Wrapper", "--source-claims"],
                 refuses="source.claim.subject")
