"""Public source-correspondence artifact and refusal controls."""

import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from project import project_arguments
from tools import compiler, records

commands = Commands(records())
source = records() / "authored.zkc"
source.write_text("""module authored;
protocol P roles(A)(x:bool@A)->(ok:bool@A){return(ok=x);}
""")
arguments = ["--source-format=zkc", f"--module=authored={source}"]

with case("one selected original supplies syntax, bindings and actual rows"):
    report = json.loads(commands.run([
        compiler, "language-check", *arguments, "--subject=authored::P",
        "--source-correspondence", "--source-claims",
    ]))
    artifact = report["source_correspondence"]
    assert artifact["admission"] == report["source_claims"]["admission"]
    assert artifact["source_ast"]["capture"] == report["capture"]
    assert artifact["bindings"]["locals"]
    assert artifact["rows"]
    for row in artifact["rows"]:
        target = artifact["snapshot"]
        for index in row["row"]:
            target = target[index]
        assert isinstance(target, list)

with case("complete Schnorr subject exports one bounded source artifact"):
    manifest = Path(__file__).resolve().parents[2] / "examples/projects/schnorr/zkc.toml"
    report = json.loads(commands.run([
        compiler, "language-check", "--source-format=zkc",
        *project_arguments(manifest), "--entry=example::Proof",
        "--source-correspondence",
    ]))
    artifact = report["source_correspondence"]
    assert artifact["snapshot"][2] == artifact["admission"]["original_sha256"]
    assert len(artifact["rows"]) > 10
    assert len(artifact["bindings"]["locals"]) > 10
    # Every domain, function and oracle row names exactly one closed instance
    # or generated definition, and every site has its occurrence row.
    owners = [item["symbol"] for item in artifact["instances"]["instances"]]
    owners += [item["symbol"] for item in artifact["generated"]]
    assert len(owners) == len(set(owners))
    for table in (4, 7):
        for row in artifact["snapshot"][table]:
            if table == 4 or row[0] in ("function", "oracle"):
                assert row[1] in owners
    assert len(artifact["generated_rows"]) == len(artifact["generated"])
    assert artifact["occurrences"]
    assert any(occurrence["nodes"] for occurrence in artifact["occurrences"])

with case("source correspondence requires a unique check-only selection"):
    for extra in (["--source-correspondence"],
                  ["--subject=authored::P", "--source-correspondence", "--source-correspondence"]):
        commands.run([compiler, "language-check", *arguments, *extra], refuses="source.options")
    commands.run([compiler, "language-emit", *arguments, "--subject=authored::P",
                  "--source-correspondence"], refuses="source.options")

print(f"Source correspondence controls: {counted()} cases; {commands.save()}")
