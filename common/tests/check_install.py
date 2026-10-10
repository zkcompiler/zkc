#!/usr/bin/env python3
"""Exercise an installed zkc and its companion compiler outside the checkout."""
import argparse
import json
from support.project import project_text
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def check(binary, compiler, output):
    output.mkdir(parents=True, exist_ok=False)
    for source, name in [(ROOT / "libraries/schnorr/lib.zkc", "schnorr.zkc"),
                         (ROOT / "examples/projects/schnorr/main.zkc", "main.zkc"),
                         (ROOT / "examples/projects/schnorr/inputs/example.Proof/witness.json", "witness.json"),
                         (ROOT / "examples/projects/schnorr/inputs/example.Proof/public.json", "public.json")]:
        shutil.copyfile(source, output / name)
    # Only the wrapper may introduce the companion compiler. Ambient checkout,
    # Cargo, Nix shell and user PATH configuration cannot satisfy this check.
    environment = {"PATH": "/no-ambient-tools", "HOME": str(output), "TMPDIR": str(output)}

    def invoke(label, *arguments, success=True):
        result = subprocess.run([str(binary), "--json", *map(str, arguments)], cwd=output,
                                env=environment, capture_output=True, text=True, timeout=120)
        (output / f"{label}.stdout").write_text(result.stdout)
        (output / f"{label}.stderr").write_text(result.stderr)
        if (result.returncode == 0) != success:
            raise RuntimeError(f"{label}: exit {result.returncode}: {result.stdout} {result.stderr}")
        return result.stdout

    invoke("help", "--help")
    invoke("version", "--version")
    (output / "zkc.toml").write_text(project_text({"format": "zkc.project/0",
        "modules": {"schnorr": "schnorr.zkc", "example": "main.zkc"}, "assets": {}}))
    checked = json.loads(invoke("check", "check", "--project=zkc.toml", "--declarations"))
    assert checked["status"] == "checked" and checked["scope"] == "definitions"
    assert any(d["name"] == "schnorr::Schnorr" for d in checked["declarations"])
    arguments = ["compile", "example::Proof", "--project=zkc.toml", "--output=proof.zkpkg"]
    built = json.loads(invoke("compile", *arguments))
    assert Path(built["compiler"]).resolve() == compiler.resolve()
    # An explicit selection must remain usable through the package wrapper.
    selected = json.loads(invoke("selected-compiler", *arguments, f"--compiler={compiler}"))
    assert Path(selected["compiler"]).resolve() == compiler.resolve()
    pin = selected["package_sha256"]
    inspected = json.loads(invoke("inspect", "inspect", "--package=proof.zkpkg", f"--sha256={pin}"))
    assert inspected["status"] == "inspected" and inspected["interface"]["kind"] == "proof"
    assert inspected["interface"]["entry"] == "example::Proof"
    refused = json.loads(invoke("wrong-pin", "inspect", "--package=proof.zkpkg", "--sha256=" + "0" * 64, success=False))
    assert refused["code"] == "entry-package-identity"
    result = json.loads(invoke("prove", "prove", "--package=proof.zkpkg", f"--sha256={pin}",
                               "--public=public.json", "--witness=witness.json", "--output=proof.bin"))
    assert result["status"] == "produced"
    verifying = ["verify", "--package=proof.zkpkg", f"--sha256={pin}",
                 "--public=public.json", "--proof=proof.bin"]
    assert json.loads(invoke("verify", *verifying))["status"] == "accepted"
    proof = output / "proof.bin"
    proof.write_bytes(proof.read_bytes()[:-1])
    assert json.loads(invoke("truncated", *verifying, success=False))["status"] == "refused"

    # The shared fold crosses source-library, generic map and native realization
    # boundaries. Exercise it with the installed compiler, outside the checkout.
    shutil.copyfile(ROOT / "examples/projects/mathematics/main.zkc", output / "mathematics.zkc")
    for name in ("vector", "symbolic"):
        shutil.copyfile(ROOT / f"libraries/zkc/{name}.zkc", output / f"{name}.zkc")
    (output / "mathematics.toml").write_text(project_text({"format": "zkc.project/0", "modules": {
        "example": "mathematics.zkc", "zkc::vector": "vector.zkc", "zkc::symbolic": "symbolic.zkc"
    }, "assets": {}}))
    checked = json.loads(invoke("math-check", "check", "--project=mathematics.toml",
                                "example::Run", "--declarations"))
    assert checked["scope"] == "entry"
    assert any(d["name"] == "zkc::vector::fold" for d in checked["declarations"])
    compiled = json.loads(invoke("math-compile", "compile", "--project=mathematics.toml",
                                 "example::Run", "--output=mathematics.zkpkg"))

    (output / "mathematics-inputs.json").write_text(json.dumps({
        "a": "2", "b": "3", "point": "4", "values": ["2", "3"]}))
    executed = json.loads(invoke("math-run", "run", "--package=mathematics.zkpkg",
                                 f"--sha256={compiled['package_sha256']}", "--session=installed_math",
                                 "--input=P=mathematics-inputs.json", "--results=mathematics-results.json"))
    assert executed["status"] == "executed"
    result = json.loads((output / "mathematics-results.json").read_text())
    assert result["roles"]["P"] == {"formal_result": "6", "runtime_result": "6"}

    # The packaged compiler also serves scaffolding and the standard project
    # workflow without ambient tools or explicit --compiler/input/output flags.
    project = output / "new-project"
    created = json.loads(invoke("new", "new", project))
    assert created["status"] == "initialized"
    value = project / "inputs/example.Main/P.json"
    value.write_text('{"value":"19"}\n')
    project_option = f"--project={project / 'zkc.toml'}"
    prepared = json.loads(invoke("prepare", "prepare", project_option))
    assert prepared["files"] == [] and prepared["preserved"] == [str(value)]
    executed = json.loads(invoke("default-run", "run", project_option))
    assert len(executed["session"]) == 32
    assert json.loads(Path(executed["results"]).read_text())["roles"]["P"]["result"] == "19"
    print(json.dumps({"status": "pass", "binary": str(binary), "compiler": str(compiler)}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    check(args.binary.absolute(), args.compiler.absolute(), args.output.resolve())
