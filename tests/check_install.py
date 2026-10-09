#!/usr/bin/env python3
"""Exercise an installed zkc and its companion compiler outside the checkout."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def check(binary, compiler, output):
    output.mkdir(parents=True, exist_ok=False)
    for source, name in [(ROOT / "libraries/schnorr/lib.zkc", "schnorr.zkc"),
                         (ROOT / "examples/projects/schnorr/main.zkc", "main.zkc"),
                         (ROOT / "examples/projects/schnorr/prover.json", "prover.json"),
                         (ROOT / "examples/projects/schnorr/verifier.json", "verifier.json")]:
        shutil.copyfile(source, output / name)
    # Only the wrapper may introduce the companion compiler. Ambient checkout,
    # Cargo, Nix shell and user PATH configuration cannot satisfy this check.
    environment = {"PATH": "/no-ambient-tools", "HOME": str(output), "TMPDIR": str(output)}

    def invoke(label, *arguments, success=True):
        result = subprocess.run([str(binary), *map(str, arguments)], cwd=output,
                                env=environment, capture_output=True, text=True, timeout=120)
        (output / f"{label}.stdout").write_text(result.stdout)
        (output / f"{label}.stderr").write_text(result.stderr)
        if (result.returncode == 0) != success:
            raise RuntimeError(f"{label}: exit {result.returncode}: {result.stdout} {result.stderr}")
        return result.stdout

    invoke("help", "--help")
    invoke("version", "--version")
    (output / "zkc.json").write_text(json.dumps({"format": "zkc.project/0",
        "modules": {"schnorr": "schnorr.zkc", "example": "main.zkc"}, "assets": {}}))
    checked = json.loads(invoke("check", "check", "--project=zkc.json", "--declarations"))
    assert checked["status"] == "checked" and checked["scope"] == "definitions"
    assert any(d["name"] == "schnorr::Schnorr" for d in checked["declarations"])
    arguments = ["compile", "--entry=example::Proof", "--project=zkc.json", "--output=proof.entry"]
    built = json.loads(invoke("compile", *arguments))
    assert Path(built["compiler"]).resolve() == compiler.resolve()
    # An explicit selection must remain usable through the package wrapper.
    selected = json.loads(invoke("selected-compiler", *arguments, f"--compiler={compiler}"))
    assert Path(selected["compiler"]).resolve() == compiler.resolve()
    pin = selected["package_sha256"]
    inspected = json.loads(invoke("inspect", "inspect", "proof.entry", pin))
    assert inspected["status"] == "inspected" and inspected["interface"]["kind"] == "proof"
    assert inspected["interface"]["entry"] == "example::Proof"
    refused = json.loads(invoke("wrong-pin", "inspect", "proof.entry", "0" * 64, success=False))
    assert refused["code"] == "entry-package-identity"
    for name, inputs, status in [("prove", "prover.json", "produced"),
                                  ("verify", "verifier.json", "accepted")]:
        result = json.loads(invoke(name, name, "proof.entry", pin, inputs, "proof.bin"))
        assert result["status"] == status
    proof = output / "proof.bin"
    proof.write_bytes(proof.read_bytes()[:-1])
    refused = json.loads(invoke("truncated", "verify", "proof.entry", pin,
                               "verifier.json", "proof.bin", success=False))
    assert refused["status"] == "refused"
    print(json.dumps({"status": "pass", "binary": str(binary), "compiler": str(compiler)}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    check(args.binary.absolute(), args.compiler.absolute(), args.output.resolve())
