"""Produce real SDK fixtures and independently check meaningful proof mutations."""

import argparse
import copy
import hashlib
import json
import subprocess
from pathlib import Path

from reference import PRIME, invocation_root, reconstruct, scalar, scalar_wire


def frames(proof):
    result = []
    cursor = 40
    while cursor < len(proof):
        length = int.from_bytes(proof[cursor:cursor + 8], "little")
        if length != 38 or cursor + 8 + length > len(proof):
            raise ValueError("expected a complete canonical SDK fixture proof")
        result.append((cursor, cursor + 8, cursor + 8 + length))
        cursor += 8 + length
    return result


def rebind(fixture, public):
    """Change only the test mutation's header; this does not produce messages."""
    changed = copy.deepcopy(fixture)
    changed["public"] = public
    for key in ("public_rows", "invocation_tree", "invocation_root", "binding_sha256"):
        changed.pop(key, None)
    return b"ZKCPRF00" + hashlib.sha256(invocation_root(changed)).digest()


def generate(driver, compiler, project, output, *, evm_artifact=None, evm_sha256=None):
    output.mkdir(parents=True, exist_ok=True)
    results = {}
    command = [str(driver), "--compiler", str(compiler), "--project", str(project),
               "--entry", "example::Proof"]
    if (evm_artifact is None) != (evm_sha256 is None):
        raise ValueError("EVM artifact and independent manifest pin are required together")
    if evm_artifact is not None:
        command += ["--evm-artifact", str(evm_artifact), "--evm-sha256", evm_sha256]

    def run(name, rounds, *, proof=None, extra=(), decision=None, stopped=False, context="65766d"):
        args = command + ["--rounds", str(rounds), "--context", context] + list(extra)
        if proof is not None:
            path = output / f"{name}.proof"
            path.write_bytes(proof)
            args += ["--proof", str(path)]
        process = subprocess.run(args, text=True, capture_output=True, timeout=90)
        if process.returncode:
            raise RuntimeError(f"native {name}: {process.stderr}")
        fixture = json.loads(process.stdout)
        if fixture.get("format") != "zkc.evm-native-fixture/0":
            raise AssertionError(f"native {name} did not export a verifier fixture: {fixture}")
        reference = reconstruct(fixture)
        if fixture["decision"] != decision or reference["decision"] != decision:
            raise AssertionError(f"{name}: native/reference decision differs from {decision}")
        if (reference["stop"] is not None) != stopped:
            raise AssertionError(f"{name}: unexpected reference stop {reference['stop']}")
        native_failed = (fixture["native"]["stop"] is not None
                         or (fixture["decision"] is None and fixture.get("native_error") is not None))
        if native_failed != stopped:
            raise AssertionError(f"{name}: unexpected native failure")
        (output / f"{name}.json").write_text(json.dumps(fixture, indent=2) + "\n")
        (output / f"{name}.expected.json").write_text(json.dumps(reference, indent=2) + "\n")
        results[name] = {"decision": decision, "stop": reference["stop"],
                         "primitives": len(reference["trace"]),
                         "transitions": reference["transitions"],
                         "native_error": fixture.get("native_error"),
                         "native_stop": fixture["native"]["stop"]}
        return fixture, reference

    honest, _ = run("honest-16", 4, decision=True)
    run("honest-1024", 10, decision=True)
    run("honest-context-max", 10, context=bytes(4096).hex(), decision=True)
    zero, _ = run("honest-zero", 0, decision=True)
    proof = bytes.fromhex(honest["proof"])
    spans = frames(proof)

    terminal = bytearray(proof)
    for (_, start, end), delta in zip(spans[-2:], (1, -1), strict=True):
        terminal[start:end] = scalar_wire(scalar(terminal[start:end]) + delta)
    run("terminal-false", 4, proof=terminal, decision=False)
    run("terminal-false-trailing-stop", 4, proof=terminal + b"\x00", stopped=True)

    early = bytearray(proof)
    _, start, end = spans[0]
    early[start:end] = scalar_wire(scalar(early[start:end]) + 1)
    _, early_reference = run("require-stop", 4, proof=early, stopped=True)
    late = bytearray(early)
    late[spans[2][0]:spans[2][1]] = bytes([255]) * 8
    _, late_reference = run("require-stop-malformed-later", 4, proof=late, stopped=True)
    if early_reference["trace"] != late_reference["trace"]:
        raise AssertionError("a frame beyond the source stop affected the primitive prefix")

    short = bytearray(proof)
    short[spans[1][0]:spans[1][1]] = (37).to_bytes(8, "little")
    run("second-frame-codec-stop", 4, proof=short, stopped=True)
    residue = bytearray(proof)
    residue[start:end] = b"ZKCV\x00\x01" + PRIME.to_bytes(32, "little")
    run("noncanonical-residue-stop", 4, proof=residue, stopped=True)
    run("truncated-proof-stop", 4, proof=proof[:spans[2][0]], stopped=True)
    run("trailing-proof-stop", 4, proof=proof + b"\x00", stopped=True)
    run("budget-zero-stop", 4, proof=proof, extra=("--budget", "0"), stopped=True)
    run("budget-one-stop", 4, proof=proof, extra=("--budget", "1"), stopped=True)
    run("budget-last-delivery-stop", 4, proof=proof, extra=("--budget", "15"), stopped=True)

    public = list(zero["public"])
    public[1] = scalar_wire(2).hex()
    run("zero-terminal-false", 0, proof=rebind(zero, public),
        extra=("--claim", "2"), decision=False)

    values_path = output / "sixteen-values.json"
    values_path.write_text(json.dumps(list(range(1, 17))) + "\n")
    public = list(honest["public"])
    public[2] = (b"ZKCV\x00\x1f" + (11).to_bytes(8, "little")).hex()
    run("round-bound-stop", 11, proof=rebind(honest, public),
        extra=("--values", str(values_path)), stopped=True)

    manifest = {"format": "zkc.evm-native-cases/0", "command": command, "cases": results,
                "scope": "SDK native/reference validation; no deployed target claim"}
    (output / "cases.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--driver", type=Path, required=True)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--project", type=Path,
                        default=Path(__file__).resolve().parents[3] / "examples/projects/sumcheck-keccak/zkc.toml")
    parser.add_argument("--evm-artifact", type=Path)
    parser.add_argument("--evm-sha256")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = generate(args.driver.resolve(), args.compiler.resolve(), args.project.resolve(), args.output.resolve(),
                      evm_artifact=args.evm_artifact, evm_sha256=args.evm_sha256)
    print(json.dumps(result["cases"], indent=2))


if __name__ == "__main__":
    main()
