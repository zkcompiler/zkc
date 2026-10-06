"""Compare restored participant execution with independent Lean field arithmetic."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--consumer", required=True, type=Path)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--checker", required=True, type=Path)
    args = parser.parse_args()
    modulus = 2**31 - 2**24 + 1
    with tempfile.TemporaryDirectory(prefix="zkc-domain-execution-") as temporary:
        work = Path(temporary)
        candidate = work / "restored.json"
        source = work / "restored.json.source.json"
        subprocess.run([args.consumer, candidate], check=True)

        def observe(command):
            result = subprocess.run(command, text=True, capture_output=True)
            assert result.returncode == 0, result.stderr or result.stdout
            return json.loads(result.stdout)

        def write(name, value):
            path = work / name
            path.write_text(json.dumps(value))
            return path

        assert observe([args.checker, "--admit", source])[0] == "checked"
        assert observe([args.checker, "--check", source, candidate])[0] == "checked"
        bundle = work / "restored.json.bundle"
        pin = hashlib.sha256(bundle.read_bytes()).hexdigest()
        source_value = json.loads(source.read_text())
        assert {binding[0] for binding in source_value[1]} == {"first_add", "second_add", "unused_mul"}
        names = [port[0] for port in source_value[3][0][4]]
        assert len(names) == 3
        for values in ([2, 3, 5], [modulus - 1, 2, modulus - 3]):
            ports = list(zip(names, values, strict=True))
            def wire(value):
                return (b"ZKCV\x01\x13" + value.to_bytes(4, "little")).hex()
            native = write("inputs.json", ["zkc.run/2", "main", "domain-example", [], [
                ["prover", [], [[name, ["wire", wire(value)]] for name, value in ports], []],
                ["verifier", [], [], []]], []])
            reference = write("reference.json", ["zkc.reference-inputs/1", "main", "domain-example", [
                ["prover", [[name, ["field:koala-bear", str(value)]] for name, value in ports]],
                ["verifier", []]], [], [], []])
            actual = observe([args.runtime, "run-protocol", source, candidate, native, args.checker])
            expected = observe([args.checker, "--reference", source, reference])
            total = sum(values) % modulus
            assert actual["outcome"] == ["returned", {"prover": [], "verifier": [["wire", "field", wire(total)]]}]
            assert expected[3] == ["returned", [["field:koala-bear", str(total)]]]
            assert actual["wire"]["messages"] == 1
            assert actual["resources"] == expected[5] == []
            invocation = write("bundle-inputs.json", ["zkc.bundle-inputs/1", "domain-example", [
                ["P", [[str(i), "field:koala-bear@plonky3.koala-bear/1", ["wire", wire(value)]]
                       for i, value in enumerate(values)], []], ["V", [], []]], []])
            compiled = observe([args.runtime, "run-bundle", bundle, pin, invocation])
            assert compiled["outcome"] == ["completed"] and compiled["acceptance"] is None
            assert compiled["roles"][1]["outputs"] == [["wire", "field:koala-bear@plonky3.koala-bear/1", wire(total)]]
            assert compiled["resources"] == []
        print("Restored specialization: independent admission, correspondence and execution passed")


if __name__ == "__main__":
    main()
