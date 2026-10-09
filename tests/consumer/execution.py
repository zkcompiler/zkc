"""Execute exact installed Compiler bytes in independent runtime processes."""

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
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="zkc-installed-execution-") as temporary:
        work = Path(temporary)
        subprocess.run([args.consumer, work], check=True, timeout=60)

        def write(name, value):
            path = work / name
            path.write_text(json.dumps(value))
            return path

        def run(*command, refusal=None):
            result = subprocess.run([args.runtime, *command], capture_output=True,
                                    text=True, timeout=60)
            assert result.returncode == (1 if refusal else 0), result.stdout + result.stderr
            record = json.loads(result.stdout)
            if refusal:
                assert record["status"] == "refused" and record["code"] == refusal, record
            return record

        result = subprocess.run([args.runtime, "invalid-command"], capture_output=True,
                                text=True, timeout=60)
        assert result.returncode == 2 and "Unknown command" in result.stderr
        assert not result.stdout

        bundle = work / "run.bundle"
        pin = hashlib.sha256(bundle.read_bytes()).hexdigest()
        inputs = write("bundle.json", ["zkc.bundle-inputs/0", "installed", [
            ["Solo", [["0", "bool@native.bool/0", ["wire", "5a4b4356000501"]]], []]], []])
        result = run("run-bundle", bundle, pin, inputs)
        assert result["outcome"] == ["completed"] and result["acceptance"] is None
        assert result["roles"][0]["outputs"] == [["wire", "bool@native.bool/0", "5a4b4356000501"]]
        run("run-bundle", bundle, "00" * 32, inputs, refusal="run-Identity")

        deployment = work / "proof.deployment"
        pin = hashlib.sha256(deployment.read_bytes()).hexdigest()
        producer = write("producer.json", ["zkc.native-proof-inputs/0", [], [
            ["0", ["wire", "5a4b4356000501"]]], "", [], "0"])
        validator = write("validator.json", ["zkc.native-proof-inputs/0", [], [], "", [], "0"])
        proof = work / "proof.bin"
        proof.write_bytes(b"previous proof")
        for command, request in [("prove-bundle", producer), ("verify-bundle", validator)]:
            refused = run(command, deployment, pin, request, proof,
                          refusal="native-proof-binding-policy")
            assert refused["binding_scope"] == "header" and refused["phase"] == "admission"
            assert proof.read_bytes() == b"previous proof"
        result = run("prove-bundle", deployment, pin, producer, proof, "--allow-header-only")
        assert result["status"] == "produced" and result["binding_scope"] == "header"
        result = run("verify-bundle", deployment, pin, validator, proof, "--allow-header-only")
        assert result["status"] == "accepted" and result["binding_scope"] == "header"
        for data, code in [(proof.read_bytes()[:-1], "proof-truncated"),
                           (proof.read_bytes() + b"x", "proof-trailing")]:
            malformed = work / "malformed.bin"
            malformed.write_bytes(data)
            run("verify-bundle", deployment, pin, validator, malformed,
                "--allow-header-only", refusal=code)
        for options in [[], ["--allow-header-only"]]:
            refused = run("verify-bundle", deployment, "00" * 32, validator, proof,
                          *options, refusal="native-proof-deployment-binding")
            assert "binding_scope" not in refused
        package = work / "run.entry"
        pin = hashlib.sha256(package.read_bytes()).hexdigest()
        inputs = write("named-run.json", {"format": "zkc.entry-run/0", "session": "installed",
            "roles": {"P": {"inputs": {"x": True}}}})
        outputs = work / "named-results.json"
        result = run("run", package, pin, inputs, f"--results={outputs}")
        assert result["status"] == "executed"
        assert json.loads(outputs.read_text())["roles"]["P"] == {"r": True}
        run("run", package, "00" * 32, inputs, refusal="entry-package-identity")

        package = work / "proof.entry"
        pin = hashlib.sha256(package.read_bytes()).hexdigest()
        producer = write("named-producer.json", {"format": "zkc.entry-proof/0",
            "public": {}, "inputs": {"x": True}})
        verifier = write("named-verifier.json", {"format": "zkc.entry-proof/0", "public": {}})
        proof = work / "named-proof.bin"
        run("prove", package, pin, producer, proof, refusal="entry-proof-binding-policy")
        assert run("prove", package, pin, producer, proof, "--allow-header-only")["status"] == "produced"
        assert run("verify", package, pin, verifier, proof, "--allow-header-only")["status"] == "accepted"
        producer.write_text(json.dumps({"format": "zkc.entry-proof/0", "public": {}, "inputs": {"x": False}}))
        run("prove", package, pin, producer, proof, "--allow-header-only")
        run("verify", package, pin, verifier, proof, "--allow-header-only", refusal="artifact-rejected")
    print("Installed source Entries, bundle and independent proof execution passed")


if __name__ == "__main__":
    main()
