"""Execute exact installed NativeCompiler bytes in independent runtime processes."""

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

        bundle = work / "run.bundle"
        pin = hashlib.sha256(bundle.read_bytes()).hexdigest()
        inputs = write("bundle.json", ["zkc.bundle-inputs/1", "installed", [
            ["Solo", [["0", "bool@native.bool/1", ["wire", "5a4b4356010501"]]], []]], []])
        result = run("run-bundle", bundle, pin, inputs)
        assert result["outcome"] == ["completed"] and result["acceptance"] is None
        assert result["roles"][0]["outputs"] == [["wire", "bool@native.bool/1", "5a4b4356010501"]]
        run("run-bundle", bundle, "00" * 32, inputs, refusal="run-Identity")

        deployment = work / "proof.deployment"
        pin = hashlib.sha256(deployment.read_bytes()).hexdigest()
        producer = write("producer.json", ["zkc.native-proof-inputs/1", [], [
            ["0", ["wire", "5a4b4356010501"]]], "", [], "0"])
        validator = write("validator.json", ["zkc.native-proof-inputs/1", [], [], "", [], "0"])
        proof = work / "proof.bin"
        result = run("produce-native-proof", deployment, pin, producer, proof)
        assert result["status"] == "produced"
        result = run("validate-native-proof", deployment, pin, validator, proof)
        assert result["status"] == "accepted"
        for data, code in [(proof.read_bytes()[:-1], "proof-truncated"),
                           (proof.read_bytes() + b"x", "proof-trailing")]:
            malformed = work / "malformed.bin"
            malformed.write_bytes(data)
            run("validate-native-proof", deployment, pin, validator, malformed, refusal=code)
        run("validate-native-proof", deployment, "00" * 32, validator, proof,
            refusal="native-proof-deployment-binding")
        package = work / "run.entry"
        pin = hashlib.sha256(package.read_bytes()).hexdigest()
        inputs = write("named-run.json", {"format": "zkc.entry-run/1", "session": "installed",
            "roles": {"P": {"inputs": {"x": True}}}})
        outputs = work / "named-results.json"
        result = run("run-entry", package, pin, inputs, f"--results={outputs}")
        assert result["status"] == "executed"
        assert json.loads(outputs.read_text())["roles"]["P"] == {"r": True}
        run("run-entry", package, "00" * 32, inputs, refusal="entry-package-identity")

        package = work / "proof.entry"
        pin = hashlib.sha256(package.read_bytes()).hexdigest()
        producer = write("named-producer.json", {"format": "zkc.entry-proof/1",
            "public": {}, "inputs": {"x": True}})
        verifier = write("named-verifier.json", {"format": "zkc.entry-proof/1", "public": {}})
        proof = work / "named-proof.bin"
        run("prove", package, pin, producer, proof, refusal="entry-proof-binding-policy")
        assert run("prove", package, pin, producer, proof, "--allow-header-only")["status"] == "produced"
        assert run("verify", package, pin, verifier, proof, "--allow-header-only")["status"] == "accepted"
        producer.write_text(json.dumps({"format": "zkc.entry-proof/1", "public": {}, "inputs": {"x": False}}))
        run("prove", package, pin, producer, proof, "--allow-header-only")
        run("verify", package, pin, verifier, proof, "--allow-header-only", refusal="artifact-rejected")
    print("Installed source Entries, bundle and independent proof execution passed")


if __name__ == "__main__":
    main()
