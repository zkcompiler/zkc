"""Execute exact installed CompilerCore bytes in independent runtime processes."""

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
    print("Installed bundle and independent proof execution passed")


if __name__ == "__main__":
    main()
