"""Compile lower SDK/CLI selections and check actual deployed refusal frontiers.

Uses the existing native SDK fixture/capture driver, Artifact::calldata, Python
ABI oracle, Sumcheck reference and passive-trace revm runner. No build is run
by this script. Supply freshly built tools and native_fixtures.py outputs from
the same source revision. Transcript cases also run actual native verification
with the selected logical transition allowance. Native VM capacity/fuel and EVM
memory/element ceilings remain separate; gas always uses the declared profile.
"""

import argparse
import json
from pathlib import Path
import subprocess

from abi import encode_verify
from probe import execute
from reference import reconstruct
import target
from validate import check_return, check_revert, check_sdk_artifact, deployed_artifact


def run_json(command):
    result = subprocess.run(list(map(str, command)), text=True, capture_output=True, timeout=300)
    if result.returncode:
        raise AssertionError(f"command refused: {command}\n{result.stdout}\n{result.stderr}")
    return json.loads(result.stdout)


def source_stop_code(fixture):
    """Apply the declared bounded FNV site code to the native stop's source site.

    The retained native execution identifies the actual guard independently of
    the EVM result; no byte from the target revert is used as an expectation.
    """
    native = fixture["native"].get("stop")
    if not isinstance(native, dict) or native.get("kind") != 'Explicit("reject")':
        raise ValueError("requires an actual native protocol rejection")
    site = native.get("site")
    if not isinstance(site, str) or not site:
        raise ValueError("native rejection has no exact source site")
    code = 2166136261
    for byte in site.encode("utf-8"):
        code = ((code ^ byte) * 16777619) & 0xFFFFFFFF
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("cli", "compiler", "solc", "native-driver", "runner", "fixtures", "project", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    parser.add_argument("--solc-sha256", required=True)
    args = parser.parse_args()
    for name in ("cli", "compiler", "solc", "native_driver", "runner", "fixtures", "project", "output"):
        setattr(args, name, getattr(args, name).resolve())
    args.output.mkdir(parents=True, exist_ok=False)
    honest = json.loads((args.fixtures / "honest-16.json").read_text())
    native = reconstruct(honest)
    if honest["rounds"] != 4 or native["decision"] is not True or native["transitions"] != 16:
        raise ValueError("requires the honest four-round, sixteen-transition native fixture")
    proof_path = args.output / "honest.proof"
    proof_path.write_bytes(bytes.fromhex(honest["proof"]))
    artifacts, receipts = {}, []

    def compile_selection(name, partial):
        limits_file = args.output / f"{name}.limits.json"
        limits_file.write_text(json.dumps(partial) + "\n")
        destination = args.output / f"{name}.evm"
        report = run_json([
            args.cli, "compile", "example::Proof", "--target=evm", "--json",
            f"--project={args.project}", f"--compiler={args.compiler}", f"--solc={args.solc}",
            f"--solc-sha256={args.solc_sha256}", f"--evm-limits={limits_file}",
            f"--output={destination}",
        ])
        (args.output / f"{name}.compile.json").write_text(json.dumps(report, indent=2) + "\n")
        effective = target.LIMITS | partial
        source = json.loads((destination / "source.json").read_text())
        if (report["status"] != "compiled" or report["evm_limits"] != effective
                or source["limits"] != effective or source["declaration"] != target.IDENTITY):
            raise AssertionError("CLI/SDK/compiler did not retain the complete effective selection")
        # This existing SDK consumer authenticates the exact manifest and all
        # files, checks the native subject and uses the sole Artifact encoder.
        captured = run_json([
            args.native_driver, "--compiler", args.compiler, "--project", args.project,
            "--entry", "example::Proof", "--rounds", "4", "--context", honest["context"],
            "--proof", proof_path, "--evm-artifact", destination,
            "--evm-sha256", report["manifest_sha256"],
        ])
        for key in ("source", "descriptor", "public", "context", "proof"):
            if captured[key] != honest[key]:
                raise AssertionError(f"SDK artifact/native fixture subject differs at {key}")
        artifact = deployed_artifact(destination / "creation.bin", destination / "runtime.bin",
                                     "binary", source["fork"])
        check_sdk_artifact(captured, artifact)
        (args.output / f"{name}.sdk.json").write_text(json.dumps(captured, indent=2) + "\n")
        artifacts[name] = (artifact, effective, report["manifest_sha256"])

    def check(selection, name, fixture, *, stop=None, revert=None, trace=None):
        artifact, limits, pin = artifacts[selection]
        matched_native = None
        if trace is None:
            # First calculate the selected deployment's independent frontier,
            # then actually verify the same proof with the matching native
            # logical transition allowance. No native capacity/fuel is changed.
            expected = reconstruct(dict(fixture, transcript_budget=limits["transcript_transitions"]))
            if expected["stop"] != stop:
                raise AssertionError(f"{name}: an unintended reference stop masked {stop}")
            trace = expected["trace"]
            supplied_proof = args.output / f"{name}.proof"
            supplied_proof.write_bytes(bytes.fromhex(fixture["proof"]))
            matched_native = run_json([
                args.native_driver, "--compiler", args.compiler, "--project", args.project,
                "--entry", "example::Proof", "--rounds", "4", "--context", fixture["context"],
                "--proof", supplied_proof, "--budget", limits["transcript_transitions"],
                "--evm-artifact", args.output / f"{selection}.evm", "--evm-sha256", pin,
            ])
            (args.output / f"{name}.native.json").write_text(
                json.dumps(matched_native, indent=2) + "\n")
            for key in ("source", "descriptor", "public", "context", "proof"):
                if matched_native[key] != fixture[key]:
                    raise AssertionError(f"{name}: native input changed at {key}")
            native_error = {None: None, "source-require": 'artifact-stopped:Explicit("reject")',
                            "transcript-budget": "exhausted:resource-budget"}[stop]
            if (matched_native["decision"] != expected["decision"]
                    or matched_native["native_error"] != native_error
                    or matched_native["transcript_budget"] != limits["transcript_transitions"]):
                raise AssertionError(f"{name}: actual matched native refusal differs")
            check_sdk_artifact(matched_native, artifact)
        calldata = encode_verify([bytes.fromhex(v) for v in fixture["public"]],
                                 bytes.fromhex(fixture["context"]), bytes.fromhex(fixture["proof"]))
        result = execute(args.runner, artifact, calldata, repeat_count=2)
        if result["phase"] != "runtime" or len(result["calls"]) != 2:
            raise AssertionError("expected two actual calls to the deployed verifier")
        # Validate every repeated call, including complete ordered primitives.
        for call in [result, *[dict(call, phase="runtime") for call in result["calls"]]]:
            if revert is None:
                check_return(call, (1).to_bytes(32, "big").hex(), trace)
            else:
                check_revert(call, *revert, trace)
        receipt = {"case": name, "selection": selection, "limits": limits,
                   "manifest_sha256": pin, "native_fixture_budget": fixture["transcript_budget"],
                   "matched_native": matched_native, "expected_deployment_stop": stop,
                   "expected_revert": revert, "execution": result}
        receipts.append(receipt)
        (args.output / f"{name}.execution.json").write_text(json.dumps(receipt, indent=2) + "\n")

    compile_selection("transcript-at", {"transcript_transitions": 16})
    compile_selection("transcript-one-short", {"transcript_transitions": 15})
    compile_selection("transcript-two", {"transcript_transitions": 2})
    compile_selection("transcript-one", {"transcript_transitions": 1})
    compile_selection("elements-at", {"public_elements": 16})
    compile_selection("elements-one-short", {"public_elements": 15})
    compile_selection("memory-lower", {"memory_bytes": target.LIMITS["memory_bytes"] - 1})
    compile_selection("memory-minimum", {"memory_bytes": target.MINIMA["memory_bytes"]})
    check("transcript-at", "transcript-exact-completion", honest)
    check("transcript-one-short", "last-delivery-refuses", honest,
          stop="transcript-budget", revert=("resource", 8))
    for fixture_name in ("require-stop", "require-stop-malformed-later"):
        fixture = json.loads((args.fixtures / f"{fixture_name}.json").read_text())
        if reconstruct(fixture)["stop"] != "source-require":
            raise AssertionError("the native source-stop fixture must retain its original stop")
        check("transcript-two", f"{fixture_name}-before-next-debit", fixture,
              stop="source-require", revert=("source", source_stop_code(fixture)))
        check("transcript-one", f"debit-before-{fixture_name}", fixture,
              stop="transcript-budget", revert=("resource", 8))
    check("elements-at", "elements-exact-completion", honest)
    check("elements-one-short", "public-elements-before-binding", honest,
          revert=("resource", 2), trace=[])
    check("memory-lower", "lower-memory-completion", honest)
    # The root workspace is allocated before decoding public values or hashing.
    # This tests an actual lower deployment refusal, not a measured peak-memory
    # threshold. Its fixed root ceiling deliberately exceeds minimum memory.
    if target.MINIMA["memory_bytes"] >= target.LIMITS["root_bytes"]:
        raise ValueError("minimum-memory control requires a larger fixed root workspace")
    check("memory-minimum", "root-allocation-before-binding", honest,
          revert=("resource", 1), trace=[])
    (args.output / "receipt.json").write_text(json.dumps({"cases": receipts}, indent=2) + "\n")
    print(json.dumps({"cases": len(receipts), "output": str(args.output)}))


if __name__ == "__main__":
    main()
