"""Run a real native fixture against exact compiled, deployed EVM bytes.

The caller obtains bytecode through the SDK's independently pinned artifact
reader. This script is an execution oracle, not another artifact authority.
"""

import argparse
import hashlib
import json
from pathlib import Path

from abi import encode_verify, malformed_cases
from oracle import check_trace
from probe import execute
from reference import invocation_root, reconstruct

REVERT_CLASSES = {"source": b"ZKCS", "decode": b"ZKCD", "resource": b"ZKCR", "fault": b"ZKCT"}
# These are the stable target diagnostic codes, not arbitrary revert payloads.
ABI_REFUSALS = {
    "selector": ("decode", 7), "short-head": ("decode", 7),
    "unaligned": ("decode", 8), "head-overlap": ("decode", 8),
    "offset-overflow": ("decode", 8), "proof-context-overlap": ("decode", 8),
    "array-count-overflow": ("decode", 9), "truncated": ("decode", 1),
    "trailing": ("decode", 10), "hole": ("decode", 8),
    "element-head-overlap": ("decode", 8), "element-tail-overlap": ("decode", 8),
    "padding": ("decode", 6),
}


def check_revert(result, kind, code, trace):
    output = (REVERT_CLASSES[kind] + code.to_bytes(32, "big")).hex()
    if (result["phase"] != "runtime" or result["status"] != "revert"
            or result["output"] != output):
        raise AssertionError(f"expected {kind}({code}), got "
                             f"{result['phase']}/{result['status']}/{result['output']}")
    check_trace(result["trace"], trace)


def check_sdk_artifact(fixture, artifact):
    """Bind supplied code and execution fork to the SDK's captured tuple."""
    captured = fixture["evm"]
    if captured is None:
        raise ValueError("fixture has no SDK Artifact::capture export")
    calldata = encode_verify([bytes.fromhex(v) for v in fixture["public"]],
                             bytes.fromhex(fixture["context"]), bytes.fromhex(fixture["proof"]))
    if captured["calldata"] != calldata.hex():
        raise AssertionError("SDK and independent Python calldata differ")
    fork = captured["manifest"]["evm_version"]
    if fork not in ("cancun", "prague"):
        raise AssertionError("SDK exported unsupported execution fork")
    if artifact.get("request", {}).get("settings", {}).get("evmVersion") != fork:
        raise AssertionError("selected execution fork differs from SDK captured artifact")
    for name in ("creation", "runtime"):
        digest = hashlib.sha256(bytes.fromhex(captured[name])).hexdigest()
        if (digest != captured[f"{name}_sha256"]
                or digest != captured["manifest"]["files"][f"{name}.bin"]):
            raise AssertionError(f"SDK exported {name} identity differs")
        if artifact[name] != captured[name]:
            raise AssertionError("supplied deployment differs from SDK captured artifact")


def bytecode(path, encoding):
    if encoding == "binary":
        return path.read_bytes().hex()
    value = path.read_text().strip().removeprefix("0x")
    bytes.fromhex(value)
    return value


def deployed_artifact(creation, runtime, encoding, fork):
    """Attach the selected fork when checking separately stored bytecode."""
    if fork not in ("cancun", "prague"):
        raise ValueError("unsupported-fork")
    return {"creation": bytecode(creation, encoding), "runtime": bytecode(runtime, encoding),
            "request": {"settings": {"evmVersion": fork}}}


def removed_final_hash_control(runner, artifact, calldata, original, expected_trace, gas,
                               supplied_mutant=None):
    """Delete the final observed opcode in a copy of the real release artifact.

    KECCAK consumes two words and produces one. POP has the same net stack
    change, leaving the length in place of the digest; the opaque final sink
    consumes it. A true return must survive, while exact trace equality fails.
    """
    if not original["trace"] or original["trace"][-1]["kind"] != "keccak256":
        raise AssertionError("final-hash control requires a final Keccak event")
    if supplied_mutant is not None:
        mutated = execute(runner, supplied_mutant, calldata, gas)
        changed_creation = bytes.fromhex(supplied_mutant["creation"])
        changed_runtime = bytes.fromhex(supplied_mutant["runtime"])
        pc = None
    else:
        pc = original["trace"][-1]["pc"]
        if sum(event.get("pc") == pc and event["kind"] == "keccak256"
               for event in original["trace"]) != 1:
            raise AssertionError("final Keccak PC is shared; supply a final-observation mutant from mutant.py")
        runtime = bytes.fromhex(artifact["runtime"])
        creation = bytes.fromhex(artifact["creation"])
        if type(pc) is not int or pc < 0 or pc >= len(runtime) or runtime[pc] != 0x20:
            raise AssertionError("final-hash PC is not in the installed verifier code")
        if not runtime or creation.count(runtime) != 1:
            raise AssertionError("runtime must have one exact occurrence in the supplied solc creation bytecode")
        offset = creation.index(runtime)
        changed_runtime = runtime[:pc] + b"\x50" + runtime[pc + 1:]
        changed_creation = creation[:offset + pc] + b"\x50" + creation[offset + pc + 1:]
        mutated = execute(runner, dict(artifact, creation=changed_creation.hex(),
                                       runtime=changed_runtime.hex()), calldata, gas)
    if mutated["status"] != original["status"] or mutated["output"] != original["output"]:
        raise AssertionError("deleted-final-hash mutant changed the observable result")
    try:
        check_trace(mutated["trace"], expected_trace)
    except AssertionError as error:
        trace_error = str(error)
    else:
        raise AssertionError("deleted-final-hash mutant passed the full primitive oracle")
    check_trace(mutated["trace"], expected_trace[:-1])
    return {"pc": pc, "creation_sha256": hashlib.sha256(changed_creation).hexdigest(),
            "runtime_sha256": hashlib.sha256(changed_runtime).hexdigest(),
            "trace_error": trace_error, "execution": mutated}


def validate(runner, artifact, fixture, expected_trace, *, gas=20_000_000,
             expected_status="return", expected_output=None, controls=True, final_hash_mutant=None,
             expected_revert_class=None, expected_revert_code=None, repeat_count=2):
    if (expected_revert_class is None) != (expected_revert_code is None):
        raise ValueError("revert class and code must be supplied together")
    if expected_revert_class is not None and expected_status != "revert":
        raise ValueError("revert class and code require a revert outcome")
    if controls and expected_status != "return":
        raise ValueError("mutation controls require a completed invocation; use --no-controls for stops")
    public = [bytes.fromhex(value) for value in fixture["public"]]
    proof = bytes.fromhex(fixture["proof"])
    context = bytes.fromhex(fixture["context"])
    calldata = encode_verify(public, context, proof)
    if fixture.get("evm") is not None:
        check_sdk_artifact(fixture, artifact)
    if expected_status == "revert" and (expected_revert_class is None or expected_revert_code is None):
        raise ValueError("revert expectations require both exact class and code")
    if expected_status == "return" and expected_output is None:
        if type(fixture["decision"]) is not bool:
            raise ValueError("completed fixture requires a native Boolean decision")
        expected_output = int(fixture["decision"]).to_bytes(32, "big").hex()
    result = execute(runner, artifact, calldata, gas, repeat_count=repeat_count)
    if result["phase"] != "runtime" or result["status"] != expected_status:
        raise AssertionError(f"unexpected EVM outcome: {result}")
    if expected_output is not None and result["output"] != expected_output:
        raise AssertionError(f"unexpected EVM output: {result['output']}")
    if expected_revert_class is not None:
        check_revert(result, expected_revert_class, expected_revert_code, expected_trace)
    check_trace(result["trace"], expected_trace)
    if len(result["calls"]) != repeat_count:
        raise AssertionError("runner did not execute every requested invocation")
    for nonce, call in enumerate(result["calls"], 1):
        if (call["nonce"] != nonce or call["address"] != result["address"]
                or call["status"] != result["status"] or call["output"] != result["output"]
                or call["reason"] != result["reason"]):
            raise AssertionError("repeated invocation differs on the same deployment")
        check_trace(call["trace"], expected_trace)
    receipt = {"native": fixture["native"], "execution": result, "controls": {},
               "creation_sha256": hashlib.sha256(bytes.fromhex(artifact["creation"])).hexdigest(),
               "runtime_sha256": hashlib.sha256(bytes.fromhex(artifact["runtime"])).hexdigest()}
    if fixture.get("evm") is not None:
        receipt["manifest_sha256"] = fixture["evm"]["manifest_sha256"]
        receipt["independent_calldata_equal"] = True
    if not controls:
        return receipt
    cases = {name: (value, *ABI_REFUSALS[name], [])
             for name, value in malformed_cases(calldata).items()}
    for name, changed_proof, code, stop in [
        ("proof-trailing", proof + b"\x00", 13, "proof-trailing"),
        ("proof-truncated", proof[:-1], 5, "proof-frame"),
    ]:
        if len(changed_proof) < 40:
            prefix, code = [], 11
        else:
            changed = dict(fixture, proof=changed_proof.hex())
            reference = reconstruct(changed)
            if reference["stop"] not in (stop, "proof-frame-length"):
                raise AssertionError(f"{name}: unexpected independent stop {reference['stop']}")
            prefix = reference["trace"]
        cases[name] = (encode_verify(public, context, changed_proof), "decode", code, prefix)
    if proof:
        cases["proof-header"] = (encode_verify(public, context, bytes([proof[0] ^ 1]) + proof[1:]),
                                 "decode", 11, [])
    changed = dict(fixture, context=(context + b"\x01").hex())
    for key in ("public_rows", "invocation_tree", "invocation_root", "binding_sha256"):
        changed.pop(key, None)
    root = invocation_root(changed)
    context_trace = [{"kind": "sha256", "input": root.hex(),
                      "output": hashlib.sha256(root).hexdigest(), "status": "return"}]
    cases["changed-context"] = (encode_verify(public, context + b"\x01", proof),
                                "decode", 12, context_trace) if len(context) < 4096 else (
                                    encode_verify(public, context + b"\x01", proof), "resource", 5, [])
    for name, (mutated, kind, code, prefix) in cases.items():
        rejected = execute(runner, artifact, mutated, gas)
        try:
            check_revert(rejected, kind, code, prefix)
        except AssertionError as error:
            raise AssertionError(f"{name}: {error}") from error
        receipt["controls"][name] = rejected
    receipt["controls"]["removed-final-hash"] = removed_final_hash_control(
        runner, artifact, calldata, result, expected_trace, gas, final_hash_mutant)
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("runner", "creation", "runtime", "fixture", "output"):
        parser.add_argument(f"--{name}", required=True, type=Path)
    parser.add_argument("--expected-trace", type=Path,
                        help="independent trace JSON; defaults to maintained Sumcheck reconstruction")
    parser.add_argument("--bytecode-format", choices=["binary", "hex"], default="binary")
    parser.add_argument("--evm-version", choices=("cancun", "prague"), default="cancun")
    parser.add_argument("--final-hash-mutant", type=Path,
                        help="mutant.py receipt when the last Keccak opcode is shared")
    parser.add_argument("--gas", type=int, default=20_000_000)
    parser.add_argument("--expected-status", choices=["return", "revert", "halt"], default="return")
    parser.add_argument("--expected-output")
    parser.add_argument("--expected-revert-class", choices=["source", "decode", "resource", "fault"])
    parser.add_argument("--expected-revert-code", type=int)
    parser.add_argument("--repeat-count", type=int, choices=range(1, 9), default=2)
    parser.add_argument("--no-controls", action="store_true")
    args = parser.parse_args()
    fixture = json.loads(args.fixture.read_text())
    if fixture.get("format") != "zkc.evm-native-fixture/0":
        raise ValueError("native fixture format")
    expected = (json.loads(args.expected_trace.read_text()) if args.expected_trace
                else reconstruct(fixture))
    trace = expected["trace"] if isinstance(expected, dict) else expected
    if isinstance(expected, dict) and expected["decision"] != fixture["decision"]:
        raise AssertionError("independent/native decision disagreement")
    expected_output = args.expected_output
    if expected_output is None and args.expected_status == "return":
        if type(fixture["decision"]) is not bool:
            raise ValueError("fixture has no native Boolean decision; specify the stopped outcome")
        expected_output = int(fixture["decision"]).to_bytes(32, "big").hex()
    receipt = validate(args.runner, deployed_artifact(args.creation, args.runtime,
                                                    args.bytecode_format, args.evm_version),
                       fixture, trace, gas=args.gas,
                       expected_status=args.expected_status, expected_output=expected_output,
                       controls=not args.no_controls,
                       expected_revert_class=args.expected_revert_class,
                       expected_revert_code=args.expected_revert_code, repeat_count=args.repeat_count,
                       final_hash_mutant=(json.loads(args.final_hash_mutant.read_text())["artifact"]
                                          if args.final_hash_mutant else None))
    receipt["expected"] = expected
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": receipt["execution"]["status"],
                      "runtime_gas": receipt["execution"]["runtime_gas"],
                      "code_size": receipt["execution"]["code_size"],
                      "controls": list(receipt["controls"])}))


if __name__ == "__main__":
    main()
