"""Compile a negative control that omits only the final delivery value hash.

The unmodified release artifact is the baseline and sole conformance subject.
This deliberately invalid test artifact is useful when loop observations share
one Keccak PC. Both executions use passive revm inspection, with no trace output
instrumentation or engine overrides.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path

from abi import encode_verify
from oracle import check_trace
from probe import SOLC_SHA256, check_solc, compile_request, execute
from reference import reconstruct
from validate import bytecode, removed_final_hash_control


def omit_final_observation(request, transitions):
    """Alter the generated helper only in a separately identified test copy."""
    if request["language"] != "Yul" or len(request["sources"]) != 1 or transitions <= 0:
        raise ValueError("expected generated Yul and a completed nonzero-round fixture")
    changed = copy.deepcopy(request)
    source = next(iter(changed["sources"].values()))
    yul = source["content"]
    needle = "let next := keccak256(p, size)"
    if yul.count(needle) != 1 or 'verbatim_1i_0o(hex"50", next)' not in yul:
        raise ValueError("generated observation helper changed; re-review the mutation")
    # Observe debits first. c0 is the checked generation, 0x120 the chain state,
    # and label=value selects the second hash of that last observation. Earlier
    # messages, request blocks/feedback and the final origin remain unchanged.
    replacement = ("let next := mload(0x120)\n"
                   f"  if iszero(and(eq(mload(0xc0), {transitions}), eq(label, 0x76616c7565))) {{\n"
                   "    next := keccak256(p, size)\n"
                   "  }")
    source["content"] = yul.replace(needle, replacement)
    return changed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("solc", "solc-input", "runner", "fixture", "creation", "runtime", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    parser.add_argument("--bytecode-format", choices=["binary", "hex"], default="binary")
    parser.add_argument("--gas", type=int, default=20_000_000)
    args = parser.parse_args()
    version = check_solc(args.solc)
    fixture = json.loads(args.fixture.read_text())
    reference = reconstruct(fixture)
    if reference["stop"] is not None or reference["decision"] != fixture["decision"]:
        raise ValueError("expected a completed native/reference fixture")
    calldata = encode_verify([bytes.fromhex(v) for v in fixture["public"]],
                             bytes.fromhex(fixture["context"]), bytes.fromhex(fixture["proof"]))
    request = json.loads(args.solc_input.read_text())
    original_artifact = {"creation": bytecode(args.creation, args.bytecode_format),
                         "runtime": bytecode(args.runtime, args.bytecode_format), "request": request}
    original = execute(args.runner, original_artifact, calldata, args.gas)
    if original["phase"] != "runtime" or original["status"] != "return":
        raise AssertionError(f"release baseline did not execute: {original}")
    if original["output"] != int(reference["decision"]).to_bytes(32, "big").hex():
        raise AssertionError("release baseline differs from native decision")
    check_trace(original["trace"], reference["trace"])
    # An unrelated request must not be relabeled as the production baseline.
    recompiled = compile_request(args.solc, request)
    if any(recompiled[key] != original_artifact[key] for key in ("creation", "runtime")):
        raise AssertionError("provided solc input does not reproduce the release bytecode")
    artifact = compile_request(args.solc, omit_final_observation(request, reference["transitions"]))
    check_solc(args.solc)
    control = removed_final_hash_control(args.runner, original_artifact, calldata, original,
                                         reference["trace"], args.gas, artifact)
    receipt = {"format": "zkc.evm-final-observation-mutant/0", "production": False,
               "solc_sha256": SOLC_SHA256, "solc_version": version,
               "baseline_runtime_sha256": hashlib.sha256(bytes.fromhex(original_artifact["runtime"])).hexdigest(),
               "native_transitions": reference["transitions"], "baseline": original,
               "artifact": artifact, "control": control}
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"baseline_primitives": len(original["trace"]),
                      "mutant_primitives": len(control["execution"]["trace"]),
                      "unchanged_output": True, "full_oracle_rejected": True}))


if __name__ == "__main__":
    main()
