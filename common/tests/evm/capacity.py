"""Exercise the accepted first-profile capacities in actual deployed bytecode."""

import argparse
import copy
import hashlib
import json
from pathlib import Path

from abi import MAX_CALLDATA, encode_verify
from oracle import check_trace
from native_fixtures import rebind
from probe import execute
from reference import reconstruct
from validate import check_revert, check_sdk_artifact, deployed_artifact


def capacities(runner, artifact, fixture, maximum_context=None, *,
               aggregate_artifact=None, aggregate_limit=None):
    if fixture.get("evm") is not None:
        check_sdk_artifact(fixture, artifact)
    public = [bytes.fromhex(v) for v in fixture["public"]]
    context, proof = bytes.fromhex(fixture["context"]), bytes.fromhex(fixture["proof"])
    expected = reconstruct(fixture)
    if expected["stop"] is not None or expected["decision"] is not True:
        raise ValueError("expected an honest completed native fixture")
    if len(context) > 4096 or len(proof) > 65536:
        raise ValueError("fixture already exceeds first-profile capacity")
    cases = {}

    def rejected(name, calldata, kind, code, trace, deployed=artifact):
        result = execute(runner, deployed, calldata, 20_000_000)
        try:
            check_revert(result, kind, code, trace)
        except AssertionError as error:
            raise AssertionError(f"{name}: {error}") from error
        cases[name] = result

    rejected("context-one-over", encode_verify(public, bytes(4097), proof), "resource", 5, [])
    rejected("proof-one-over", encode_verify(public, context, proof + bytes(65537 - len(proof))), "resource", 5, [])
    # At the byte ceiling, admission succeeds and trailing proof bytes are
    # rejected only after the complete protocol trace, including the final hash.
    rejected("proof-at-cap-trailing", encode_verify(public, context, proof + bytes(65536 - len(proof))),
             "decode", 13, expected["trace"])
    vector = b"ZKCV\x00\x42" + (1025).to_bytes(4, "little") + bytes(32 * 1025)
    rejected("elements-one-over", encode_verify([vector, *public[1:]], context, proof), "resource", 2, [])
    rounds = b"ZKCV\x00\x1f" + (11).to_bytes(8, "little")
    # Round admission is a reached loop operation after invocation binding.
    # Rebind this negative-control header so a header mismatch cannot mask it.
    changed = copy.deepcopy(fixture)
    changed["public"] = [value.hex() for value in [*public[:2], rounds]]
    changed["proof"] = rebind(fixture, changed["public"]).hex()
    for key in ("public_rows", "invocation_tree", "invocation_root", "binding_sha256"):
        changed.pop(key, None)
    round_prefix = reconstruct(changed)
    rejected("authored-rounds-one-over", encode_verify([*public[:2], rounds], context,
                                                      bytes.fromhex(changed["proof"])), "source", 6, round_prefix["trace"])
    rejected("public-frame-one-over", encode_verify([bytes(65537), *public[1:]], context, proof),
             "resource", 5, [])
    if (aggregate_artifact is None) != (aggregate_limit is None):
        raise ValueError("aggregate deployment and its immutable public-byte limit are required together")
    if aggregate_artifact is not None:
        lengths = list(map(len, public))
        # Earlier frames must be well typed and individually bounded. Only the
        # last frame takes the sum one byte over this deployment's lower cap.
        if (len(lengths) < 2 or max(lengths) > 65536 or sum(lengths) != aggregate_limit + 1
                or sum(lengths[:-1]) > aggregate_limit):
            raise ValueError("aggregate case must cross its cap with multiple bounded frames")
        rejected("public-bytes-one-over", encode_verify(public, context, proof),
                 "resource", 11, [], aggregate_artifact)
    calldata = encode_verify(public, context, proof)
    rejected("calldata-one-over", calldata + bytes(MAX_CALLDATA + 1 - len(calldata)), "resource", 10, [])
    # Cancun can stop in dispatcher setup. Prague first requires the EIP-7623
    # calldata floor, which can leave enough execution gas to reach primitives.
    # A gas halt may retain only an exact prefix of the completed reference.
    intrinsic = 21000 + sum(4 if byte == 0 else 16 for byte in calldata)
    if artifact.get("request", {}).get("settings", {}).get("evmVersion") == "prague":
        intrinsic = max(intrinsic, 21000 + sum(10 if byte == 0 else 40 for byte in calldata))
    exhausted = execute(runner, artifact, calldata, intrinsic + 8)
    if exhausted["phase"] != "runtime" or exhausted["status"] != "halt" or "OutOfGas" not in exhausted["reason"]:
        raise AssertionError(f"expected a real EVM gas halt: {exhausted}")
    if exhausted["output"] != "":
        raise AssertionError("gas halt returned data")
    if len(exhausted["trace"]) >= len(expected["trace"]):
        raise AssertionError("gas control did not stop before the complete reference frontier")
    check_trace(exhausted["trace"], expected["trace"][:len(exhausted["trace"])])
    cases["evm-out-of-gas"] = exhausted
    if maximum_context is not None:
        context = bytes.fromhex(maximum_context["context"])
        if len(context) != 4096:
            raise ValueError("positive context-bound fixture must have exactly 4096 context bytes")
        reference = reconstruct(maximum_context)
        result = execute(runner, artifact, encode_verify(
            [bytes.fromhex(v) for v in maximum_context["public"]], context,
            bytes.fromhex(maximum_context["proof"])), 20_000_000)
        if (reference["decision"] is not True or maximum_context["decision"] is not True
                or result["phase"] != "runtime" or result["status"] != "return"
                or result["output"] != (1).to_bytes(32, "big").hex()):
            raise AssertionError("maximum-context native/EVM acceptance disagreement")
        check_trace(result["trace"], reference["trace"])
        cases["context-at-cap"] = result
    return {"format": "zkc.evm-capacity-execution/0", "cases": cases,
            "aggregate_public_bytes_limit": aggregate_limit,
            "identities": {name + "_sha256": hashlib.sha256(bytes.fromhex(artifact[name])).hexdigest()
                           for name in ("creation", "runtime")},
            "aggregate_identities": {name + "_sha256": hashlib.sha256(
                bytes.fromhex(aggregate_artifact[name])).hexdigest() for name in ("creation", "runtime")}
            if aggregate_artifact is not None else None,
            "not_measured": ["root/memory ceilings cannot be independently reached by this fixed bounded source",
                             "lower logical-budget deployments require matching compiler EvmOptions"]
                            + (["aggregate public-byte ceiling needs the separate lower-cap deployment"]
                               if aggregate_artifact is None else [])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("runner", "creation", "runtime", "fixture", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    parser.add_argument("--maximum-context-fixture", type=Path)
    parser.add_argument("--aggregate-creation", type=Path)
    parser.add_argument("--aggregate-runtime", type=Path)
    parser.add_argument("--aggregate-public-bytes", type=int)
    parser.add_argument("--bytecode-format", choices=["binary", "hex"], default="binary")
    parser.add_argument("--evm-version", choices=("cancun", "prague"), default="cancun")
    args = parser.parse_args()
    aggregate_args = (args.aggregate_creation, args.aggregate_runtime, args.aggregate_public_bytes)
    if any(value is not None for value in aggregate_args) and not all(value is not None for value in aggregate_args):
        parser.error("aggregate creation, runtime and immutable public-byte limit are required together")
    result = capacities(args.runner, deployed_artifact(args.creation, args.runtime,
                                                      args.bytecode_format, args.evm_version),
                        json.loads(args.fixture.read_text()),
                        json.loads(args.maximum_context_fixture.read_text()) if args.maximum_context_fixture else None,
                        aggregate_artifact=deployed_artifact(args.aggregate_creation, args.aggregate_runtime,
                                                             args.bytecode_format, args.evm_version)
                        if args.aggregate_creation else None, aggregate_limit=args.aggregate_public_bytes)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({name: {"status": value["status"], "gas": value["runtime_gas"],
                            "primitives": len(value["trace"])} for name, value in result["cases"].items()}, indent=2))


if __name__ == "__main__":
    main()
