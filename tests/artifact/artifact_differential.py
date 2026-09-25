#!/usr/bin/env python3
"""Compare compiled artifact validation with original-source Lean execution.

The corpus combines every strict byte prefix with semantic substitutions and
seeded byte mutations. Each case uses a fresh native process and fresh Lean
execution. Only public primitive answers are memoized by exact request identity.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random

import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "support"))

from run_reference import run_reference, write_json  # noqa: E402
from journal import Journal, TIMEOUT, positive_timeout  # noqa: E402


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(",", ":")).encode()).hexdigest()


def native_class(result):
    if result["status"] == "accepted":
        return "accepted"
    code = result.get("code") or ""
    if code == "rejected:require" or code == "artifact-rejected":
        return "reject"
    if code.startswith("exhausted:"):
        return "exhausted"
    return "refused"


def messages(proof):
    offset, result = 40, []
    while offset < len(proof):
        size = int.from_bytes(proof[offset:offset+8], "little")
        assert size <= len(proof) - offset - 8
        result.append((offset, proof[offset+8:offset+8+size]))
        offset += size + 8
    return result


def corpus(proof, seed, mutations, prefixes):
    yield "honest", proof
    if prefixes:
        for n in range(len(proof)):
            yield f"prefix-{n}", proof[:n]
    yield "trailing-byte", proof + b"\0"
    yield "trailing-message", proof + (7).to_bytes(8, "little") + b"ZKCV\x01\x05\x01"
    for i, (offset, payload) in enumerate(messages(proof)):
        for length in [0, 1, len(payload) - 1, len(payload) + 1, 2**64 - 1]:
            candidate = bytearray(proof)
            candidate[offset:offset+8] = length.to_bytes(8, "little")
            yield f"length-{i}-{length}", bytes(candidate)
        if payload[:6] == b"ZKCV\x01\x01":
            candidate = bytearray(proof)
            value = (int.from_bytes(payload[6:], "little") + 1) % 52435875175126190479447740508185965837690552500527637822603658699938581184513
            candidate[offset+14:offset+8+len(payload)] = value.to_bytes(32, "little")
            yield f"canonical-field-{i}", bytes(candidate)
            candidate[offset+14:offset+8+len(payload)] = b"\xff" * (len(payload) - 6)
            yield f"noncanonical-field-{i}", bytes(candidate)
        if payload[:6] in (b"ZKCV\x01\x06", b"ZKCV\x01\x07"):
            candidate = bytearray(proof)
            candidate[offset+8+23] ^= 1  # setup identifier inside the PCS envelope
            yield f"foreign-metadata-{i}", bytes(candidate)
        if payload[:6] == b"ZKCV\x01\x09":
            candidate = bytearray(proof)
            candidate[offset+14:offset+8+len(payload)] = b"\xff" * (len(payload) - 6)
            yield f"malformed-group-{i}", bytes(candidate)
        for j, (_, other) in enumerate(messages(proof)):
            if j > i and other[:6] == payload[:6] and len(other) == len(payload) and other != payload:
                candidate = bytearray(proof)
                candidate[offset+8:offset+8+len(payload)] = other
                yield f"same-type-substitute-{i}-{j}", bytes(candidate)
    rng = random.Random(seed)
    for index in range(mutations):
        candidate = bytearray(proof)
        edits = []
        for _ in range(rng.randrange(1, 5)):
            offset, bit = rng.randrange(len(proof)), 1 << rng.randrange(8)
            candidate[offset] ^= bit
            edits.append((offset, bit))
        yield f"bits-{index}-" + "_".join(f"{i}-{b}" for i, b in edits), bytes(candidate)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["native", "compiler", "lean_checker", "lean_reference", "primitive", "fixtures", "output"]:
        parser.add_argument("--" + name.replace("_", "-"), type=Path, required=True)
    parser.add_argument("--mutations", type=int, default=128)
    parser.add_argument("--skip-prefixes", action="store_true")
    parser.add_argument("--seed", type=int, default=20260914)
    parser.add_argument("--protocol", action="append", help="fixture directory name; may be repeated")
    parser.add_argument("--shards", type=int, default=1, help="partition the fixed corpus for parallel processes")
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument("--timeout", type=positive_timeout, default=TIMEOUT)
    args = parser.parse_args()
    if not 0 <= args.shard_index < args.shards:
        parser.error("require 0 <= shard-index < shards")
    args.output.mkdir(parents=True, exist_ok=False)
    journal = Journal(args.output / "commands", timeout=args.timeout)
    results, memo = [], {}
    for protocol in args.protocol or ["dleq", "committed-two-factor"]:
        fixture = args.fixtures / protocol
        observation_tag = "zkc.artifact-observation/1"
        work = args.output / (protocol + "-work")
        work.mkdir(exist_ok=True)
        proof_path = work / "candidate.bin"
        original = (fixture / "proof.bin").read_bytes()
        for index, (name, candidate) in enumerate(corpus(original, args.seed, args.mutations, not args.skip_prefixes)):
            if index % args.shards != args.shard_index:
                continue
            proof_path.write_bytes(candidate)
            command = [str(args.native), "validate-artifact",
                       *[str(fixture / (n + ".json")) for n in ["source", "descriptor", "construction", "physical", "validator"]],
                       str(args.compiler), str(args.lean_checker), str(proof_path), "10000"]
            call = journal.attempt(command)
            assert call.returncode in (0, 1), (call.returncode, call.stderr)
            native = json.loads(call.stdout)
            reference = run_reference(args.lean_reference, args.primitive,
                fixture / "source.json", fixture / "descriptor.json", fixture / "validator.json",
                proof_path, work / "reference", memo, transcript_budget=10000)
            if reference[0] != observation_tag:
                raise AssertionError((protocol, name, "unexpected source/input admission refusal", reference))
            same_class = native_class(native) == reference[1][0]
            same_events = native.get("events", []) == reference[2]
            same_bytes = native.get("proof_bytes") == int(reference[4])
            native_draws = sum(e[0] == "challenge" for e in native.get("events", []))
            same_draws = native_draws == int(reference[5])
            same_history = sum(e[0] in ("message", "challenge") for e in native.get("events", [])) == int(reference[6])
            passed = same_class and same_events and same_bytes and same_draws and same_history
            record = {"protocol": protocol, "case": name, "proof_sha256": hashlib.sha256(candidate).hexdigest(),
                      "size": len(candidate), "outcome": native_class(native), "native_code": native.get("code"),
                      "reference_code": reference[1][1], "events": len(reference[2]),
                      "events_sha256": digest(reference[2]), "bytes": reference[4], "draws": reference[5],
                      "pass": passed}
            results.append(record)
            if not passed:
                failure = args.output / (protocol + "-" + name)
                failure.mkdir(exist_ok=True)
                (failure / "proof.bin").write_bytes(candidate)
                write_json(failure / "native.json", native)
                write_json(failure / "reference.json", reference)
                write_json(args.output / "results.json", {"status": "failed", "cases": results})
                raise AssertionError((protocol, name, {"class": same_class, "events": same_events,
                                                     "bytes": same_bytes, "draws": same_draws,
                                                     "history": same_history}, str(failure)))
            if len(results) % 100 == 0:
                print(json.dumps({"checked": len(results), "latest": protocol + "/" + name}), flush=True)
    write_json(args.output / "results.json", {"status": "pass", "seed": args.seed,
        "shards": args.shards, "shard_index": args.shard_index, "cases": results,
        "tools": {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                  for path in [args.native, args.compiler, args.lean_checker, args.lean_reference, args.primitive]},
        "scope": "exact outcome class, full public event sequence, consumed bytes, selected draws and history count; finite corpus, shared trusted public crypto"})
    print(json.dumps({"status": "pass", "cases": len(results)}), flush=True)


if __name__ == "__main__":
    main()
