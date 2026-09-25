#!/usr/bin/env python3
"""Run the original-source Lean validator with exact public primitive replies.

The public service receives only each complete request emitted by Lean. It
cannot supply source control flow, a witness, or a prearranged outcome tape.
The saved replies are reproducible evidence, not cryptographic certificates.

Every test that drives the reference this way uses this module. Which request
Lean asks for, in what order, and what it is told, is the comparison those tests
make, so two drivers that answered slightly differently would make two different
comparisons under one name.
"""
import argparse
import json
from pathlib import Path

from journal import Journal


def write_json(path, value):
    Path(path).write_text(json.dumps(value, separators=(",", ":")) + "\n")


def run_reference(lean, primitive, source, descriptor, inputs, proof, output,
                  memo=None, max_requests=4096, transcript_budget=None, journal=None):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    # Without one of its own, the reference's invocations would be the only
    # thing a test drives that left no record of having been driven.
    journal = Journal(output) if journal is None else journal
    replies_path = output / "replies.json"
    replies = ["zkc.primitive-replies/1", []]
    memo = {} if memo is None else memo
    used = set()
    for _ in range(max_requests + 1):
        write_json(replies_path, replies)
        policy = [] if transcript_budget is None else [str(transcript_budget)]
        call = journal.attempt([lean, "reference", source, descriptor,
                                inputs, proof, replies_path, *policy])
        assert call.returncode in (0, 1), (call.returncode, call.stderr)
        try:
            observation = json.loads(call.stdout)
        except json.JSONDecodeError as error:
            raise RuntimeError(f"Lean reference failed: {call.returncode}: {call.stderr}") from error
        write_json(output / "observation.json", observation)
        if call.returncode or observation[1][0] != "pending-primitive":
            return observation
        request = observation[1][2]
        key = json.dumps(request, ensure_ascii=True, separators=(",", ":"))
        if key in used:
            raise AssertionError("exact cache answer was not consumed")
        used.add(key)
        if key not in memo:
            # Each request is retained under its own name: which ones were asked
            # for, and in what order, is part of what a failure has to show.
            request_path = output / f"request-{len(replies[1]):04d}.json"
            write_json(request_path, request)
            response = journal.attempt([primitive, request_path])
            if response.returncode:
                raise RuntimeError(f"Public primitive refused request: {response.stdout}")
            memo[key] = json.loads(response.stdout)
        replies[1].append([request, memo[key]])
    raise RuntimeError("reference request ceiling exceeded; no outcome inferred")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("lean", "primitive", "source", "descriptor", "inputs", "proof", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--transcript-budget", type=int)
    args = parser.parse_args()
    observation = run_reference(**vars(args))
    if observation[0] != "zkc.artifact-observation/1":
        print(json.dumps({"admission": observation}))
    else:
        print(json.dumps({"outcome": observation[1][0], "events": len(observation[2]),
                          "public_requests": len(observation[3]), "bytes": observation[4],
                          "draws": observation[5], "transcript_actions": observation[6]}))


if __name__ == "__main__":
    main()
