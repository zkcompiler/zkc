"""Build a zkc-run vectors file from the backend runner's run record.

The positive vector carries the runner's statement, wire, and challenge
stream verbatim, expecting acceptance; the corrupt-nonce vector flips
the wire's final byte so the executor's grinding check must refuse with
a verdict (expected challenges are deliberately empty there — the
corrupted stream is not predicted, only its reject class is).
"""

import json
import re
import sys


def main() -> None:
    runner_out, verifier_id_path, out_path, mode = sys.argv[1:5]
    text = open(runner_out).read()
    statement = re.search(r"statement f_root: (\d+)", text).group(1)
    challenges = re.search(r"prover challenges: (.+)", text).group(1).split(",")
    wire = re.search(r"wire: ([0-9a-f]+)", text).group(1)
    verifier_id = open(verifier_id_path).read().strip()
    if mode == "accept":
        vector = {
            "name": "runner-round-trip",
            "statement": {"f_root": statement},
            "proof": wire,
            "expect": "accept",
            "challenges": challenges,
        }
    else:
        flipped = wire[:-2] + format(int(wire[-2:], 16) ^ 0x01, "02x")
        vector = {
            "name": "corrupted-nonce",
            "statement": {"f_root": statement},
            "proof": flipped,
            "expect": "check_failure",
            "challenges": [],
        }
    json.dump(
        {"artifact_id": verifier_id, "vectors": [vector]},
        open(out_path, "w"),
        indent=1,
    )


if __name__ == "__main__":
    main()
