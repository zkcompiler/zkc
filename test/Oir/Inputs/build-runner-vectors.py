"""Build a zkc-run vectors file from the backend runner's run record.

The positive vector carries the runner's statement, wire, and challenge
stream verbatim, expecting acceptance. The corrupt-nonce vector flips
the nonce word's low byte so the grinding check must refuse; the
corrupt-path vector flips a byte inside an input authentication path so
the Merkle multi-opening check must refuse (expected challenges are
deliberately empty there — the corrupted stream is not predicted, only
its reject class is).

The `prover` mode builds the prover-endpoint corpus instead: the same
statement and stream, the runner's fixed witness trace as the payload
hex, and the whole wire as the expected emission — byte equality with
the upstream-driven pipeline is the differential gate for the emitted
prover's borrowed-kernel fills, exact because both grinds return the
deterministic least witness in this serial build. A short-payload
refusal rides along as the negative control.
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
    # The trace comes from the run record like every other field, so the
    # corpus cannot drift from the fixture it describes.
    trace = re.search(r"trace: ([0-9a-f]+)", text).group(1)
    verifier_id = open(verifier_id_path).read().strip()
    if mode == "prover":
        json.dump(
            {
                "artifact_id": verifier_id,
                "prover_vectors": [
                    {
                        "name": "runner_wire",
                        "statement": {"f_root": statement},
                        "witness": {"codeword": trace},
                        "expect": "ok",
                        "proof": wire,
                        "challenges": challenges,
                    },
                    {
                        "name": "short_witness_payload",
                        "statement": {"f_root": statement},
                        "witness": {"codeword": "00000001"},
                        "expect": "fill",
                        "label": "openval",
                        "message": (
                            "fri witness payload must hold a power-of-two "
                            "number of rows, at least two"
                        ),
                        "proof": "",
                        "challenges": [],
                    },
                ],
            },
            open(out_path, "w"),
            indent=1,
        )
        return
    if mode not in {"accept", "corrupt-nonce", "corrupt-path"}:
        raise SystemExit(f"unknown mode {mode!r}")

    def flip(at: int) -> str:
        return (
            wire[: 2 * at]
            + format(int(wire[2 * at : 2 * at + 2], 16) ^ 0x01, "02x")
            + wire[2 * at + 2 :]
        )

    if mode == "accept":
        vector = {
            "name": "runner-round-trip",
            "statement": {"f_root": statement},
            "proof": wire,
            "expect": "accept",
            "challenges": challenges,
        }
    elif mode == "corrupt-nonce":
        # The nonce's own low byte: after the opened value (16), three
        # round roots (96), and the final coefficient (16), the nonce is
        # bytes 128..132 — the grinding check must refuse.
        vector = {
            "name": "corrupted-nonce",
            "statement": {"f_root": statement},
            "proof": flip(131),
            "expect": "check_failure",
            "challenges": [],
        }
    else:
        # One byte inside the first input authentication path (the
        # openings start at 132: four query leaves, then the paths) —
        # the Merkle multi-opening check must refuse.
        vector = {
            "name": "corrupted-path",
            "statement": {"f_root": statement},
            "proof": flip(148),
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
