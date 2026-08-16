"""Build a zkc-run vectors file from the backend runner's run record.

The positive vector carries the runner's statement, wire, and challenge
stream verbatim, expecting acceptance. The corrupt-nonce vector flips
the nonce word's low byte so the grinding check must refuse; the
corrupt-path vector flips a byte inside an input authentication path so
the Merkle multi-opening check must refuse; the corrupt-sibling vector
flips a byte inside a round's sibling values so the fold-consistency
check must refuse (expected challenges are
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
    # The wire layout the corrupt offsets index into, named so the
    # arithmetic is checkable: the absorbed prefix, then the openings.
    OPENED_VALUE = 16
    ROOTS = 3 * 32
    FINAL_POLY = 16
    NONCE_END = OPENED_VALUE + ROOTS + FINAL_POLY + 4
    OPENINGS = NONCE_END
    LEAVES = 4 * 4
    INPUT_PATHS = 4 * 4 * 32

    def flip(at: int) -> str:
        return (
            wire[: 2 * at]
            + format(int(wire[2 * at : 2 * at + 2], 16) ^ 0x01, "02x")
            + wire[2 * at + 2 :]
        )

    # Each corrupt mode flips one byte inside the named region, and the
    # named check must refuse: the nonce's low byte at the grinding
    # check, an input path digest at the Merkle multi-opening, a
    # first-round sibling at the fold consistency.
    corrupt_modes = {
        "corrupt-nonce": ("corrupted-nonce", NONCE_END - 1),
        "corrupt-path": ("corrupted-path", OPENINGS + LEAVES),
        "corrupt-sibling": ("corrupted-sibling", OPENINGS + LEAVES + INPUT_PATHS),
    }
    if mode == "accept":
        vector = {
            "name": "runner-round-trip",
            "statement": {"f_root": statement},
            "proof": wire,
            "expect": "accept",
            "challenges": challenges,
        }
    elif mode in corrupt_modes:
        name, offset = corrupt_modes[mode]
        vector = {
            "name": name,
            "statement": {"f_root": statement},
            "proof": flip(offset),
            "expect": "check_failure",
            "challenges": [],
        }
    else:
        raise SystemExit(f"unknown mode {mode!r}")
    json.dump(
        {"artifact_id": verifier_id, "vectors": [vector]},
        open(out_path, "w"),
        indent=1,
    )


if __name__ == "__main__":
    main()
