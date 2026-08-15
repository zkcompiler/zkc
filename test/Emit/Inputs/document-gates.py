"""Remove from a document something the emitter must not proceed without.

Each mutation here is a document the reference executor refuses, or a
shape whose emitted code would be wrong. The emitter is a source-free
consumer, so it has to reach the same answer from the artifact alone.
"""

import json
import sys


def mutate(document: dict, where: str) -> dict:
    if where == "unrouted-class":
        # Drop a codec route while leaving the rows that use the class.
        # The reference refuses this document outright (zkc-E400).
        used = {
            row[3] for row in document["program"] if row[0] in ("read", "squeeze")
        }
        for klass in sorted(used):
            if klass in document["codecs"]:
                del document["codecs"][klass]
                break
        else:
            raise SystemExit("no routed class is used by a row")
    elif where == "open-stream":
        # Drop expect_end. Without it the emitted verifier never asks
        # whether the proof was exhausted, so it accepts trailing bytes.
        document["program"] = [
            row for row in document["program"] if row[0] != "expect_end"
        ]
        # decide's operand is the sponge, so the remaining rows still
        # reference valid results; only the stream is left open.
    elif where == "pow-wrong-space":
        # Widen the proof-of-work squeeze's space so it is no longer
        # 2^bits for the hole's declared bit count. The trial the fill
        # would run is then not the check the verifier performs, and
        # the emitter must refuse (zkc-E412's emit-time form), exactly
        # as the reference executor does at run time.
        for row in document["program"]:
            if row[0] == "squeeze" and row[2] == "pow":
                row[7] = str(int(row[7]) * 2)
                break
        else:
            raise SystemExit("no pow squeeze to widen")
    else:
        raise SystemExit(f"unknown mutation {where!r}")
    return document


def main() -> int:
    source, target, where = sys.argv[1], sys.argv[2], sys.argv[3]
    with open(source, encoding="utf-8") as handle:
        document = json.load(handle)
    with open(target, "w", encoding="utf-8") as handle:
        json.dump(
            mutate(document, where), handle, separators=(",", ":"), sort_keys=True
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
