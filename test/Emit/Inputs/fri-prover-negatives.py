"""Derive prover vectors whose fills must refuse, from an accepting one.

Each mutation keeps the corpus well-formed and moves exactly one thing
the fills gate on, so the vector proves which refusal fires rather than
that something went wrong.
"""

import json
import sys

# BabyBear's prime: the first word no canonical payload may carry.
BB = 2013265921


def mutate(corpus: dict, where: str) -> dict:
    accepting = next(
        case for case in corpus["prover_vectors"] if case["expect"] == "ok"
    )
    case = json.loads(json.dumps(accepting))
    case["proof"] = ""
    case["challenges"] = []
    case["expect"] = "fill"
    case["label"] = "openval"
    if where == "noncanonical-word":
        trace = case["witness"]["codeword"]
        case["witness"]["codeword"] = format(BB, "08x") + trace[8:]
        case["name"] = "noncanonical_payload_word"
        case["message"] = (
            "fri witness payload word is outside the canonical field range"
        )
    elif where == "short-trace":
        # Halve the trace: the fold chain reaches the family's final
        # length one round early, so the last commit has nothing left to
        # commit and says so.
        trace = case["witness"]["codeword"]
        case["witness"]["codeword"] = trace[: len(trace) // 2]
        case["name"] = "trace_height_below_the_family"
        case["label"] = "commit3"
        case["message"] = (
            "the commit fill expects a codeword longer than the final 2 evaluations"
        )
    elif where == "long-trace":
        # Double the trace: the fold chain ends above the family's final
        # length, and the final fill names the length it expected.
        trace = case["witness"]["codeword"]
        case["witness"]["codeword"] = trace + trace
        case["name"] = "trace_height_above_the_family"
        case["label"] = "final"
        case["message"] = (
            "the final fill expects the fully folded codeword (2 evaluations); got 4"
        )
    else:
        raise SystemExit(f"unknown mutation {where!r}")
    return {
        "artifact_id": corpus["artifact_id"],
        "prover_vectors": [accepting, case],
    }


def main() -> int:
    source, target, where = sys.argv[1], sys.argv[2], sys.argv[3]
    with open(source, encoding="utf-8") as handle:
        corpus = json.load(handle)
    with open(target, "w", encoding="utf-8") as handle:
        json.dump(mutate(corpus, where), handle, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
