"""Put hostile text where the emitter reads a document string.

Every string in a canonical OIR document reaches the emitted crate: the
source identity lands in a string literal, labels and class names land
in comments and in struct fields. This script writes the mutated
document back in canonical form, so what the emitter refuses is the
content rather than the encoding.
"""

import json
import sys

# The payload is chosen so that escaping its position is not a matter of
# opinion: `compile_error!` fires if and only if it lands as code, and is
# inert text otherwise. The test then asserts nothing more than that the
# emitted crate builds.
INJECT = 'aaa" ; compile_error!("escaped its literal"); const X: &str = "bbb'
BREAK = 'commit_A\ncompile_error!("escaped its comment");\n// x'


def mutate(document: dict, where: str) -> dict:
    if where == "source-quote":
        document["source"] = "sha256:" + INJECT
    elif where == "comment-break":
        # The read row's label is written into a line comment.
        for row in document["program"]:
            if row[0] == "read":
                row[2] = BREAK
                break
        else:
            raise SystemExit("this document has no read row")
    elif where == "duplicate-label":
        document["entry"] = [["val", "tg"], ["val", "tg"], ["stream"]]
        document["statement_labels"] = ["y", "y"]
    elif where == "keyword-label":
        document["statement_labels"] = ["yield"]
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
