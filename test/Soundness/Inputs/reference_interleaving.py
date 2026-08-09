"""Exercise the reference soundness-pricing interleaving boundary.

The refusal must fire on the production path — ``derive.sealed_view`` — not
on a helper called directly, so dropping the integration point cannot leave
this test green. The de-interleaved twin of the same protocol must pass,
proving the witness is otherwise valid and the refusal is specifically about
interleaving.
"""

import copy

from oracle import derive, model
from oracle.model import Refusal


def _interleaved() -> dict:
    """The twin of test/Soundness/Inputs/interleaved-open.mlir: two evalopen
    bodies genuinely interleaved in the spine (A's first message, B's first,
    A's second, B's second), which sealing accepts and pricing must refuse."""
    anchors_a = {
        "commitment": "sha256:50feaa7e90906c60034b0db9b872015920f5"
                      "2bf543de7873fd102adbae1b9a7f",
        "point": "sha256:7ebb83c8fe1e5617c803993577102fa4d4b7"
                 "6a851fd855a2a25282ca680923ac",
        "value": "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd"
                 "9fc7cfa04d4ca35c89025b10c379",
    }
    anchors_b = {
        "commitment": "sha256:65b60629324703b7d7f6fea1362d18f78b3c"
                      "1c865a8e890003477de2a8480f43",
        "point": "sha256:085712992bf36d0c86e3e8654f555f12fd6c"
                 "b4b39c1692daddb5b7b82f14e11f",
        "value": "sha256:308efab7d1ff27bcb8edb1d1ec89290f2662"
                 "1e6372fa7708f6fe5fda83ad45ba",
    }
    return {
        "policy": "analysis_only_artifact",
        "kappa": {
            "codecs": {"scalar": "ts_be8"},
            "iv": "artifact-id",
            "sponge": "toy_duplex",
        },
        "sources": [
            model.source(
                "eva",
                "sumcheck_evaluation",
                {"statement": "sha256:6c3aebe70e2969b448bcd2b7d38a34b7eebb"
                              "1cae4b73d18b8f9d1b0693e2e6c9"},
            ),
            model.source(
                "evb",
                "sumcheck_evaluation",
                {"statement": "sha256:2fca346db656187102ce806ac732e06a62df"
                              "0dbb2829e511a770556d398e1a6e"},
            ),
        ],
        "events": [
            model.slot("ma0", "scalar", True, ("opa", "m", 0)),
            model.slot("mb0", "scalar", True, ("opb", "m", 0)),
            model.slot("ma1", "scalar", True, ("opa", "m", 1)),
            model.slot("mb1", "scalar", True, ("opb", "m", 1)),
            model.chal("ca", "scalar", "il.ca", "2305843009213693952"),
            model.chal("cb", "scalar", "il.cb", "2305843009213693952"),
        ],
        "reduces": [
            model.reduce_row(
                "opa", "evalopen", ["eva"], ["ca"],
                [("opena", "single_opening")], anchors=[anchors_a],
            ),
            model.reduce_row(
                "opb", "evalopen", ["evb"], ["cb"],
                [("openb", "single_opening")], anchors=[anchors_b],
            ),
        ],
        "material_bindings": [
            model.material("ma0", anchors_a["commitment"]),
            model.material("ma1", anchors_a["value"]),
            model.material("ca", anchors_a["point"]),
            model.material("mb0", anchors_b["commitment"]),
            model.material("mb1", anchors_b["value"]),
            model.material("cb", anchors_b["point"]),
        ],
        "sinks": [
            model.route("residual", "opena", "evalopen-terminal-not-modeled"),
            model.route("residual", "openb", "evalopen-terminal-not-modeled"),
        ],
    }


interleaved = _interleaved()

# Fixture guard: the de-interleaved twin (A's body contiguous, then B's) must
# pass the same production entry, so the refusal below is about interleaving
# and nothing else.
contiguous = copy.deepcopy(interleaved)
events = contiguous["events"]
contiguous["events"] = [events[0], events[2], events[1], events[3],
                        events[4], events[5]]
derive.sealed_view(contiguous, model.VOCABULARY)

try:
    derive.sealed_view(interleaved, model.VOCABULARY)
except Refusal as error:
    print(error)
else:
    raise AssertionError("reference soundness pricing admitted interleaving")
