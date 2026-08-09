"""Both implementations must refuse the same broken derivation requests.

A skeleton the two agree on proves the structural half only if they also
agree on what is not derivable. These break one thing each: an occurrence
the artifact does not have, a premise whose notion does not chain, a value
the sealed protocol supplies and a caller may not, a target the root does
not reach.

Usage: request_mutations.py <request.json> <artifact.mlirbc> <signature.json>
                            <vocabulary.json> <profiles.json> <zkc-derive>
"""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..",
                                "reference"))

from oracle import derive, model, wellformed, witnesses
from oracle.model import Refusal

CLAIM = "sha256:083c1ba0d4e0e2d742ada57aca166a13ae8431ba6fd8438285954011ddaba4a7"
OTHER = "sha256:d8793823555a01692a958f1dfe4cbf8f61e8ab50546b93d5ef548379c8c5b760"

RBR = "zkc.rbr.sumcheck@reduction:sumcheck"
SR = "zkc.sr.from_rbr_knowledge@path:rbr_to_sr:knowledge:straightline"
FS = "zkc.fs.duplex_knowledge@path:sr_to_fs_duplex:knowledge:straightline"

PLAN = ["derivation", "plan"]
SR_NODE = [*PLAN, "premises", "source_sr"]
RBR_NODE = [*SR_NODE, "premises", "source_rbr"]


def _at(document, path):
    node = document
    for key in path:
        node = node[key]
    return node


def _set(document, path, value):
    _at(document, path[:-1])[path[-1]] = value


def _drop(document, path):
    del _at(document, path[:-1])[path[-1]]


MUTATIONS: list[tuple[str, object]] = [
    # The site has to name an occurrence the artifact actually has.
    ("the site names a different artifact",
     lambda d: _set(d, [*RBR_NODE, "site", "artifact_id"], "0" * 64)),
    ("the site names a claim digest the artifact does not carry",
     lambda d: _set(d, [*RBR_NODE, "site", "owner_claim", "descriptor_digest"],
                    OTHER)),
    ("the site names a transformer position with no reduction",
     lambda d: _set(d, [*RBR_NODE, "site", "transformer_position"], 7)),
    ("the site names an output the reduction does not produce",
     lambda d: _set(d, [*RBR_NODE, "site", "output_index"], 3)),
    ("a path occurrence names a claim the artifact does not carry",
     lambda d: _set(d, [*PLAN, "site", "claim", "descriptor_digest"], OTHER)),

    # The plan is explicit; nothing is searched for and nothing falls back.
    ("the plan applies a binding the signature does not declare",
     lambda d: _set(d, [*RBR_NODE, "binding"], "zkc.absent@reduction:none")),
    ("the plan applies a binding the context did not select",
     lambda d: _set(d, ["derivation", "selected_bindings"], [SR, FS])),
    ("a premise port the rule declares is unfilled",
     lambda d: _drop(d, [*SR_NODE, "premises", "source_rbr"])),
    ("a premise port the rule does not declare is filled",
     lambda d: _set(d, [*RBR_NODE, "premises", "ghost"],
                    copy.deepcopy(_at(d, RBR_NODE)))),
    ("the notion chain skips a step",
     lambda d: _set(d, [*SR_NODE, "premises", "source_rbr"],
                    copy.deepcopy(_at(d, SR_NODE)))),

    # A request asks about the protocol; it may not assert it.
    ("a request asserts a value the sealed protocol supplies",
     lambda d: _set(d, ["derivation", "resolved_parameters", RBR,
                        "field_class"],
                    {"sort": "reduction_contract", "value": "sumcheck"})),
    ("a parameter the binding reads is not resolved",
     lambda d: _drop(d, ["derivation", "resolved_parameters", RBR,
                         "field_order"])),
    ("a parameter is resolved at the wrong sort",
     lambda d: _set(d, ["derivation", "resolved_parameters", RBR,
                        "field_class"],
                    {"sort": "integer", "value": "1"})),
    ("a parameter nothing reads is resolved",
     lambda d: _set(d, ["derivation", "resolved_parameters", RBR, "ghost"],
                    {"sort": "integer", "value": "1"})),

    # The root has to reach the target, not something near it.
    ("the target names a different notion than the root concludes",
     lambda d: _set(d, ["derivation", "target", "index", "notion"],
                    "state_restoration")),
    ("the target names a different track",
     lambda d: _set(d, ["derivation", "target", "index", "track"],
                    "soundness")),
    ("the target names a different subject",
     lambda d: _set(d, ["derivation", "target", "subject", "claim",
                        "descriptor_digest"], OTHER)),
    ("the target declares a resource the root does not quantify over",
     lambda d: _at(d, ["derivation", "target", "resource_variables"]).append(
         {"name": "q", "sort": "integer"})),

    # The format is closed.
    ("the request carries a field the format does not declare",
     lambda d: _set(d, ["derivation", "extra"], 1)),
]


def main() -> int:
    request_path, sealed, signature_path = sys.argv[1:4]
    vocabulary_path, profiles_path, tool = sys.argv[4:7]
    base = model.load_json(open(request_path).read())

    signature = wellformed.load(model.load_json(open(signature_path).read()))
    view = derive.sealed_view(
        witnesses.PIR_WITNESSES["sumcheck-fs"], model.VOCABULARY
    )

    def is_refusal(action) -> bool:
        try:
            action()
        except Refusal:
            return True
        return False

    def unexpected() -> None:
        raise TypeError("refusal harness exception probe")

    try:
        is_refusal(unexpected)
    except TypeError:
        print("unexpected exceptions escape the refusal boundary")
    else:
        raise AssertionError("unexpected exception counted as a refusal")

    disagreements = 0
    with tempfile.TemporaryDirectory() as work:
        probe = os.path.join(work, "request.json")

        # Positive control, for the same reason as the signature battery: a
        # non-zero exit is only evidence of refusal once the tool is known to
        # accept something. Without this line, substituting a tool that fails
        # unconditionally leaves every case below reporting agreement.
        with open(probe, "w") as handle:
            json.dump(base, handle)
        control = subprocess.run(
            [tool, sealed, f"--signature={signature_path}",
             f"--protocol-vocabulary={vocabulary_path}",
             f"--construction-profile-registry={profiles_path}",
             f"--request={probe}", "--skeleton", "-o=/dev/null"],
            capture_output=True, text=True)
        if control.returncode != 0:
            print("the unmutated request does not derive; every refusal "
                  "below would be vacuous")
            print(control.stderr.strip()[:400])
            return 1
        print("control: the unmutated request derives")

        for name, mutate in MUTATIONS:
            document = copy.deepcopy(base)
            mutate(document)
            with open(probe, "w") as handle:
                json.dump(document, handle)
            carrier = subprocess.run(
                [tool, sealed, f"--signature={signature_path}",
                 f"--protocol-vocabulary={vocabulary_path}",
                 f"--construction-profile-registry={profiles_path}",
                 f"--request={probe}", "--skeleton", "-o=/dev/null"],
                capture_output=True, text=True).returncode != 0
            reference = is_refusal(
                lambda: derive.derive(
                    signature, view, derive.read_request(document, signature)
                )
            )
            if carrier and reference:
                print(f"both refuse: {name}")
                continue
            disagreements += 1
            if carrier:
                detail = "carrier only refuses"
            elif reference:
                detail = "reference only refuses"
            else:
                detail = "neither refuses"
            print(f"DISAGREE ({detail}): {name}")

    print(f"{len(MUTATIONS) - disagreements}/{len(MUTATIONS)} refused by both")
    return 1 if disagreements else 0


if __name__ == "__main__":
    raise SystemExit(main())
