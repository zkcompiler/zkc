#!/usr/bin/env python3
"""Check the constructed-participant renderer's operation classification.

Synthetic exports exercise operation shapes independently of the compiled
examples. Each rendering is elaborated by Lean's parser and kernel, and the
rendered instructions are compared with constructors written independently of
the renderer. Wrongly shaped operations must refuse the whole export with the
renderer's shape diagnostic. Loops whose block arguments capture outer values,
including a nested loop capturing the enclosing induction index, render with
direct references to the captured values; a captured transcript or a capture
whose block argument has another sort refuses.
"""

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import support.evidence  # noqa: E402
import support.lake  # noqa: E402

spec = importlib.util.spec_from_file_location("constructed_participant", HERE / "bridges/construction/render.py")
renderer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(renderer)

TRANSCRIPT = '!runtime.capability<"transcript:merlin3.bls12-381.fr64be/0">'
FIELD = '!algebra.field<"bls12-381.fr">'
INDICES = "!algebra.indices"


def loop(site, carried, operands, results, arguments, body, yielded):
    attributes = [["carried", ["integer", str(carried)]], ["count", ["string", ""]], ["maximum", ["integer", "4"]],
                  ["parameter", ["bool", False]], ["site", ["string", site]]]
    return ["protocol.loop", attributes, [], operands, results, [[arguments, body, yielded]]]


def indices(operation, operands, binding):
    attributes = [["binding", ["symbol", "b"]], ["parameters", ["strings", []]], ["site", ["string", "s0"]]]
    return [f"algebra.exec.{operation}", attributes, [binding, [], ""], operands, [INDICES], []]


# Inputs: a field value (0), a count (1) and the host transcript (2). The outer
# loop carries the transcript and captures the field value; its body adds the
# captured value to the input, then runs an inner loop that carries the
# transcript and captures the outer induction index (3) and that sum (6).
CAPTURING = [
    loop("s", 1, [1, 2, 0], [TRANSCRIPT], ["ui64", TRANSCRIPT, FIELD], [
        ["algebra.field_add", [], [], [5, 0], [FIELD], []],
        loop("t", 1, [1, 4, 3, 6], [TRANSCRIPT], ["ui64", TRANSCRIPT, "ui64", FIELD], [
            indices("indices_empty", [], "indices.empty"),
            indices("indices_append", [11, 9], "indices.append"),
            ["algebra.field_add", [], [], [10, 10], [FIELD], []],
        ], [8]),
    ], [7]),
    ["algebra.field_equal", [], [], [0, 0], ["i1"], []],
]


def export(inputs, instructions, returned):
    policy = ["zkc.native-proof-policy/0", "entry", "role00000000", "role00000001", "0",
              "merlin3.bls12-381.fr64be/0", ["9"], [str(index) for index in range(len(inputs) - 1)], [["q", "d"]],
              "zkc.framed/0", ""]
    return ["zkc.constructed-participant/0", "sha256:" + "0" * 64, "sha256:" + "1" * 64, policy, "_math_1",
            inputs, ["i1", TRANSCRIPT], instructions, returned, []]


def check(output, lake):
    output.mkdir(parents=True, exist_ok=True)
    # A validator that conjoins two Boolean checks, as a composed Sigma verifier does.
    conjunction = export(["i1", "i1", TRANSCRIPT], [["arith.andi", [], [], [0, 1], ["i1"], []]], [3, 2])
    source = renderer.render(conjunction, "RenderedConjunction").replace("module\n\n", "", 1)
    source = source.replace("public import Zkc.Construction.Participant\n", "")
    source = source.replace("@[expose] public section\n", "")
    source += '''
open Zkc.Construction in
example : RenderedConjunction.participant.instructions =
    [⟨.calculate .booleanAnd, [0, 1], [.data .boolean], []⟩] := by
  decide +kernel
'''
    captured = renderer.render(export([FIELD, "ui64", TRANSCRIPT], CAPTURING, [4, 3]), "RenderedCaptures")
    captured = captured.replace("module\n\n", "", 1).replace("public import Zkc.Construction.Participant\n", "")
    source += captured.replace("@[expose] public section\n", "")
    base, extension = '!algebra.field<"base">', '!algebra.field<"extension">'
    embedding_attrs = [["binding", ["symbol", "embed"]], ["parameters", ["strings", []]],
                       ["site", ["string", "embedding"]]]
    embedding = ["algebra.exec.field_embed", embedding_attrs,
                 ["field.embed", ["extension"], ""], [0], [extension], []]
    embedded = renderer.render(export([base, TRANSCRIPT], [embedding], [2, 1]), "RenderedEmbedding")
    embedded = embedded.replace("module\n\n", "", 1).replace("public import Zkc.Construction.Participant\n", "")
    source += embedded.replace("@[expose] public section\n", "")
    source += '''
open Zkc.Construction in
example : RenderedEmbedding.participant.instructions =
    [⟨.calculate (.fieldEmbed "extension" "base"), [0], [.data (.field "extension")], []⟩] := by
  decide +kernel
'''
    source += '''
open Zkc.Construction in
example : RenderedCaptures.participant.instructions =
    [⟨.loop "s" 4 [6], [1, 2], [.transcript "merlin3.bls12-381.fr64be/0"], [
      ⟨.calculate (.fieldAdd "bls12-381.fr"), [0, 0], [.data (.field "bls12-381.fr")], []⟩,
      ⟨.loop "t" 4 [7], [1, 4], [.transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [8, 3], [.indices], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [5, 5], [.data (.field "bls12-381.fr")], []⟩]⟩]⟩,
     ⟨.calculate (.fieldEqual "bls12-381.fr"), [0, 0], [.data .boolean], []⟩] ∧
    RenderedCaptures.participant.returned = [4, 3] := by
  decide +kernel
'''
    path = output / "Rendered.lean"
    path.write_text("module\n\npublic import Zkc.Construction.Participant\n\n@[expose] public section\n" + source, encoding="utf-8")
    run = subprocess.run([lake, "lean", path], cwd=HERE,
                         capture_output=True, encoding="utf-8", timeout=120)
    (output / "lean.log").write_text(run.stdout + run.stderr, encoding="utf-8")
    if run.returncode:
        raise AssertionError(run.stdout + run.stderr)
    # A conjunction must read and produce Booleans; another shape refuses the export.
    inputs = ["i1", "i1", FIELD, TRANSCRIPT]
    malformed = [export(inputs, [["arith.andi", [], [], operands, results, []]], [4, 3])
                 for operands, results in [([2, 2], ["i1"]), ([0, 1], [FIELD]), ([0], ["i1"])]]
    for data in malformed:
        try:
            renderer.render(data, "Rejected")
        except ValueError as error:
            if "boolean conjunction shape" not in str(error):
                raise AssertionError(f"renderer refused a malformed conjunction for another reason: {error}")
            continue
        raise AssertionError("renderer accepted a malformed Boolean conjunction")
    # An attributed conjunction is not the recognized operation; it is retained
    # as unsupported for the Lean rules to refuse.
    attributed = export(["i1", "i1", TRANSCRIPT],
                        [["arith.andi", [["site", ["string", "s"]]], [], [0, 1], ["i1"], []]], [3, 2])
    if '.unsupported "arith.andi"' not in renderer.render(attributed, "Unsupported"):
        raise AssertionError("renderer classified an attributed conjunction")
    # A loop captures data only: a captured transcript, or a capture whose block
    # argument has another sort, refuses the export.
    capture_refusals = [
        ("loop capture sort", [loop("s", 0, [1, 2], [], ["ui64", TRANSCRIPT], [], [])]),
        ("loop block arguments", [loop("s", 1, [1, 2, 0], [TRANSCRIPT], ["ui64", TRANSCRIPT, "ui64"], [], [4])]),
    ]
    for diagnostic, instructions in capture_refusals:
        try:
            renderer.render(export([FIELD, "ui64", TRANSCRIPT], instructions, [0, 2]), "Rejected")
        except ValueError as error:
            if diagnostic not in str(error):
                raise AssertionError(f"renderer refused a malformed capture for another reason: {error}")
            continue
        raise AssertionError(f"renderer accepted a loop expected to refuse with {diagnostic}")
    embedding_refusals = [
        ("field embedding ports", embedding_attrs, ["field.embed", ["extension"], ""], [], [extension]),
        ("field embedding ports", embedding_attrs, ["field.embed", ["extension"], ""], [0], ["i1"]),
        ("field embedding binding", embedding_attrs, ["field.embed", ["base"], ""], [0], [extension]),
        ("field embedding binding", embedding_attrs, ["field.equal", ["extension"], ""], [0], [extension]),
        ("field embedding attributes", embedding_attrs[:-1], ["field.embed", ["extension"], ""], [0], [extension]),
        ("field embedding attributes", [embedding_attrs[0], ["parameters", ["strings", ["extra"]]],
                                        embedding_attrs[2]], ["field.embed", ["extension"], ""], [0], [extension]),
    ]
    # An explicit implementation is outside this mathematical profile. Retain
    # the exact binding boundary instead of erasing a third field of any type.
    embedding_refusals.extend(
        ("field embedding binding", embedding_attrs,
         ["field.embed", ["extension"], implementation], [0], [extension])
        for implementation in ("unregistered/field.embed", None, False, 0, [], {}))
    # Valid tagged payloads still need the operation's exact attribute roles.
    for position, attribute in ((0, ["string", "embed"]), (0, ["bool", True]),
                                (2, ["symbol", "embedding"]), (2, ["bool", False])):
        attrs = list(embedding_attrs)
        attrs[position] = [attrs[position][0], attribute]
        embedding_refusals.append(("field embedding attributes", attrs,
                                   ["field.embed", ["extension"], ""], [0], [extension]))
    # Check the common tagged-value decoder before a diagnostic-only attribute
    # can be dropped. In particular, bool is not an integer payload.
    for kind, payload in (("string", {}), ("symbol", 0), ("bool", 1),
                          ("integer", 1), ("integer", "1.5"), ("strings", "x"),
                          ("strings", [1]), ("text", [])):
        attrs = [*embedding_attrs[:2], ["site", [kind, payload]]]
        embedding_refusals.append(("invalid attribute payload", attrs,
                                   ["field.embed", ["extension"], ""], [0], [extension]))
    for diagnostic, attrs, binding, operands, results in embedding_refusals:
        try:
            renderer.render(export([base, TRANSCRIPT],
                [["algebra.exec.field_embed", attrs, binding, operands, results, []]], [0, 1]), "RejectedEmbedding")
        except ValueError as error:
            if diagnostic not in str(error):
                raise AssertionError(f"renderer refused a malformed embedding for another reason: {error}")
            continue
        raise AssertionError(f"renderer accepted an embedding expected to refuse with {diagnostic}")
    report = {"status": "pass", "kernel_cases": 3,
              "refusal_cases": len(malformed) + len(capture_refusals) + len(embedding_refusals), "unsupported_cases": 1,
              "renderer_sha256": support.lake.sha(Path(renderer.__file__)),
              "subject_sha256": support.lake.sha(path)}
    (output / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=support.evidence.records("construction-renderer"))
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    print(json.dumps(check(args.output.resolve(), support.lake.resolve(args.lake)), indent=2))
