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

BOOLEAN = ["apply", "bool", []]
INDEX = ["apply", "index", []]
TRANSCRIPT = ["apply", "transcript", [["domain", "Transcript", "merlin3.bls12-381.fr64be/0"]]]
FIELD = ["apply", "field", [["domain", "Field", "bls12-381.fr"]]]
INDICES = ["apply", "indices", []]


def loop(site, carried, operands, results, arguments, body, yielded):
    attributes = [["carried", ["integer", "signless", "64", str(carried)]], ["count", ["string", ""]], ["maximum", ["integer", "signless", "64", "4"]],
                  ["parameter", ["bool", False]], ["site", ["string", site]]]
    return ["protocol.loop", attributes, [], operands, results, [[arguments, body, yielded]]]


def indices(operands, binding):
    attributes = [["binding", ["symbol", ["b"]]], ["parameters", ["array", []]], ["site", ["string", "s0"]]]
    return ["exec.apply", attributes, [binding, [], "", [] if binding == "indices.empty" else [INDICES, INDEX], [INDICES]], operands, [INDICES], []]


# Inputs: a field value (0), a count (1) and the host transcript (2). The outer
# loop carries the transcript and captures the field value; its body adds the
# captured value to the input, then runs an inner loop that carries the
# transcript and captures the outer induction index (3) and that sum (6).
CAPTURING = [
    loop("s", 1, [1, 2, 0], [TRANSCRIPT], [INDEX, TRANSCRIPT, FIELD], [
        ["algebra.field_add", [], [], [5, 0], [FIELD], []],
        loop("t", 1, [1, 4, 3, 6], [TRANSCRIPT], [INDEX, TRANSCRIPT, INDEX, FIELD], [
            indices([], "indices.empty"),
            indices([11, 9], "indices.append"),
            ["algebra.field_add", [], [], [10, 10], [FIELD], []],
        ], [8]),
    ], [7]),
    ["algebra.field_equal", [], [], [0, 0], [BOOLEAN], []],
]


def export(inputs, instructions, returned):
    policy = ["zkc.native-proof-policy/0", "entry", "role00000000", "role00000001", "0",
              "merlin3.bls12-381.fr64be/0", ["9"], [str(index) for index in range(len(inputs) - 1)], [["q", "d"]],
              "zkc.framed/0", "", []]
    return ["zkc.constructed-participant/0", "sha256:" + "0" * 64, "sha256:" + "1" * 64, policy, "_math_1",
            inputs, [BOOLEAN, TRANSCRIPT], instructions, returned, []]


def check(output, lake):
    """Render controls; `lake=None` leaves all generated kernel checks pending."""
    output.mkdir(parents=True, exist_ok=True)
    policy_refusals = []
    current = export([TRANSCRIPT], [], [0])
    for selected in [current[3][:-1], current[3] + [[]]]:
        policy_refusals.append((selected, "array of size 12"))
    for gates in [None, False, "", {}, [["q", "0"]], [["q", "1"]], [["q"]]]:
        policy_refusals.append((current[3][:-1] + [gates], "policy gates"))
    for selected, diagnostic in policy_refusals:
        data = export([TRANSCRIPT], [], [0])
        data[3] = selected
        try:
            renderer.render(data, "RejectedPolicy")
        except renderer.Refused as error:
            if diagnostic not in str(error):
                raise AssertionError(f"policy refused for another reason: {error}")
            continue
        raise AssertionError("renderer accepted an unsupported policy")
    # The native data.index attribute is unsigned i64. A different signedness,
    # width or string spelling must not silently acquire index semantics.
    index_literal = ["data.index", [["value", ["integer", "unsigned", "64", "18446744073709551615"]]],
                     [], [], [INDEX], []]
    index_source = renderer.render(export([TRANSCRIPT], [index_literal], [1, 0]), "RenderedIndex")
    field_literal = ["algebra.constant", [["value", ["parameter",
                     ["field_literal", "bls12-381.fr", "natural", "1"]]]], [], [], [FIELD], []]
    field_source = renderer.render(export([TRANSCRIPT], [field_literal], [1, 0]), "RenderedField")
    for value in (["integer", "signed", "64", "1"], ["integer", "signless", "64", "1"],
                  ["integer", "unsigned", "32", "1"], ["string", "1"]):
        malformed = ["data.index", [["value", value]], [], [], [INDEX], []]
        try:
            renderer.render(export([TRANSCRIPT], [malformed], [1, 0]), "InvalidIndex")
        except renderer.Refused:
            continue
        raise AssertionError("renderer accepted the wrong data.index attribute type")
    for value in (["string", "1"], ["parameter", ["field_literal", "koala-bear", "natural", "1"]]):
        malformed = ["algebra.constant", [["value", value]], [], [], [FIELD], []]
        try:
            renderer.render(export([TRANSCRIPT], [malformed], [1, 0]), "InvalidField")
        except renderer.Refused:
            continue
        raise AssertionError("renderer accepted a field literal with the wrong type or domain")
    # A validator that conjoins two Boolean checks, as a composed Sigma verifier does.
    conjunction = export([BOOLEAN, BOOLEAN, TRANSCRIPT], [["arith.andi", [], [], [0, 1], [BOOLEAN], []]], [3, 2])
    source = renderer.render(conjunction, "RenderedConjunction").replace("module\n\n", "", 1)
    source = source.replace("public import Zkc.Construction.Participant\n", "")
    source = source.replace("@[expose] public section\n", "")
    source += index_source.replace("module\n\n", "", 1).replace(
        "public import Zkc.Construction.Participant\n", "").replace("@[expose] public section\n", "")
    source += field_source.replace("module\n\n", "", 1).replace(
        "public import Zkc.Construction.Participant\n", "").replace("@[expose] public section\n", "")
    source += '''
open Zkc.Construction in
example : RenderedIndex.participant.instructions =
    [⟨.calculate (.indexConstant 18446744073709551615), [], [.data .index], []⟩] := by
  decide +kernel
open Zkc.Construction in
example : RenderedField.participant.instructions =
    [⟨.calculate (.fieldConstant "bls12-381.fr" 1), [], [.data (.field "bls12-381.fr")], []⟩] := by
  decide +kernel
'''
    source += '''
open Zkc.Construction in
example : RenderedConjunction.participant.instructions =
    [⟨.calculate .booleanAnd, [0, 1], [.data .boolean], []⟩] := by
  decide +kernel
'''
    captured = renderer.render(export([FIELD, INDEX, TRANSCRIPT], CAPTURING, [4, 3]), "RenderedCaptures")
    captured = captured.replace("module\n\n", "", 1).replace("public import Zkc.Construction.Participant\n", "")
    source += captured.replace("@[expose] public section\n", "")
    base = ["apply", "field", [["domain", "Field", "koala-bear"]]]
    extension = ["apply", "field", [["domain", "Field", "koala-bear.ext4-binomial3"]]]
    embedding_attrs = [["binding", ["symbol", ["embed"]]], ["parameters", ["array", []]],
                       ["site", ["string", "embedding"]]]
    embedding = ["exec.apply", embedding_attrs,
                 ["field.embed", [["domain", "Field", "koala-bear.ext4-binomial3"]], "", [base], [extension]], [0], [extension], []]
    embedded = renderer.render(export([base, TRANSCRIPT], [embedding], [2, 1]), "RenderedEmbedding")
    embedded = embedded.replace("module\n\n", "", 1).replace("public import Zkc.Construction.Participant\n", "")
    source += embedded.replace("@[expose] public section\n", "")
    source += '''
open Zkc.Construction in
example : RenderedEmbedding.participant.instructions =
    [⟨.calculate (.fieldEmbed "koala-bear.ext4-binomial3" "koala-bear"), [0], [.data (.field "koala-bear.ext4-binomial3")], []⟩] := by
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
    for name, attrs, namespace in (
            ("protocol.local_call", [["callee", ["symbol", ["source_helper"]]],
                                     ["role", ["string", "role00000001"]],
                                     ["site", ["string", "invoke"]]], "RenderedParticipantCall"),
            ("func.call", [["callee", ["symbol", ["source_helper"]]],
                           ["runtime.site", ["string", "handler"]]], "RenderedScopedCall")):
        data = export([FIELD, TRANSCRIPT], [[name, attrs, [], [0], [BOOLEAN], []]], [2, 1])
        rendered = renderer.render(data, namespace).replace("module\n\n", "", 1)
        source += rendered.replace("public import Zkc.Construction.Participant\n", "").replace(
            "@[expose] public section\n", "")
        source += f"\nopen Zkc.Construction in\nexample : {namespace}.participant.instructions =\n" \
                  '    [⟨.call "source_helper", [0], [.data .boolean], []⟩] := by decide +kernel\n'
    boolean = export([TRANSCRIPT], [["exec.boolean", [["site", ["string", "literal"]],
                        ["value", ["bool", True]]], [], [], [BOOLEAN], []]], [1, 0])
    rendered = renderer.render(boolean, "RenderedBoolean").replace("module\n\n", "", 1)
    source += rendered.replace("public import Zkc.Construction.Participant\n", "").replace(
        "@[expose] public section\n", "")
    source += '\nopen Zkc.Construction in\nexample : RenderedBoolean.participant.instructions =\n' \
              '    [⟨.calculate (.booleanConstant true), [], [.data .boolean], []⟩] := by decide +kernel\n'
    path = output / "Rendered.lean"
    path.write_text("module\n\npublic import Zkc.Construction.Participant\n\n@[expose] public section\n" + source, encoding="utf-8")
    if lake is not None:
        run = subprocess.run([lake, "lean", path], cwd=HERE,
                             capture_output=True, encoding="utf-8", timeout=120)
        (output / "lean.log").write_text(run.stdout + run.stderr, encoding="utf-8")
        if run.returncode:
            raise AssertionError(run.stdout + run.stderr)
    # A conjunction must read and produce Booleans; another shape refuses the export.
    inputs = [BOOLEAN, BOOLEAN, FIELD, TRANSCRIPT]
    malformed = [export(inputs, [["arith.andi", [], [], operands, results, []]], [4, 3])
                 for operands, results in [([2, 2], [BOOLEAN]), ([0, 1], [FIELD]), ([0], [BOOLEAN])]]
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
    attributed = export([BOOLEAN, BOOLEAN, TRANSCRIPT],
                        [["arith.andi", [["site", ["string", "s"]]], [], [0, 1], [BOOLEAN], []]], [3, 2])
    if '.unsupported "arith.andi"' not in renderer.render(attributed, "Unsupported"):
        raise AssertionError("renderer classified an attributed conjunction")
    # A loop captures data only: a captured transcript, or a capture whose block
    # argument has another sort, refuses the export.
    capture_refusals = [
        ("loop capture sort", [loop("s", 0, [1, 2], [], [INDEX, TRANSCRIPT], [], [])]),
        ("loop block arguments", [loop("s", 1, [1, 2, 0], [TRANSCRIPT], [INDEX, TRANSCRIPT, INDEX], [], [4])]),
    ]
    for diagnostic, instructions in capture_refusals:
        try:
            renderer.render(export([FIELD, INDEX, TRANSCRIPT], instructions, [0, 2]), "Rejected")
        except ValueError as error:
            if diagnostic not in str(error):
                raise AssertionError(f"renderer refused a malformed capture for another reason: {error}")
            continue
        raise AssertionError(f"renderer accepted a loop expected to refuse with {diagnostic}")
    embedding_refusals = []
    from copy import deepcopy
    mutations = [
        lambda row: row[2].pop(),
        lambda row: row[2][1][0].__setitem__(1, "Group"),
        lambda row: row[2].__setitem__(2, "selected/field.embed"),
        lambda row: row[2].__setitem__(3, [extension]),
        lambda row: row[2].__setitem__(4, [base]),
        lambda row: row.__setitem__(3, []),
        lambda row: row.__setitem__(4, [BOOLEAN]),
        lambda row: row[1][0].__setitem__(1, ["symbol", ["namespace", "embed"]]),
        lambda row: row[1][1].__setitem__(1, ["array", [["parameter", ["natural", "0"]]]]),
        lambda row: row[1][2].__setitem__(1, ["text", "old escape"]),
    ]
    for mutate in mutations:
        row = deepcopy(embedding)
        mutate(row)
        embedding_refusals.append(row)
    for row in embedding_refusals:
        try:
            renderer.render(export([base, TRANSCRIPT], [row], [0, 1]), "RejectedEmbedding")
        except ValueError:
            continue
        raise AssertionError("renderer accepted a forged typed embedding")
    changed = deepcopy(embedding)
    changed[2][0] = "field.equal"
    if '.unsupported "exec.apply:field.equal"' not in renderer.render(
            export([base, TRANSCRIPT], [changed], [2, 1]), "UnsupportedBinding"):
        raise AssertionError("renderer treated another binding as field embedding")
    report = {"status": "pass", "kernel_cases": 6,
              "refusal_cases": len(malformed) + len(capture_refusals) + len(embedding_refusals) + len(policy_refusals), "unsupported_cases": 2,
              "renderer_sha256": support.lake.sha(Path(renderer.__file__)),
              "subject_sha256": support.lake.sha(path)}
    report["kernel_checked"] = lake is not None
    if lake is None:
        report["rendered_cases"] = report.pop("kernel_cases")
        report["status"] = "rendered"
    (output / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=support.evidence.records("construction-renderer"))
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--render-only", action="store_true", help="write scratch controls without running Lean")
    args = parser.parse_args()
    lake = None if args.render_only else support.lake.resolve(args.lake)
    print(json.dumps(check(args.output.resolve(), lake), indent=2))
