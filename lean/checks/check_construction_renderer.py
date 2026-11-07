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

Associated members come from the export's catalogue rows. Lean admits those
rows against its own catalogue: a participant whose identities the Lean
catalogue omits renders, and `Participant.checkCatalogue` refuses it with
`structured-catalogue-unknown`; rows that disagree with the Lean catalogue or
omit a named identity refuse there too, and a binding whose member the rows do
not supply refuses in the renderer.
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

BLS_MODULUS = "52435875175126190479447740508185965837690552500527637822603658699938581184513"
TWO_ADIC_PRIME = ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "PrimeField"]
TWO_ADIC_EXTENSION = ["TwoAdicField", "Field", "CommRing", "CharacteristicNotTwo", "ExtensionField",
                      "IndexRandomness", "IndexBlockRandomness"]
# The native rows of the identities the synthetic participants name, as the
# exporter writes them: closed under associated members, in catalogue order.
BLS_ROWS = [
    ["nominal", "bls12-381.fr", "Field", [["PairingG1", "bls12-381.g1"], ["PairingG2", "bls12-381.g2"],
                                          ["PairingGT", "bls12-381.gt"]],
     ["Field", "CommRing", "PrimeField", "CharacteristicNotTwo", "PairingField"], BLS_MODULUS],
    ["nominal", "bls12-381.g2", "Group", [["Scalar", "bls12-381.fr"]], ["Group", "ScalarAction"], None],
    ["nominal", "bls12-381.gt", "Group", [["Scalar", "bls12-381.fr"]], ["Group", "ScalarAction"], None],
    ["nominal", "bls12-381.g1", "Group", [["Scalar", "bls12-381.fr"]], ["Group", "ScalarAction"], None],
    ["nominal", "merlin3.bls12-381.fr64be/0", "Transcript", [["ChallengeField", "bls12-381.fr"]],
     ["FieldTranscript", "Transcript"], None]]


def rows(*extra):
    return [BLS_ROWS + list(extra), []]


def extension_rows(base_id, extension_id, characteristic):
    return [["nominal", base_id, "Field", [], TWO_ADIC_PRIME, characteristic],
            ["nominal", extension_id, "Field", [["BaseField", base_id]], TWO_ADIC_EXTENSION, characteristic]]


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


def export(inputs, instructions, returned, catalogue=None):
    policy = ["zkc.native-proof-policy/0", "entry", "role00000000", "role00000001", "0",
              "merlin3.bls12-381.fr64be/0", ["9"], [str(index) for index in range(len(inputs) - 1)], [["q", "d"]],
              "zkc.framed/0", "", []]
    return ["zkc.constructed-participant/0", "sha256:" + "0" * 64, "sha256:" + "1" * 64, policy, "_math_1",
            inputs, [BOOLEAN, TRANSCRIPT], instructions, returned, [], catalogue or rows()]


def embedding_export(base_id, extension_id, catalogue):
    base = ["apply", "field", [["domain", "Field", base_id]]]
    extension = ["apply", "field", [["domain", "Field", extension_id]]]
    attributes = [["binding", ["symbol", ["embed"]]], ["parameters", ["array", []]],
                  ["site", ["string", "embedding"]]]
    row = ["exec.apply", attributes, ["field.embed", [["domain", "Field", extension_id]], "", [base], [extension]],
           [0], [extension], []]
    return export([base, TRANSCRIPT], [row], [2, 1], catalogue)


def strip(rendered):
    """A rendering without its module header, to share one Lean file."""
    return rendered.replace("module\n\n", "", 1).replace("public import Zkc.Construction.Participant\n", "").replace(
        "@[expose] public section\n", "")


def catalogue_controls():
    """Rendered participants with the catalogue admission each must receive.

    The renderer projects members through any well-formed rows; Lean's
    catalogue decides. Native rows of BabyBear and Goldilocks extensions are
    installed but outside the Lean catalogue, and refuse as unknown.
    """
    from copy import deepcopy
    quartic = rows(*extension_rows("koala-bear", "koala-bear.ext4-binomial3", "2130706433"))
    cases = [("AdmittedBls", export([TRANSCRIPT], [], [0]), None),
             ("AdmittedQuartic", embedding_export("koala-bear", "koala-bear.ext4-binomial3", quartic), None)]
    for namespace, base_id, extension_id, characteristic in [
            ("OutsideBabyBear", "baby-bear", "baby-bear.ext4-binomial11", "2013265921"),
            ("OutsideGoldilocks", "goldilocks", "goldilocks.ext2-binomial7", "18446744069414584321")]:
        outside = rows(*extension_rows(base_id, extension_id, characteristic))
        cases.append((namespace, embedding_export(base_id, extension_id, outside), "structured-catalogue-unknown"))
    # Consistent rows that differ from the Lean catalogue's: capability order.
    reordered = deepcopy(quartic)
    reordered[0][4][4] = ["Transcript", "FieldTranscript"]
    cases.append(("ReorderedSuite", export([TRANSCRIPT], [], [0], reordered), "structured-catalogue-mismatch"))
    # A named identity without its row: the suite of the transcript sort.
    missing = [[row for row in BLS_ROWS if row[2] != "Transcript"], []]
    cases.append(("MissingSuite", export([TRANSCRIPT], [], [0], missing), "structured-domain-unknown"))
    return cases


def renderer_member_refusals():
    """A binding member or required capability the rows do not supply refuses before Lean."""
    quartic = rows(*extension_rows("koala-bear", "koala-bear.ext4-binomial3", "2130706433"))[0]
    without_member = [row[:3] + [[]] + row[4:] if row[1] == "koala-bear.ext4-binomial3" else row for row in quartic]
    without_capability = [row[:4] + [[fact for fact in row[4] if fact != "ExtensionField"]] + row[5:]
                          if row[1] == "koala-bear.ext4-binomial3" else row for row in quartic]
    count = 0
    for catalogue, diagnostic in [(rows(), "unknown associated domain"),
                                  ([without_member, []], "missing associated domain member"),
                                  ([without_capability, []], "missing binding capability")]:
        try:
            renderer.render(embedding_export("koala-bear", "koala-bear.ext4-binomial3", catalogue), "Rejected")
        except ValueError as error:
            if diagnostic not in str(error):
                raise AssertionError(f"renderer refused a member for another reason: {error}")
            count += 1
            continue
        raise AssertionError(f"renderer resolved a member the rows do not supply ({diagnostic})")
    return count


def product_controls():
    """Projection expansion is checked against independently written Lean data."""
    product = ["variant", ["tuple", [["atom", "test.record"]]], [["Record", [INDEX, INDEX]]]]
    make = ["exec.variant", [["alternative", ["string", "Record"]], ["site", ["string", "make"]]],
            [], [0, 1], [product], []]
    match = ["exec.match", [["alternatives", ["array", [["string", "Record"]]]],
                            ["site", ["string", "project"]]], [], [3, 0], [INDEX, INDEX, INDEX],
             [[[INDEX, INDEX, INDEX], [], ["exec.complete", [1, 2, 0]], "Record", [INDEX, INDEX]]]]
    data = export([INDEX, INDEX, TRANSCRIPT], [make, match], [4, 5, 6, 2])
    data[6] = [INDEX, INDEX, INDEX, TRANSCRIPT]
    return strip(renderer.render(data, "RenderedProduct")) + r'''
open Zkc.Construction in
example : RenderedProduct.participant.instructions = [
    ⟨.calculate (.makeProduct "[\"test.record\"]" "Record" (.cons .index (.cons .index .nil))),
      [0, 1], [.data (.product "[\"test.record\"]" "Record" (.cons .index (.cons .index .nil)))], []⟩,
    ⟨.calculate (.getProduct "[\"test.record\"]" "Record" (.cons .index (.cons .index .nil))
      .index (.there .here)), [3], [.data .index], []⟩,
    ⟨.calculate (.getProduct "[\"test.record\"]" "Record" (.cons .index (.cons .index .nil))
      .index .here), [3], [.data .index], []⟩] ∧
    RenderedProduct.participant.returned = [4, 0, 5, 2] := by decide +kernel
'''


def local_branch_controls():
    guard = ["exec.apply", [["binding", ["symbol", ["require"]]], ["parameters", ["array", []]],
                            ["site", ["string", "guard"]]],
             ["control.require", [], "", [BOOLEAN], []], [0], [], []]
    branch = ["exec.test", [["site", ["string", "choose"]]], [], [0, 1], [BOOLEAN],
              [[[BOOLEAN], [], ["exec.complete", [0]], "then", []],
               [[BOOLEAN], [guard], ["exec.complete", [0]], "else", []]]]
    data = export([BOOLEAN, BOOLEAN, TRANSCRIPT], [branch], [3, 2])
    return strip(renderer.render(data, "RenderedLocalBranch")) + '''
open Zkc.Construction in
example : RenderedLocalBranch.participant.instructions = [
    ⟨.localBranch, [0, 1], [.data .boolean],
      [⟨[.data .boolean], [], [0]⟩,
       ⟨[.data .boolean], [⟨.require "guard", [0], [], []⟩], [0]⟩]⟩] := by decide +kernel
'''


def local_range_controls():
    region = [[INDEX, INDEX, BOOLEAN], [], ["exec.complete", [2, 0]], True]
    instruction = ["exec.range", [["site", ["string", "traverse"]]], [], [0, 1, 2, 3], [INDEX], [region]]
    data = export([INDEX, INDEX, INDEX, BOOLEAN, TRANSCRIPT], [instruction], [5, 4])
    data[6] = [INDEX, TRANSCRIPT]
    return strip(renderer.render(data, "RenderedLocalRange")) + '''
open Zkc.Construction in
example : RenderedLocalRange.participant.instructions = [
    ⟨.localRange true, [0, 1, 2, 3], [.data .index],
      [⟨[.data .index, .data .index, .data .boolean], [], [2, 0]⟩]⟩] := by decide +kernel
'''


def embedded_math_controls():
    folded = ["data.finite_fold", [["domain", ["symbol", ["range"]]],
                                   ["step", ["symbol", ["sum"]]]], [], [0, 1, 2], [INDEX], []]
    instruction = ["exec.compute", [["callee", ["symbol", ["calculation"]]],
                                     ["site", ["string", "compute"]]], [], [0, 1, 2], [INDEX],
                   [[[INDEX, INDEX, INDEX], [folded], ["func.return", [3]]]]]
    data = export([INDEX, INDEX, INDEX, TRANSCRIPT], [instruction], [4, 3])
    data[6] = [INDEX, TRANSCRIPT]
    return strip(renderer.render(data, "RenderedMathCompute")) + '''
open Zkc.Construction in
example : RenderedMathCompute.participant.instructions = [
    ⟨.mathCompute, [0, 1, 2], [.data .index],
      [⟨[.data .index, .data .index, .data .index],
        [⟨.finiteFold "range" "sum" "", [0, 1, 2], [.data .index], []⟩], [3]⟩]⟩] := by decide +kernel
'''


def checked_primitive_controls():
    attrs = [["binding", ["symbol", ["installed"]]], ["parameters", ["array", []]],
             ["site", ["string", "comparison"]]]
    instruction = ["exec.apply", attrs, ["index.equal", [], "", [INDEX, INDEX], [BOOLEAN]],
                   [0, 1], [BOOLEAN], []]
    data = export([INDEX, INDEX, TRANSCRIPT], [instruction], [3, 2])
    data[6] = [BOOLEAN, TRANSCRIPT]
    return strip(renderer.render(data, "RenderedCheckedPrimitive")) + '''
open Zkc.Construction in
example : RenderedCheckedPrimitive.participant.instructions =
    [⟨.execute .indexEqual, [0, 1], [.data .boolean], []⟩] := by decide +kernel
'''


def sequence_controls():
    sequence = ["apply", "sequence", [["type", INDEX]]]
    attrs = [["binding", ["symbol", ["installed"]]], ["parameters", ["array", []]],
             ["site", ["string", "sequence"]]]
    body = [
        ["exec.apply", attrs, ["sequence.empty", [["type", INDEX]], "", [], [sequence]], [], [sequence], []],
        ["exec.apply", attrs, ["sequence.append", [["type", INDEX]], "", [sequence, INDEX], [sequence]],
         [2, 0], [sequence], []],
        ["exec.apply", attrs, ["sequence.at", [["type", INDEX]], "", [sequence, INDEX], [INDEX]],
         [3, 0], [INDEX], []],
        ["data.sequence_length", [], [], [3], [INDEX], []],
        ["data.sequence_empty", [], [], [], [sequence], []]]
    data = export([INDEX, TRANSCRIPT], body, [4, 1])
    data[6] = [INDEX, TRANSCRIPT]
    return strip(renderer.render(data, "RenderedSequences")) + '''
open Zkc.Construction in
example : RenderedSequences.participant.instructions = [
    ⟨.execute (.sequenceEmpty .index), [], [.data (.sequence .index)], []⟩,
    ⟨.execute (.sequenceAppend .index), [2, 0], [.data (.sequence .index)], []⟩,
    ⟨.execute (.sequenceAt .index), [3, 0], [.data .index], []⟩,
    ⟨.calculate (.sequenceLength .index), [3], [.data .index], []⟩,
    ⟨.calculate (.sequenceEmpty .index), [], [.data (.sequence .index)], []⟩] := by decide +kernel
'''


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
    # Closed frames preserve duplicate captures, arm order and every result.
    from copy import deepcopy
    selection = ["data.branch", [["alternatives", ["array", [["string", "then"], ["string", "else"]]]]],
                 [], [0, 1, 1], [BOOLEAN, BOOLEAN], [
                     [[BOOLEAN, BOOLEAN], [], ["data.yield", [0, 1]], "then", []],
                     [[BOOLEAN, BOOLEAN], [], ["data.yield", [1, 0]], "else", []]]]
    selected = export([BOOLEAN, BOOLEAN, TRANSCRIPT], [selection], [3, 2])
    source += strip(renderer.render(selected, "RenderedSelection"))
    source += '''
open Zkc.Construction in
example : RenderedSelection.participant.instructions =
    [⟨.mathBranch, [0, 1, 1], [.data .boolean, .data .boolean],
      [⟨[.data .boolean, .data .boolean], [], [0, 1]⟩,
       ⟨[.data .boolean, .data .boolean], [], [1, 0]⟩]⟩] := by decide +kernel
'''
    selection_refusals = [
            (0, [BOOLEAN], "Math branch captures"),
            (2, ["data.yield", [0, 3]], "Math yielded"),
            (3, "then", "Math branch arm"),
            (4, [BOOLEAN], "Math branch arm")]
    for index, replacement, diagnostic in selection_refusals:
        invalid = deepcopy(selected)
        invalid[7][0][5][1][index] = replacement
        try:
            renderer.render(invalid, "RejectedSelection")
        except renderer.Refused as error:
            if diagnostic not in str(error):
                raise AssertionError(f"selected arm refused for another reason: {error}")
        else:
            raise AssertionError("renderer accepted a malformed dormant selected arm")
    captured = renderer.render(export([FIELD, INDEX, TRANSCRIPT], CAPTURING, [4, 3]), "RenderedCaptures")
    captured = captured.replace("module\n\n", "", 1).replace("public import Zkc.Construction.Participant\n", "")
    source += captured.replace("@[expose] public section\n", "")
    base = ["apply", "field", [["domain", "Field", "koala-bear"]]]
    extension = ["apply", "field", [["domain", "Field", "koala-bear.ext4-binomial3"]]]
    embedding_attrs = [["binding", ["symbol", ["embed"]]], ["parameters", ["array", []]],
                       ["site", ["string", "embedding"]]]
    embedding = ["exec.apply", embedding_attrs,
                 ["field.embed", [["domain", "Field", "koala-bear.ext4-binomial3"]], "", [base], [extension]], [0], [extension], []]
    quartic = rows(*extension_rows("koala-bear", "koala-bear.ext4-binomial3", "2130706433"))
    embedded = renderer.render(export([base, TRANSCRIPT], [embedding], [2, 1], quartic), "RenderedEmbedding")
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
    [⟨.loop "s" 4, [1, 2], [.transcript "merlin3.bls12-381.fr64be/0"], [⟨[.data .index, .transcript "merlin3.bls12-381.fr64be/0"], [
      ⟨.calculate (.fieldAdd "bls12-381.fr"), [0, 0], [.data (.field "bls12-381.fr")], []⟩,
      ⟨.loop "t" 4, [1, 4], [.transcript "merlin3.bls12-381.fr64be/0"], [⟨[.data .index, .transcript "merlin3.bls12-381.fr64be/0"], [
        ⟨.indicesEmpty, [], [.indices], []⟩,
        ⟨.indicesAppend, [8, 3], [.indices], []⟩,
        ⟨.calculate (.fieldAdd "bls12-381.fr"), [5, 5], [.data (.field "bls12-381.fr")], []⟩], [7]⟩]⟩], [6]⟩]⟩,
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
    catalogue_cases = catalogue_controls()
    for namespace, data, _ in catalogue_cases:
        source += strip(renderer.render(data, namespace))
    source += "\nopen Zkc.Construction Zkc.Source.Structured in\nexample : [" + ", ".join(
        f"{namespace}.participant.checkCatalogue {namespace}.catalogue constructionCatalogue"
        for namespace, _, _ in catalogue_cases) + \
        "] = [" + ", ".join(".ok ()" if code is None else f'.error "{code}"' for _, _, code in catalogue_cases) + \
        "] := by\n  decide +kernel\n"
    source += product_controls() + local_branch_controls() + local_range_controls() + embedded_math_controls() + checked_primitive_controls() + sequence_controls()
    path = output / "Rendered.lean"
    path.write_text("module\n\npublic import Zkc.Construction.Participant\npublic import Zkc.Construction.CatalogueAdmission\n\n"
                    "@[expose] public section\n" + source, encoding="utf-8")
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
            renderer.render(export([base, TRANSCRIPT], [row], [0, 1], quartic), "RejectedEmbedding")
        except ValueError:
            continue
        raise AssertionError("renderer accepted a forged typed embedding")
    changed = deepcopy(embedding)
    changed[2][0] = "field.equal"
    if '.unsupported "exec.apply:field.equal"' not in renderer.render(
            export([base, TRANSCRIPT], [changed], [2, 1]), "UnsupportedBinding"):
        raise AssertionError("renderer treated another binding as field embedding")
    member_refusals = renderer_member_refusals()
    report = {"status": "pass", "kernel_cases": 13, "catalogue_cases": len(catalogue_cases),
              "refusal_cases": len(malformed) + len(capture_refusals) + len(embedding_refusals) + len(policy_refusals)
              + member_refusals + len(selection_refusals), "unsupported_cases": 2,
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
