"""Ordered physical crossings at local control ports, checked against source."""

import copy
import json

import pytest

from journal import Journal
from toolchain import Toolchain, records
from variant_codec import descriptor


CONTROLS = ("if", "match", "for-capture", "for-carried", "for-both")
FIELD = "bls12-381.fr"


def source(control, repeated=False, captures=None):
    """Two distinct fixed-layout results make operand-order mutations observable."""
    arguments = [["x", "table:F"], ["y", "table:F"], ["r", "field:F"],
                 ["condition", "bool"], ["lower", "index"], ["upper", "index"]]
    body = [["op", "first", "poly.fold", ["F"], [], ["x", "r"], ["a"]],
            ["op", "second", "poly.fold", ["F"], [], ["y", "r"], ["b"]]]
    nested = [["op", "inside", "poly.fold", ["F"], [], ["a", "r"], ["next"]],
              ["yield", ["next", "b"]]]
    captures = ["a", "b", "r"] if captures is None else captures
    if control == "if":
        body.append(["if", "control", "condition", captures, nested,
                     [["yield", ["a", "b"]]], ["out", "other"]])
    elif control == "match":
        variant = descriptor("Choice", [("Left", ["bool"]), ("Right", ["bool"])])
        body.append(["variant", "choice", variant, "Left", ["condition"], "chosen"])
        body.append(["match", "control", "chosen", captures,
                     [["Left", ["flag"], nested],
                      ["Right", ["flag"], [["yield", ["a", "b"]]]]], ["out", "other"]])
    else:
        carried = [["acc", "x"], ["saved", "y"]] if control == "for-capture" else [
            ["acc", "a"], ["saved", "b"]]
        captures = ["r"] if control == "for-carried" else captures
        if control == "for-carried":
            nested = [["op", "inside", "poly.fold", ["F"], [], ["acc", "r"], ["next"]],
                      ["yield", ["next", "saved"]]]
        body.append(["for", "control", "i", "lower", "upper", carried, captures,
                     nested, ["out", "other"]])
    if repeated:
        again = copy.deepcopy(body[-1])
        again[1] = "again"
        again[-1] = ["out_again", "other_again"]
        for region in regions(again):
            for instruction in region:
                if instruction[0] == "op":
                    instruction[1] += "_again"
        body.append(again)
    body.append(["return", body[-1][-1].copy()])
    concrete = [[name, ty.replace(":F", ":" + FIELD)] for name, ty in arguments]
    library = ["zkc.library/1",
            [["generic_function", "Work", [["F", "Field"]], [["CommRing", ["F"]]],
              arguments, ["table:F", "table:F"], body]],
            [["configure", "Concrete", "Work", [["F", FIELD]],
              [["first", "arkworks-msb/poly.fold"], ["second", "arkworks-msb/poly.fold"]]]],
            ["zkc.protocol/1", [], [],
             [["protocol", "Main", ["P"], [],
               [[name, "P", ty] for name, ty in concrete],
               [["P", "table:" + FIELD], ["P", "table:" + FIELD]], [],
               [["local", "call", "P", "Concrete", [name for name, _ in concrete], ["out", "other"]],
                ["return", ["out", "other"]]]]],
             [["instance", "concrete", "Main", [], [], [["P", "P"]]]],
             [["entry", "main", "concrete"]]]]
    if control != "match":
        return library
    # Local variants currently belong to explicit common functions, not generic
    # definitions. Exercise their shared checker through whole-source validation.
    common = library[3]
    def close(instructions):
        for instruction in instructions:
            if instruction[0] == "op":
                _, site, contract, _, attrs, inputs, outputs = instruction
                implementation = "arkworks-msb/poly.fold" if site in ("first", "second") else ""
                common[1].append([site, contract, [FIELD], implementation])
                instruction[:] = ["op", site, site, attrs, inputs, outputs]
            elif instruction[0] == "match":
                for _, _, nested in instruction[4]:
                    close(nested)
    close(body)
    common[2].append(["function", "Work", concrete, ["table:" + FIELD] * 2, body, ["Work", []]])
    common[3][0][7][0][3] = "Work"
    return common


def regions(instruction):
    if instruction[0] == "if":
        return instruction[4:6]
    if instruction[0] == "match":
        return [arm[2] for arm in instruction[4]]
    return [instruction[7]]


def compile_case(control, release=False, repeated=False, label="positive", captures=None):
    tools = Toolchain()
    journal = Journal(records(f"{control}-{release}-{repeated}-{label}"))
    original = source(control, repeated, captures)
    source_path = journal.write("source.json", original)
    # Both independent source-admission paths must accept the small carrier.
    journal.run([tools.compiler, "protocol-admit", source_path])
    journal.run([tools.checker("interactive-protocol"), "--admit", source_path])
    flags = ["--release-storage"] if release else []
    candidate = journal.json([tools.compiler, "protocol-compile", source_path, *flags])
    return tools, journal, source_path, candidate


def check_candidate(tools, journal, source_path, candidate, label="candidate", error=None,
                    whole_error=None):
    path = journal.write(f"{label}.json", candidate)
    function = next(f for f in candidate[3] if f[5][0] == "Work")
    checker = tools.checker("interactive-protocol")
    if json.loads(source_path.read_text())[0] == "zkc.library/1":
        journal.run([checker, "--check-local", source_path, "Concrete", path, function[1]], refuses=error)
    journal.run([checker, "--check-generic", source_path, path],
                refuses=whole_error or ("source-local-unmatched" if error else None))
    return path


@pytest.mark.parametrize("control", CONTROLS)
@pytest.mark.parametrize("release", (False, True), ids=("retained", "released"))
def test_control_representations(control, release):
    tools, journal, source_path, candidate = compile_case(control, release)
    path = check_candidate(tools, journal, source_path, candidate)
    journal.run([tools.compiler, "protocol-import", path])
    journal.save()


@pytest.mark.parametrize("control", ("if", "match", "for-capture", "for-both"))
def test_interleaved_control_capture_crossings(control):
    tools, journal, source_path, candidate = compile_case(
        control, label="interleaved-captures", captures=["a", "r", "b"])
    check_candidate(tools, journal, source_path, candidate)
    body, start, _ = crossing_block(candidate)
    body[start], body[start + 1] = body[start + 1], body[start]
    check_candidate(tools, journal, source_path, candidate, "reordered",
                    "local-conversion-correspondence")
    journal.save()


def test_condition_can_also_be_a_control_capture():
    tools, journal, source_path, candidate = compile_case(
        "if", label="captured-condition", captures=["a", "condition", "b", "r"])
    check_candidate(tools, journal, source_path, candidate)
    journal.save()


def crossing_block(candidate, site="control"):
    body = next(f[4] for f in candidate[3] if f[5][0] == "Work")
    index = next(i for i, instruction in enumerate(body) if instruction[1] == site)
    relayouts = {binding[0] for binding in candidate[1] if binding[1] == "table.relayout"}
    start = index
    while start and body[start - 1][0] == "op" and body[start - 1][2] in relayouts:
        start -= 1
    assert index - start >= 2
    return body, start, index


@pytest.mark.parametrize("control", CONTROLS)
def test_repeated_control_crossings(control):
    tools, journal, source_path, candidate = compile_case(control, repeated=True)
    body, start, index = crossing_block(candidate)
    _, next_start, next_index = crossing_block(candidate, "again")
    first, second = body[start:index], body[next_start:next_index]
    assert [op[4] for op in first] == [op[4] for op in second]
    assert {op[5][0] for op in first}.isdisjoint(op[5][0] for op in second)
    check_candidate(tools, journal, source_path, candidate)
    journal.save()


MUTATIONS = {
    "crossing-order": "local-conversion-correspondence",
    "crossing-input": "local-conversion-correspondence",
    "control-operands": "local-control-correspondence",
    "hoisted-crossing": "local-conversion-correspondence",
    "extra-crossing": "local-control-correspondence",
    "control-site": "local-control-correspondence",
    "inner-site": "local-operation-correspondence",
    "inner-operand": "local-operation-correspondence",
    "result-flow": "local-return-correspondence",
}


@pytest.mark.parametrize("control", CONTROLS)
@pytest.mark.parametrize("mutation", MUTATIONS)
def test_control_crossing_correspondence(control, mutation):
    tools, journal, source_path, candidate = compile_case(control, label=mutation)
    body, start, index = crossing_block(candidate)
    instruction = body[index]
    if mutation == "crossing-order":
        body[start], body[start + 1] = body[start + 1], body[start]
    elif mutation == "crossing-input":
        body[start][4] = body[start + 1][4].copy()
    elif mutation == "control-operands":
        operands = instruction[5] if control.startswith("for") and control != "for-capture" else (
            instruction[6] if control == "for-capture" else instruction[3])
        if control.startswith("for") and control != "for-capture":
            operands[0][1], operands[1][1] = operands[1][1], operands[0][1]
        else:
            operands[0], operands[1] = operands[1], operands[0]
    elif mutation == "hoisted-crossing":
        # The producer still dominates the conversion, but another operation
        # now intervenes before its actual use at the control boundary.
        conversion = body.pop(start)
        second_input = next(i for i, op in enumerate(body) if op[1] == "second") - 1
        body.insert(second_input, conversion)
    elif mutation == "extra-crossing":
        conversion = copy.deepcopy(body[start])
        conversion[1], conversion[5] = "extra_layout", ["extra_value"]
        body.insert(index, conversion)
    elif mutation == "control-site":
        instruction[1] = "changed_control"
    elif mutation == "inner-site":
        regions(instruction)[0][0][1] = "changed_inner"
    elif mutation == "inner-operand":
        nested = regions(instruction)[0]
        nested[0][4][0] = nested[-1][1][1]
    else:
        body[-1][1].reverse()
    path = journal.write("mutated.json", candidate)
    # These mutations remain admitted physical programs. Their refusal must
    # come from source correspondence, not incidental type or name failures.
    journal.run([tools.compiler, "protocol-import", path])
    check_candidate(tools, journal, source_path, candidate, "mutated", MUTATIONS[mutation])
    journal.save()


@pytest.mark.parametrize("control", CONTROLS)
@pytest.mark.parametrize("mutation", ("missing-crossing", "wrong-endpoints", "wrong-attributes"))
def test_control_crossing_admission(control, mutation):
    tools, journal, source_path, candidate = compile_case(control, label=mutation)
    body, start, _ = crossing_block(candidate)
    if mutation == "missing-crossing":
        removed = body.pop(start)
        native_error = "local-control-capture" if control == "for-capture" else "interactive-unavailable"
        lean_error = "unbound:" + removed[5][0]
    elif mutation == "wrong-endpoints":
        body[start][2] = next(b[0] for b in candidate[1]
                              if b[1] == "table.relayout" and b[2][1] == "arkworks.mle-lsb/1")
        native_error = lean_error = "binding-operation-signature"
    else:
        body[start][3] = ["1"]
        native_error = lean_error = "interactive-kernel-parameters"
    path = journal.write("mutated.json", candidate)
    journal.run([tools.compiler, "protocol-import", path], refuses=native_error)
    check_candidate(tools, journal, source_path, candidate, "mutated", lean_error, lean_error)
    journal.save()


def test_carried_capture_crossings_are_not_reused():
    tools, journal, source_path, candidate = compile_case("for-both", label="reuse")
    body, start, index = crossing_block(candidate)
    assert index - start == 4
    assert body[start][4] == body[start + 2][4]
    kept, removed = body[start][5][0], body[start + 2][5][0]
    body.pop(start + 2)

    def replace(value):
        return [replace(item) for item in value] if isinstance(value, list) else kept if value == removed else value

    candidate = replace(candidate)
    path = journal.write("reused.json", candidate)
    journal.run([tools.compiler, "protocol-import", path])
    check_candidate(tools, journal, source_path, candidate, "reused", "local-conversion-correspondence")
    journal.save()


@pytest.mark.parametrize("control", CONTROLS)
def test_control_fixed_implementation(control):
    tools, journal, source_path, _ = compile_case(control, label="fixed-implementation")
    alternate = json.loads(source_path.read_text())
    if alternate[0] == "zkc.library/1":
        alternate[2][0][4][0][1] = "arkworks/poly.fold"
    else:
        next(binding for binding in alternate[1] if binding[0] == "first")[3] = "arkworks/poly.fold"
    path = journal.write("alternate-source.json", alternate)
    candidate = journal.json([tools.compiler, "protocol-compile", path])
    check_candidate(tools, journal, source_path, candidate, "alternate", "local-selection-correspondence")
    journal.save()


@pytest.mark.parametrize("control", CONTROLS)
def test_repeated_control_crossings_are_not_reused(control):
    tools, journal, source_path, candidate = compile_case(control, repeated=True, label="reuse")
    body, start, index = crossing_block(candidate)
    _, next_start, next_index = crossing_block(candidate, "again")
    replacements = {later[5][0]: earlier[5][0]
                    for earlier, later in zip(body[start:index], body[next_start:next_index], strict=True)}
    del body[next_start:next_index]

    def replace(value):
        return [replace(item) for item in value] if isinstance(value, list) else replacements.get(value, value)

    candidate = replace(candidate)
    path = journal.write("reused.json", candidate)
    journal.run([tools.compiler, "protocol-import", path])
    check_candidate(tools, journal, source_path, candidate, "reused", "local-missing-conversion")
    journal.save()
