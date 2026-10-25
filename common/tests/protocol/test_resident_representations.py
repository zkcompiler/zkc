"""Checked compiler resident programs execute through the current Native Runner."""

import json

import pytest

from variant_codec import descriptor


GROUP = "group:bls12-381.g1@blst/g1"
SCALAR = "field:bls12-381.fr@blst/fr"
ARK_GROUP = "group:bls12-381.g1@arkworks.g1/0"
ARK_SCALAR = "field:bls12-381.fr@arkworks.fr/0"
SEQUENCE = "sequence<field:bls12-381.fr>@logical.sequence/0[blst/fr]"
NESTED = ("sequence<sequence<field:bls12-381.fr>>"
          "@logical.sequence/0[logical.sequence/0[blst/fr]]")
ARRAY = "field_array<bls12-381.fr,4>@blst/field-array[blst/fr]"
FIXED = "fixed_vector<field:bls12-381.fr,4>@blst/fixed-vector[blst/fr]"


def instructions(body):
    for instruction in body:
        yield instruction
        if instruction[0] == "if":
            yield from instructions(instruction[4])
            yield from instructions(instruction[5])
        elif instruction[0] == "for":
            yield from instructions(instruction[7])
        elif instruction[0] == "match":
            for _, _, arm in instruction[4]:
                yield from instructions(arm)


@pytest.mark.parametrize("mode,returned,stopped", [
    ("resident", 16, 2), ("ports", 8, 10), ("branch", 12, 6), ("loop", 10, 8),
])
def test_compiled_resident_execution(toolchain, directory, journal, mode, returned, stopped):
    artifact = directory / "program.json"
    program = journal.json([
        toolchain.tool("compiler", "test/zkc-resident_representations-test"), "--emit", mode,
    ], keep=artifact)
    assert program[0] == "zkc.program/0"
    bindings = {binding[0]: binding for binding in program[1]}
    assert len(bindings) == len(program[1])
    assert all(len(binding) == 5 for binding in program[1])
    assert bindings["scale"] == [
        "scale", "curve.scale", ["bls12-381.g1"], "blst/resident/curve.scale", [],
    ]
    assert bindings["guard"] == ["guard", "control.require", [], "arkworks/control.require", []]
    conversions = {name: binding for name, binding in bindings.items()
                   if binding[1] == "representation.convert"}
    assert set(bindings) == {"scale", "guard"} | conversions.keys()
    for binding in conversions.values():
        assert binding[3] == "native/representation.convert"
        assert (binding[2], binding[4]) in [
            (["field:bls12-381.fr"], [ARK_SCALAR, SCALAR]),
            (["group:bls12-381.g1"], [ARK_GROUP, GROUP]),
        ]

    assert len(program[3]) == 1
    participant = program[3][0]
    assert participant[3] == "P"
    assert [instruction[0] for instruction in participant[6]] == ["local", "return"]
    call = participant[6][0]
    functions = {function[1]: function for function in program[2]}
    work = functions[call[2]]
    ports = [ARK_GROUP, ARK_SCALAR] if mode == "ports" else [GROUP, SCALAR]
    ports += ["bool@native.bool/0", "index@native.index/0", "index@native.index/0",
              "bool@native.bool/0", ARK_SCALAR]
    assert [ty for _, ty in work[2]] == ports
    assert [ty for _, ty in participant[4]] == ports
    assert work[3] == participant[5] == [GROUP]
    # Expansion may retain the unused source definition; no executable helper
    # call or cast may survive inside any emitted local function.
    for function in program[2]:
        assert all(instruction[0] in {"op", "if", "for", "yield", "return"}
                   for instruction in instructions(function[4]))
        if function is not work:
            assert [ty for _, ty in function[2]] == [GROUP, SCALAR]
            assert function[3] == [GROUP]

    body = work[4]
    branch = next(instruction for instruction in body if instruction[0] == "if")
    loop = next(instruction for instruction in body if instruction[0] == "for")
    ops = [instruction for instruction in instructions(body) if instruction[0] == "op"]
    adapters = [op for op in ops if op[2] in conversions]
    assert len(adapters) == {"resident": 0, "ports": 6, "branch": 1, "loop": 1}[mode]
    assert branch[5] == [["yield", [branch[3][0]]]]
    assert body[-1] == ["return", loop[8]]
    assert loop[5][0][1] == branch[6][0]

    if mode == "ports":
        # The group and scalar conversions execute in operand order, after the
        # guard, and feed exactly the first resident call's differing ports.
        assert body[0][2] == "guard"
        assert [bindings[op[2]][2][0] for op in body[1:3]] == [
            "group:bls12-381.g1", "field:bls12-381.fr",
        ]
        assert body[3][4] == [op[5][0] for op in body[1:3]]
    else:
        # Adjacent resident operations and the expanded source helper share
        # their physical values, with no inserted round trip.
        first, adjacent, helper = body[1:4]
        assert all(op[2] == "scale" for op in (first, adjacent, helper))
        assert adjacent[4][0] == first[5][0]
        assert helper[4][0] == adjacent[5][0]
        assert "expanded" in helper[1] and "helper_scale" in helper[1]
        assert branch[3][0] == helper[5][0]
    if mode in {"branch", "loop"}:
        reached = branch[4] if mode == "branch" else loop[7]
        assert reached[0][2] == "guard"
        assert reached[1] == adapters[0]
        assert reached[2][4][1] == adapters[0][5][0]

    report = journal.json([
        toolchain.driver("resident_representations"), artifact, mode,
    ], keep="native.json")
    assert report == {"mode": mode, "returned": returned, "stopped": stopped}


@pytest.mark.parametrize("mode,returned,stopped", [
    ("sequence", 4, 0), ("variant", 4, 0), ("control", 8, 8), ("dense", 9, 21),
])
def test_compiled_resident_aggregates(toolchain, directory, journal, mode, returned, stopped):
    emitted = directory / "aggregates"
    journal.run([
        toolchain.tool("compiler", "test/zkc-aggregate_layouts-test"), "--emit", emitted,
    ], keep="compiler.txt")
    artifact = emitted / f"{mode}.json"
    original = artifact.read_bytes()
    program = json.loads(original)
    assert program[0] == "zkc.program/0"
    assert all(len(binding) == 5 for binding in program[1])
    bindings = {binding[0]: binding for binding in program[1]}
    assert len(bindings) == len(program[1])
    participant, = program[3]
    assert participant[3] == "P"
    assert [instruction[0] for instruction in participant[6]] == ["local", "return"]
    call = participant[6][0]
    work = next(function for function in program[2] if function[1] == call[2])
    ports = {
        "sequence": [SCALAR], "variant": [SCALAR],
        "control": [ARK_SCALAR, "bool@native.bool/0", "index@native.index/0",
                    "index@native.index/0"],
        "dense": ["vector:bls12-381.fr@blst/fr", "index@native.index/0"],
    }[mode]
    output = {"sequence": NESTED, "variant": SEQUENCE, "control": SEQUENCE,
              "dense": SCALAR}[mode]
    assert [ty for _, ty in participant[4]] == ports
    assert [ty for _, ty in work[2]] == ports
    assert work[3] == participant[5] == [output]
    body = list(instructions(work[4]))
    assert all(instruction[0] in {"op", "if", "for", "variant", "match", "yield", "return"}
               for instruction in body)
    ops = [instruction for instruction in body if instruction[0] == "op"]
    conversions = {name for name, binding in bindings.items()
                   if binding[1] == "representation.convert"}
    for name in conversions:
        # The only adaptation allowed here is an exact scalar leaf conversion.
        assert bindings[name][1:] == [
            "representation.convert", ["field:bls12-381.fr"],
            "native/representation.convert", [ARK_SCALAR, SCALAR],
        ]
    assert len([op for op in ops if op[2] in conversions]) == (2 if mode == "control" else 0)
    used = {op[2] for op in ops}
    families = [binding for name, binding in bindings.items() if name in used
                if binding[1].startswith(("sequence.", "field_array.", "fixed_vector."))]
    assert families
    assert all(len(binding[4]) == 1 for binding in families)
    layouts = {binding[4][0] for binding in families}
    assert layouts == {"sequence": {SEQUENCE, NESTED}, "variant": {SEQUENCE},
                       "control": {SEQUENCE}, "dense": {ARRAY, FIXED}}[mode]

    if mode == "variant":
        nominal = descriptor("SelectedChoice", [
            ["none", []], ["some", ["sequence<field:bls12-381.fr>"]],
            ["unused", ["fixed_vector<field:bls12-381.fr,2>"]],
        ])
        packed, = [instruction for instruction in body if instruction[0] == "variant"]
        assert packed[2] == (nominal + "@logical.variant/0[logical.sequence/0[blst/fr],"
                             "blst/fixed-vector[blst/fr]]")
        assert packed[3] == "some"
        matched, = [instruction for instruction in body if instruction[0] == "match"]
        assert matched[2] == packed[5]
        assert [(label, len(payload)) for label, payload, _ in matched[4]] == [
            ("none", 0), ("some", 1), ("unused", 1),
        ]
    if mode == "control":
        branch = next(instruction for instruction in work[4] if instruction[0] == "if")
        loop = next(instruction for instruction in work[4] if instruction[0] == "for")
        for reached in [branch[4], loop[7]]:
            operations = [instruction for instruction in reached if instruction[0] == "op"]
            assert [bindings[op[2]][1] for op in operations] == [
                "control.require", "representation.convert", "sequence.append",
            ]
            assert operations[2][4][1] == operations[1][5][0]
        assert not any(instruction[0] == "op" and instruction[2] in conversions
                       for instruction in work[4])

    report = journal.json([
        toolchain.driver("resident_representations"), artifact, mode,
    ], keep="native.json")
    assert report == {"mode": mode, "returned": returned, "stopped": stopped}
    assert artifact.read_bytes() == original
