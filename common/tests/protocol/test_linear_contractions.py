"""Compiler-selected shared contractions execute through the ordinary native Runner."""

from pathlib import Path

import pytest


def mathematical_source(family, control="direct"):
    """Keep both uses and the stopping guard in actual scoped CFG fixtures."""
    fixture = Path(__file__).parents[1] / "fixtures/linear-contractions" / (control + ".mlir")
    source = fixture.read_text()
    if family == "field":
        for old, new in [
            ("ristretto255.scalar", "bls12-381.fr"),
            ("ristretto255.group", "bls12-381.fr"),
            ("!data.group_vector", "!data.field_vector"),
            ("!algebra.group", "!algebra.field"),
            ("curve.scale_each", "vector.mul"),
            ("curve.msm", "vector.dot"),
        ]:
            source = source.replace(old, new)
    return source


@pytest.mark.parametrize("control", ["direct", "if", "for"])
@pytest.mark.parametrize("family", ["field", "group"])
@pytest.mark.parametrize("linear", [False, True], ids=["dense", "diagonal"])
def test_linear_contractions(toolchain, directory, journal, family, linear, control):
    source = directory / "source.mlir"
    source.write_text(mathematical_source(family, control))

    def export(name, pipeline):
        physical = directory / f"{name}.mlir"
        journal.run(
            [toolchain.optimizer, source, "--verify-each", pipeline], keep=physical
        )
        candidate = directory / f"{name}.json"
        program = journal.json(
            [toolchain.compiler, "protocol-export", physical], keep=candidate
        )
        return candidate, program

    candidate, program = export(
        "selected",
        f"--zkc-participant-pipeline=linear-contractions={str(linear).lower()}",
    )
    assert program[0] == "zkc.program/0"
    bindings = {binding[0]: binding for binding in program[1]}
    assert len(program[3]) == 1
    participant = program[3][0]
    assert participant[3] == "P"
    assert [op[0] for op in participant[6]] == ["local", "return"]
    call = participant[6][0]
    function = next(function for function in program[2] if function[1] == call[2])

    # Inspect the emitted operations independently of their region nesting.
    def operations(value):
        if isinstance(value, list):
            if value and value[0] == "op":
                yield value
            else:
                for child in value:
                    yield from operations(child)

    kernels = {op[1]: op for op in operations(function[4])}
    weighted, first, guard, second = [
        kernels[f"lc_{len(name)}_{name}"]
        for name in ("weighted", "first", "between", "second")
    ]
    assert first[4][1] == second[4][1] == weighted[5][0]
    assert first[4][0] != second[4][0]
    assert bindings[guard[2]][1] == "control.require"

    backend = "dalek" if family == "group" else "arkworks"
    contracts = (
        ["curve.scale_each", "curve.msm", "curve.msm"]
        if family == "group"
        else ["vector.mul", "vector.dot", "vector.dot"]
    )
    prefix = backend + ("-diagonal" if linear else "")
    assert [bindings[op[2]][3] for op in (weighted, first, second)] == [
        f"{prefix}/{contract}" for contract in contracts
    ]
    if not linear:
        assert all("-diagonal/" not in binding[3] for binding in program[1])
        # Omitting the option must preserve the ordinary dense defaults too.
        _, default = export("default", "--zkc-participant-pipeline")
        assert default == program

    journal.run(
        [toolchain.driver("linear_contractions"), candidate, family, control],
        keep="native.stdout",
    )
