"""Compiler-selected shared contractions execute through the ordinary native Runner."""

import pytest


def mathematical_source(family, control="direct"):
    """Keep both uses observable, with a stopping guard between them."""
    group = family == "group"
    identity = "ristretto255.group" if group else "bls12-381.fr"
    scalar = "ristretto255.scalar" if group else identity
    result = f'!algebra.{"group" if group else "field"}<"{identity}">'
    producer, reduction = (
        ("curve.scale_each", "curve.msm") if group else ("vector.mul", "vector.dot")
    )
    map_op, reduce_op = (
        ("group_scale_each", "group_msm") if group else ("vector_mul", "vector_dot")
    )
    arguments = "%left: !V, %right: !V, %factors: !V, %values: !A, %allowed: i1"
    inputs = "%left, %right, %factors, %values, %allowed"
    types = "!V, !V, !V, !A, i1"
    source = f'''!V = !algebra.field_vector<"{scalar}">
!A = !algebra.{"group_vector" if group else "field_vector"}<"{identity}">
!R = {result}
module {{ "protocol.module"() ({{
  "runtime.binding"() {{sym_name="map", contract="{producer}", arguments=["{identity}"], implementation=""}} : () -> ()
  "runtime.binding"() {{sym_name="reduce", contract="{reduction}", arguments=["{identity}"], implementation=""}} : () -> ()
  "runtime.binding"() {{sym_name="guard", contract="control.require", arguments=[], implementation=""}} : () -> ()
  local.func @Work({arguments}) -> (!R, !R) attributes {{logical_origin=["Work", []]}} {{
    %weighted = "algebra.exec.{map_op}"(%factors, %values) {{binding=@map, site="weighted", parameters=[]}} : (!V, !A) -> !A
    %first = "algebra.exec.{reduce_op}"(%left, %weighted) {{binding=@reduce, site="first", parameters=[]}} : (!V, !A) -> !R
    "local.exec.require"(%allowed) {{binding=@guard, site="between", parameters=[]}} : (i1) -> ()
    %second = "algebra.exec.{reduce_op}"(%right, %weighted) {{binding=@reduce, site="second", parameters=[]}} : (!V, !A) -> !R
    local.return %first, %second : !R, !R
  }}
  "protocol.func"() ({{ ^entry({arguments}):
    %out:2 = "protocol.local_call"({inputs}) {{callee=@Work, role="P", site="work"}} : ({types}) -> (!R, !R)
    "protocol.return"(%out#0, %out#1) : (!R, !R) -> ()
  }}) {{sym_name="main", function_type=({types}) -> (!R, !R), roles=["P"], input_roles=[["P"],["P"],["P"],["P"],["P"]], output_roles=[["P"],["P"]]}} : () -> ()
}}) {{profile=#protocol.profile<protocol>}} : () -> () }}
'''

    if control == "direct":
        return source
    start = source.index("    %weighted =")
    end = source.index("    local.return %first, %second : !R, !R", start)
    body = source[start:end].replace("%", "%inner_")
    inner_arguments = arguments.replace("%", "%inner_")
    inner_inputs = inputs.replace("%", "%inner_")
    unused_arguments = arguments.replace("%", "%unused_")
    if control == "if":
        nested = f"""    %yes = "local.bool_constant"() {{value=true, site="yes"}} : () -> i1
    %result:2 = "local.if"(%yes, {inputs}) ({{ ^chosen({inner_arguments}):
{body}    "local.yield"(%inner_first, %inner_second) : (!R, !R) -> ()
    }}, {{ ^unused({unused_arguments}):
      "local.stop"() {{site="unused", reason="abort"}} : () -> ()
    }}) {{site="branch"}} : (i1, {types}) -> (!R, !R)
"""
    else:
        source = source.replace(
            "  local.func @Work",
            '  "runtime.binding"() {sym_name="constant", contract="index.constant", arguments=[], implementation=""} : () -> ()\n  local.func @Work',
        )
        start = source.index("    %weighted =")
        end = source.index("    local.return %first, %second : !R, !R", start)
        nested = f"""    %zero = "algebra.exec.index_constant"() {{binding=@constant, site="zero", parameters=["0"]}} : () -> ui64
    %count = "algebra.exec.index_constant"() {{binding=@constant, site="count", parameters=["2"]}} : () -> ui64
    %seed = "algebra.exec.{reduce_op}"(%left, %values) {{binding=@reduce, site="seed", parameters=[]}} : (!V, !A) -> !R
    %result:2 = "local.for"(%zero, %count, %seed, %seed, {inputs}) ({{ ^step(%i: ui64, %old_first: !R, %old_second: !R, {inner_arguments}):
{body}    "local.yield"(%inner_first, %inner_second, {inner_inputs}) : (!R, !R, {types}) -> ()
    }}) {{site="loop"}} : (ui64, ui64, !R, !R, {types}) -> (!R, !R)
"""
    return (
        source[:start]
        + nested
        + source[end:].replace(
            "local.return %first, %second", "local.return %result#0, %result#1", 1
        )
    )


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
        kernels[name] for name in ("weighted", "first", "between", "second")
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
