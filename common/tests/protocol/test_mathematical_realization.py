"""Shared mathematical realization through source, Entry, and native execution."""

from source_modules import core_packages, library_modules

import json
from pathlib import Path

import pytest

from entry import Entry, joint_artifact

ROOT = Path(__file__).resolve().parents[3]
MODULES = library_modules(*core_packages())
HEADER = """module sample;
use zkc::vector::{Vector, indexing []};
use zkc::matrix::{Matrix};
use zkc::finite as finite;
use zkc::finite_domain as domains;
domain F=field("koala-bear");
"""


def work_instructions(entry):
    package = json.loads(entry.package.read_text())
    bundle = joint_artifact(package)
    program = json.loads(bundle["candidate"])
    bindings = {binding[0]: binding for binding in program[1]}
    work = next(
        function
        for function in program[2]
        if function[0] == "function" and function[1].endswith("4h776f726b")
    )
    operations = []

    def visit(value, depth=0):
        if not isinstance(value, list) or not value:
            return
        if value[0] == "op":
            operations.append((bindings[value[2]], value, depth))
        if value[0] == "for":
            depth += 1
        for item in value:
            if isinstance(item, list):
                visit(item, depth)

    visit(work[4])
    return operations


def work_operations(entry):
    return [(binding[1], depth) for binding, _, depth in work_instructions(entry)]


@pytest.mark.parametrize(
    "body",
    [
        "finite::fold(xs,seed,fn(s,x)=>s+x*x)",
        "finite::fold(xs,seed,fn(s,x)=>x*x+s)",
        "finite::fold(zkc::vector::indices(xs),seed,fn(s,i)=>s+zkc::vector::get(xs,i)*zkc::vector::get(xs,i))",
        "finite::fold(xs,seed,fn(s,x)=>s+square(x))",
    ],
)
@pytest.mark.parametrize("flags", [[], ["--no-simplify"]])
def test_equivalent_reductions_use_bulk(toolchain, journal, directory, body, flags):
    source = (
        HEADER
        + f"""
math fn square(x:F)->F {{ return x*x; }}
fn work(xs:Vector<F>,seed:F)->F {{ return {body}; }}
protocol Run roles(P)(xs:Vector<F>@P,seed:F@P)->(result:F@P) {{
  return work(xs,seed);
}}
entry fn Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
"""
    )
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    operations = work_operations(entry)
    assert operations.count(("vector.dot", 0)) == 1
    assert not any(depth for _, depth in operations)
    for name, xs in [("empty", []), ("ordinary", [2, 3, 7])]:
        assert entry.run(name, {"xs": [str(x) for x in xs], "seed": "11"})[
            "result"
        ] == str(11 + sum(x * x for x in xs))


@pytest.mark.parametrize("style", ["map", "collect"])
def test_numerical_expression_shares_scalar_work(toolchain, journal, directory, style):
    expression = "(x+(a*a))*(x+(a*a))"
    body = (
        "map shifted(each xs,a)"
        if style == "map"
        else f"zkc::vector::collect(xs,fn(x)=>{expression})"
    )
    source = (
        HEADER
        + f"""
math fn shifted(x:F,a:F)->F {{ return {expression}; }}
fn work(xs:Vector<F>,a:F)->Vector<F> {{ return {body}; }}
protocol Run roles(P)(xs:Vector<F>@P,a:F@P)->(result:Vector<F>@P) {{
  return work(xs,a);
}}
entry fn Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
"""
    )
    entry = Entry(toolchain, journal, directory, source, MODULES)
    operations = work_operations(entry)
    assert operations.count(("numerical.map", 0)) == 1
    assert not any(contract in ("field.mul", "vector.fill", "vector.add")
                   for contract, _ in operations)
    binding, instruction, _ = next(
        site for site in work_instructions(entry) if site[0][1] == "numerical.map"
    )
    assert binding[2] == ["koala-bear", "10"]  # Column x and scalar a.
    _, _, nodes, outputs = json.loads(instruction[3][0])
    # Both authored copies of a*a and x+a*a have one shared DAG node.
    assert sum(node[0] == "mul" for node in nodes) == 2
    assert sum(node[0] == "add" for node in nodes) == 1
    result = nodes[outputs[0]]
    assert result[0] == "mul" and result[1] == result[2]
    assert nodes[result[1]][0] == "add"
    assert entry.run("values", {"xs": ["2", "3"], "a": "5"})["result"] == ["729", "784"]
    assert entry.run("empty", {"xs": [], "a": "5"})["result"] == []


@pytest.mark.parametrize("orientation", ["row", "column"])
@pytest.mark.parametrize("bulk", [True, False])
def test_nested_contraction_keeps_empty_admission(
    toolchain, journal, directory, orientation, bulk
):
    source = (
        HEADER
        + f"""
fn work(m:Matrix<F>,xs:Vector<F>,seed:F)->Vector<F> {{
  return zkc::vector::collect(zkc::matrix::{orientation}_indices(m),fn(i)=>
    finite::fold(domains::zip(zkc::matrix::{orientation}_values(m,i),xs),seed,
                 fn(s,(a,b))=>s+a*b));
}}
protocol Run roles(P)(m:Matrix<F>@P,xs:Vector<F>@P,seed:F@P)
  ->(result:Vector<F>@P) {{ return work(m,xs,seed); }}
entry fn Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
"""
    )
    flags = [] if bulk else ["--no-finite-bulk"]
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    if bulk:
        operations = work_operations(entry)
        contract = (
            "matrix.mul_vector"
            if orientation == "row"
            else "matrix.transpose_mul_vector"
        )
        assert operations.count((contract, 0)) == 1
        assert not any(depth for _, depth in operations)
    row = orientation == "row"

    def matrix(outer, inner, entries=()):
        return {
            "rows": str(outer if row else inner),
            "columns": str(inner if row else outer),
            "entries": [
                [str(r if row else c), str(c if row else r), str(v)]
                for r, c, v in sorted(
                    entries, key=lambda e: (e[0], e[1]) if row else (e[1], e[0])
                )
            ],
        }

    assert entry.run(
        "sparse",
        {"m": matrix(3, 2, [(0, 0, 3), (2, 1, 7)]), "xs": ["5", "11"], "seed": "13"},
    )["result"] == ["28", "13", "90"]
    assert (
        entry.run("empty-inner", {"m": matrix(3, 0), "xs": [], "seed": "13"})["result"]
        == ["13"] * 3
    )
    # The vector is deliberately incompatible. No inner fold runs.
    assert (
        entry.run("empty-outer", {"m": matrix(0, 2), "xs": ["7"], "seed": "13"})[
            "result"
        ]
        == []
    )
    refused = entry.run(
        "mismatch",
        {"m": matrix(2, 2), "xs": ["7"], "seed": "13"},
        refuses="entry-host-run-failed",
    )
    assert "rejected:require" in json.dumps(refused)
