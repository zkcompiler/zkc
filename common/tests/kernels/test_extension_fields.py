"""Registered field kernels through a .zkc Entry, with an integer oracle.

The reference is integer convolution modulo each registered binomial. Neither
compiler operations nor the backend's extension implementation compute expected
values.
"""

import random

import pytest

from binomial_reference import PLONKY3_FIELDS as FIELDS
from entry import Entry

SOURCE = """module sample;
domain E = field("{field}");
type Vector<F:Field> = builtin("vector", F);
type Matrix<F:Field> = builtin("matrix", F);
fn work(a:E, b:E, xs:Vector<E>, m:Matrix<E>) -> (E,E,Vector<E>,E,Vector<E>,Vector<E>,E) {{
  let product = a * b;
  let inverse = kernel<E>("field.inverse", a);
  let scaled = kernel<E>("vector.scale", xs, b);
  let dot = kernel<E>("vector.dot", xs, scaled);
  let mv = kernel<E>("matrix.mul_vector", m, xs);
  let tmv = kernel<E>("matrix.transpose_mul_vector", m, xs);
  let bilinear = kernel<E>("matrix.bilinear", m, xs, xs);
  return (product, inverse, scaled, dot, mv, tmv, bilinear);
}}
protocol Run roles(P)(a:E@P, b:E@P, xs:Vector<E>@P, m:Matrix<E>@P)
  -> (result:(E,E,Vector<E>,E,Vector<E>,Vector<E>,E)@P) {{
  let result @P = work(a,b,xs,m);
  return (result=result);
}}
entry fn Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
"""


def wire(kind, value):
    if kind == "field":
        return str(value[0]) if len(value) == 1 else [str(x) for x in value]
    if kind == "vector":
        return [wire("field", x) for x in value]
    return {
        "rows": "2",
        "columns": "2",
        "entries": [[str(r), str(c), wire("field", a)] for r, c, a in value],
    }


@pytest.mark.parametrize(
    "field",
    [
        "koala-bear.ext8-binomial3",
        "koala-bear.ext4-binomial3",
        "baby-bear",
        "baby-bear.ext4-binomial11",
        "goldilocks",
        "goldilocks.ext2-binomial7",
    ],
)
@pytest.mark.parametrize("flags", [[], ["--no-simplify"], ["--release-storage"]])
def test_field_kernel_results_and_zero_inverse(
    toolchain, journal, directory, field, flags
):
    ext = FIELDS[field]
    p = ext.modulus
    d, ZERO, add, mul, power = ext.degree, ext.ZERO, ext.add, ext.mul, ext.power
    X = [7] if d == 1 else [0, 1] + [0] * (d - 2)
    TOP = [0] * (d - 1) + [1]
    entry = Entry(toolchain, journal, directory, SOURCE.format(field=field), flags)
    rng = random.Random(917 + d)

    def value():
        return [rng.randrange(p) for _ in range(d)]

    # Extension basis products wrap; the same source helper also exercises bases.
    cases = [("wrap", X, TOP, [X, TOP], [[0, 1, TOP], [1, 0, X]])]
    if p == 18446744069414584321:
        a = [2**63 + 13 + j for j in range(d)]
        b = [p - 1 - 7 * j for j in range(d)]
        cases.append(("wide", a, b, [a, b], [[0, 1, a], [1, 0, b], [1, 1, a]]))
    for i in range(4):
        cases.append(
            (
                f"random{i}",
                value(),
                value(),
                [value(), value()],
                [[r, c, value()] for r in range(2) for c in range(2)],
            )
        )
    for name, a, b, xs, matrix in cases:
        inputs = {
            "a": wire("field", a),
            "b": wire("field", b),
            "xs": wire("vector", xs),
            "m": wire("matrix", matrix),
        }
        actual = entry.run(name, inputs)["result"]
        scaled = [mul(x, b) for x in xs]
        dot = add(mul(xs[0], scaled[0]), mul(xs[1], scaled[1]))
        mv, tmv = [ZERO[:], ZERO[:]], [ZERO[:], ZERO[:]]
        for r, c, coefficient in matrix:
            mv[r] = add(mv[r], mul(coefficient, xs[c]))
            tmv[c] = add(tmv[c], mul(coefficient, xs[r]))
        expected = [
            ("field", mul(a, b)),
            ("field", power(a, p**d - 2)),
            ("vector", scaled),
            ("field", dot),
            ("vector", mv),
            ("vector", tmv),
            ("field", add(mul(xs[0], mv[0]), mul(xs[1], mv[1]))),
        ]
        assert actual == [wire(kind, result) for kind, result in expected]
    inputs["a"] = wire("field", ZERO)
    report = entry.run("zero-inverse", inputs, refuses="entry-host-run-failed")
    assert "zero-inverse" in str(report)
    # Malformed noncanonical coordinates are refused before values reach a kernel.
    inputs["a"] = wire("field", [p] + [0] * (d - 1))
    entry.run("noncanonical-field", inputs, refuses=True)
