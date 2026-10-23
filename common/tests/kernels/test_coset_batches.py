"""Batched re-evaluation checked against direct integer polynomial arithmetic."""

import pytest

from binomial_reference import P
from coset_reference import FIELDS, CosetReference
from entry import Entry, joint_execution
from source_modules import library_modules


@pytest.mark.parametrize("field", FIELDS)
@pytest.mark.parametrize("flags", [[], ["--no-simplify"], ["--release-storage"]])
def test_coset_batches_preserve_columns_shifts_degree_checks_and_inputs(
    toolchain, journal, directory, field, flags
):
    reference = CosetReference(field)
    modulus, degree = reference.modulus, reference.degree

    def scalar(seed):
        high = 1 << 63 if field.startswith("goldilocks") else 0
        return tuple(
            (high + seed * seed + 7 * seed + 11 * i + 1) % modulus
            for i in range(degree)
        )

    zero, one = reference.zero, reference.one
    encode = reference.encode

    def word(coefficients, shift, size):
        return [
            reference.horner(coefficients, point)
            for point in reference.domain(shift, size)
        ]

    source = f'''module sample;
domain F=field("{field}");
type Vector<E:Field>=builtin("vector",E);
fn extend(xs:Vector<F>,width:index,height:index,input_shift:F,output_shift:F,size:index)
    ->(Vector<F>,Vector<F>) {{
  let result=kernel<F>("poly.coset_extend",xs,width,height,input_shift,output_shift,size);
  return(result,xs);
}}
protocol Work roles(P)(xs:Vector<F>@P,width:index@P,height:index@P,input_shift:F@P,
    output_shift:F@P,size:index@P)->(result:(Vector<F>,Vector<F>)@P) {{
  return extend(xs,width,height,input_shift,output_shift,size);
}}
entry fn Demo(inputs: Work::Inputs) {{ return Work::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    input_shift, output_shift = scalar(3), scalar(7)

    def refuse(name, data, cause):
        report = entry.run(name, data, refuses="entry-host-run-failed")
        assert joint_execution(report)["roles"][0]["after"][1]["cause"] == [
            "backend",
            {"omitted_bytes": 0, "text": cause},
        ]

    def inputs(columns, height, size):
        values = [encode(x) for cs in columns for x in word(cs, input_shift, height)]
        expected = [encode(x) for cs in columns for x in word(cs, output_shift, size)]
        return {
            "xs": values,
            "width": len(columns),
            "height": height,
            "input_shift": encode(input_shift),
            "output_shift": encode(output_shift),
            "size": size,
        }, expected

    # Independent roots, asymmetric coefficients and distinct shifts catch a
    # transpose, column permutation, or truncated extension-valued shift.
    for height, size, width in [(1, 4, 1), (4, 4, 3), (4, 8, 3), (8, 16, 2)]:
        columns = [
            [scalar(19 * column + i + 1) for i in range(height)]
            for column in range(width)
        ]
        data, expected = inputs(columns, height, size)
        assert entry.run(f"extend-{height}-{size}-{width}", data)["result"] == [
            expected,
            data["xs"],
        ]

    columns = [[], [scalar(11)], [scalar(13), scalar(17)]]
    data, expected = inputs(columns, 4, 2)
    assert entry.run("shrink-normalized", data)["result"] == [expected, data["xs"]]
    # First column succeeds; a later quadratic must prevent all publication.
    invalid = [columns[0], [zero, zero, one]]
    data, _ = inputs(invalid, 4, 4)
    refuse(
        "shrink-late-quadratic", data | {"size": 2}, "refused:coset-coefficient-count"
    )

    for name, changes, cause in [
        ("shape", {"width": 3}, "refused:coset-batch-shape"),
        ("input-size", {"height": 3, "xs": data["xs"][:6]}, "refused:coset-size"),
        ("output-size", {"size": 3}, "refused:coset-size"),
        ("zero-input-shift", {"input_shift": encode(zero)}, "refused:coset-zero-shift"),
        (
            "zero-output-shift",
            {"output_shift": encode(zero)},
            "refused:coset-zero-shift",
        ),
        ("extent-overflow", {"width": 2**64 - 1}, "exhausted:size-overflow"),
    ]:
        refuse(name, data | changes, cause)
    empty = {
        "xs": [],
        "width": 0,
        "height": 0,
        "size": 3,
        "input_shift": encode(zero),
        "output_shift": encode(zero),
    }
    assert entry.run("empty-unused-domains", empty)["result"] == [[], []]
    refuse("empty-shape", empty | {"xs": [encode(one)]}, "refused:coset-batch-shape")


@pytest.mark.parametrize("field", FIELDS)
@pytest.mark.parametrize("flags", [[], ["--no-simplify"], ["--release-storage"]])
def test_coset_interpolation_and_batch_point_evaluation(
    toolchain, journal, directory, field, flags
):
    f = CosetReference(field)
    high = 1 << 63 if field.startswith("goldilocks") else 0
    shift = tuple(high + 3 + j for j in range(f.degree))
    point = tuple(high + 17 + 2 * j for j in range(f.degree))
    coefficients = [
        tuple(high + 11 * i + 7 * j + 1 for j in range(f.degree)) for i in range(3)
    ]
    source = f'''module sample;
domain F=field("{field}");
type Vector<E:Field>=builtin("vector",E);
fn work(xs:Vector<F>,shift:F,point:F)->(Vector<F>,Vector<F>,Vector<F>) {{
  let first=kernel<F>("vector.slice",xs,0,4);
  let polynomial=kernel<F>("poly.coset_interpolate",first,shift);
  let coefficients=kernel<F>("poly.coefficients",polynomial);
  let points=kernel<F>("poly.coset_evaluate_at",xs,3,4,shift,point);
  return(coefficients,points,xs);
}}
protocol Work roles(P)(xs:Vector<F>@P,shift:F@P,point:F@P)
    ->(result:(Vector<F>,Vector<F>,Vector<F>)@P) {{ return work(xs,shift,point); }}
entry fn Demo(inputs:Work::Inputs) {{ return Work::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    domain = f.domain(shift, 4)
    columns = [
        coefficients,
        [f.one],
        [tuple(high + 31 * i + 13 * j + 2 for j in range(f.degree)) for i in range(4)],
    ]
    values = [f.horner(cs, x) for cs in columns for x in domain]
    # Recover coefficients from independent Horner samples, then evaluate the
    # same word at an off-domain point and at every node (including exact hits).
    for row, at in enumerate([point, *domain]):
        data = {
            "xs": list(map(f.encode, values)),
            "shift": f.encode(shift),
            "point": f.encode(at),
        }
        assert entry.run(f"interpolate-point-{row}", data)["result"] == [
            list(map(f.encode, coefficients)),
            [f.encode(f.horner(cs, at)) for cs in columns],
            data["xs"],
        ]
    # An arbitrary word uses generic Lagrange products, independently of the
    # native transform and the coset-specific direct evaluation formula.
    words = [
        [
            tuple(high + 29 * c + 19 * i + 5 * j + 2 for j in range(f.degree))
            for i in range(4)
        ]
        for c in range(3)
    ]
    data = {
        "xs": [f.encode(x) for word in words for x in word],
        "shift": f.encode(shift),
        "point": f.encode(point),
    }
    result = entry.run("arbitrary-word", data)["result"]
    assert result[1:] == [
        [f.encode(f.lagrange(word, domain, point)) for word in words],
        data["xs"],
    ]


def test_column_batch_library_retains_checked_domains_and_width(
    toolchain, journal, directory
):
    source = """module sample;
use zkc::coset as c;
use zkc::vector::{Vector};
domain F=field("koala-bear");
protocol Work roles(P)(xs:Vector<F>@P,width:index@P)->(data:Vector<F>@P,width:index@P,
    shift:F@P,size:index@P) {
  let input=c::column_batch(c::coset_domain<F>(1,2),width,xs);
  let output=c::extend_batch(input,c::coset_domain<F>(3,4));
  let geometry=c::batch_domain(output);
  return(data=c::batch_values(output),width=c::batch_width(output),
    shift=c::domain_shift(geometry),size=c::domain_size(geometry));
}
entry fn Demo(inputs: Work::Inputs) { return Work::run(inputs); }
"""
    entry = Entry(
        toolchain, journal, directory, source, library_modules("core/polynomial")
    )
    root = pow(1791270792, (1 << 24) // 4, P)
    # p=2+5X and q=7+11X, each given at +1,-1.
    data = [
        str(sum(c * pow(3 * pow(root, i, P), j, P) for j, c in enumerate(cs)) % P)
        for cs in ([2, 5], [7, 11])
        for i in range(4)
    ]
    assert entry.run(
        "two-columns", {"xs": ["7", str(P - 3), "18", str(P - 4)], "width": 2}
    ) == {"data": data, "width": "2", "shift": "3", "size": "4"}
    assert entry.run("zero-columns", {"xs": [], "width": 0}) == {
        "data": [],
        "width": "0",
        "shift": "3",
        "size": "4",
    }
    entry.run(
        "wrong-width",
        {"xs": ["7", str(P - 3)], "width": 2},
        refuses="entry-host-run-failed",
    )
