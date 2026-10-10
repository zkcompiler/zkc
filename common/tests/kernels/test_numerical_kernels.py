"""Direct small-coset calculations test native numerical kernels through Entry.

Coefficient sums and folded coefficients are evaluated directly, independently
of the native DFT and inverse DFT. Extension arithmetic is integer convolution.
"""

import random

import pytest

from entry import Entry
from octic_reference import P, ZERO, ONE, add, mul


def wire(kind, value, extension):
    def scalar(v):
        return [str(x) for x in v] if extension else str(v[0])
    return scalar(value) if kind == 'field' else [scalar(v) for v in value]


def direct(coefficients, point):
    result, power = ZERO, ONE
    for coefficient in coefficients:
        result = add(result, mul(coefficient, power))
        power = mul(power, point)
    return result


@pytest.mark.parametrize('extension', [False, True])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_coset_evaluation_interpolation_fold_and_refusals(toolchain, journal, directory, extension, flags):
    field = 'koala-bear' + ('.ext8-binomial3' if extension else '')
    source = f'''module sample;
domain F=field("{field}");
type Vector<E:Field>=builtin("vector",E);
fn work(cs:Vector<F>,shift:F,beta:F,n:index,query:index)
  ->(Vector<F>,Vector<F>,Vector<F>,F,index) {{
  let p=kernel<F>("poly.from_coefficients",cs);
  let values=kernel<F>("poly.coset_evaluate",p,shift,n);
  let back=kernel<F>("poly.coset_interpolate",values,shift);
  let coefficients=kernel<F>("poly.coefficients",back);
  let folded=kernel<F>("poly.even_odd_fold",values,shift,beta);
  let selected=kernel<F>("vector.get",values,query);
  let count=kernel<F>("poly.coefficient_count",back);
  return(values,coefficients,folded,selected,count);
}}
protocol Run roles(P)(cs:Vector<F>@P,shift:F@P,beta:F@P,n:index@P,query:index@P)
  ->(result:(Vector<F>,Vector<F>,Vector<F>,F,index)@P) {{
  let result @P =work(cs,shift,beta,n,query);
  return(result=result);
}}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    rng = random.Random(619)

    def scalar():
        return [rng.randrange(P) for _ in range(8)] if extension else [rng.randrange(P)] + [0] * 7

    for n in (2, 4, 8, 16, 32, 64):
        cs = [scalar() for _ in range(n // 2)]
        shift, beta = scalar(), scalar()
        # The public KoalaBear coset convention fixes this primitive 2^24 root.
        # Verify its order locally before using it; no backend data is queried.
        root = pow(1791270792, (1 << 24) // n, P)
        assert pow(root, n, P) == 1 and pow(root, n // 2, P) == P - 1
        points = [mul(shift, [pow(root, i, P)] + [0] * 7) for i in range(n)]
        values = [direct(cs, point) for point in points]
        folded_cs = [add(cs[i], mul(beta, cs[i + 1] if i + 1 < len(cs) else ZERO))
                     for i in range(0, len(cs), 2)]
        folded = [direct(folded_cs, mul(point, point)) for point in points[:n // 2]]
        inputs = {'cs': wire('vector', cs, extension), 'shift': wire('field', shift, extension),
                  'beta': wire('field', beta, extension), 'n': n, 'query': n - 1}
        assert entry.run(f'coset-{n}', inputs)['result'] == [wire('vector', values, extension),
            wire('vector', cs, extension), wire('vector', folded, extension),
            wire('field', values[-1], extension), str(len(cs))]

    inputs = {'cs': wire('vector', [ONE], extension), 'shift': wire('field', ONE, extension),
              'beta': wire('field', ONE, extension), 'n': 4, 'query': 0}
    for name, port, value in [('non-power', 'n', 3), ('zero-shift', 'shift', wire('field', ZERO, extension)),
                              ('out-of-range', 'query', 4), ('max-query', 'query', 2**64 - 1),
                              ('singleton', 'n', 1)]:
        entry.run(name, inputs | {port: value}, refuses='entry-run-incomplete')


def test_index_collection_transport_preserves_duplicates_above_field_characteristic(toolchain, journal, directory):
    source = '''module sample;
type Indices=builtin("indices");
fn twice(q:index)->Indices {
  let empty=kernel("indices.empty");
  let one=kernel("indices.append",empty,q);
  return kernel("indices.append",one,q);
}
fn size(xs:Indices)->index { return kernel("indices.length",xs); }
protocol Run roles(P,V)(q:index@P)->(result:Indices@V,count:index@V) {
  let collection @P =twice(q);
  let received=send P->V(collection);
  let count @V =size(received);
  return(result=received,count=count);
}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source)
    for query in (0, P + 1, 2**64 - 1):
        outputs = entry.run_roles(str(query), {'P': {'inputs': {'q': query}}, 'V': {'inputs': {}}})
        expected = [str(query)] * 2
        assert outputs == {'P': {}, 'V': {'result': expected, 'count': '2'}}
