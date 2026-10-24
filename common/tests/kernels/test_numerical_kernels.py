"""Direct small-coset calculations test native numerical kernels through Entry.

Coefficient sums and folded coefficients are evaluated directly, independently
of the native DFT and inverse DFT. Extension arithmetic is integer convolution.
"""

import random

import pytest

from binomial_reference import PLONKY3_FIELDS as FIELDS, P
from entry import Entry


def wire(kind, value, extension):
    def scalar(v):
        return [str(x) for x in v] if extension else str(v[0])
    return scalar(value) if kind == 'field' else [scalar(v) for v in value]


def direct(ext, coefficients, point):
    result, power = ext.ZERO, ext.ONE
    for coefficient in coefficients:
        result = ext.add(result, ext.mul(coefficient, power))
        power = ext.mul(power, point)
    return result


@pytest.mark.parametrize('field', ['koala-bear', 'koala-bear.ext8-binomial3',
                                   'koala-bear.ext4-binomial3', 'baby-bear',
                                   'baby-bear.ext4-binomial11', 'goldilocks',
                                   'goldilocks.ext2-binomial7'])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_coset_evaluation_interpolation_fold_and_refusals(toolchain, journal, directory, field, flags):
    ext = FIELDS[field]
    extension = ext.degree > 1
    p = ext.modulus
    d, ZERO, ONE, add, mul = ext.degree, ext.ZERO, ext.ONE, ext.add, ext.mul
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
entry fn Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    rng = random.Random(619 + d)

    def scalar():
        return [rng.randrange(p) for _ in range(d)] if extension else ext.embed(rng.randrange(p))

    for n in (2, 4, 8, 16, 32, 64):
        cs = [scalar() for _ in range(n // 2)]
        shift, beta = scalar(), scalar()
        # Independent Plonky3 0.8.0 base-root facts; extensions deliberately
        # use the base subgroup even when every shift coordinate is nonzero.
        maximal_root, log = {'koala-bear': (1791270792, 24),
                             'baby-bear': (440564289, 27),
                             'goldilocks': (1753635133440165772, 32)}[field.split('.')[0]]
        root = pow(maximal_root, (1 << log) // n, p)
        assert pow(root, n, p) == 1 and pow(root, n // 2, p) == p - 1
        points = [mul(shift, ext.embed(pow(root, i, p))) for i in range(n)]
        values = [direct(ext, cs, point) for point in points]
        folded_cs = [add(cs[i], mul(beta, cs[i + 1] if i + 1 < len(cs) else ZERO))
                     for i in range(0, len(cs), 2)]
        folded = [direct(ext, folded_cs, mul(point, point)) for point in points[:n // 2]]
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
        entry.run(name, inputs | {port: value}, refuses='entry-host-run-failed')


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
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source)
    for query in (0, P + 1, 2**64 - 1):
        outputs = entry.run_roles(str(query), {'P': {'q': query}, 'V': {}})
        expected = [str(query)] * 2
        assert outputs == {'P': {}, 'V': {'result': expected, 'count': '2'}}
