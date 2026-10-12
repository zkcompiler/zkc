"""Total callback selection, original value semantics, and ordered controls."""

from collections import Counter
import json

import pytest

from entry import Entry
from input_files import decimal_values
from octic_reference import ONE, P, ZERO, add, mul
from source_modules import finite_modules

FLAGS = [(), ('--no-simplify',), ('--no-finite-bulk',),
         ('--no-simplify', '--no-finite-bulk')]
MODES = ['default', 'no-simplify', 'ordered', 'ordered-no-simplify']
PREFIX = '''module sample;
use zkc::vector as vec;
use zkc::finite_math as total;
use zkc::finite_domain as domains;
domain F = field("FIELD");
math fn multiply(a:F,b:F)->F { return a*b; }
math fn wrapped(a:F,b:F)->F { return multiply(a,b); }
// These helpers infer Copy(T) and Drop(T), respectively. The callback must
// retain their exact result values through specialization and preparation.
math fn duplicate<T:Type>(value:T)->(T,T) { return (value,value); }
math fn first<T:Type>(pair:(T,T))->T { return pair.0; }
'''
FOLD = '''
protocol Inspect roles(P)(values:vec::Vector<F>@P, initial:F@P)->(value:F@P) {
  return total::fold(vec::elements(values), initial, fn(p,x)=>CALLBACK);
}
run Demo = Inspect;
'''


def compile_entry(toolchain, journal, directory, source, flags, modules=()):
    options = [*finite_modules(), *modules, *flags]
    entry = Entry(toolchain, journal, directory, source, options)
    bundle = journal.json([
        toolchain.compiler, 'language-bundle', '--source-format=zkc',
        '--entry=sample::Demo', f'--module=sample={directory}/kernels.zkc',
        *options,
    ])
    program = json.loads(bundle['candidate'])
    bindings = {binding[0]: binding[1] for binding in program[1]}
    sites = Counter()

    def visit(node):
        if isinstance(node, list):
            if node and node[0] == 'op':
                sites[bindings[node[2]]] += 1
            for child in node:
                visit(child)

    # Count actual executable sites, not declarations or raw text mentions.
    visit(program[2])
    visit(program[3])
    return entry, sites


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
@pytest.mark.parametrize('field', ['koala-bear', 'koala-bear.ext8-binomial3'])
@pytest.mark.parametrize('callback,contract', [
    ('p*x', 'vector.product'), ('p+x', 'vector.sum'),
    ('wrapped(p,x)', 'vector.product'),
    ('multiply(first(duplicate(p)),x)', 'vector.product'),
], ids=['product', 'sum', 'wrapped-product', 'inferred-usage-product'])
def test_total_fold_selects_actual_bulk_sites(
        toolchain, journal, directory, flags, field, callback, contract):
    source = (PREFIX + FOLD).replace('FIELD', field).replace('CALLBACK', callback)
    entry, sites = compile_entry(toolchain, journal, directory, source, flags)
    assert bool(sites[contract]) == ('--no-finite-bulk' not in flags)
    extension = field.endswith('ext8-binomial3')
    if extension:
        values = [[2, 1, 0, 0, 0, 0, 0, 0],
                  [3, 0, 0, 0, 0, 0, 0, 1], [5, 2, 0, 0, 0, 0, 0, 0]]
        zero, one, seed = ZERO, ONE, [7, 3, 0, 0, 0, 0, 0, 0]
        combine = mul if contract == 'vector.product' else add
    else:
        values, zero, one, seed = [2, 3, 5], 0, 1, 7
        combine = ((lambda a, b: a*b % P) if contract == 'vector.product'
                   else (lambda a, b: (a+b) % P))
    identity = one if contract == 'vector.product' else zero
    for label, items, initial in [
        ('empty', [], identity), ('values', values, identity),
        ('zero-factor', [values[0], zero, values[2]], identity),
        ('seeded', values, seed), ('empty-seeded', [], seed),
        ('zero-seed', values, zero), ('sixty-four', [values[0]] * 64, seed),
    ]:
        expected = initial
        for value in items:
            expected = combine(expected, value)
        assert entry.run(label, {'values': items, 'initial': initial}) == {
            'value': decimal_values(expected)}


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
@pytest.mark.parametrize('repeated_capture', [False, True], ids=['distinct', 'same-binding'])
def test_wrapped_collection_keeps_capture_positions(
        toolchain, journal, directory, flags, repeated_capture):
    source = PREFIX + '''
math fn collect<I:Type+Copy+Drop>(rows:domain<I>,
  body:math fn(item:I)->F where item_from(item,rows))->vec::Vector<F>
  = finite("math.collect.vector");
math fn affine(x:F,factor:F,offset:F)->F { return wrapped(x,factor)+offset; }
protocol Inspect roles(P)(values:vec::Vector<F>@P, factor:F@P, offset:F@P)
    ->(value:vec::Vector<F>@P) {
  return collect(vec::elements(values), fn(x)=>affine(x,factor,offset));
}
run Demo = Inspect;
'''
    if repeated_capture:
        source = source.replace('affine(x,factor,offset)', 'affine(x,factor,factor)')
    entry, sites = compile_entry(toolchain, journal, directory,
                                 source.replace('FIELD', 'koala-bear'), flags)
    assert bool(sites['vector.scale']) == ('--no-finite-bulk' not in flags)
    for label, values, factor, offset in [
        ('empty', [], 7, 11), ('different', [2, 3, 5], 7, 11),
        ('equal-values', [2, 3, 5], 7, 7), ('zero-factor', [2, 3, 5], 0, 11),
    ]:
        assert entry.run(label, {'values': values, 'factor': factor,
                                 'offset': offset}) == {
            'value': decimal_values([
                (x*factor+(factor if repeated_capture else offset)) % P for x in values])}


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
def test_nonassociative_and_predicated_callbacks_remain_ordered(
        toolchain, journal, directory, flags):
    source = PREFIX + '''
protocol Inspect roles(P)(values:vec::Vector<F>@P, initial:F@P, enabled:bool@P)
    ->(square:F@P, filtered:F@P) {
  let square @P = total::fold(vec::elements(values), initial,
    fn(p,x)=>wrapped(p,p)*x);
  let filtered @P = total::fold_where(vec::elements(values), initial,
    fn(x)=>enabled, fn(p,x)=>wrapped(p,x));
  return (square, filtered);
}
run Demo = Inspect;
'''
    entry, sites = compile_entry(toolchain, journal, directory,
                                 source.replace('FIELD', 'koala-bear'), flags)
    assert not sites['vector.product']
    for enabled in (False, True):
        for label, values in [('empty', []), ('values', [2, 3, 5])]:
            square = filtered = 7
            for value in values:
                square = square*square*value % P
                if enabled:
                    filtered = filtered*value % P
            assert entry.run(f'{label}-{enabled}', {
                'values': values, 'initial': 7, 'enabled': enabled,
            }) == decimal_values({'square': square, 'filtered': filtered})


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
def test_nested_callback_retains_conditional_domain_admission(
        toolchain, journal, directory, flags):
    source = PREFIX + '''
math fn nested(p:F,x:F,limit:index)->F {
  return total::fold(domains::range(0,limit), p, fn(s,i)=>s*x);
}
protocol Inspect roles(P)(values:vec::Vector<F>@P, initial:F@P, limit:index@P)
    ->(value:F@P) {
  return total::fold(vec::elements(values), initial, fn(p,x)=>nested(p,x,limit));
}
run Demo = Inspect;
'''
    entry, sites = compile_entry(toolchain, journal, directory,
                                 source.replace('FIELD', 'koala-bear'), flags)
    assert not sites['vector.product']
    assert entry.run('ordinary', {'values': [2, 3], 'initial': 7, 'limit': 2}) == {
        'value': '252'}
    assert entry.run('inner-empty', {'values': [2, 3], 'initial': 7, 'limit': 0}) == {
        'value': '7'}
    inputs = {'values': [], 'initial': 7, 'limit': str(2**64-1)}
    assert entry.run('outer-empty', inputs) == {'value': '7'}
    entry.run('inner-bound', inputs | {'values': [2]}, refuses='entry-run-incomplete')
