"""Nested indexed Math helpers in table claims and AIR denominator arithmetic.

Count executable operation sites independently of checking values. References
use integer arithmetic, including polynomial reduction for the extension field.
These are arithmetic components, not complete Sumcheck, PCS or AIR proofs.
"""

import random

import pytest

from input_files import decimal_values
from octic_reference import P, add as extension_add, mul as extension_mul
from source_modules import library_modules
from test_compositional_protocol_math import ProjectEntry, project_modules, published_inputs
from test_total_callback_selection import compile_entry

FLAGS = [(), ('--no-simplify',), ('--no-finite-bulk',),
         ('--no-simplify', '--no-finite-bulk')]
MODES = ['default', 'no-simplify', 'no-finite-bulk', 'both']
FIELDS = ['koala-bear', 'koala-bear.ext8-binomial3']
CONSUMERS = [
    ('table-inner-product', 'table_claims', 'Claims'),
    ('lookup-denominators', 'lookup_denominators', 'Products'),
]


class ReferenceField:
    def __init__(self, field):
        self.extension = field.endswith('ext8-binomial3')

    def value(self, constant, high=0):
        # High coordinates exercise X^8 = 3, rather than only embedded scalars.
        return ([constant % P, high, 0, 0, 0, 0, 0, high] if self.extension
                else constant % P)

    def add(self, left, right):
        return extension_add(left, right) if self.extension else (left + right) % P

    def subtract(self, left, right):
        return ([(x - y) % P for x, y in zip(left, right, strict=True)]
                if self.extension else (left - right) % P)

    def multiply(self, left, right):
        return extension_mul(left, right) if self.extension else left * right % P

    def random(self, rng):
        return [rng.randrange(P) for _ in range(8)] if self.extension else rng.randrange(P)


def table_reference(field, inputs):
    square = weighted = inputs['initial']
    for value in inputs['values']:
        weight = field.add(field.multiply(inputs['factor'], value), inputs['offset'])
        square = field.add(square, field.multiply(value, value))
        weighted = field.add(weighted, field.multiply(value, weight))
    return {'square_claim': square, 'weighted_claim': weighted}


def denominator_reference(field, inputs):
    result = {}
    for output, shift in [('product', 'gamma'), ('other_product', 'other_gamma')]:
        product = inputs['initial']
        for value in inputs['fingerprints']:
            denominator = field.add(
                field.multiply(inputs['gate'], field.subtract(inputs[shift], value)),
                field.subtract(field.value(1), inputs['gate']))
            product = field.multiply(product, denominator)
        result[output] = product
    return result


def compile_consumer(toolchain, journal, directory, flags, field, consumer):
    project, module, protocol = consumer
    # Import the maintained source unchanged, with the manifest's module closure.
    source = f'''module sample;
use {module}::{{{protocol}}};
domain F = field("{field}");
run Demo = {protocol}<F>;
'''
    return compile_entry(toolchain, journal, directory, source, flags,
                         modules=project_modules(project))


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
@pytest.mark.parametrize('field', FIELDS)
def test_table_claims_select_indexed_dot_and_keep_distinct_values(
        toolchain, journal, directory, flags, field):
    entry, sites = compile_consumer(toolchain, journal, directory, flags, field, CONSUMERS[0])
    bulk = '--no-finite-bulk' not in flags
    assert bool(sites['vector.dot']) == bulk, sites
    # The weighted collect reads the exact container named by its index domain.
    assert bool(sites['vector.scale']) == bulk, sites
    arithmetic = ReferenceField(field)
    zero, one = arithmetic.value(0), arithmetic.value(1)
    values = [arithmetic.value(2, 1), arithmetic.value(3, 2), arithmetic.value(5, 3)]
    seed, factor, offset = (arithmetic.value(7, 4), arithmetic.value(11, 5),
                            arithmetic.value(13, 6))
    base = {'values': values, 'factor': factor, 'offset': offset, 'initial': zero}
    rng = random.Random(17391)
    cases = [
        ('empty', base | {'values': []}),
        ('empty-seeded', base | {'values': [], 'initial': seed}),
        ('different-values', base),
        ('seeded', base | {'initial': seed}),
        ('zero-entry', base | {'values': [values[0], zero, values[2]], 'initial': seed}),
        ('all-zero', base | {'values': [zero] * 3, 'initial': seed}),
        ('zero-weight', base | {'factor': zero, 'offset': zero, 'initial': seed}),
        ('equal-captures', base | {'offset': factor}),
        ('swapped-captures', base | {'factor': offset, 'offset': factor}),
        ('same-values', base | {'factor': one, 'offset': zero}),
        ('singleton', base | {'values': [values[0]]}),
        ('repeated-rows', base | {'values': [values[1]] * 64, 'initial': seed}),
        ('random', {'values': [arithmetic.random(rng) for _ in range(7)],
                    'factor': arithmetic.random(rng), 'offset': arithmetic.random(rng),
                    'initial': arithmetic.random(rng)}),
    ]
    for label, inputs in cases:
        assert entry.run(label, inputs) == decimal_values(table_reference(arithmetic, inputs))


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
@pytest.mark.parametrize('field', FIELDS)
def test_lookup_products_select_nested_indexed_lanes_and_reduction(
        toolchain, journal, directory, flags, field):
    entry, sites = compile_consumer(toolchain, journal, directory, flags, field, CONSUMERS[1])
    bulk = '--no-finite-bulk' not in flags
    assert bool(sites['vector.product']) == bulk, sites
    # Product selection alone would miss a fallback in denominator_at's collect.
    assert bool(sites['vector.scale']) == bulk, sites
    arithmetic = ReferenceField(field)
    zero, one = arithmetic.value(0), arithmetic.value(1)
    values = [arithmetic.value(2, 1), arithmetic.value(3, 2), arithmetic.value(5, 3)]
    seed = arithmetic.value(7, 4)
    gamma, other_gamma = arithmetic.value(11, 5), arithmetic.value(13, 6)
    base = {'fingerprints': values, 'gamma': gamma, 'other_gamma': other_gamma,
            'gate': one, 'initial': one}
    rng = random.Random(25307)
    cases = [
        ('empty', base | {'fingerprints': []}),
        ('empty-seeded', base | {'fingerprints': [], 'initial': seed}),
        ('different-shifts', base),
        ('seeded', base | {'initial': seed}),
        ('zero-seed', base | {'initial': zero}),
        ('zero-entry', base | {'fingerprints': [values[0], zero, values[2]]}),
        ('active-zero', base | {'fingerprints': [values[0], gamma, values[2]]}),
        ('inactive-zero', base | {'fingerprints': [gamma, other_gamma],
                                  'gate': zero, 'initial': seed}),
        ('inactive', base | {'gate': zero, 'initial': seed}),
        ('equal-shifts', base | {'other_gamma': gamma}),
        ('swapped-shifts', base | {'gamma': other_gamma, 'other_gamma': gamma}),
        ('singleton', base | {'fingerprints': [values[0]]}),
        ('repeated-rows', base | {'fingerprints': [values[1]] * 64, 'initial': seed}),
        # The component evaluates a polynomial; it does not enforce Booleanity.
        ('nonboolean-gate', base | {'gate': arithmetic.value(2, 1)}),
        ('random', {'fingerprints': [arithmetic.random(rng) for _ in range(7)],
                    'gamma': arithmetic.random(rng), 'other_gamma': arithmetic.random(rng),
                    'gate': one, 'initial': arithmetic.random(rng)}),
    ]
    for label, inputs in cases:
        assert entry.run(label, inputs) == decimal_values(
            denominator_reference(arithmetic, inputs))


def integer_inputs(value):
    if isinstance(value, dict):
        return {key: integer_inputs(item) for key, item in value.items()}
    if isinstance(value, list):
        return [integer_inputs(item) for item in value]
    return int(value)


@pytest.mark.parametrize('consumer', CONSUMERS, ids=['table', 'lookup'])
@pytest.mark.parametrize('field', FIELDS)
def test_published_indexed_arithmetic_projects(toolchain, journal, directory, consumer, field):
    project, module, _ = consumer
    entry_name = 'ExtensionDemo' if field.endswith('ext8-binomial3') else 'Demo'
    selector = f'{module}::{entry_name}'
    entry = ProjectEntry(toolchain, journal, directory, project, selector, ())
    inputs = integer_inputs(published_inputs(project, selector))
    reference = table_reference if project == 'table-inner-product' else denominator_reference
    assert entry.run('published', inputs) == decimal_values(reference(ReferenceField(field), inputs))


INVALID_PREMISES = [
    '''math fn read_other(left: vec::Vector<F>, right: vec::Vector<F>, i: index)
    -> F where in_bounds(i, left) {
  return vec::at(right, i);
}
''',
    '''math fn selected(values: vec::Vector<F>, i: index, other: index) -> F
    where in_bounds(i, values) {
  return vec::at(values, other);
}
''',
    '''math fn claim(left: vec::Vector<F>, right: vec::Vector<F>) -> F
    where equal_extent(left, right) {
  return total::fold(vec::indices(left), 0,
    fn(state, i) => state + vec::at(left, i) * vec::at(right, i));
}
protocol Invalid roles(P)(left: vec::Vector<F> @P, right: vec::Vector<F> @P)
    -> (value: F @P) {
  require vec::length(left) == vec::length(right);
  return claim(left, right);
}
run Demo = Invalid;
''',
]


@pytest.mark.parametrize('field', FIELDS)
@pytest.mark.parametrize('body', INVALID_PREMISES,
                         ids=['wrong-container', 'wrong-index', 'runtime-extent-check'])
def test_indexed_helpers_require_source_premises(toolchain, journal, directory, field, body):
    source = directory / 'invalid.zkc'
    source.write_text(f'''module sample;
use zkc::vector as vec;
use zkc::finite_math as total;
domain F = field("{field}");
''' + body)
    journal.run([toolchain.compiler, 'language-check', '--source-format=zkc',
                 f'--module=sample={source}', *library_modules('zkc')], refuses='source.data-bound')
