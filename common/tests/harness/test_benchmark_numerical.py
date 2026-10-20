"""Bounded generator controls; these checks do not invoke compiled tools."""
from copy import deepcopy
from functools import reduce
import importlib
import importlib.util
import json
from pathlib import Path

import pytest

import binary_reference as binary
from binomial_reference import Binomial
from coset_reference import CosetReference


ROOT = Path(__file__).resolve().parents[3]
FIELDS = ('koala-bear', 'bls12-381.fr', 'koala-bear.ext4-binomial3',
          'koala-bear.ext8-binomial3', binary.BASE, binary.CUBIC)


@pytest.fixture
def bench(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT/'common/benchmarks'))
    return {name: importlib.import_module('bench.'+name)
            for name in ('algebra', 'coverage', 'expressions', 'operations', 'stark')}


def decode(value):
    return tuple(int(x, 0) for x in value) if isinstance(value, list) else (int(value, 0),)


@pytest.mark.parametrize('field', FIELDS)
def test_scalar_oracles_match_existing_references_in_every_coordinate(bench, field):
    a = bench['algebra']
    f = a.FieldOracle(field)
    xs, ys = f.dense(4, 281), f.dense(4, 282)
    for x, y in zip(xs, ys, strict=True):
        if field == binary.BASE:
            expected_add, expected_mul = (x[0] ^ y[0],), (binary.mul(x[0], y[0]),)
        elif field == binary.CUBIC:
            expected_add, expected_mul = tuple(binary.cubic_add(x, y)), tuple(binary.cubic_mul(x, y))
        elif f.degree > 1:
            ref = Binomial(f.degree)
            expected_add, expected_mul = tuple(ref.add(x, y)), tuple(ref.mul(x, y))
        else:
            expected_add = ((x[0]+y[0]) % f.modulus,)
            expected_mul = ((x[0]*y[0]) % f.modulus,)
        assert f.add(x, y) == expected_add
        assert f.mul(x, y) == expected_mul
        assert decode(f.encode(x)) == x
        assert f.sub(f.add(x, y), y) == x
        if f.degree > 1:
            assert all(x[1:]) and all(expected_mul[1:])
    if f.binary:
        assert f.support == (ROOT/'common/tests/support/binary_reference.py',)
        assert f.mul((2,) + (0,)*(f.degree-1), (1 << 63,) + (0,)*(f.degree-1))[0] == 0x1b
    elif f.degree > 1:
        x = (0, 1) + (0,)*(f.degree-2)
        assert f.power(x, f.degree) == (3,) + (0,)*(f.degree-1)


def source_order_result(name, f, row, c):
    """Evaluate the small authored formulas in their source order.

    Production expectations expand Horner/shared products differently. This is
    a finite list of test calculations, with no parser or source interpreter.
    """
    add, mul = f.add, f.mul
    x = row[0]
    if name == 'short-horner':
        return add(mul(add(mul(add(x, c[0]), x), c[1]), x), c[2])
    if name == 'deep-horner':
        value = x
        for i in range(12):
            value = add(mul(value, x), c[i % 2])
        return value
    if name == 'wide-independent':
        x, y, z, w = row
        return add(mul(add(mul(x, x), c[0]), add(mul(y, y), c[1])),
                   mul(add(mul(z, z), c[2]), add(mul(w, w), c[3])))
    if name == 'shared-subexpression':
        x, y = row
        t = add(mul(x, y), c[0])
        u = add(mul(t, t), c[1])
        return add(add(mul(u, t), mul(u, x)), mul(t, y))
    if name == 'capture-heavy':
        high = add(mul(c[0], c[1]), mul(c[2], c[3]))
        low = add(mul(c[4], c[5]), mul(c[6], c[7]))
        return add(add(mul(add(mul(high, x), low), x), c[0]), c[7])
    if name == 'input-heavy':
        return reduce(add, [mul(row[0], row[1]), mul(row[2], row[3]), mul(row[4], row[5]),
                            mul(row[6], row[7]), mul(row[0], row[7])], f.zero)
    if name == 'difference-products':
        u, t = f.sub(row[0], row[1]), add(row[0], row[1])
        return add(mul(add(mul(u, u), c[0]), add(mul(t, t), c[1])), mul(u, t))
    assert name == 'alternating-powers'
    x, y = row
    xx, yy = mul(x, x), mul(y, y)
    return add(mul(add(mul(xx, x), c[0]), add(mul(yy, y), c[0])), mul(add(xx, yy), add(x, y)))


@pytest.mark.parametrize('field', FIELDS)
@pytest.mark.parametrize('size', (0, 1, 3))
def test_authored_expressions_check_complete_values_and_typed_incorrect_controls(bench, field, size):
    module = bench['expressions']
    f = bench['algebra'].FieldOracle(field)
    for name, definition in module.EXPRESSIONS.items():
        for sink in ('map', 'sum', 'product'):
            program = module.expression({'field': field, 'elements': size, 'expression': name, 'sink': sink})
            inputs = program.inputs[0]['P']
            columns = [[decode(value) for value in inputs[column+'s']] for column in definition.columns]
            captures = [decode(inputs[c]) for c in definition.captures]
            rows = [source_order_result(name, f, row, captures) for row in zip(*columns, strict=True)]
            expected = rows if sink == 'map' else reduce(f.add if sink == 'sum' else f.mul, rows,
                                                        f.zero if sink == 'sum' else f.one)
            encoded = list(map(f.encode, expected)) if sink == 'map' else f.encode(expected)
            assert inputs['expected'] == encoded, (field, name, sink)
            wrong = program.incorrect['P']
            assert wrong['expected'] != encoded
            assert {k: v for k, v in wrong.items() if k != 'expected'} == {k: v for k, v in inputs.items() if k != 'expected'}
            values = wrong['expected'] if sink == 'map' else [wrong['expected']]
            assert all(len(decode(value)) == f.degree for value in values)
            assert all(0 <= coordinate < f.modulus for value in values for coordinate in decode(value))
            assert 'math fn term(' in program.source
            assert 'map term(each ' in program.source
            assert 'total::' not in program.source
            if field in (binary.BASE, binary.CUBIC):
                assert program.support == (ROOT/'common/tests/support/binary_reference.py',)
            if f.degree > 1 and size:
                assert all(all(value[1:]) for column in columns for value in column)
                assert all(all(c[1:]) for c in captures)


def test_fixed_panel_covers_tails_and_keeps_two_shapes_held_out(bench):
    cases = [c for c in bench['coverage'].cases() if c.name == 'expression']
    assert len(cases) == 50
    assert {c.shape['field'] for c in cases} == set(FIELDS)
    assert {0, 1, 31, 32, 33, 127, 128, 129, 1024, 4096} <= {c.shape['elements'] for c in cases}
    held_out = {'difference-products', 'alternating-powers'}
    assert {c.shape['expression'] for c in cases if c.shape['role'] == 'validation-only'} == held_out
    assert not any(c.shape['expression'] in held_out and c.shape['role'] == 'design' for c in cases)
    assert bench['coverage'].SMOKE == ('finite-kb-reduce-17', 'finite-kb-collect-17', 'finite-fr-bulk-17',
        'scan-scalar-17', 'scan-bulk-17', 'control-7x13', 'polynomial-ext1-32', 'polynomial-ext8-32',
        'extension-17', 'curve-1', 'pairing-2', 'transcript-4x1', 'fri-n64-d16-q8', 'air-h8-w1-b4')


def test_binary_oracle_uses_and_declares_the_selected_source_tree(bench, tmp_path):
    reference = tmp_path/'common/tests/support/binary_reference.py'
    reference.parent.mkdir(parents=True)
    reference.write_bytes((ROOT/'common/tests/support/binary_reference.py').read_bytes())
    for family in ('expression', 'field_vector'):
        case = next(c for c in bench['coverage'].cases()
                    if c.name == family and c.shape['field'] == binary.BASE)
        program = case.generate(tmp_path, tmp_path/'generated')
        assert program.support == (reference,)
        assert program.inputs == case.generate(ROOT, ROOT/'unused').inputs
    assert Path(bench['algebra'].binary_reference(reference).__file__) == reference


def test_unknown_generators_refuse_instead_of_selecting_another_operation(bench):
    with pytest.raises(ValueError, match='unknown expression sink'):
        bench['expressions'].expression({'expression': 'short-horner', 'field': 'koala-bear',
                                         'elements': 1, 'sink': 'median'})
    with pytest.raises(ValueError, match='unknown field vector operation'):
        bench['operations'].field_vector({'field': 'koala-bear', 'elements': 1, 'operation': 'median'})
    with pytest.raises(ValueError, match='unknown transform operation'):
        bench['operations'].transform({'extension_degree': 1, 'elements': 32, 'operation': 'roundtrip'})
    with pytest.raises(ValueError, match='unknown curve operation'):
        bench['operations'].curve_operation({'elements': 1, 'operation': 'pairing'})
    for width, degree in ((1, 2), (2, 4)):
        with pytest.raises(ValueError, match='coupled AIR requires'):
            bench['stark'].recurrence(ROOT, {'constraint': 'coupled', 'height': 8,
                                             'width': width, 'constraint_degree': degree})


@pytest.mark.parametrize('field', FIELDS)
def test_field_vector_controls_use_scalar_expectations(bench, field):
    f = bench['algebra'].FieldOracle(field)
    for size in (0, 3):
        for operation in ('add', 'subtract', 'hadamard', 'scale', 'sum', 'product', 'dot'):
            program = bench['operations'].field_vector({'field': field, 'elements': size, 'operation': operation})
            data = program.inputs[0]['P']
            xs = [decode(x) for x in data['xs']]
            ys = [decode(y) for y in data.get('ys', [])]
            if operation in ('add', 'subtract', 'hadamard', 'scale'):
                if operation == 'scale':
                    ys = [decode(data['c'])] * size
                combine = {'add': f.add, 'subtract': f.sub, 'hadamard': f.mul, 'scale': f.mul}[operation]
                expected = [f.encode(combine(x, y)) for x, y in zip(xs, ys, strict=True)]
            else:
                if operation == 'dot':
                    xs = [f.mul(x, y) for x, y in zip(xs, ys, strict=True)]
                expected = f.encode(reduce(f.mul if operation == 'product' else f.add, xs,
                                           f.one if operation == 'product' else f.zero))
            assert data['expected'] == expected
            assert program.incorrect['P']['expected'] != expected


@pytest.mark.parametrize('degree', (1, 4, 8))
def test_transform_directions_have_complete_independent_expectations(bench, degree):
    generate = bench['operations'].transform
    shape = {'elements': 32, 'extension_degree': degree}
    forward = generate(shape | {'operation': 'dft'})
    backward = generate(shape | {'operation': 'interpolate'})
    a, data = bench['algebra'], forward.inputs[0]['P']
    coefficients = list(map(decode, data['xs']))
    root = pow(1791270792, (1 << 24)//32, a.P)
    expected = [a.horner(coefficients, (pow(root, i, a.P),) + (0,)*(degree-1)) for i in range(32)]
    assert list(map(decode, data['expected'])) == expected
    assert backward.inputs[0]['P']['xs'] == data['expected']
    assert backward.inputs[0]['P']['expected'] == data['xs']
    assert 'poly.coset_interpolate' not in forward.source
    assert 'poly.coset_evaluate' not in backward.source
    assert forward.incorrect['P']['expected'] != data['expected']
    assert backward.incorrect['P']['expected'] != data['xs']


@pytest.mark.parametrize('degree', (1, 4, 8))
@pytest.mark.parametrize('layout', ('columns', 'rows'))
def test_batch_coset_forms_match_direct_integer_evaluation_and_layout(bench, degree, layout):
    a = bench['algebra']
    shape = {'extension_degree': degree, 'height': 4, 'width': 3,
             'evaluation_size': 8, 'layout': layout}
    programs = [bench['operations'].coset_batch(shape | {'form': form})
                for form in ('columns', 'library')]
    assert programs[0].inputs == programs[1].inputs
    data = programs[0].inputs[0]['P']
    shift = decode(data['shift'])
    coefficients = [a.dense(4, degree, 302+column) for column in range(3)]
    root = pow(1791270792, (1 << 24)//8, a.P)
    columns = [[a.horner(cs, tuple(c*pow(root, i, a.P) % a.P for c in shift))
                for i in range(8)] for cs in coefficients]
    expected = ([x for column in columns for x in column] if layout == 'columns' else
                [columns[column][row] for row in range(8) for column in range(3)])
    assert list(map(decode, data['expected'])) == expected
    assert all(p.incorrect['P']['expected'] != data['expected'] for p in programs)
    assert 'v::concat' in programs[0].source
    assert 'coset::extend_columns' in programs[1].source


@pytest.mark.parametrize('degree', (1, 4, 8))
@pytest.mark.parametrize('kind', ('off-domain', 'on-domain'))
def test_coset_point_forms_have_independent_point_major_expectations_and_mutation_controls(
        bench, degree, kind):
    field = 'koala-bear' + (f'.ext{degree}-binomial3' if degree != 1 else '')
    f = CosetReference(field)
    shape = {'extension_degree': degree, 'height': 4, 'width': 3,
             'points': 3, 'point_kind': kind}
    forms = ('coefficients', 'library', 'reused-coefficients')
    programs = {form: bench['operations'].coset_point(shape | {'form': form}) for form in forms}
    first = programs['coefficients']
    assert all(program.inputs == first.inputs for program in programs.values())
    assert len({program.source for program in programs.values()}) == 3
    data = first.inputs[0]['P']
    height, width = int(data['height']), int(data['width'])
    words = list(map(decode, data['xs']))
    points, shift = list(map(decode, data['points'])), decode(data['shift'])
    assert len(words) == height * width and len(points) == shape['points']
    assert len(set(words)) == len(words) and len(set(points)) == len(points)
    if degree > 1:
        assert all(shift[1:]) and all(all(point[1:]) for point in points)
        assert all(all(value[1:]) for value in words)

    def evaluate(values, at, offset):
        domain = f.domain(offset, height)
        return [f.lagrange(values[column * height:(column + 1) * height], domain, point)
                for point in at for column in range(width)]

    # Generic Lagrange basis products only consume the supplied word, unlike
    # the generator's coefficient Horner oracle and radix-two input transform.
    expected = evaluate(words, points, shift)
    assert list(map(decode, data['expected'])) == expected
    domain = f.domain(shift, height)
    assert all((point in domain) == (kind == 'on-domain') for point in points)
    if kind == 'on-domain':
        assert expected == [words[column * height + row]
                            for row in range(len(points)) for column in range(width)]

    changed_words = words.copy()
    changed_words[height + 1] = f.add(changed_words[height + 1], f.one)
    changed = evaluate(changed_words, points, shift)
    assert changed != expected
    assert all(changed[i] == expected[i] for i in range(len(expected)) if i % width != 1)
    assert evaluate(words, [f.add(points[0], f.one), *points[1:]], shift) != expected
    assert evaluate(words, points, f.mul(shift, f.embed(2))) != expected
    swapped = [*words[height:2 * height], *words[:height], *words[2 * height:]]
    assert evaluate(swapped, points, shift) != expected

    for form, program in programs.items():
        wrong = program.incorrect['P']
        assert {k: v for k, v in wrong.items() if k != 'expected'} == {
            k: v for k, v in data.items() if k != 'expected'}
        assert len(wrong['expected']) == len(expected)
        assert list(map(decode, wrong['expected'])) != expected
        assert all(len(decode(value)) == degree for value in wrong['expected'])
        assert all(0 <= coordinate < f.modulus
                   for value in wrong['expected'] for coordinate in decode(value))
        assert program.dependencies == ('core.collections', 'core.polynomial')
        assert ('opening::opening_claims' in program.source) == (form == 'library')
        assert ('polynomial::evaluate' in program.source) == (form != 'library')
        before = deepcopy(program.inputs)
        wrong['expected'][0] = f.encode(f.zero)
        assert program.inputs == before
        assert bench['operations'].coset_point(shape | {'form': form}).inputs == before
    assert 'repeated interpolation per point and column' in first.oracle
    assert 'one interpolation per column' in programs['reused-coefficients'].oracle


def test_coset_point_catalog_keeps_fixed_matched_strategies_and_separate_domain_controls(bench):
    cases = [case for case in bench['coverage'].cases() if case.name == 'coset_point']
    assert len(cases) == 78
    assert len({case.identifier for case in cases}) == len(cases)
    assert {case.shape['extension_degree'] for case in cases} == {1, 4, 8}
    off_domain = [case for case in cases if case.shape['point_kind'] == 'off-domain']
    assert {case.shape['height'] for case in off_domain} == {32, 1024, 4096}
    assert {case.shape['width'] for case in off_domain} == {1, 4, 16}
    assert {case.shape['points'] for case in off_domain} == {1, 8}
    groups = {}
    for case in cases:
        key = tuple(sorted((k, v) for k, v in case.shape.items() if k != 'form'))
        groups.setdefault(key, set()).add(case.shape['form'])
        assert case.category == 'operation'
        assert case.shape['form'] in case.mix
        if case.shape['point_kind'] == 'on-domain':
            assert (case.shape['height'], case.shape['width'], case.shape['points']) == (4, 4, 4)
            generated = case.generate(ROOT, ROOT/'unused')
            assert generated.inputs == bench['operations'].coset_point(case.shape).inputs
    for key, forms in groups.items():
        count = dict(key)['points']
        assert forms == ({'coefficients', 'library'} if count == 1 else
                         {'coefficients', 'library', 'reused-coefficients'})


def test_coset_point_generator_refuses_unknown_forms_and_point_kinds(bench):
    shape = {'extension_degree': 1, 'height': 4, 'width': 1,
             'points': 1, 'point_kind': 'off-domain', 'form': 'library'}
    generate = bench['operations'].coset_point
    with pytest.raises(ValueError, match='unknown coset point form'):
        generate(shape | {'form': 'automatic'})
    with pytest.raises(ValueError, match='unknown coset point kind'):
        generate(shape | {'point_kind': 'mixed'})
    with pytest.raises(ValueError, match='on-domain point count exceeds height'):
        generate(shape | {'point_kind': 'on-domain', 'points': 5})


@pytest.mark.parametrize('operation', ('vector-scale', 'scale-each', 'msm'))
def test_separate_curve_operations_check_all_scalar_expectations(bench, operation):
    program = bench['operations'].curve_operation({'elements': 33, 'operation': operation})
    data, modulus = program.inputs[0]['P'], bench['algebra'].FR
    xs = list(map(int, data['xs']))
    factors = [int(data['scale'])]*len(xs) if operation == 'vector-scale' else list(map(int, data['weights']))
    products = [x*y % modulus for x, y in zip(xs, factors, strict=True)]
    assert data['expected'] == (str(sum(products) % modulus) if operation == 'msm' else list(map(str, products)))
    assert program.incorrect['P']['expected'] != data['expected']
    calls = {'vector-scale': 'curve::scale(points,scale)', 'scale-each': 'curve::scale_each(weights,points)',
             'msm': 'curve::msm(weights,points)'}
    assert calls[operation] in program.source
    assert all(call not in program.source for name, call in calls.items() if name != operation)
    if operation != 'msm':
        assert 'curve::get(out,i)==generator*v::get(expected,i)' in program.source
    assert 'not independent curve arithmetic' in program.oracle


def test_coupled_air_traces_satisfy_bundles_and_reject_neighbor_mutations(bench):
    spec = importlib.util.spec_from_file_location('benchmark_test_ring', ROOT/'compiler/adapters/ring_arena.py')
    arena = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(arena)
    cases = [c for c in bench['coverage'].cases() if c.name == 'air' and c.shape.get('constraint') == 'coupled']
    for case in cases:
        shape = case.shape
        bundle, initial, final, trace = bench['stark'].recurrence(ROOT, shape)
        table = bundle[3][0]
        ring, bindings, assertions = table[5:8]
        width, height = shape['width'], shape['height']
        assert trace[:width] == initial and trace[-width:] == final
        degrees = []
        for node in ring[2]:
            degrees.append(1 if node[0] == 'input' else 0 if node[0] == 'constant' else
                           degrees[node[1]] if node[0] == 'neg' else
                           max(degrees[node[1]], degrees[node[2]]) if node[0] == 'add' else
                           degrees[node[1]]+degrees[node[2]])
        assert max(degrees[i] for i in ring[3]) == shape['constraint_degree']

        def failures(values, public):
            failed = []
            for row in range(height):
                def fetch(index):
                    binding = bindings[index]
                    value = public[binding[1]] if binding[0] == 'public' else values[((row+int(binding[2])) % height)*width+binding[3]]
                    return arena.scalar(value)
                outputs = arena.evaluate(ring, fetch)
                for output, selector in assertions:
                    active = row == 0 if selector == ['first'] else row == height-1 if selector == ['last'] else row < height-1
                    if active and outputs[output] != arena.ZERO:
                        failed.append((row, output))
            return failed

        assert not failures(trace, initial+final)
        wrong = trace.copy()
        wrong[width+1] = (wrong[width+1]+1) % arena.P
        assert failures(wrong, initial+final)
        assert failures(trace, [(initial[0]+1) % arena.P, *initial[1:], *final])
        # Replacing the coupled transitions by the original independent
        # recurrence is invalid even with matching new endpoint claims.
        independent = initial.copy()
        current = initial.copy()
        for _ in range(1, height):
            current = [(x*x+i+1) % arena.P for i, x in enumerate(current)]
            independent.extend(current)
        assert failures(independent, initial+current)
        profiles = [c for c in bench['coverage'].cases() if c.name in ('air', 'stark') and c.shape == shape]
        programs = [c.generate(ROOT, ROOT/'unused') for c in profiles]
        assert len(programs) == 2
        assert programs[0].assets == programs[1].assets
        assert programs[0].inputs[0]['witness'] == programs[1].inputs[0]['witness']
        assert 'coupled degree-' in programs[0].oracle
        for case, program in zip(profiles, programs, strict=True):
            other = case.generate(ROOT, ROOT/'unused', statement=1)
            assert other.source == program.source and other.assets == program.assets
            assert other.inputs[0]['public'] != program.inputs[0]['public']


def test_added_catalog_inputs_fit_conservative_default_size_envelope(bench):
    def nodes(value):
        if isinstance(value, dict):
            return 1 + len(value) + sum(map(nodes, value.values()))
        if isinstance(value, list):
            assert len(value) <= 16_384
            return 1 + sum(map(nodes, value))
        return 1

    largest = 0
    for case in bench['coverage'].cases():
        if case.name not in ('expression', 'field_vector', 'transform', 'coset_point', 'curve_operation'):
            continue
        program = case.generate(ROOT, ROOT/'unused')
        # Keep formatted fixtures below 4 MiB; the document ceiling is 16 MiB.
        # this is not an execution-work or intermediate-allocation proof.
        for values in (program.inputs[0], program.incorrect):
            encoded = json.dumps(values, indent=2).encode()
            largest = max(largest, len(encoded))
            assert len(encoded) < 4 << 20
            assert nodes(values) < 200_000
            assert 'capacity' not in values and 'limits' not in values
        before = deepcopy(program.inputs)
        assert case.generate(ROOT, ROOT/'unused').inputs == before
    assert largest > 100_000
