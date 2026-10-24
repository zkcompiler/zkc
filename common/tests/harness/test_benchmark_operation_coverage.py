"""Operation panel contracts and independent complete-output checks; no tools."""
import importlib
import json
from pathlib import Path

import pytest

from coset_reference import CosetReference


ROOT = Path(__file__).resolve().parents[3]


@pytest.fixture
def bench(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT/'common/benchmarks'))
    return {name: importlib.import_module('bench.'+name)
            for name in ('algebra', 'coverage', 'operations')}


@pytest.mark.parametrize('height,size,width', [(1, 1, 1), (3, 8, 3), (15, 64, 1),
                                             (16, 64, 3), (17, 64, 3), (64, 64, 1),
                                             (17, 4096, 1)])
def test_bn254_coefficient_forms_match_horner_at_every_output(bench, height, size, width):
    shape = {'height': height, 'width': width, 'evaluation_size': size, 'shift': 7}
    programs = [bench['operations'].coefficient_batch(shape | {'form': form})
                for form in ('batch', 'padded-columns')]
    left, right = programs
    assert left.inputs == right.inputs and left.incorrect == right.incorrect
    inputs = left.inputs[0]['P']
    oracle = CosetReference('bn254.fr')
    coefficients = [oracle.embed(int(value)) for value in inputs['xs']]
    domain = oracle.domain(oracle.embed(7), size)
    expected = [oracle.encode(oracle.horner(coefficients[column*height:(column+1)*height], point))
                for column in range(width) for point in domain]
    assert inputs['expected'] == expected
    assert len(expected) == width*size
    assert all(coefficients[(column+1)*height-1][0] for column in range(width))
    for program in programs:
        assert 'return v::equal(out,expected)' in program.source
        wrong = program.incorrect['P']
        assert {key for key in inputs if inputs[key] != wrong[key]} == {'expected'}
        assert len(wrong['expected']) == len(expected)
        assert wrong['expected'][0] != expected[0] and wrong['expected'][1:] == expected[1:]
        assert program.dependencies == ('core.collections', 'core.polynomial')
    assert 'coset::evaluate_batch(xs,width,height,shift,size)' in left.source
    assert 'v::fill<F>(0,size-height)' in right.source
    assert 'coset::evaluate_batch(padded,1,size,shift,size)' in right.source
    assert 'from_coefficients' not in right.source  # It would trim the padding.


@pytest.mark.parametrize('change', [{'height': 0}, {'width': 0}, {'height': 9},
                                    {'evaluation_size': 0}, {'evaluation_size': 3},
                                    {'shift': 0}, {'shift': -1}, {'form': 'interpolate'},
                                    {'height': True}, {'evaluation_size': 1 << 29}])
def test_coefficient_generator_refuses_invalid_shapes(bench, change):
    shape = {'height': 3, 'width': 1, 'evaluation_size': 8, 'shift': 7, 'form': 'batch'}
    with pytest.raises(ValueError, match='invalid BN254 coefficient batch control'):
        bench['operations'].coefficient_batch(shape | change)


def test_coefficient_catalog_is_a_fixed_paired_panel(bench):
    cases = [case for case in bench['coverage'].cases() if case.name == 'coefficient_batch']
    shapes = {(case.shape['height'], case.shape['width'], case.shape['evaluation_size']) for case in cases}
    assert shapes == {(15, 1, 64), (16, 1, 64), (17, 1, 64), (64, 1, 64),
                      (17, 1, 4096), (17, 3, 4096), (4096, 1, 4096), (4096, 3, 4096),
                      (1024, 1, 32768), (32768, 1, 32768)}
    assert len(cases) == 2*len(shapes)
    for height, width, size in shapes:
        pair = [case for case in cases if case.shape['height'] == height
                and case.shape['width'] == width and case.shape['evaluation_size'] == size]
        assert {case.shape['form'] for case in pair} == {'batch', 'padded-columns'}
        assert all(case.shape['field'] == 'bn254.fr' and case.shape['shift'] == 7 for case in pair)


@pytest.mark.parametrize('field,short', [('koala-bear', 'kb'), ('bls12-381.fr', 'fr')])
def test_dense_vector_publication_cases_check_full_outputs(bench, field, short):
    modulus = bench['algebra'].FieldOracle(field).modulus
    cases = {case.identifier: case for case in bench['coverage'].cases()}
    for operation, size in (('add', 1024), ('hadamard', 8192)):
        program = cases[f'field-vector-{short}-{operation}-{size}'].generate(ROOT, ROOT/'unused')
        inputs = program.inputs[0]['P']
        xs, ys = [list(map(int, inputs[name])) for name in ('xs', 'ys')]
        expected = [(x+y if operation == 'add' else x*y) % modulus
                    for x, y in zip(xs, ys, strict=True)]
        assert len(expected) == size and list(map(int, inputs['expected'])) == expected
        assert 'v::equal(out,expected)' in program.source
        assert program.incorrect['P']['expected'][1:] == inputs['expected'][1:]


@pytest.mark.parametrize('field,short', [('koala-bear', 'kb'), ('bls12-381.fr', 'fr')])
def test_vector_literals_pair_typed_operands_with_full_repeated_addition(bench, field, short):
    modulus = bench['algebra'].FieldOracle(field).modulus
    cases = {case.identifier: case for case in bench['coverage'].cases()}
    for size, trips in ((1024, 17), (8192, 1)):
        programs = [cases[f'vector-literal-{short}-n{size}-{trips}-{form}'].generate(ROOT, ROOT/'unused')
                    for form in ('constant', 'operand')]
        left, right = programs
        assert left.inputs == right.inputs and left.incorrect == right.incorrect
        values = left.inputs[0]['P']
        assert len(values['expected']) == len(values['value']) == size
        assert list(map(int, values['expected'])) == [int(value)*trips % modulus for value in values['value']]
        attributes = ','.join(f'"{value}"' for value in values['value'])
        assert f'for i in 0..trips {{ total=v::add(total,kernel<F>("vector.constant"; {attributes})); }}' in left.source
        assert 'vector.constant' not in right.source
        assert 'return v::equal(total,expected)' in left.source
        assert 'exported loop' in left.oracle


@pytest.mark.parametrize('field,size', [('koala-bear', 0), ('koala-bear.ext4-binomial3', 3)])
def test_vector_literal_refuses_unimplemented_element_types(bench, field, size):
    with pytest.raises(ValueError, match='nonempty prime-field vector'):
        bench['operations'].literal({'field': field, 'elements': size, 'trips': 1, 'form': 'constant'}, root=ROOT)


def test_added_panels_respect_host_input_tree_and_byte_limits(bench):
    def nodes(value):
        if isinstance(value, dict):
            return 1 + len(value) + sum(map(nodes, value.values()))
        if isinstance(value, list):
            assert len(value) <= 32_768
            return 1 + sum(map(nodes, value))
        return 1

    largest = 0
    for case in bench['coverage'].cases():
        if case.name not in ('coefficient_batch', 'vector_literal'):
            continue
        program = case.generate(ROOT, ROOT/'unused')
        for inputs in (program.inputs[0], program.incorrect):
            # Normal readable ingress ceilings; no application capacity overrides.
            encoded = json.dumps({'arguments': {'inputs': inputs}}, indent=2).encode()
            largest = max(largest, len(encoded))
            assert len(encoded) < 16 << 20
            assert nodes(inputs) < 200_000
            assert 'limits' not in inputs and 'capacity' not in inputs
    assert largest > 4 << 20  # Dense 32768 BN254 coefficients plus the full output.
