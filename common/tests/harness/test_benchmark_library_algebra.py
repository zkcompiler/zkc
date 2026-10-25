"""Independent small arithmetic and capture checks, without compiled tools."""
from collections import Counter
from copy import deepcopy
import hashlib
import importlib
import json
from pathlib import Path
import shutil
import sys
from types import SimpleNamespace

import pytest

from coset_reference import CosetReference


ROOT = Path(__file__).resolve().parents[3]
FAMILIES = {'kzg': 28, 'curve_family': 40, 'sparse_matrix': 53, 'opening_quotient': 72,
            'quotient_split': 18, 'literal': 48, 'relation_rows': 12}
FR = 52435875175126190479447740508185965837690552500527637822603658699938581184513
DALEK = 2**252 + 27742317777372353535851937790883648493


@pytest.fixture
def bench(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT/'common/benchmarks'))
    return {name: importlib.import_module('bench.'+name) for name in
            ('coverage', 'library_algebra', 'algebra', 'execution', 'runner')}


def decode(value):
    return tuple(map(int, value)) if isinstance(value, list) else (int(value),)


def prime_interpolant(points, values, modulus):
    """Generic coefficient Lagrange interpolation; no roots-of-unity shortcut."""
    result = [0] * len(points)
    for i, (x, value) in enumerate(zip(points, values, strict=True)):
        basis, denominator = [1], 1
        for j, y in enumerate(points):
            if i == j:
                continue
            product = [0] * (len(basis)+1)
            for k, coefficient in enumerate(basis):
                product[k] = (product[k]-y*coefficient) % modulus
                product[k+1] = (product[k+1]+coefficient) % modulus
            basis = product
            denominator = denominator*(x-y) % modulus
        scale = value*pow(denominator, -1, modulus) % modulus
        result = [(old+scale*coefficient) % modulus
                  for old, coefficient in zip(result, basis, strict=True)]
    return result


@pytest.mark.parametrize('field', ['bls12-381.fr', 'koala-bear'])
@pytest.mark.parametrize('n', [1, 2, 8])
@pytest.mark.parametrize('kind', ['on-domain', 'off-domain'])
@pytest.mark.parametrize('order', ['natural', 'bit-reversed'])
def test_generic_kzg_matches_lagrange_polynomial_and_derivative(bench, field, n, kind, order):
    modulus = FR if field == 'bls12-381.fr' else 2130706433
    programs = [bench['library_algebra'].kzg(
        {'field': field, 'elements': n, 'point_kind': kind, 'operation': operation,
         'order': order}, root=ROOT)
        for operation in ('evaluate', 'quotient')]
    inputs = programs[1].inputs[0]['P']
    generator, at = int(inputs['generator']), int(inputs['at'])
    points = [pow(generator, i, modulus) for i in range(n)]
    if order == 'bit-reversed' and n > 1:
        bits = n.bit_length()-1
        points = [points[int(f'{i:0{bits}b}'[::-1], 2)] for i in range(n)]
    assert len(set(points)) == n and all(pow(x, n, modulus) == 1 for x in points)
    assert (at in points) == (kind == 'on-domain')
    values = list(map(int, inputs['values']))
    coefficients = prime_interpolant(points, values, modulus)
    def evaluate(x):
        return sum(c*pow(x, i, modulus) for i, c in enumerate(coefficients)) % modulus
    value = evaluate(at)
    quotient = [(evaluate(x)-value)*pow((x-at) % modulus, -1, modulus) % modulus
                if x != at else
                sum(i*c*pow(at, i-1, modulus) for i, c in enumerate(coefficients) if i) % modulus
                for x in points]
    assert list(map(int, inputs['expected'])) == [value]+quotient
    assert programs[0].inputs[0]['P']['expected'] == [str(value)]
    assert {k: v for k, v in inputs.items() if k != 'expected'} == {
        k: v for k, v in programs[0].inputs[0]['P'].items() if k != 'expected'}
    for program, call in zip(programs, ('evaluate', 'quotient'), strict=True):
        assert program.dependencies == ('commitments.kzg',)
        constructor = 'two_adic' if order == 'natural' else 'two_adic_bit_reversed'
        assert f'evaluation::{constructor}(n,generator)' in program.source
        assert 'evaluation::evaluations(unity,values)' in program.source
        assert f'kzg::{call}(input,at)' in program.source
        assert 'coset::' not in program.source and 'pairing' not in program.source
        assert 'v::equal(out,expected)' in program.source


@pytest.mark.parametrize('curve', ['bls-g1', 'bls-g2', 'bn-g1', 'bn-g2', 'ristretto', 'edwards'])
@pytest.mark.parametrize('form', ['fixed-base', 'shared-scalar', 'per-point', 'msm'])
def test_curve_forms_check_every_scalar_with_explicit_shared_provider_scope(bench, curve, form):
    group, field = bench['library_algebra'].CURVES[curve]
    modulus = {'ristretto255.scalar': DALEK, 'bls12-381.fr': FR,
               'bn254.fr': 21888242871839275222246405745257275088548364400416034343698204186575808495617}[field]
    f = bench['algebra'].FieldOracle(field)
    assert f.modulus == modulus
    assert f.mul((modulus-2,), (modulus-3,)) == (6,)
    program = bench['library_algebra'].curve_family({'curve': curve, 'elements': 5, 'form': form}, root=ROOT)
    inputs = program.inputs[0]['P']
    xs, weights = [list(map(int, inputs[key])) for key in ('xs', 'weights')]
    if form == 'fixed-base':
        expected = weights
        assert 'curve::collect(weights,fn(weight)=>generator*weight)' in program.source
    elif form == 'shared-scalar':
        expected = [(x*int(inputs['scale'])) % modulus for x in xs]
        assert 'curve::scale(points,scale)' in program.source
    else:
        products = [(x*w) % modulus for x, w in zip(xs, weights, strict=True)]
        expected = [sum(products) % modulus] if form == 'msm' else products
        assert ('curve::msm(weights,points)' if form == 'msm' else
                'curve::scale_each(weights,points)') in program.source
    assert list(map(int, inputs['expected'])) == expected
    assert all(0 <= value < modulus for value in xs+weights+expected)
    assert 0 in xs and 0 in weights
    assert f'group("{group}")' in program.source
    assert 'for i in 0..v::length(expected)' in program.source
    assert 'curve::length(out)==v::length(expected)' in program.source
    assert 'curve::get(out,i)+generator==generator*(v::get(expected,i)+1)' in program.source
    assert 'shared-provider' in program.oracle and 'self-consistency' in program.oracle
    assert 'not independent curve coordinates' in program.oracle


@pytest.mark.parametrize('distribution', ['uniform', 'clustered', 'empty-rows'])
@pytest.mark.parametrize('nnz', [0, 29, 68])
def test_sparse_directions_match_dense_contractions_and_exact_occupancy(bench, distribution, nnz):
    programs = [bench['library_algebra'].sparse_matrix(
        {'rows': 17, 'columns': 31, 'nnz': nnz, 'distribution': distribution, 'direction': direction},
        root=ROOT) for direction in ('forward', 'transpose')]
    matrices = [p.inputs[0]['P']['matrix'] for p in programs]
    assert matrices[0] == matrices[1]
    matrix = matrices[0]
    entries = [tuple(map(int, entry)) for entry in matrix['entries']]
    assert len(entries) == nnz and len({(r, c) for r, c, _ in entries}) == nnz
    assert entries == sorted(entries)
    dense = [[0]*31 for _ in range(17)]
    for r, c, value in entries:
        assert 0 <= r < 17 and 0 <= c < 31 and 0 < value < FR
        dense[r][c] = value
    if distribution == 'empty-rows':
        assert all(not any(dense[r]) for r in range(1, 17, 2))
    counts = [sum(value != 0 for value in row) for row in dense]
    if distribution == 'uniform':
        assert max(counts)-min(counts) <= 1
    if distribution == 'clustered' and nnz == 68:
        assert sum(counts[:2]) == 62 and max(counts) > 5*min(counts)
    for direction, program in zip(('forward', 'transpose'), programs, strict=True):
        inputs = program.inputs[0]['P']
        xs = list(map(int, inputs['xs']))
        vectors = dense if direction == 'forward' else list(zip(*dense, strict=True))
        expected = [sum(x*y for x, y in zip(row, xs, strict=True)) % FR for row in vectors]
        assert list(map(int, inputs['expected'])) == expected
        assert 'v::equal(out,expected)' in program.source
        operation = 'multiply' if direction == 'forward' else 'transpose_multiply'
        assert f'mat::{operation}(matrix,xs)' in program.source
    left, right = [p.inputs[0]['P'] for p in programs]
    assert sum(int(x)*int(y) for x, y in zip(left['expected'], right['xs'], strict=True)) % FR == \
           sum(int(x)*int(y) for x, y in zip(left['xs'], right['expected'], strict=True)) % FR


@pytest.mark.parametrize('degree', [1, 4, 8])
@pytest.mark.parametrize('blocks', [4, 8])
def test_quotient_blocks_match_direct_horner_with_padding(bench, degree, blocks):
    shape = {'extension_degree': degree, 'elements': 8, 'block_width': 2, 'blocks': blocks}
    programs = [bench['library_algebra'].quotient_split(shape | {'form': form}, root=ROOT)
                for form in ('library', 'reference')]
    assert programs[0].inputs == programs[1].inputs
    inputs = programs[0].inputs[0]['P']
    field = 'koala-bear' + (f'.ext{degree}-binomial3' if degree != 1 else '')
    ref = CosetReference(field)
    coefficients = bench['algebra'].FieldOracle(field).dense(8, 472)
    shift = decode(inputs['shift'])
    domain = ref.domain(shift, 8)
    assert list(map(decode, inputs['values'])) == [ref.horner(coefficients, x) for x in domain]
    coefficients += [ref.zero] * (2*blocks-8)
    expected = [ref.horner(coefficients[2*b:2*b+2], x) for b in range(blocks) for x in domain]
    assert list(map(decode, inputs['expected'])) == expected
    assert 'air_poly::split_quotient' in programs[0].source
    assert 'out=v::concat(out' in programs[1].source
    assert 'v::equal(out,expected)' in programs[0].source


@pytest.mark.parametrize('degree', [1, 4, 8])
@pytest.mark.parametrize('kind,count', [('repeated', 4), ('distinct', 4), ('mixed', 8), ('repeated', 0)])
def test_opening_forms_match_lagrange_claims_and_rational_quotients_in_all_coordinates(
        bench, degree, kind, count):
    shape = {'extension_degree': degree, 'height': 8, 'width': 4,
             'openings': count, 'point_kind': kind}
    programs = [bench['library_algebra'].opening_quotient(shape | {'form': form}, root=ROOT)
                for form in ('library', 'reference')]
    assert programs[0].inputs == programs[1].inputs
    inputs = programs[0].inputs[0]['P']
    field = 'koala-bear' + (f'.ext{degree}-binomial3' if degree != 1 else '')
    ref = CosetReference(field)
    shift, zeta, ratio, first = [decode(inputs[key]) for key in ('shift', 'zeta', 'ratio', 'first')]
    domain = ref.domain(shift, 8)
    selected, rotations = [list(map(int, inputs[key])) for key in ('selected', 'rotations')]
    columns = [list(map(decode, inputs['xs'][8*i:8*(i+1)])) for i in range(4)]
    points = [ref.mul(zeta, ref.domain(ref.one, 8)[rotation]) for rotation in rotations]
    assert not set(points) & set(domain)
    if count:
        assert len(set(selected)) == 4
        assert len(set(points)) == {'repeated': 1, 'distinct': count, 'mixed': 3}[kind]
    claimed = list(map(decode, inputs['claimed']))
    for column, point, claim in zip(selected, points, claimed, strict=True):
        assert claim == ref.lagrange(columns[column], domain, point)
    # Evaluate the defining rational identity at every row, independently of
    # the generator's coefficient division, transform and vector accumulation.
    expected = []
    initial = list(map(decode, inputs['initial']))
    for row, x in enumerate(domain):
        value = initial[row]
        for i, (column, point, claim) in enumerate(zip(selected, points, claimed, strict=True)):
            inverse = ref.power(ref.sub(x, point), ref.modulus**degree-2)
            quotient = ref.mul(ref.sub(columns[column][row], claim), inverse)
            weight = ref.mul(first, ref.power(ratio, i))
            value = ref.add(value, ref.mul(weight, quotient))
        expected.append(value)
    expected.append(ref.mul(first, ref.power(ratio, count)))
    assert list(map(decode, inputs['expected'])) == expected
    if degree > 1:
        assert all(all(value[1:]) for value in map(decode, inputs['xs']))
        assert all(all(value[1:]) for value in expected)
    for program in programs:
        assert 'opening::bind_openings(' in program.source
        assert 'coset::column_batch(' in program.source
        assert 'opening::vector_accumulator(' in program.source
        assert 'v::equal(v::append(out,next),expected)' in program.source
    assert 'opening::deep_columns(batch,bound,accumulator)' in programs[0].source
    assert 'coset::opening_quotient(column,shift,at,v::get(claimed,i))' in programs[1].source
    assert 'out=v::accumulate(out,quotient,next)' in programs[1].source
    assert 'next=next*ratio' in programs[1].source
    assert 'deep_columns' not in programs[1].source


def test_catalog_preserves_old_cases_and_keeps_new_panels_bounded(bench):
    cases = bench['coverage'].cases()
    # Preserve the original snapshot independently of later operation panels.
    vector_additions = {f'field-vector-{short}-{operation}-{size}' for short in ('kb', 'fr')
                        for operation, size in (('add', 1024), ('hadamard', 8192))}
    old = [case for case in cases if case.name not in FAMILIES
           and case.name not in ('coefficient_batch', 'vector_literal')
           and case.identifier not in vector_additions
           and not (case.name == 'stark' and case.shape.get('field') in ('baby-bear', 'goldilocks'))]
    assert len(old) == 456
    assert hashlib.sha256(json.dumps([vars(case) for case in old], sort_keys=True).encode()).hexdigest() == \
        '12f3f5ca9bbb1d2fcf328f711bc6323d7afe1c4becb6e122cebddb5f101e14ee'
    assert bench['coverage'].SMOKE == (
        'finite-kb-reduce-17', 'finite-kb-collect-17', 'finite-fr-bulk-17',
        'scan-scalar-17', 'scan-bulk-17', 'control-7x13', 'polynomial-ext1-32',
        'polynomial-ext8-32', 'extension-17', 'curve-1', 'pairing-2',
        'transcript-4x1', 'fri-n64-d16-q8', 'air-h8-w1-b4')
    assert Counter(case.name for case in cases if case.name in FAMILIES) == FAMILIES
    assert len({case.identifier for case in cases}) == len(cases)
    openings = [c.shape for c in cases if c.name == 'opening_quotient']
    assert {s['extension_degree'] for s in openings} == {1, 4, 8}
    assert {s['width'] for s in openings} == {1, 4, 8}
    for shape in openings:
        assert len([s for s in openings if s == shape | {'form': 'library'}]) == 1
        assert len([s for s in openings if s == shape | {'form': 'reference'}]) == 1


@pytest.mark.parametrize('field', ['bls12-381.fr', 'bn254.fr', 'koala-bear',
                                 'koala-bear.ext4-binomial3', 'koala-bear.ext8-binomial3',
                                 'gf2-64.pentanomial-4-3-1',
                                 'gf2-64.pentanomial-4-3-1.ext3-trinomial1'])
def test_bilinear_and_literal_controls_use_complete_field_elements(bench, field):
    f = bench['algebra'].FieldOracle(field, root=ROOT)
    def element(value):
        return tuple(int(x, 16) if x.startswith('0x') else int(x)
                     for x in (value if isinstance(value, list) else [value]))
    shape = {'rows': 7, 'columns': 13, 'nnz': 29,
             'distribution': 'clustered', 'direction': 'bilinear', 'field': field}
    matrix = bench['library_algebra'].sparse_matrix(shape, root=ROOT)
    inputs = matrix.inputs[0]['P']
    expected = f.zero
    for r, c, coefficient in inputs['matrix']['entries']:
        expected = f.add(expected, f.mul(element(inputs['left'][int(r)]),
                              f.mul(element(coefficient), element(inputs['xs'][int(c)]))))
    assert inputs['expected'] == [f.encode(expected)]
    assert 'mat::bilinear(matrix,left,xs)' in matrix.source
    operations = importlib.import_module('bench.operations')
    programs = [operations.literal({'field': field, 'trips': 17, 'form': form}, root=ROOT)
                for form in ('constant', 'operand')]
    assert programs[0].inputs == programs[1].inputs
    value = element(programs[0].inputs[0]['P']['value'])
    expected = f.zero
    for _ in range(17):
        expected = f.add(expected, value)
    assert programs[0].inputs[0]['P']['expected'] == f.encode(expected)
    assert 'kernel<F>("field.constant";' in programs[0].source
    assert 'field.constant' not in programs[1].source


def test_every_new_case_has_canonical_output_only_negatives_and_bounded_inputs(bench):
    def nodes(value):
        if isinstance(value, dict):
            return 1+len(value)+sum(nodes(x) for x in value.values())
        if isinstance(value, list):
            assert len(value) <= 65_536
            return 1+sum(nodes(x) for x in value)
        return 1

    for case in bench['coverage'].cases():
        if case.name not in FAMILIES:
            continue
        program = case.generate(ROOT, ROOT/'unused')
        good, bad = program.inputs[0]['P'], program.incorrect['P']
        assert {key for key in good if good[key] != bad[key]} == {'expected'}
        field = case.shape.get('field', 'koala-bear')
        oracle = bench['algebra'].FieldOracle(field, root=ROOT)
        modulus = oracle.modulus
        before, after = deepcopy(good['expected']), deepcopy(bad['expected'])
        def number(value):
            return int(value, 16) if value.startswith('0x') else int(value)
        def differences(left, right):
            if isinstance(left, list):
                assert isinstance(right, list) and len(left) == len(right)
                return sum(differences(x, y) for x, y in zip(left, right, strict=True))
            assert isinstance(left, str) and isinstance(right, str)
            assert 0 <= number(left) < modulus and 0 <= number(right) < modulus
            return int(left != right)
        assert differences(before, after) == 1
        while isinstance(before, list) and isinstance(before[0], list):
            before, after = before[0], after[0]
        if isinstance(before, list):
            assert len(before) == len(after)
            assert before[1:] == after[1:]
            before, after = before[0], after[0]
        assert number(after) == (number(before) ^ 1 if oracle.binary else (number(before)+1) % modulus)
        assert nodes(program.inputs[0]) < 200_000 and nodes(program.incorrect) < 200_000
        # Keep the full pretty-printed request below the Host's 16 MiB input
        # ceiling; the larger octic panel needs more than 1 MiB.
        assert len(json.dumps(program.inputs[0], indent=2).encode()) < 4 << 20
        assert len(json.dumps(program.incorrect, indent=2).encode()) < 4 << 20
        assert program.support == ((ROOT/'compiler/adapters/ring_arena.py',)
                                   if case.name == 'relation_rows' else oracle.support)
        assert case.generate(ROOT, ROOT/'unused').inputs == program.inputs


def test_relation_row_oracle_checks_nonzero_and_inactive_residuals(bench, monkeypatch):
    stark = importlib.import_module('bench.stark')
    shape = {'height': 3, 'width': 1, 'data': 'valid'}
    bundle, *_ = stark.recurrence(ROOT, shape)
    # This deliberately is not a valid recurrence. Hand-calculated residuals
    # expose omission of transition assertions, scopes or zero inactive slots.
    monkeypatch.setattr(stark, 'recurrence', lambda root, shape: (bundle, [2], [11], [2, 6, 11]))
    for data, expected in [('valid', [0, 0, 1, 0, 0, 2130706433-26, 0, 0, 0]),
                           ('perturbed', [0, 0, 2, 0, 0, 2130706433-39, 0, 0, 0])]:
        program = bench['library_algebra'].relation_rows(shape | {'data': data}, root=ROOT)
        assert list(map(int, program.inputs[0]['P']['expected'])) == expected
        assert '"relation.table_rows"' in program.source
        assert program.assets == {'trace': bundle}
        assert 'inactive slots are zero' in program.oracle


def test_selected_source_library_closure_is_captured_without_running_a_real_compiler(bench, tmp_path):
    selected = tmp_path/'selected-source'
    selected.mkdir()
    shutil.copy(ROOT/'zkc.workspace.toml', selected/'zkc.workspace.toml')
    shutil.copytree(ROOT/'libraries/core', selected/'libraries/core')
    shutil.copytree(ROOT/'libraries/commitments/kzg', selected/'libraries/commitments/kzg')
    shutil.copytree(ROOT/'libraries/relations/air', selected/'libraries/relations/air')
    (selected/'compiler/adapters').mkdir(parents=True)
    shutil.copy(ROOT/'compiler/adapters/ring_arena.py', selected/'compiler/adapters/ring_arena.py')
    owners = ['libraries/commitments/kzg/lib.zkc', 'libraries/core/polynomial/coset.zkc',
              'libraries/core/polynomial/opening.zkc', 'libraries/core/algebra/curve.zkc',
              'libraries/core/primitives/collections/matrix.zkc',
              'libraries/relations/air/polynomial.zkc']
    for owner in owners:
        path = selected/owner
        path.write_text(path.read_text()+'\n// Selected-source capture sentinel.\n')
    compiler = tmp_path/'compiler-stub'
    compiler.write_text(f'''#!{sys.executable}
import json,sys
from pathlib import Path
for a in sys.argv[1:]:
    if a.startswith('--observations='): Path(a.split('=',1)[1]).write_text(json.dumps({{'completed':True}}))
print('{{"options":{{}}}}')
''')
    compiler.chmod(0o755)
    args = SimpleNamespace(source=selected, compiler=compiler, timeout=10, compiler_option=[])
    capture = bench['runner'].Capture(tmp_path/'capture')
    for family in FAMILIES:
        case = next(c for c in bench['coverage'].cases() if c.name == family)
        program = case.generate(selected, tmp_path/'unused')
        bench['execution'].compile_program(args, tmp_path/'generated', capture, {}, case, program)
    for owner in owners:
        assert (capture.directory/'source'/owner).read_bytes() == (selected/owner).read_bytes()
        assert 'Selected-source capture sentinel' in (capture.directory/'source'/owner).read_text()
    assert (capture.directory/'source/libraries/commitments/kzg/zkc.toml').is_file()
    assert (capture.directory/'source/libraries/core/polynomial/evaluation_domain.zkc').is_file()
    capture.check()


@pytest.mark.parametrize('generator,shape,message', [
    ('kzg', {'field': 'bls12-381.fr', 'elements': 8, 'operation': 'pairing', 'point_kind': 'off-domain'}, 'KZG operation'),
    ('kzg', {'field': 'koala-bear', 'elements': 8, 'operation': 'evaluate', 'point_kind': 'unknown'}, 'point kind'),
    ('kzg', {'field': 'bls12-381.fr', 'elements': 3, 'operation': 'evaluate', 'point_kind': 'off-domain'}, 'power-of-two'),
    ('curve_family', {'curve': 'edwards', 'elements': 3, 'form': 'unknown'}, 'curve form'),
    ('sparse_matrix', {'rows': 2, 'columns': 2, 'nnz': 5, 'distribution': 'uniform', 'direction': 'forward'}, 'dimensions'),
    ('sparse_matrix', {'rows': 2, 'columns': 2, 'nnz': 3, 'distribution': 'empty-rows', 'direction': 'forward'}, 'capacity'),
    ('sparse_matrix', {'rows': 2, 'columns': 2, 'nnz': 1, 'distribution': 'other', 'direction': 'forward'}, 'distribution'),
    ('sparse_matrix', {'rows': 2, 'columns': 2, 'nnz': 1, 'distribution': 'uniform', 'direction': 'other'}, 'direction'),
    ('opening_quotient', {'extension_degree': 1, 'height': 8, 'width': 4, 'openings': 4, 'point_kind': 'on-domain', 'form': 'library'}, 'point kind'),
    ('opening_quotient', {'extension_degree': 1, 'height': 8, 'width': 4, 'openings': 4, 'point_kind': 'distinct', 'form': 'unknown'}, 'form'),
    ('opening_quotient', {'extension_degree': 1, 'height': 8, 'width': 4, 'openings': 9, 'point_kind': 'distinct', 'form': 'library'}, 'count or width'),
])
def test_invalid_generator_choices_fail_explicitly(bench, generator, shape, message):
    with pytest.raises(ValueError, match=message):
        getattr(bench['library_algebra'], generator)(shape, root=ROOT)
