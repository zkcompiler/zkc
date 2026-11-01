"""Bounded STARK preparation and independent integer controls; no native tools."""
import hashlib
import importlib
import json
from pathlib import Path
import random

import pytest

from project import project_inputs


ROOT = Path(__file__).resolve().parents[3]
PROFILES = [
    ('baby-bear', 'baby_bear_quartic', 2013265921, 'baby-bear.ext4-binomial11',
     'merlin3.baby-bear.ext4-binomial11.rejection31le/0', 4, 4, 94, 16, 31),
    ('goldilocks', 'goldilocks_quadratic', 18446744069414584321, 'goldilocks.ext2-binomial7',
     'merlin3.goldilocks.ext2-binomial7.rejection64le/0', 2, 8, 100, 8, 7),
]
PANEL = [(8, 1, 2, 4, False), (32, 1, 2, 4, False), (128, 1, 2, 4, False),
         (32, 4, 2, 4, False), (32, 16, 2, 4, False), (32, 4, 2, 8, False),
         (8, 2, 2, 4, True), (32, 4, 2, 4, True), (128, 4, 2, 4, True),
         (32, 8, 2, 4, True), (32, 4, 3, 8, True)]


@pytest.fixture
def bench(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT/'common/benchmarks'))
    return {name: importlib.import_module('bench.'+name) for name in ('coverage', 'stark')}


def dimensions(shape):
    return (shape['height'], shape['width'], shape.get('constraint_degree', 2),
            shape['evaluation_size']//shape['height'], shape.get('constraint') == 'coupled')


def field_cases(bench, field):
    return [c for c in bench['coverage'].cases() if c.name == 'stark' and c.shape.get('field') == field]


def residuals(bundle, trace, public, row, modulus):
    """Interpret emitted scalar ring nodes independently of ring_arena.py."""
    table = bundle[3][0]
    height, width = table[2][1], table[4][0][3]
    ring, bindings, assertions = table[5:8]
    inputs = []
    for binding in bindings:
        if binding[0] == 'public':
            inputs.append(public[binding[1]])
        else:
            assert binding[:2] == ['read', 0]
            inputs.append(trace[((row+int(binding[2])) % height)*width+binding[3]])
    values = []
    for node in ring[2]:
        tag = node[0]
        if tag == 'input': value = inputs[node[1]]
        elif tag == 'constant': value = int(node[2])
        elif tag == 'add': value = values[node[1]]+values[node[2]]
        elif tag == 'mul': value = values[node[1]]*values[node[2]]
        else:
            assert tag == 'neg'
            value = -values[node[1]]
        values.append(value % modulus)
    outputs = [values[i] for i in ring[3]]
    result = []
    for index, selector in assertions:
        if selector == ['first']: active = row == 0
        elif selector == ['last']: active = row == height-1
        else:
            assert selector == ['interior', 0, 1]
            active = row < height-1
        result.append(outputs[index] if active else 0)
    return result


@pytest.mark.parametrize('profile', PROFILES, ids=[p[0] for p in PROFILES])
def test_field_panel_names_profiles_and_owning_manifest_closures(bench, profile):
    field, configuration, modulus, extension, suite, degree, word_bytes, tag, poseidon_width, shift = profile
    cases = field_cases(bench, field)
    assert len(cases) == len(PANEL) and {dimensions(c.shape) for c in cases} == set(PANEL)
    legacy = {dimensions(c.shape) for c in bench['coverage'].cases()
              if c.name == 'stark' and 'field' not in c.shape}
    assert set(PANEL) <= legacy
    assert not set(c.identifier for c in cases) & set(bench['coverage'].SMOKE)
    assert {c.shape['height'] for c in cases if c.shape['width'] == 1} == {8, 32, 128}
    assert {c.shape['width'] for c in cases if c.shape['height'] == 32} >= {1, 4, 8, 16}
    record = bench['stark'].LIBRARY_PROFILES[field]
    assert (record.degree, record.coordinate_bytes, record.vector_tag) == (degree, word_bytes, tag)
    for case in cases:
        assert configuration.replace('_', '-') in case.identifier
        assert f'poseidon2-{poseidon_width}' in case.identifier
        assert {key: case.shape[key] for key in ('field', 'profile', 'characteristic', 'extension_field',
                                                'transcript', 'poseidon_width', 'coset_shift')} == {
            'field': field, 'profile': configuration, 'characteristic': modulus, 'extension_field': extension,
            'transcript': suite, 'poseidon_width': poseidon_width, 'coset_shift': shift}
        assert max(case.shape['height'], case.shape['evaluation_size']) <= 512
        assert case.shape['height']*case.shape['width'] <= 512
        assert 'same-stack' in case.limitation and 'field-only' in case.limitation
        program = case.generate(ROOT, ROOT/'unused')
        assert program.dependencies == ('arguments.stark.single_table', f'arguments.stark.configurations.{configuration}')
        # Resolve the real owning manifests directly. Root workspace aliases are
        # maintained by the library owner, independently of this harness test.
        modules = {}
        for name in program.dependencies:
            manifest = ROOT/'libraries'/Path(*name.split('.'))/'zkc.toml'
            found, assets = project_inputs(manifest)
            assert not assets
            modules.update(found)
        owner = modules[f'stark::configurations::{configuration}']
        assert owner == ROOT/f'libraries/arguments/stark/configurations/{configuration}/lib.zkc'
        declaration = owner.read_text()
        for identity in (field, extension, f'rows.merkle-poseidon2-{poseidon_width}.{field}/0',
                         f'rows.merkle-poseidon2-{poseidon_width}.{extension}/0'):
            assert f'"{identity}"' in declaration
        assert f'return {shift};' in declaration
        assert f'use stark::configurations::{configuration}::{{Base,Extension}};' in program.source
        assert f'use stark::configurations::{configuration}::{{Poseidon2}};' in program.source
        assert f'fiat_shamir("{suite}",coins)' in program.source
        h, _, _, blowup, _ = dimensions(case.shape)
        assert f'ScalarTableArgument<Poseidon2,0,Trace,0,{h.bit_length()-1},{blowup.bit_length()-1},8>' in program.source


@pytest.mark.parametrize('profile', PROFILES, ids=[p[0] for p in PROFILES])
@pytest.mark.parametrize('panel', PANEL)
@pytest.mark.parametrize('statement', [0, 1])
def test_field_traces_and_emitted_constraints_match_independent_integers(bench, profile, panel, statement):
    field, _, modulus, *_ = profile
    case = next(c for c in field_cases(bench, field) if dimensions(c.shape) == panel)
    height, width, degree, _, coupled = panel
    program = case.generate(ROOT, ROOT/'unused', statement)
    public = list(map(int, program.inputs[0]['public']['public_data']))
    trace = list(map(int, program.inputs[0]['witness']['trace']))
    assert len(public) == 2*width and len(trace) == height*width
    assert all(0 <= x < modulus for x in public+trace)
    if field == 'goldilocks':
        assert any(x > 2**63 for x in trace)
    rng = random.Random(101+statement)
    initial = [rng.randrange(modulus) for _ in range(width)]
    assert public[:width] == trace[:width] == initial
    for row in range(height-1):
        previous = trace[row*width:(row+1)*width]
        for col in range(width):
            x = previous[col]
            if coupled:
                product = x*previous[(col+1) % width]
                if degree == 3: product *= x
                expected = product+previous[(col-1) % width]+col+1
            else:
                expected = x*x+col+1
            assert trace[(row+1)*width+col] == expected % modulus
    assert public[width:] == trace[-width:]
    bundle = program.assets['trace']
    assert bundle[0] == 'zkc.relation-bundle/0'
    assert bundle[1] == [[f'public-{i}', field] for i in range(2*width)]
    table = bundle[3][0]
    assert table[:5] == ['trace', 'required', ['fixed', height], 'cyclic', [['trace', 'witness', field, width]]]
    assert set(table[5][1]) == {field}
    assert table[7] == [[3*col+i, selector] for col in range(width)
                       for i, selector in enumerate((['first'], ['last'], ['interior', 0, 1]))]
    # The structural arena builder has a KoalaBear arithmetic reference, which
    # is never used here. Its only constants are small canonical base integers.
    assert all(node[1] == field and 0 <= int(node[2]) <= width < modulus
               for node in table[5][2] if node[0] == 'constant')
    assert all(not any(residuals(bundle, trace, public, row, modulus)) for row in range(height))
    perturbed = trace.copy()
    perturbed[(height//2)*width] = (perturbed[(height//2)*width]+1) % modulus
    assert any(any(residuals(bundle, perturbed, public, row, modulus)) for row in range(height))
    changed = list(map(int, program.changed['public_data']))
    assert changed == [(public[0]+1) % modulus, *public[1:]]
    assert any(residuals(bundle, trace, changed, 0, modulus))


@pytest.mark.parametrize('field', [p[0] for p in PROFILES])
def test_field_statement_rotation_keeps_source_assets_and_preparation_deterministic(bench, field):
    for case in field_cases(bench, field):
        programs = [case.generate(ROOT, ROOT/'unused', statement) for statement in range(4)]
        assert all(p.proof and p.entry == 'example::Proof' and p.mutate_proof is not None for p in programs)
        assert all(p.source == programs[0].source and p.assets == programs[0].assets for p in programs)
        assert len({json.dumps(p.inputs[0]['public'], sort_keys=True) for p in programs}) == 4
        for statement, program in enumerate(programs):
            assert program.inputs == case.generate(ROOT, ROOT/'unused', statement).inputs
            assert program.changed not in [p.inputs[0]['public'] for p in programs]


def frame(payload):
    return len(payload).to_bytes(8, 'little')+payload


@pytest.mark.parametrize('profile', PROFILES, ids=[p[0] for p in PROFILES])
@pytest.mark.parametrize('coordinate', [0, 2**32+17, 2**63+9, -2, -1])
def test_field_claim_mutation_preserves_all_other_framed_coordinates(bench, profile, coordinate):
    field, _, modulus, _, _, degree, word_bytes, tag, *_ = profile
    first = coordinate % modulus
    words = [first, *(modulus-i-2 for i in range(2*degree-1))]
    claim = b'ZKCV\x00'+bytes([tag])+(2).to_bytes(4, 'little')
    claim += b''.join(x.to_bytes(word_bytes, 'little') for x in words)
    # Another field's vector and a root must be skipped, even at equal element
    # widths. The complete invocation identity and following frames stay exact.
    other_tag = 100 if tag == 94 else 94
    other = b'ZKCV\x00'+bytes([other_tag])+(1).to_bytes(4, 'little')+bytes(16)
    root = b'ZKCV\x00\x21'+bytes(range(32))
    prefix = b'ZKCPRF00'+bytes(range(32))+frame(root)+frame(other)
    proof = prefix+frame(claim)+frame(root)
    program = field_cases(bench, field)[0].generate(ROOT, ROOT/'unused')
    mutated = program.mutate_proof(proof)
    offset = len(prefix)+8+10
    assert len(mutated) == len(proof)
    assert mutated == proof[:offset]+((first+1) % modulus).to_bytes(word_bytes, 'little')+proof[offset+word_bytes:]
    result = [int.from_bytes(mutated[i:i+word_bytes], 'little')
              for i in range(offset, offset+2*degree*word_bytes, word_bytes)]
    assert result == [(first+1) % modulus, *words[1:]]
    assert all(0 <= x < modulus for x in result)
    with pytest.raises(ValueError, match='missing extension claim'):
        program.mutate_proof(prefix)
    short = claim[:10+degree*word_bytes-1]
    with pytest.raises(ValueError, match='missing extension claim'):
        program.mutate_proof(prefix+frame(short))
    with pytest.raises(ValueError, match='truncated proof frame'):
        program.mutate_proof(proof[:len(prefix)+8+len(claim)-1])


@pytest.mark.parametrize('shape,message', [
    ({'field': 'unknown'}, 'unsupported STARK field family'),
    ({'field': 'baby-bear', 'profile': 'goldilocks_quadratic'}, 'field and configuration must match'),
    ({'field': 'goldilocks', 'profile': 'baby_bear_quartic'}, 'field and configuration must match'),
])
def test_stark_family_selection_refuses_unsupported_or_mixed_profiles(bench, shape, message):
    with pytest.raises(ValueError, match=message):
        bench['stark'].library(ROOT, shape | {'height': 8, 'width': 1, 'evaluation_size': 32, 'queries': 8})


@pytest.mark.parametrize('field', [p[0] for p in PROFILES])
def test_octic_air_control_remains_koala_only(bench, field):
    with pytest.raises(ValueError, match='octic AIR control requires KoalaBear'):
        bench['stark'].air(ROOT, {'field': field})


def test_existing_koala_air_stark_and_fri_preparations_are_unchanged(bench):
    # Logical FRI source snapshot, independently checked against pre-policy HEAD:
    # all 31 existing cases at statements
    # zero and one, including source, shape, inputs, assets and refusal inputs.
    rows = []
    for case in bench['coverage'].cases():
        if case.name not in ('air', 'stark', 'fri') or 'field' in case.shape:
            continue
        for statement in (0, 1):
            p = case.generate(ROOT, ROOT/'unused', statement)
            rows.append({'case': vars(case), 'statement': statement, 'source': p.source, 'assets': p.assets,
                         'inputs': p.inputs, 'changed': p.changed, 'entry': p.entry, 'dependencies': p.dependencies,
                         'proof': p.proof, 'oracle': p.oracle,
                         'support': [str(path.relative_to(ROOT)) for path in p.support]})
    assert len(rows) == 62
    encoded = json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()
    assert hashlib.sha256(encoded).hexdigest() == 'b23613c0dabc125ae82901abfc91bad34313baafdc59d99469a522ce4160c2e7'
