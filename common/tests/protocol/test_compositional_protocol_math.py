"""Small protocol arithmetic slices through public projects and ordinary Hosts.

Independent integer references establish values and row residuals, not complete
FRI or LogUp proofs. Compiler modes exercise the same authored consumers.
"""

import json
from pathlib import Path
import random
from project import project_inputs

import pytest

from entry import Entry
from input_files import decimal_values

ROOT = Path(__file__).resolve().parents[3]
PROJECTS = ROOT / 'examples/projects'
KOALA_BEAR = 2130706433
BLS_SCALAR = 52435875175126190479447740508185965837690552500527637822603658699938581184513
FLAGS = [(), ('--no-simplify',), ('--no-finite-bulk',),
         ('--no-simplify', '--no-finite-bulk')]
MODES = ['default', 'no-simplify', 'no-finite-bulk', 'both']


class ProjectEntry(Entry):
    """Select an authored project while reusing Entry's Host/input/journal path."""

    def __init__(self, toolchain, journal, directory, project, selector, flags):
        self.tools, self.journal, self.directory = toolchain, journal, directory
        self.package = directory / f'{selector.replace("::", ".")}.zkpkg'
        report = journal.json([
            toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
            f'--project={PROJECTS / project / "zkc.toml"}', selector,
            f'--output={self.package}', *flags,
        ])
        self.pin = report['package_sha256']


def published_inputs(project, selector):
    path = PROJECTS / project / 'inputs' / selector.replace('::', '.') / 'P.json'
    return json.loads(path.read_text())


def project_modules(project):
    """Import the authored modules into small adapters without copying source."""
    path = PROJECTS / project / 'zkc.toml'
    modules, _ = project_inputs(path)
    return [f'--module={name}={source}' for name, source in modules.items()]


def evaluate(coefficients, point, modulus):
    """Horner evaluation of a coefficient list, independent of native kernels."""
    value = 0
    for coefficient in reversed(coefficients):
        value = (value * point + coefficient) % modulus
    return value


def polynomial_fold(coefficients, size, shift, beta):
    """Fold coefficients first, then evaluate on squared coset points."""
    p = KOALA_BEAR
    # The installed KoalaBear convention's primitive 2^24 root. Its order is
    # checked here; neither evaluations nor expected folds come from a kernel.
    root = pow(1791270792, (1 << 24) // size, p)
    assert pow(root, size, p) == 1
    assert pow(root, size // 2, p) == p - 1
    points = [shift * pow(root, i, p) % p for i in range(size)]
    values = [evaluate(coefficients, point, p) for point in points]
    folded_coefficients = [
        (coefficients[i] + beta * (coefficients[i + 1] if i + 1 < len(coefficients) else 0)) % p
        for i in range(0, len(coefficients), 2)
    ]
    folded = [evaluate(folded_coefficients, point * point % p, p)
              for point in points[:size // 2]]
    inputs = {
        'low': values[:size // 2], 'high': values[size // 2:],
        'inverse_x': [pow(point, -1, p) for point in points[:size // 2]],
        'next': folded, 'beta': beta, 'inverse_two': pow(2, -1, p),
    }
    return inputs, values, folded


FRI_KERNEL_ADAPTER = '''module sample;
use zkc::vector::{Vector};
domain F = field("koala-bear");
fn fold_word(word: Vector<F>, shift: F, beta: F) -> Vector<F> {
  return kernel<F>("poly.even_odd_fold", word, shift, beta);
}
protocol Compare roles(P)(word: Vector<F> @P, shift: F @P, beta: F @P)
    -> (folded: Vector<F> @P) { return fold_word(word, shift, beta); }
run Demo = Compare;
'''


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
def test_fri_pairs_match_polynomial_and_existing_kernel(toolchain, journal, directory, flags):
    entry = ProjectEntry(toolchain, journal, directory, 'fri-fold', 'fri_fold::Demo', flags)
    kernel_dir = directory / 'kernel'
    kernel_dir.mkdir()
    kernel = Entry(toolchain, journal, kernel_dir, FRI_KERNEL_ADAPTER,
                   [f'--module=fri={ROOT}/libraries/fri/lib.zkc', *flags])

    fixture, _, folded = polynomial_fold([3, 2, 1, 4], 4, 1, 5)
    assert folded == [34, KOALA_BEAR - 8]
    assert decimal_values(fixture) == published_inputs('fri-fold', 'fri_fold::Demo')
    rng = random.Random(731)
    cases = [
        ('published', [3, 2, 1, 4], 4, 1, 5),
        ('constant', [KOALA_BEAR - 7], 2, 3, 19),
        ('odd-coefficient-count', [rng.randrange(KOALA_BEAR) for _ in range(7)], 8, 9, 23),
        ('full-degree', [rng.randrange(KOALA_BEAR) for _ in range(16)], 16, 11, KOALA_BEAR - 2),
        ('even-part', [8, 9, 10, 11, 12], 8, 5, 0),
    ]
    for label, coefficients, size, shift, beta in cases:
        inputs, values, expected = polynomial_fold(coefficients, size, shift, beta)
        result = entry.run(label, inputs)
        assert result == decimal_values({'folded': expected, 'residuals': [0] * (size // 2)})
        assert kernel.run(label + '-kernel', {'word': values, 'shift': shift, 'beta': beta}) == {
            'folded': result['folded']}

        # A changed next-layer value has a localized, signed residual.
        changed = list(expected)
        changed[-1] = (changed[-1] + 1) % KOALA_BEAR
        assert entry.run(label + '-next', inputs | {'next': changed}) == decimal_values({
            'folded': expected, 'residuals': [0] * (len(expected) - 1) + [KOALA_BEAR - 1]})

    assert entry.run('empty', {'low': [], 'high': [], 'inverse_x': [], 'next': [],
                              'beta': 5, 'inverse_two': pow(2, -1, KOALA_BEAR)}) == {
        'folded': [], 'residuals': []}


def tuple_fingerprints(rows, delta):
    # Explicit powers and a sum, rather than the source's ordered pair-state fold.
    return [sum(value * pow(delta, k, KOALA_BEAR) for k, value in enumerate(row)) % KOALA_BEAR
            for row in rows]


def logup_reference(rows, counts, reciprocals, gamma, delta):
    assert len(rows) == len(counts) == len(reciprocals)
    fingerprints = tuple_fingerprints(rows, delta)
    raw = [(gamma - value) % KOALA_BEAR for value in fingerprints]
    return {
        'fingerprints': fingerprints,
        'denominators': [(count * value + 1 - count) % KOALA_BEAR
                         for count, value in zip(counts, raw)],
        'reciprocal_residuals': [(count * (reciprocal * value - 1)) % KOALA_BEAR
                                for count, reciprocal, value in zip(counts, reciprocals, raw)],
        'boolean_residuals': [count * (count - 1) % KOALA_BEAR for count in counts],
    }


def logup_inputs(rows, counts, reciprocals, gamma, delta):
    arity = len(rows[0]) if rows else 0
    assert all(len(row) == arity for row in rows)
    assert len(rows) == len(counts) == len(reciprocals)
    return {'tuple_values': [value for row in rows for value in row], 'arity': arity,
            'counts': counts, 'reciprocals': reciprocals, 'gamma': gamma, 'delta': delta}


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
def test_logup_rows_match_independent_compression_and_residuals(toolchain, journal, directory, flags):
    entry = ProjectEntry(toolchain, journal, directory, 'logup-rows', 'logup_rows::Demo', flags)
    p = KOALA_BEAR
    fixture_rows = [[1, 3], [4, 2], [5, 3]]
    fixture_counts = [1, 1, 0]
    fixture_reciprocals = [pow(4, -1, p), pow(3, -1, p), 0]
    fixture = logup_inputs(fixture_rows, fixture_counts, fixture_reciprocals, 11, 2)
    assert decimal_values(fixture) == published_inputs('logup-rows', 'logup_rows::Demo')
    assert entry.run('published', fixture) == decimal_values({
        'fingerprints': [7, 8, 11], 'denominators': [4, 3, 1],
        'reciprocal_residuals': [0, 0, 0], 'boolean_residuals': [0, 0, 0]})

    changed = [(fixture_reciprocals[0] + 1) % p, fixture_reciprocals[1], 0]
    perturbed = logup_reference(fixture_rows, fixture_counts, changed, 11, 2)
    assert perturbed['reciprocal_residuals'] == [4, 0, 0]
    assert entry.run('perturbed-reciprocal', fixture | {'reciprocals': changed}) == decimal_values(perturbed)

    rng = random.Random(947)
    cases = [
        ('coordinate-order', [[2, 7, 11], [11, 7, 2]], [1, 1], 131, 3),
        ('zero-compression', [[2, 7, 11], [11, 7, 2]], [1, 1], 17, 0),
        ('modular', [[rng.randrange(p) for _ in range(5)] for _ in range(7)],
         [1, 0, 1, 1, 0, 1, 1], p - 17, p - 9),
        ('empty-tuples', [[], []], [1, 0], 11, 2),
        ('inactive-zero-denominator', [[5, 3]], [0], 11, 2),
        # A reciprocal equation can vanish while the Boolean equation does not.
        ('nonboolean-count', [[1, 3]], [2], 11, 2),
        ('empty-rows', [], [], 11, 2),
    ]
    for label, rows, counts, gamma, delta in cases:
        fingerprints = tuple_fingerprints(rows, delta)
        reciprocals = [pow((gamma - value) % p, -1, p) if count else 0
                       for count, value in zip(counts, fingerprints)]
        expected = logup_reference(rows, counts, reciprocals, gamma, delta)
        assert expected['reciprocal_residuals'] == [0] * len(rows)
        if label == 'coordinate-order':
            assert fingerprints == [122, 50]
        if label == 'nonboolean-count':
            assert expected['boolean_residuals'] == [2]
        if label == 'inactive-zero-denominator':
            assert fingerprints == [gamma] and expected['denominators'] == [1]
        inputs = logup_inputs(rows, counts, reciprocals, gamma, delta)
        if not rows:
            inputs['arity'] = 4  # Zero rows need no tuple coordinates at any arity.
        assert entry.run(label, inputs) == decimal_values(expected)


WEIGHTS_ADAPTER = '''module sample;
use logup_rows::{compression_weights};
use zkc::field_array::{Array};
domain Fr = field("bls12-381.fr");
protocol Inspect roles(P)(delta: Fr @P) -> (weights: Array<Fr, 4> @P) {
  return compression_weights(delta);
}
run Demo = Inspect;
'''


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
def test_fixed_compression_weights_project_and_public_import(toolchain, journal, directory, flags):
    entry = ProjectEntry(toolchain, journal, directory, 'logup-rows',
                         'logup_rows::CompressionWeights', flags)
    adapter_dir = directory / 'imported'
    adapter_dir.mkdir()
    imported = Entry(toolchain, journal, adapter_dir, WEIGHTS_ADAPTER,
                     [*project_modules('logup-rows'), *flags])
    assert published_inputs('logup-rows', 'logup_rows::CompressionWeights') == {'delta': '2'}
    for delta, expected in [(2, [1, 2, 4, 8]), (0, [1, 0, 0, 0]),
                            (BLS_SCALAR - 1, [1, BLS_SCALAR - 1, 1, BLS_SCALAR - 1])]:
        assert expected == [pow(delta, k, BLS_SCALAR) for k in range(4)]
        output = decimal_values({'weights': expected})
        assert entry.run(f'weights-{delta}', {'delta': delta}) == output
        assert imported.run(f'imported-weights-{delta}', {'delta': delta}) == output
