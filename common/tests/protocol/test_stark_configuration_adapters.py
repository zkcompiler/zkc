"""Outer row adapters against independently committed row-major tables."""

import pytest

from entry import Entry, joint_execution
from source_modules import library_modules


SOURCE = '''module sample;
use stark::configurations::PRESET::{Poseidon2};
use zkc::vector::{Vector};
use zkc::indices::{Indices};
use zkc::oracle::{Root, Path};
use zkc::oracle as oracle;

protocol Run roles(P)(word: Vector<Poseidon2::VALUE> @P,
    positions: Indices @P, width: index @P, height: index @P)
    -> (root: Root<Poseidon2::ROW_COMMITMENT> @P,
        reference_root: Root<Poseidon2::ROW_COMMITMENT> @P,
        rows: Vector<Poseidon2::VALUE> @P,
        reference_rows: Vector<Poseidon2::VALUE> @P,
        proof: Path<Poseidon2::ROW_COMMITMENT> @P,
        reference_proof: Path<Poseidon2::ROW_COMMITMENT> @P, accepted: bool @P) {
  let committed @P = Poseidon2::commit_KIND(word, width);
  let reference @P = oracle::commit<Poseidon2::ROW_COMMITMENT>(word, width);
  let opened @P = Poseidon2::open_KIND(committed.1, positions, height);
  let reference_opened @P = oracle::open_many<Poseidon2::ROW_COMMITMENT>(reference.1, positions);
  let accepted @P = Poseidon2::check_KIND(committed.0, width, height, positions, opened.0, opened.1);
  return (root = committed.0, reference_root = reference.0,
    rows = opened.0, reference_rows = reference_opened.0,
    proof = opened.1, reference_proof = reference_opened.1, accepted = accepted);
}
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }

protocol AdapterOpening roles(P)(word: Vector<Poseidon2::VALUE> @P,
    positions: Indices @P, width: index @P, height: index @P)
    -> (rows: Vector<Poseidon2::VALUE> @P,
        proof: Path<Poseidon2::ROW_COMMITMENT> @P) {
  let committed @P = Poseidon2::commit_KIND(word, width);
  let opened @P = Poseidon2::open_KIND(committed.1, positions, height);
  return (rows = opened.0, proof = opened.1);
}
entry fn AdapterOnly(inputs: AdapterOpening::Inputs) { return AdapterOpening::run(inputs); }
'''


@pytest.mark.parametrize('preset,degree,modulus', [
    ('baby_bear_quartic', 4, 2013265921),
    ('goldilocks_quadratic', 2, 18446744069414584321),
    ('koala_bear_quartic', 4, 2130706433),
])
@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
@pytest.mark.parametrize('kind', ['base', 'extension'])
def test_outer_rows_preserve_roots_rows_and_opening_proofs(
        toolchain, journal, directory, preset, degree, modulus, flags, kind):
    source = (SOURCE.replace('PRESET', preset).replace('KIND', kind)
              .replace('ROW_COMMITMENT', 'BaseRows' if kind == 'base' else 'ExtensionRows')
              .replace('VALUE', 'Base' if kind == 'base' else 'Extension'))
    entry = Entry(toolchain, journal, directory, source,
                  [*library_modules(f'arguments/stark/configurations/{preset}'), *flags])
    for height in (1, 4):
        for width in (1, 2, 3):
            word = [[str(((i + 1) * 193 + j * (modulus // 17)) % modulus)
                     for j in range(degree)] for i in range(width * height)]
            if kind == 'base':
                word = [value[0] for value in word]
            # Unsorted, duplicate requests retain complete rows in request order.
            positions = [height - 1, 0, height - 1]
            inputs = {'word': word, 'positions': positions, 'width': width, 'height': height}
            result = entry.run(f'{height}-{width}', inputs)
            assert result['root'] == result['reference_root']
            assert result['proof'] == result['reference_proof']
            expected = [value for k in positions for value in word[k * width:(k + 1) * width]]
            assert result['rows'] == result['reference_rows'] == expected
            assert result['accepted'] is True

    refusal_directory = directory / 'adapter-only'
    refusal_directory.mkdir()
    adapter = Entry(toolchain, journal, refusal_directory, source,
                    [*library_modules(f'arguments/stark/configurations/{preset}'), *flags],
                    entry='AdapterOnly')
    for name, invalid in [('partial-row', {'word': word[:-1]}),
                          ('empty-word', {'word': []}),
                          ('out-of-range', {'positions': [height]})]:
        refused = adapter.run(name, inputs | invalid, refuses='entry-host-run-failed')
        assert joint_execution(refused)['outcome'] == ['participant-stopped', 0]
