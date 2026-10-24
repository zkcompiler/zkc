"""Natural FRI pair leaves against independently arranged row tables."""

import pytest

from entry import Entry, joint_execution
from source_modules import library_modules


SOURCE = '''module sample;
use stark::configurations::PRESET::{Poseidon2};
use zkc::vector::{Vector};
use zkc::indices::{Indices};
use zkc::oracle::{Root, Path};
use zkc::oracle as oracle;

protocol Run roles(P)(word: Vector<Poseidon2::Extension> @P,
    paired: Vector<Poseidon2::Extension> @P, positions: Indices @P, half: index @P)
    -> (root: Root<Poseidon2::ExtensionRows> @P,
        reference_root: Root<Poseidon2::ExtensionRows> @P,
        rows: Vector<Poseidon2::Extension> @P,
        reference_rows: Vector<Poseidon2::Extension> @P,
        proof: Path<Poseidon2::ExtensionRows> @P,
        reference_proof: Path<Poseidon2::ExtensionRows> @P, accepted: bool @P) {
  let committed @P = Poseidon2::commit_pairs(word);
  let reference @P = oracle::commit<Poseidon2::ExtensionRows>(paired, 2);
  let opened @P = Poseidon2::open_pairs(committed.1, positions, half);
  let reference_opened @P = oracle::open_many<Poseidon2::ExtensionRows>(reference.1, positions);
  let accepted @P = Poseidon2::check_pairs(committed.0, half, positions, opened.0, opened.1);
  return (root = committed.0, reference_root = reference.0,
    rows = opened.0, reference_rows = reference_opened.0,
    proof = opened.1, reference_proof = reference_opened.1, accepted = accepted);
}
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }

protocol AdapterOpening roles(P)(word: Vector<Poseidon2::Extension> @P,
    positions: Indices @P, half: index @P)
    -> (rows: Vector<Poseidon2::Extension> @P,
        proof: Path<Poseidon2::ExtensionRows> @P) {
  let committed @P = Poseidon2::commit_pairs(word);
  let opened @P = Poseidon2::open_pairs(committed.1, positions, half);
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
def test_pair_leaves_preserve_roots_rows_and_opening_proofs(
        toolchain, journal, directory, preset, degree, modulus, flags):
    entry = Entry(toolchain, journal, directory, SOURCE.replace('PRESET', preset),
                  [*library_modules(f'arguments/stark/configurations/{preset}'), *flags])
    for half in (1, 4):
        word = [[str(((i + 1) * 193 + j * (modulus // 17)) % modulus)
                 for j in range(degree)] for i in range(2 * half)]
        # Natural pair k holds the values at k and k + half. Deliberately
        # unsorted, duplicate requests must retain their order in the opening.
        paired = [value for k in range(half) for value in (word[k], word[k + half])]
        positions = [half - 1, 0, half - 1]
        inputs = {'word': word, 'paired': paired, 'positions': positions, 'half': half}
        result = entry.run(f'half-{half}', inputs)
        assert result['root'] == result['reference_root']
        assert result['proof'] == result['reference_proof']
        expected = [value for k in positions for value in (word[k], word[k + half])]
        assert result['rows'] == result['reference_rows'] == expected
        assert result['accepted'] is True

    refusal_directory = directory / 'adapter-only'
    refusal_directory.mkdir()
    adapter = Entry(toolchain, journal, refusal_directory, SOURCE.replace('PRESET', preset),
                    [*library_modules(f'arguments/stark/configurations/{preset}'), *flags],
                    entry='AdapterOnly')
    inputs = {key: inputs[key] for key in ('word', 'positions', 'half')}
    for name, invalid in [('odd-word', {'word': word[:-1]}),
                          ('empty-word', {'word': []}),
                          ('out-of-range', {'positions': [half]})]:
        refused = adapter.run(name, inputs | invalid, refuses='entry-host-run-failed')
        assert joint_execution(refused)['outcome'] == ['participant-stopped', 0]
