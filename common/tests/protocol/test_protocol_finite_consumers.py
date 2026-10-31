"""Finite AIR arithmetic and complete AIR, FRI and machine proof controls."""

from pathlib import Path

import pytest

from entry import Entry, joint_execution
from input_files import decimal_values
from octic_reference import P, ZERO, ONE, add, mul, power
from source_modules import core_packages, library_modules
import test_air_stark as stark
import test_fri as fri
import test_machine_stark as machine
from test_total_callback_selection import compile_entry as compile_counted_entry

ROOT = Path(__file__).resolve().parents[3]
SHARED = library_modules(*core_packages())
AIR = library_modules('relations/air')
FLAGS = [(), ('--no-simplify',), ('--no-finite-bulk',),
         ('--no-simplify', '--no-finite-bulk')]
MODES = ['default', 'no-simplify', 'ordered', 'ordered-no-simplify']

ARITHMETIC = '''module sample;
use zkc::vector::{Vector};
use air::polynomial::{recombine};
domain F = field("koala-bear.ext8-binomial3");
protocol Inspect roles(P)(claims: Vector<F> @P, height: index @P, x: F @P)
    -> (value: F @P) {
  return recombine(claims, height, x);
}
entry fn Demo(inputs: Inspect::Inputs) { return Inspect::run(inputs); }
'''


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
def test_air_recombination_matches_independent_powers(
        toolchain, journal, directory, flags):
    entry = Entry(toolchain, journal, directory, ARITHMETIC, [*AIR, *flags])
    x = [11, 3, 0, 0, 0, 0, 0, 0]
    for count, height in [(0, 0), (1, 8), (5, 0), (5, 8)]:
        claims = [[i + 1, 0, i * i, 0, 0, 0, 0, 0] for i in range(count)]
        if count:
            claims += [ZERO]
        expected = ZERO
        for i, claim in enumerate(claims):
            expected = add(expected, mul(claim, power(x, height * i)))
        inputs = {'claims': claims, 'height': height, 'x': x}
        assert entry.run(f'{count}-{height}', inputs) == decimal_values({'value': expected})


TERMINAL = '''module sample;
use zkc::vector::{Vector};
use fri::{terminal};
domain F = field("koala-bear.ext8-binomial3");
protocol Inspect roles(P)(coefficients: Vector<F> @P, shift: F @P,
    size: index @P, position: index @P) -> (value: F @P) {
  return terminal(coefficients, shift, size, position);
}
entry fn Demo(inputs: Inspect::Inputs) { return Inspect::run(inputs); }
'''


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
def test_fri_terminal_coefficients_and_domain_admission(toolchain, journal, directory, flags):
    # Expose the production helper without changing its body or the public API.
    source = fri.LIBRARY.read_text()
    assert source.count('fn terminal<') == 1
    library = directory / 'fri-terminal.zkc'
    library.write_text(source.replace('fn terminal<', 'pub fn terminal<'))
    entry = Entry(toolchain, journal, directory, TERMINAL,
                  [*SHARED, f'--module=fri={library}', *flags])
    root = pow(1791270792, (1 << 24) // 8, P)
    for label, coefficients in [('empty', []), ('zero', [ZERO, ZERO]),
                                ('constant', [ONE, ZERO]),
                                ('ordered', fri.FULL_DEGREE + [ZERO, ZERO])]:
        for position in [0, 3, 7]:
            x = mul(fri.SHIFT, [pow(root, position, P)] + [0] * 7)
            inputs = {'coefficients': coefficients, 'shift': fri.SHIFT,
                      'size': 8, 'position': position}
            assert entry.run(f'{label}-{position}', inputs) == decimal_values({
                'value': fri.evaluate(coefficients, x)})
    # Empty coefficients must still admit the domain and position.
    for label, changed in [('size', {'size': 3}), ('position', {'position': 8})]:
        entry.run(label, inputs | {'coefficients': []} | changed,
                  refuses='entry-host-run-failed')


PADDING = '''module sample;
use zkc::vector::{Vector};
use fri::{padded};
domain F = field("koala-bear.ext8-binomial3");
protocol Inspect roles(P)(coefficients: Vector<F> @P, count: index @P)
    -> (values: Vector<F> @P) {
  return padded(coefficients, count);
}
entry fn Demo(inputs: Inspect::Inputs) { return Inspect::run(inputs); }
'''


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
def test_fri_padding_preserves_coefficients_and_refuses_oversize(
        toolchain, journal, directory, flags):
    source = fri.LIBRARY.read_text()
    assert source.count('fn padded<') == 1
    library = directory / 'fri-padding.zkc'
    library.write_text(source.replace('fn padded<', 'pub fn padded<'))
    entry = Entry(toolchain, journal, directory, PADDING,
                  [*SHARED, f'--module=fri={library}', *flags])
    for label, coefficients, count in [('empty', [], 4), ('zero', [ZERO], 4),
                                       ('constant', [ONE], 4),
                                       ('trailing-zero', [ONE, ZERO], 4),
                                       ('maximum', fri.FULL_DEGREE, 8)]:
        assert entry.run(label, {'coefficients': coefficients, 'count': count}) == decimal_values(
            {'values': coefficients + [ZERO] * (count - len(coefficients))})
    for label, coefficients, count in [('one-too-many', [ONE, ONE], 1),
                                       ('degree-bound', fri.FULL_DEGREE, 4)]:
        refused = entry.run(label, {'coefficients': coefficients, 'count': count},
                            refuses='entry-host-run-failed')
        role, = joint_execution(refused)['roles']
        assert role['after'][0] == 'stopped'
        assert role['after'][1]['cause'] == ['explicit', {'text': 'reject', 'omitted_bytes': 0}]


REDUCTION = '''module sample;
use zkc::indices as indices;
use zkc::vector::{Vector};


use air::interaction::{Reduction, LogUp, GrandProduct, interactions};
domain F = field("koala-bear");
fn build<R: Reduction<F>>(values: Vector<F>, rows: index,
    gamma: F, delta: F, active: bool) -> (Vector<F>, Vector<F>) {
  let none = indices::empty();
  let channel = if active { indices::append(none, 0) } else { none };
  let arity = if active { indices::append(none, 2) } else { none };
  let degrees = if active { indices::append(none, 1) } else { none };
  let records = interactions(1, degrees, channel, channel, arity, degrees, degrees);
  let challenges = kernel<F>("vector.append",
    kernel<F>("vector.append", kernel<F>("vector.empty"), gamma), delta);
  return R::build(records, values, rows, challenges);
}
protocol Inspect<R: Reduction<F>> roles(P)(values: Vector<F> @P, rows: index @P,
    gamma: F @P, delta: F @P, active: bool @P)
    -> (columns: Vector<F> @P, claims: Vector<F> @P) {
  let built @P = build<R>(values, rows, gamma, delta, active);
  return (columns = built.0, claims = built.1);
}
entry fn Demo(inputs: Inspect<LogUp<F>>::Inputs) { return Inspect<LogUp<F>>::run(inputs); }
'''


@pytest.mark.parametrize('flags', FLAGS, ids=MODES)
@pytest.mark.parametrize('reduction', ['LogUp', 'GrandProduct'])
def test_interaction_product_admission_and_inactive_rows(
        toolchain, journal, directory, flags, reduction):
    source = REDUCTION.replace('entry fn Demo(inputs: Inspect<LogUp<F>>::Inputs) { return Inspect<LogUp<F>>::run(inputs); }',
                               f'entry fn Demo(inputs: Inspect<{reduction}<F>>::Inputs) {{ return Inspect<{reduction}<F>>::run(inputs); }}')
    entry, sites = compile_counted_entry(toolchain, journal, directory, source,
                                        flags, modules=AIR)
    # Observe the production library's nonzero fold, including generic usage
    # inference. Correct values alone would not detect a lost bulk selection.
    assert bool(sites['vector.product']) == ('--no-finite-bulk' not in flags)
    # fp = [7, 11]. The second denominator is zero before Boolean gating.
    inputs = {'values': [1, 5, 3, 3, 1, 0], 'rows': 2,
              'gamma': 11, 'delta': 2, 'active': True}
    reciprocal = pow(4, -1, P)
    expected = ({'columns': [reciprocal, 0, reciprocal, reciprocal], 'claims': [reciprocal]}
                if reduction == 'LogUp' else {'columns': [4, 4], 'claims': [4]})
    assert entry.run('inactive-zero', inputs) == decimal_values(expected)
    assert entry.run('no-records', inputs | {'values': [], 'active': False}) == {
        'columns': [], 'claims': []}
    assert entry.run('no-records-no-rows', inputs | {
        'values': [], 'active': False, 'rows': 0}) == {'columns': [], 'claims': []}
    for label, changed in [
        ('active-zero', {'values': [1, 5, 3, 3, 1, 1]}),
        ('shape-before-zero', {'values': [1, 5, 3, 3, 1]}),
    ]:
        refused = entry.run(label, inputs | changed, refuses='entry-host-run-failed')
        cause = joint_execution(refused)['roles'][0]['after'][1]['cause']
        assert cause[0] == 'explicit'
        assert cause[1]['text'] == ('abort' if label == 'active-zero' else 'reject')


@pytest.mark.parametrize('flags', [('--no-finite-bulk',),
                                  ('--no-simplify', '--no-finite-bulk')],
                         ids=['ordered', 'ordered-no-simplify'])
@pytest.mark.parametrize('family', ['fri', 'air', 'logup', 'grand-product'])
def test_complete_protocols_with_ordered_finite_consumers(
        toolchain, journal, directory, flags, family):
    options = list(flags)
    if family == 'fri':
        package, pin = fri.compile_entry(toolchain, journal, directory, flags=options,
                                        terminal_log=1, log_size=6, queries=4)
        for name, coefficients in [('zero', []), ('full-degree', fri.FULL_DEGREE * 2)]:
            producer = fri.request(journal, name, fri.word(coefficients, 6), queries=4)
            verifier = fri.request(journal, name + '-verify', queries=4)
            proof = directory / f'{name}.proof'
            made = journal.json([toolchain.runtime, '--json', 'prove', f'--package={package}',
                                 f'--sha256={pin}', *producer, f'--output={proof}'])
            checked = journal.json([toolchain.runtime, '--json', 'verify', f'--package={package}',
                                    f'--sha256={pin}', *verifier, f'--proof={proof}'])
            assert made['status'] == 'produced' and checked['status'] == 'accepted'
            stark.check_fri_frames(fri.messages(proof.read_bytes()), rounds=3,
                                   queries=4, log_size=6, terminal_log=1)
    elif family == 'air':
        package, pin = stark.compile_entry(toolchain, journal, directory, flags=options)
        public, witness = stark.inputs()
        machine.prove_and_verify(toolchain, journal, directory, package, pin,
                                 'recurrence', (public, witness))
    else:
        entry = 'ProofLogUp' if family == 'logup' else 'ProofProduct'
        package, pin = machine.compile_entry(toolchain, journal, directory, entry, flags=options)
        machine.check_transcript_schedule(package)
        for name in ['store-load', 'arithmetic-only']:
            machine.prove_and_verify(toolchain, journal, directory, package, pin,
                                     name, machine.requests(name))
