"""Consistent malicious provers stopped by the machine argument's verifier.

Mutations change prover computations before commitment, so all hashes and
transcript challenges remain consistent. Exact source guards identify which
verifier obligation rejects. Honest controls retain the modified prover.
"""
from input_files import input_files
from test_fri import emitted_guard_sites
import json
import re

import pytest

from test_machine_stark import (EXAMPLE, FIXTURES, alter_vector, assert_refused,
                               compile_entry, prepare, prove_and_verify, requests)

TRUNCATE = ('air::polynomial',
            '  require boolean::negate(less(capacity, actual));\n'
            '  let padded = concat(coefficients, fill<F>(0, capacity - actual));',
            '  let padded = zkc::vector::slice(concat(coefficients, fill<F>(0, capacity)), 0, capacity);')


def guards(package):
    """Resolve only the machine protocol's guards through shared FRI wrappers."""
    emitted = json.loads(package.read_text())['original']
    roster = [('profile', 'role00000001', 0), ('prover-profile', 'role00000000', 0)]
    roster += [(name, 'role00000001', 0) for name in ('closure', 'identity', 'fri')]
    roster += [(name, 'role00000001', 1) for name in ('base', 'auxiliary', 'quotient', 'deep')]
    return emitted_guard_sites(emitted, {'': roster})


def stopped_at(report, package, name):
    stop = report['execution']['stop']
    assert stop['role'] == 'role00000001' and stop['kind'] == 'Explicit("reject")', stop
    chain = re.fullmatch(r'(?:apply_\d+_)+((?:s\d+_)*s\d+)', stop['site'])[1]
    assert chain == guards(package)[name], stop


def rejected_proof(toolchain, journal, directory, package, pin, pair, name, guard):
    producer = input_files(journal, name + '-prover', public=pair[0], witness=pair[1])
    verifier = input_files(journal, name + '-verifier', public=pair[0])
    proof = directory / (name + '.proof')
    made = journal.json([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}'])
    assert made['status'] == 'produced'
    result = journal.attempt([toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}'])
    stopped_at(assert_refused(result), package, guard)


@pytest.mark.parametrize('entry', ['ProofLogUp', 'ProofProduct'])
def test_machine_false_quotient_is_rejected_at_identity(toolchain, journal, directory, entry):
    package, pin = compile_entry(toolchain, journal, directory, entry, edits=[TRUNCATE])
    prove_and_verify(toolchain, journal, directory, package, pin, 'honest', requests('store-load'))
    pair = requests('store-load')
    # Row zero is an add, so changing only its clock violates CPU initial and
    # transition assertions while leaving all program and RAM tuples intact.
    pair[1]['cpu'] = alter_vector(pair[1]['cpu'], 1)
    rejected_proof(toolchain, journal, directory, package, pin, pair, 'false-clock', 'identity')


@pytest.mark.parametrize('entry', ['ProofLogUp', 'ProofProduct'])
def test_machine_committed_false_auxiliary_is_rejected(toolchain, journal, directory, entry):
    # Replace one auxiliary column value after construction, keeping the honest
    # final claims. Commit, quotient and open the changed column consistently.
    old = ('    let built = R::build(layout.records, values, height, challenges);\n'
           '    let lde = extend_columns(built.0, layout.reduction.columns, height, shift, size);\n'
           '    Auxiliary { columns: built.0, lde, claims: built.1 }')
    new = ('    let built = R::build(layout.records, values, height, challenges);\n'
           '    let changed = concat(fill<Extension>(vector::get(built.0, 0) + 1, 1),\n'
           '      slice(built.0, 1, length(built.0) - 1));\n'
           '    let lde = extend_columns(changed, layout.reduction.columns, height, shift, size);\n'
           '    Auxiliary { columns: changed, lde, claims: built.1 }')
    package, pin = compile_entry(toolchain, journal, directory, entry,
                                edits=[TRUNCATE, ('stark::whole_bundle', old, new)])
    rejected_proof(toolchain, journal, directory, package, pin, requests('store-load'),
                   'false-auxiliary', 'identity')


def test_machine_known_configuration_binds_a_consistent_other_execution(toolchain, journal, directory):
    # Add 11 then -2 gives the same final state as the configured add 10 then
    # -1. The prover uses those other instructions and their honest witness;
    # all polynomial and bus identities hold for that other program.
    original = json.loads((FIXTURES / 'arithmetic-only/run.json').read_text())
    original[1][0][1] = '11'
    original[1][1][1] = str(prepare.machine.P - 2)
    foreign = prepare.run_inputs(original)
    pair = requests('arithmetic-only')
    pair = pair[0], foreign[1]
    source = (EXAMPLE / 'main.zkc').read_text()
    old = '  let statementP @P = statement(initial, final, cpu_height, program_height, instructions,'
    new = '  let statementP @P = statement(initial, final, cpu_height, program_height, other_program(instructions),'
    assert source.count(old) == 1
    source = source.replace(old,new) + r"""
fn other_program(values: Vector<Base>) -> Vector<Base> {
  let prefix = kernel<Base>("vector.slice", values, 0, 2);
  let first = kernel<Base>("vector.get", values, 2);
  let middle = kernel<Base>("vector.slice", values, 3, 2);
  let second = kernel<Base>("vector.get", values, 5);
  let tail = kernel<Base>("vector.slice", values, 6, 6);
  let start = kernel<Base>("vector.append", prefix, first + 1);
  let next = kernel<Base>("vector.concat", start, middle);
  let changed = kernel<Base>("vector.append", next, second - 1);
  return kernel<Base>("vector.concat", changed, tail);
}
"""
    checked = directory / 'checked'
    checked.mkdir()
    package, pin = compile_entry(toolchain, journal, checked, 'ProofLogUp', source=source)
    rejected_proof(toolchain, journal, directory, package, pin, pair, 'foreign-program', 'identity')
    # Ablation isolates the known-slot obligation: disabling just that check
    # admits this same internally consistent false configuration.
    disabled = directory / 'disabled'
    disabled.mkdir()
    edit = ('stark::whole_bundle', '    both(known, combined == recombine(opened.quotient, height, zeta))',
            '    combined == recombine(opened.quotient, height, zeta)')
    package, pin = compile_entry(toolchain, journal, disabled, 'ProofLogUp', source=source, edits=[edit])
    prove_and_verify(toolchain, journal, directory, package, pin, 'without-known-slot-check', pair)
