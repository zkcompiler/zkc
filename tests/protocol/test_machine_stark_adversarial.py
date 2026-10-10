"""Consistent malicious provers stopped by the machine argument's verifier.

Mutations change prover computations before commitment, so all hashes and
transcript challenges remain consistent. Exact source guards identify which
verifier obligation rejects. Honest controls retain the modified prover.
"""
import json
import re

import pytest

from test_machine_stark import (EXAMPLE, FIXTURES, alter_vector, assert_refused,
                               compile_entry, prepare, prove_and_verify, requests)

TRUNCATE = ('air_polynomial',
            '  require not(less(capacity, actual));\n'
            '  let padded = concat(coefficients, fill<F>(0, capacity - actual));',
            '  let padded = slice(concat(coefficients, fill<F>(0, capacity)), 0, capacity);')


def guards(package):
    """Read guard sites from this exact package, using the enclosing protocol.

    The entry applies ThreeTableArgument once. The latter has nine guards;
    helper protocols cannot contribute to this set. No fixed generated names
    or site numbers are assumed.
    """
    emitted = json.loads(package.read_text())['original']
    functions, current = {}, None
    for line in emitted.splitlines():
        header = re.search(r'"(protocol|local)\.func"\(\) <\{.*sym_name = "(\w+)"', line)
        if header:
            current = functions.setdefault(header[2], {'guards': [], 'applies': []}) if header[1] == 'protocol' else None
        if current is None:
            continue
        guard = re.search(r'"protocol\.guard".*owner = "(\w+)", site = "(s\d+)"', line)
        if guard:
            current['guards'].append(guard.groups())
        applied = re.search(r'"protocol\.apply".*callee = @(\w+),.*site = "(s\d+)"', line)
        if applied:
            current['applies'].append(applied.groups())
    (entry,) = [f for f in functions.values() if not f['guards'] and len(f['applies']) == 1]
    ((symbol, call),) = entry['applies']
    sites = functions[symbol]['guards']
    assert [owner for owner, _ in sites] == [
        'role00000001', 'role00000000', *(['role00000001'] * 7)]
    names = ['profile', 'prover-profile', 'closure', 'identity', 'fri', 'base', 'auxiliary', 'quotient', 'deep']
    return {name: call + '_' + site for name, (_, site) in zip(names, sites, strict=True)}


def stopped_at(report, package, name):
    stop = report['execution']['stop']
    assert stop['role'] == 'role00000001' and stop['kind'] == 'Explicit("reject")', stop
    chain = re.fullmatch(r'(?:apply_\d+_)+((?:s\d+_)*s\d+)', stop['site'])[1]
    assert chain == guards(package)[name], stop


def rejected_proof(toolchain, journal, directory, package, pin, pair, name, guard):
    producer = journal.write(name + '-prover.json', pair[0])
    verifier = journal.write(name + '-verifier.json', pair[1])
    proof = directory / (name + '.proof')
    made = journal.json([toolchain.runtime, 'prove', package, pin, producer, proof])
    assert made['status'] == 'produced'
    result = journal.attempt([toolchain.runtime, 'verify', package, pin, verifier, proof])
    stopped_at(assert_refused(result), package, guard)


@pytest.mark.parametrize('entry', ['ProofLogUp', 'ProofProduct'])
def test_machine_false_quotient_is_rejected_at_identity(toolchain, journal, directory, entry):
    package, pin = compile_entry(toolchain, journal, directory, entry, edits=[TRUNCATE])
    prove_and_verify(toolchain, journal, directory, package, pin, 'honest', requests('store-load'))
    pair = requests('store-load')
    # Row zero is an add, so changing only its clock violates CPU initial and
    # transition assertions while leaving all program and RAM tuples intact.
    pair[0]['inputs']['cpu'] = alter_vector(pair[0]['inputs']['cpu'], 1)
    rejected_proof(toolchain, journal, directory, package, pin, pair, 'false-clock', 'identity')


@pytest.mark.parametrize('entry', ['ProofLogUp', 'ProofProduct'])
def test_machine_committed_false_auxiliary_is_rejected(toolchain, journal, directory, entry):
    # Replace one auxiliary column value after construction, keeping the honest
    # final claims. Commit, quotient and open the changed column consistently.
    old = ('    let built = R::build(layout.records, values, height, challenges);\n'
           '    let lde = extend_columns(built.0, layout.reduction.columns, height, shift, size);\n'
           '    Auxiliary { columns: built.0, lde, claims: built.1 }')
    new = ('    let built = R::build(layout.records, values, height, challenges);\n'
           '    let changed = concat(fill<Extension>(get(built.0, 0) + 1, 1),\n'
           '      slice(built.0, 1, length(built.0) - 1));\n'
           '    let lde = extend_columns(changed, layout.reduction.columns, height, shift, size);\n'
           '    Auxiliary { columns: changed, lde, claims: built.1 }')
    package, pin = compile_entry(toolchain, journal, directory, entry,
                                edits=[TRUNCATE, ('air_bundle', old, new)])
    rejected_proof(toolchain, journal, directory, package, pin, requests('store-load'),
                   'false-auxiliary', 'identity')


def test_machine_known_configuration_binds_a_consistent_other_execution(toolchain, journal, directory):
    # Add 11 then -2 gives the same final state as the configured add 10 then
    # -1. The prover uses those other instructions and their honest witness;
    # all polynomial and bus identities hold for that other program.
    original = json.loads((FIXTURES / 'arithmetic-only/run.json').read_text())
    original[1][0][1] = '11'
    original[1][1][1] = str(prepare.machine.P - 2)
    foreign = prepare.run_requests(original)
    pair = requests('arithmetic-only')
    pair[0]['inputs'] = foreign[0]['inputs']
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
    edit = ('air_bundle', '    both(known, combined == recombine(opened.quotient, height, zeta))',
            '    combined == recombine(opened.quotient, height, zeta)')
    package, pin = compile_entry(toolchain, journal, disabled, 'ProofLogUp', source=source, edits=[edit])
    prove_and_verify(toolchain, journal, directory, package, pin, 'without-known-slot-check', pair)
