"""The accumulator-machine relation and its staged reductions on both evaluators.

The adapter in compiler/adapters/accumulator-machine runs an imperative
reference interpreter and lays its records out as Bundle carriers; it never
evaluates the relation. Here the C++ and Rust Bundle evaluators admit and
evaluate those carriers independently, and their replies must be identical.
Honest executions satisfy the relation. Each mutation names the exact failing
assertion rows, unbalanced channel tuples, range failures or refusal, worked
out by hand from the machine's rules rather than taken from either evaluator.
Agreement on these cases is evidence about these carriers, not a proof of the
relation's adequacy or of any reduction's soundness.
"""
from copy import deepcopy
import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
ADAPTER = ROOT / 'compiler/adapters/accumulator-machine'
sys.path.insert(0, str(ADAPTER))

import accumulator_machine as machine  # noqa: E402
import interaction_reductions as reductions  # noqa: E402
import regenerate  # noqa: E402
from ring_arena import (BASE, EXTENSION, ONE, P, Refusal, add, compact, decode, encode,  # noqa: E402
                        inverses, mul, scalar, sub)

FIXTURES = ADAPTER / 'fixtures'
BUNDLE, NAMES = machine.machine_bundle()
LOGUP, PRODUCT = reductions.LOGUP, reductions.PRODUCT
WITH_MEMORY, WITHOUT_MEMORY = [True, True, True], [True, True, False]

# Initial accumulator 1: add 4 -> 5, M0 = 5, load the unwritten M1 -> 0, set 9,
# M1 = 9, load M0 -> 5, add 2 -> 7. Memory events: (clock, address, value,
# write) = (1,0,5,1), (2,1,0,0), (4,1,9,1), (5,0,5,0).
MEMORY_PROGRAM = [('add-immediate', 4), ('store', 0), ('load', 1), ('set-immediate', 9),
                  ('store', 1), ('load', 0), ('add-immediate', 2), ('halt', 0)]
MEMORY_EVENTS = {(1, 0, 5, 1), (2, 1, 0, 0), (4, 1, 9, 1), (5, 0, 5, 0)}
# Initial accumulator 3 gives 12; no memory instruction.
ARITHMETIC = regenerate.ARITHMETIC_ONLY
# Executes four steps; the four configured rows after the Halt are unused.
SLACK_PROGRAM = [('add-immediate', 4), ('add-immediate', 1), ('add-immediate', 1), ('halt', 0),
                 ('add-immediate', 9), ('add-immediate', 9), ('add-immediate', 9), ('add-immediate', 9)]
# A Load whose accumulator is zero, and a second Store to address zero: the
# rows the selector forgeries below attack. Honest results are 9 and 6.
LOAD_TARGET = [('set-immediate', 7), ('store', 1), ('set-immediate', 0), ('load', 1),
               ('add-immediate', 2), ('add-immediate', 0), ('add-immediate', 0), ('halt', 0)]
STORE_TARGET = [('set-immediate', 5), ('store', 0), ('set-immediate', 6), ('store', 0),
                ('load', 0), ('add-immediate', 0), ('add-immediate', 0), ('halt', 0)]
# M1 = 3 at clock 1; the honest Load at clock 3 returns 3 and the result is 4.
COLLISION_PROGRAM = [('set-immediate', 3), ('store', 1), ('set-immediate', 0), ('load', 1),
                     ('add-immediate', 1), ('add-immediate', 0), ('add-immediate', 0), ('halt', 0)]


def rows_of(program, initial, **options):
    return machine.layout(machine.execute(program, initial), **options)


def forged(executed, configured, initial, **options):
    """Rows of one execution checked against another configured program."""
    rows = rows_of(executed, initial, **options)
    rows.instructions = [[pc, machine.OPCODES[m], o] for pc, (m, o) in enumerate(configured)]
    return rows


def replaced(program, pc, instruction):
    program = list(program)
    program[pc] = instruction
    return program


def candidate(rows):
    return [BUNDLE, *machine.carriers(BUNDLE, rows)]


def fixture(name):
    return [json.loads((FIXTURES / 'bundle.json').read_text())] + [
        json.loads((FIXTURES / name / f'{part}.json').read_text())
        for part in ['bundle-configuration', 'bundle-instance', 'bundle-witness']]


def zero(value):
    return value == '0' or value == ['0'] * 8


def replies(toolchain, journal, candidates):
    """Both evaluators' reports, which must be identical line by line."""
    wire = ''.join(compact(c) + '\n' for c in candidates)
    reports = []
    for executable in [toolchain.tool('compiler', 'test/zkc-relation_bundle_conformance-test'),
                       toolchain.driver('relation_bundle_conformance')]:
        reports.append([json.loads(row) for row in journal.run([executable], stdin=wire).splitlines()])
    assert len(reports[0]) == len(reports[1]) == len(candidates)
    for index, (cpp, rust) in enumerate(zip(*reports)):
        assert cpp == rust, (index, cpp, rust)
    return reports[0]


def bundle_outcome(report, bundle=BUNDLE, names=None):
    """Failing (table, assertion, row), unbalanced (channel, tuple) and range failures."""
    if not report['accepted']:
        return report['error']
    tables = [t[0] for t in bundle[3]]
    channels = [c[0] for c in bundle[2]]
    names = names or NAMES
    result = report['result']
    assert report['identity'] == machine.identity(bundle)
    failures = {(tables[t], names[tables[t]][a], row)
                for t, a, row, value in result['residuals'] if not zero(value)}
    unbalanced = {(channels[b[1]], tuple(int(x) for x in b[3]))
                  for b in result['balances'] if not b[-1]}
    ranges = {(tables[t], i, row) for t, i, row in result['range_failures']}
    assert result['satisfied'] == (not failures and not unbalanced and not ranges)
    return failures, unbalanced, ranges


def fails(*failures, unbalanced=(), ranges=()):
    return set(failures), set(unbalanced), set(ranges)


HOLDS = fails()


def test_fixtures_regenerate_from_the_reference_interpreter():
    files = regenerate.generate()
    present = {str(p.relative_to(FIXTURES)) for p in FIXTURES.rglob('*') if p.is_file()}
    assert present == set(files)
    for name, text in files.items():
        assert (FIXTURES / name).read_text() == text, name
    # Hand-computed results of the fixture programs, independent of the adapter.
    expected = {'store-load': ('0', '108'), 'store-load-initial-seven': ('7', '115'),
                'arithmetic-only': ('3', '12')}
    for name, publics in expected.items():
        _, _, instance, _ = fixture(name)
        assert tuple(instance[2]) == publics, name
        assert machine.read_run(json.loads((FIXTURES / name / 'run.json').read_text())) == (
            regenerate.RUNS[name][0], int(publics[0]))


@pytest.mark.parametrize('program, code', [
    (MEMORY_PROGRAM[:6], 'machine-program-length'),
    ([('add-immediate', 1)] * 8, 'machine-program-halt'),
    ([('add-immediate', 1)] * 2 + [('halt', 0)] * 6, 'machine-execution-length'),
    (replaced(MEMORY_PROGRAM, 4, ('store', 2)), 'machine-address'),
    (replaced(MEMORY_PROGRAM, 4, ('jump', 0)), 'machine-opcode'),
    (replaced(MEMORY_PROGRAM, 0, ('add-immediate', P)), 'machine-operand'),
])
def test_interpreter_refuses_programs_outside_the_machine(program, code):
    with pytest.raises(Refusal) as refused:
        machine.execute(program, 0)
    assert refused.value.code == code


def test_run_reader_refuses_other_formats():
    with pytest.raises(Refusal) as refused:
        machine.read_run(['zkc.accumulator-machine-run/1', [], '0'])
    assert refused.value.code == 'machine-run-schema'


def bundle_cases():
    cases = []
    for name in regenerate.RUNS:
        cases.append((f'fixture {name}', fixture(name), HOLDS))
    cases.append(('changed initial accumulator, honest execution', candidate(rows_of(MEMORY_PROGRAM, 2)), HOLDS))
    cases.append(('program rows after the first halt are unused', candidate(rows_of(SLACK_PROGRAM, 1)), HOLDS))
    cases.append(('memory schedule longer than the execution',
                  candidate(rows_of(MEMORY_PROGRAM, 1, memory_clocks=16)), HOLDS))
    cases.append(('memory present without events',
                  candidate(rows_of(ARITHMETIC, 3, memory_present=True)), HOLDS))

    def mutation(name, expected, rows=None):
        rows = rows or rows_of(MEMORY_PROGRAM, 1)
        cases.append((name, candidate(rows), expected))

    # Publics and terminal constraints.
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.result = 8
    mutation('public result differs', fails(('cpu', 'final accumulator is the public result', 7)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.initial = 2
    mutation('public initial accumulator differs',
             fails(('cpu', 'accumulator starts at the public initial value', 0)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.set('cpu', 7, 'accumulator_after', 99)
    rows.result = 99
    mutation('halt changes the accumulator', fails(('cpu', 'halt keeps the accumulator', 7)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.cpu, rows.memory, rows.schedule = rows.cpu[:4], rows.memory[:8], rows.schedule[:8]
    rows.use = [[1]] * 4 + [[0]] * 4
    rows.result = 9
    mutation('execution stops before halting', fails(('cpu', 'last step halts', 3)), rows)
    rows = forged([('add-immediate', 4), ('add-immediate', 0), ('add-immediate', 2), ('halt', 0)],
                  [('add-immediate', 4), ('halt', 0), ('add-immediate', 2), ('halt', 0)], 1)
    for column, value in [('opcode', 5), ('select_add', 0), ('select_halt', 1)]:
        rows.set('cpu', 1, column, value)
    mutation('execution continues past a halt', fails(('cpu', 'no halt before the last step', 1)), rows)

    # Instruction semantics: each forged step is consistent except for one rule.
    rows = forged(replaced(MEMORY_PROGRAM, 6, ('add-immediate', 3)), MEMORY_PROGRAM, 1)
    rows.set('cpu', 6, 'operand', 2)
    mutation('add-immediate adds another value', fails(('cpu', 'add-immediate adds the operand', 6)), rows)
    rows = forged(replaced(MEMORY_PROGRAM, 3, ('set-immediate', 10)), MEMORY_PROGRAM, 1)
    rows.set('cpu', 3, 'operand', 9)
    mutation('set-immediate sets another value', fails(('cpu', 'set-immediate replaces the accumulator', 3)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.set('cpu', 4, 'accumulator_after', 11)
    rows.set('cpu', 5, 'accumulator_before', 11)
    mutation('store changes the accumulator', fails(('cpu', 'store keeps the accumulator', 4)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.set('cpu', 3, 'accumulator_before', 1)
    mutation('accumulator does not carry', fails(('cpu', 'accumulator carries to the next step', 2)), rows)

    # Decoding. A Load with accumulator zero decoded from selectors (-1, 2):
    # the result is the address, with no memory event.
    rows = forged(replaced(LOAD_TARGET, 3, ('set-immediate', 1)), LOAD_TARGET, 0)
    for column, value in [('opcode', 3), ('select_set', -1), ('select_add', 2)]:
        rows.set('cpu', 3, column, value)
    mutation('load without a read through non-Boolean selectors',
             fails(('cpu', 'set selector is Boolean', 3), ('cpu', 'add selector is Boolean', 3)), rows)
    # A Store to address zero decoded from (add, load, store) = (1, -2, 2):
    # multiplicity zero, so the write disappears.
    rows = forged(replaced(STORE_TARGET, 3, ('add-immediate', 0)), STORE_TARGET, 0)
    for column, value in [('opcode', 4), ('select_load', -2), ('select_store', 2)]:
        rows.set('cpu', 3, column, value)
    mutation('store elided through non-Boolean selectors',
             fails(('cpu', 'load selector is Boolean', 3), ('cpu', 'store selector is Boolean', 3)), rows)
    rows = forged(replaced(LOAD_TARGET, 3, ('set-immediate', 1)), LOAD_TARGET, 0)
    for column, value in [('opcode', 3), ('select_set', 1), ('select_add', 1)]:
        rows.set('cpu', 3, column, value)
    mutation('load decoded from two active selectors',
             fails(('cpu', 'exactly one selector is active', 3)), rows)
    rows = forged(replaced(STORE_TARGET, 3, ('add-immediate', 0)), STORE_TARGET, 0)
    rows.set('cpu', 3, 'opcode', 4)
    mutation('store executed as add', fails(('cpu', 'opcode decodes the selectors', 3)), rows)

    # Program authority, pc and clock.
    mutation('executed operand differs from the configured program',
             fails(unbalanced={('program', (6, 2, 3)), ('program', (6, 2, 2))}),
             forged(replaced(MEMORY_PROGRAM, 6, ('add-immediate', 3)), MEMORY_PROGRAM, 1))
    rows = forged(MEMORY_PROGRAM[4:], MEMORY_PROGRAM, 1)
    rows.use = [[0]] * 4 + [[1]] * 4
    for row in range(4):
        rows.set('cpu', row, 'pc', row + 4)
    mutation('execution skips the program prefix', fails(('cpu', 'pc starts at zero', 0)), rows)
    rows = forged(MEMORY_PROGRAM[:3] + [('halt', 0)], MEMORY_PROGRAM, 1)
    rows.use = [[1], [1], [1], [0], [0], [0], [0], [1]]
    rows.set('cpu', 3, 'pc', 7)
    mutation('execution jumps to the halt', fails(('cpu', 'pc advances', 2)), rows)
    rows = rows_of(ARITHMETIC, 3)
    for row in range(4):
        rows.set('cpu', row, 'clock', row + 1)
    mutation('clock starts at one', fails(('cpu', 'clock starts at zero', 0)), rows)
    rows = rows_of(ARITHMETIC, 3)
    rows.set('cpu', 2, 'clock', 5)
    rows.set('cpu', 3, 'clock', 6)
    mutation('clock skips ahead', fails(('cpu', 'clock advances', 1)), rows)
    # The Load at clock 2 claims clock 5 and reads the value stored at clock 4.
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.set('cpu', 2, 'clock', 5)
    rows.set('cpu', 2, 'accumulator_after', 9)
    rows.set('cpu', 3, 'accumulator_before', 9)
    rows.memory[5] = [0, 0, 0, 0, 0]
    rows.memory[11] = [9, 9, 1, 0, 9]
    mutation('load reads from a later clock',
             fails(('cpu', 'clock advances', 1), ('cpu', 'clock advances', 2)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.set('use', 2, 'use', 2)
    mutation('program use is not Boolean',
             fails(('program', 'use is Boolean', 2), unbalanced={('program', (2, 3, 1))},
                   ranges={('program', 0, 2)}), rows)
    # An unreachable configured row relabelled as pc 1 offers another instruction.
    rows = forged([('add-immediate', 4), ('set-immediate', 50), ('add-immediate', 1), ('halt', 0)],
                  SLACK_PROGRAM, 1)
    rows.instructions[4] = [1, 1, 50]
    rows.use = [[1], [0], [1], [1], [1], [0], [0], [0]]
    mutation('configured pc repeats',
             fails(('program', 'configured pc advances', 3), ('program', 'configured pc advances', 4)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.instructions[0], rows.instructions[1] = rows.instructions[1], rows.instructions[0]
    mutation('configured rows out of pc order',
             fails(('program', 'configured pc starts at zero', 0), ('program', 'configured pc advances', 0),
                   ('program', 'configured pc advances', 1)), rows)

    # Memory: initialization, carry, read and write gates.
    rows = rows_of(MEMORY_PROGRAM, 1)
    for row in (1, 3, 5, 7):
        rows.memory[row][:2] = [3, 3]
    rows.set('memory', 5, 'value', 3)
    rows.set('memory', 9, 'before', 3)
    rows.set('cpu', 2, 'accumulator_after', 3)
    rows.set('cpu', 3, 'accumulator_before', 3)
    mutation('address one starts nonzero', fails(('memory', 'address one starts at zero', 0)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.memory[0][:2] = [4, 4]
    rows.set('memory', 2, 'before', 4)
    mutation('address zero starts nonzero', fails(('memory', 'address zero starts at zero', 0)), rows)

    def stale_read(rows, first):
        """Address 0 holds 6 from memory row `first` on; the Load at clock 5 sees it."""
        for row in range(first, 16, 2):
            rows.memory[row][1] = 6
            if row > first:
                rows.memory[row][0] = 6
        rows.set('memory', 10, 'value', 6)
        for row, before, after in [(5, 9, 6), (6, 6, 8), (7, 8, 8)]:
            rows.set('cpu', row, 'accumulator_before', before)
            rows.set('cpu', row, 'accumulator_after', after)
        rows.result = 8
        return rows

    rows = stale_read(rows_of(MEMORY_PROGRAM, 1), 10)
    rows.set('memory', 10, 'before', 6)
    mutation('cell state does not carry', fails(('memory', 'cell state carries to the next clock', 8)), rows)
    mutation('idle row changes the cell', fails(('memory', 'no write keeps the cell', 8)),
             stale_read(rows_of(MEMORY_PROGRAM, 1), 8))
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.set('memory', 10, 'value', 6)
    for row, before, after in [(5, 9, 6), (6, 6, 8), (7, 8, 8)]:
        rows.set('cpu', row, 'accumulator_before', before)
        rows.set('cpu', row, 'accumulator_after', after)
    rows.result = 8
    mutation('read returns another value', fails(('memory', 'read returns the cell', 10)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    for row in (9, 11, 13, 15):
        rows.memory[row][1] = 10
        if row > 9:
            rows.memory[row][0] = 10
    mutation('write stores another value', fails(('memory', 'write stores the value', 9)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.memory[13] = [9, 4, 0, 1, 4]
    rows.memory[15][:2] = [4, 4]
    mutation('write without an event', fails(('memory', 'write requires an event', 13)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.set('memory', 5, 'event', 2)
    mutation('memory event count two',
             fails(('memory', 'event is Boolean', 5), unbalanced={('memory', (2, 1, 0, 0))},
                   ranges={('memory', 0, 5)}), rows)
    # The Store at clock 4 lands in address 0; the later Load of address 0 sees it.
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.memory[8] = [5, 9, 1, 1, 9]
    for row in (9, 11, 13, 15):
        rows.memory[row] = [0, 0, 0, 0, 0]
    for row in (10, 12, 14):
        rows.memory[row][:2] = [9, 9]
    rows.set('memory', 10, 'value', 9)
    for row, before, after in [(5, 9, 9), (6, 9, 11), (7, 11, 11)]:
        rows.set('cpu', row, 'accumulator_before', before)
        rows.set('cpu', row, 'accumulator_after', after)
    rows.result = 11
    mutation('memory event at another address',
             fails(unbalanced={('memory', (4, 1, 9, 1)), ('memory', (4, 0, 9, 1))}), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.instructions[4] = [4, 4, 2]
    rows.set('cpu', 4, 'operand', 2)
    for row in (9, 11, 13, 15):
        rows.memory[row] = [0, 0, 0, 0, 0]
    mutation('store to an address outside the cells', fails(unbalanced={('memory', (4, 2, 9, 1))}), rows)
    mutation('load answered by a read at another clock',
             fails(unbalanced={('memory', (3, 1, 5, 0)), ('memory', (5, 1, 3, 0))}), collision_rows())
    mutation('memory events beyond the configured schedule',
             fails(unbalanced={('memory', (4, 1, 9, 1)), ('memory', (5, 0, 5, 0))}),
             rows_of(MEMORY_PROGRAM, 1, memory_clocks=4))

    # Configured schedule.
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.schedule[0] = [0, 1]
    mutation('schedule starts at address one',
             fails(('memory', 'schedule starts at address zero', 0), ('memory', 'schedule alternates addresses', 0),
                   ('memory', 'schedule advances the clock after address one', 0)), rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.schedule[0] = [1, 0]
    mutation('schedule starts at clock one',
             fails(('memory', 'schedule starts at clock zero', 0),
                   ('memory', 'schedule advances the clock after address one', 0)), rows)
    # Swapped addresses at clock 2 let the Load of address 1 read address 0's chain.
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.schedule[4], rows.schedule[5] = [2, 1], [2, 0]
    rows.memory[4] = [5, 5, 1, 0, 5]
    rows.memory[5] = [0, 0, 0, 0, 0]
    rows.set('cpu', 2, 'accumulator_after', 5)
    rows.set('cpu', 3, 'accumulator_before', 5)
    mutation('schedule aliases the two cells',
             fails(('memory', 'schedule alternates addresses', 3), ('memory', 'schedule alternates addresses', 5),
                   ('memory', 'schedule advances the clock after address one', 4),
                   ('memory', 'schedule advances the clock after address one', 5)), rows)

    # Presence and heights.
    mutation('memory table absent with memory events',
             fails(unbalanced={('memory', e) for e in MEMORY_EVENTS}),
             rows_of(MEMORY_PROGRAM, 1, memory_present=False))
    changed = candidate(rows_of(MEMORY_PROGRAM, 1))
    changed[2][3][0], changed[3][2][0] = ['absent'], None
    cases.append(('required table absent', changed, 'bundle-table-missing'))
    changed = candidate(rows_of(MEMORY_PROGRAM, 1))
    changed[2][3][2] = ['absent']
    cases.append(('absent table with witness data', changed, 'bundle-witness-presence'))
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.cpu = rows.cpu[:6]
    mutation('cpu height not a power of two', 'bundle-height', rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.cpu_height = 32
    mutation('cpu height above its maximum', 'bundle-height', rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.cpu_height = 16
    mutation('cpu height differs from its rows', 'bundle-group-shape', rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.schedule, rows.memory = rows.schedule[:12], rows.memory[:12]
    mutation('memory height not a power of two', 'bundle-height', rows)
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.instructions, rows.use = rows.instructions * 4, rows.use * 4
    mutation('program height above its maximum', 'bundle-height', rows)
    changed = candidate(rows_of(MEMORY_PROGRAM, 1))
    changed[2][3][1] = ['present', 8, []]
    cases.append(('instance overrides the configured program height', changed, 'bundle-height-authority'))
    return cases


def test_machine_executions_and_mutations_agree(toolchain, journal):
    cases = bundle_cases()
    reports = replies(toolchain, journal, [c for _, c, _ in cases])
    covered = set()
    for (name, _, expected), report in zip(cases, reports):
        found = bundle_outcome(report)
        journal.check(name, found == expected, {'found': repr(found), 'expected': repr(expected)})
        if not isinstance(found, str):
            covered |= {(table, assertion) for table, assertion, _ in found[0]}
            covered |= {channel for channel, _ in found[1]}
    # Every assertion and channel is the only or a necessary witness of some mutation.
    declared = {(table, n) for table, names in NAMES.items() for n in names} | set(machine.CHANNELS)
    journal.check('every assertion and channel detects a mutation', covered == declared,
                  sorted(map(str, declared - covered)))


def test_execution_tables_cannot_be_spliced_or_rebased(toolchain, journal):
    # Both complete runs satisfy the same Bundle. Their program is identical,
    # but the changed initial accumulator changes the value stored and loaded.
    first = rows_of(MEMORY_PROGRAM, 1)
    second = rows_of(MEMORY_PROGRAM, 2)
    memory_difference = {
        ('memory', (clock, 0, value, write))
        for clock, write in [(1, 1), (5, 0)] for value in [5, 6]}
    cases = [('first run', first, HOLDS), ('second run', second, HOLDS)]

    rows = deepcopy(first)
    rows.cpu = deepcopy(second.cpu)
    cases.append(('foreign CPU with original public boundaries', rows,
                  fails(('cpu', 'accumulator starts at the public initial value', 0),
                        ('cpu', 'final accumulator is the public result', 7),
                        unbalanced=memory_difference)))
    rows = deepcopy(first)
    rows.memory = deepcopy(second.memory)
    cases.append(('foreign RAM with original CPU', rows,
                  fails(unbalanced=memory_difference)))
    rows = deepcopy(first)
    other_program = replaced(MEMORY_PROGRAM, 6, ('add-immediate', 3))
    rows.instructions = rows_of(other_program, 1).instructions
    cases.append(('foreign authorized program', rows,
                  fails(unbalanced={('program', (6, 2, 2)), ('program', (6, 2, 3))})))

    # A complete-run relation starts at pc/clock zero. Rebase both ends of each
    # bus together, preserving its balance and internal successor constraints.
    rows = deepcopy(first)
    for row in rows.cpu:
        row[1] += 1
    for row in rows.schedule:
        row[0] += 1
    cases.append(('clock continuation with consistent bus records', rows,
                  fails(('cpu', 'clock starts at zero', 0),
                        ('memory', 'schedule starts at clock zero', 0))))
    rows = deepcopy(first)
    for row in rows.cpu:
        row[0] += 1
    for row in rows.instructions:
        row[0] += 1
    cases.append(('pc continuation with consistent program records', rows,
                  fails(('cpu', 'pc starts at zero', 0),
                        ('program', 'configured pc starts at zero', 0))))
    reports = replies(toolchain, journal, [candidate(rows) for _, rows, _ in cases])
    for (name, _, expected), report in zip(cases, reports):
        actual = bundle_outcome(report)
        journal.check(name, actual == expected,
                      {'actual': repr(actual), 'expected': repr(expected)})


# Staged reductions.

def staged_outcome(report, reduction):
    """(Bundle satisfied, failing staged (table, assertion, row), failing global names)."""
    if not report['accepted']:
        return report['error']
    assert report['staged_identity'] == reduction.identity
    tables = [t[0] for t in reduction.tables]
    result = report['staged_result']
    failures = {(tables[t], reduction.assertion_names[t][a], row)
                for _, t, a, row, value in result['residuals'] if not zero(value)}
    closing = {reduction.global_names[i] for i, value in enumerate(result['global']) if not zero(value)}
    assert result['satisfied'] == (not failures and not closing)
    return report['result']['satisfied'], failures, closing


def staged(bundle_holds=True, *failures, closing=()):
    """Bundle satisfaction, failing staged assertion rows and failing global checks."""
    return bundle_holds, set(failures), set(closing)


CHALLENGES = {kind: reductions.fixture_challenges(f'mutation/{kind}', 4) for kind in (LOGUP, PRODUCT)}


def honest(kind, rows, presence=WITH_MEMORY, challenges=None, **options):
    reduction = reductions.Reduction(kind, BUNDLE, presence)
    carriers = machine.carriers(BUNDLE, rows)
    assignment = reduction.assign(*carriers, CHALLENGES[kind] if challenges is None else challenges, **options)
    return reduction, [BUNDLE, *carriers, reduction.program, assignment]


def cell(case, reduction, table, row, column):
    """The auxiliary element at (table, row, column) of the one-phase assignment."""
    t = [entry[0] for entry in reduction.tables].index(table)
    width = len(reduction.columns[t])
    return case[5][2][0][2][t][0], row * width + column


def change(case, reduction, table, row, column, update):
    values, index = cell(case, reduction, table, row, column)
    values[index] = encode(reduction.field, update(decode(reduction.field, values[index])))


def change_claim(case, reduction, name, update):
    claims = case[5][2][0][1]
    index = reduction.claims.index(name)
    claims[index] = encode(reduction.field, update(decode(reduction.field, claims[index])))


def plus_one(value):
    return add(value, ONE)


def collision_rows():
    """The Load at clock 3 returns 5 while memory records a read of 3 at clock 5.

    Under compression delta = 1 both tuples, (3,1,5,0) and (5,1,3,0), have
    fingerprint 9.
    """
    rows = forged(replaced(COLLISION_PROGRAM, 3, ('set-immediate', 5)), COLLISION_PROGRAM, 0)
    for column, value in [('opcode', 3), ('operand', 1), ('select_set', 0), ('select_load', 1)]:
        rows.set('cpu', 3, column, value)
    rows.memory[11] = [3, 3, 1, 0, 3]
    return rows


def machine_staged_cases():
    cases = []
    for name in regenerate.RUNS:
        base = fixture(name)
        presence = [entry[0] == 'present' for entry in base[2][3]]
        label = 'with-memory' if presence[2] else 'without-memory'
        for kind in (LOGUP, PRODUCT):
            reduction = reductions.Reduction(kind, BUNDLE, presence)
            program = json.loads((FIXTURES / f'{kind}-{label}.json').read_text())
            assignment = json.loads((FIXTURES / name / f'{kind}-assignment.json').read_text())
            assert program == reduction.program
            cases.append((f'{kind}: fixture {name}', [*base, program, assignment], reduction, staged()))

    # LogUp column order: cpu = [program inverse, memory inverse, program sum,
    # memory sum]; program and memory tables = [inverse, sum].
    def logup(name, expected, edit, rows=None):
        reduction, case = honest(LOGUP, rows or rows_of(MEMORY_PROGRAM, 1))
        edit(case, reduction)
        cases.append((f'{LOGUP}: {name}', case, reduction, expected))

    logup('inverse on an inactive row is unconstrained', staged(),
          lambda c, r: change(c, r, 'cpu', 0, 1, plus_one))
    logup('inverse on an active row changed',
          staged(True, ('cpu', 'memory interaction 1 inverts its denominator', 1),
                 ('cpu', 'memory sum accumulates each row', 1)),
          lambda c, r: change(c, r, 'cpu', 1, 1, plus_one))
    logup('program inverse changed',
          staged(True, ('program', 'program interaction 0 inverts its denominator', 0),
                 ('program', 'program sum starts with the first row', 0)),
          lambda c, r: change(c, r, 'program', 0, 0, plus_one))
    logup('interior running sum changed',
          staged(True, ('cpu', 'program sum accumulates each row', 3),
                 ('cpu', 'program sum accumulates each row', 4)),
          lambda c, r: change(c, r, 'cpu', 3, 2, plus_one))
    logup('program-table running sum changed',
          staged(True, ('program', 'program sum accumulates each row', 4),
                 ('program', 'program sum accumulates each row', 5)),
          lambda c, r: change(c, r, 'program', 4, 1, plus_one))
    logup('first memory sum changed',
          staged(True, ('cpu', 'memory sum starts with the first row', 0), ('cpu', 'memory sum accumulates each row', 1)),
          lambda c, r: change(c, r, 'cpu', 0, 3, plus_one))
    logup('first memory-table sum changed',
          staged(True, ('memory', 'memory sum starts with the first row', 0),
                 ('memory', 'memory sum accumulates each row', 1)),
          lambda c, r: change(c, r, 'memory', 0, 1, plus_one))
    logup('last memory-table sum changed',
          staged(True, ('memory', 'memory sum accumulates each row', 15),
                 ('memory', 'memory sum ends at its claim', 15)),
          lambda c, r: change(c, r, 'memory', 15, 1, plus_one))

    def omit_first_row(case, reduction):
        values, index = cell(case, reduction, 'cpu', 0, 2)
        first = decode(reduction.field, values[index])
        for row in range(8):
            change(case, reduction, 'cpu', row, 2, lambda v: sub(v, first))
        change_claim(case, reduction, 'cpu-program-sum', lambda v: sub(v, first))

    logup('sum starts without the first row',
          staged(True, ('cpu', 'program sum starts with the first row', 0), closing={'program sums close'}),
          omit_first_row)
    logup('claim changed', staged(True, ('cpu', 'program sum ends at its claim', 7), closing={'program sums close'}),
          lambda c, r: change_claim(c, r, 'cpu-program-sum', plus_one))
    logup('memory claim changed',
          staged(True, ('memory', 'memory sum ends at its claim', 15), closing={'memory sums close'}),
          lambda c, r: change_claim(c, r, 'memory-memory-sum', plus_one))

    def shift_claims(first, second):
        def edit(case, reduction):
            change_claim(case, reduction, first, plus_one)
            change_claim(case, reduction, second, lambda v: sub(v, ONE))
        return edit

    logup('program claims shifted consistently',
          staged(True, ('cpu', 'program sum ends at its claim', 7), ('program', 'program sum ends at its claim', 7)),
          shift_claims('cpu-program-sum', 'program-program-sum'))
    logup('memory claims shifted consistently',
          staged(True, ('cpu', 'memory sum ends at its claim', 7), ('memory', 'memory sum ends at its claim', 15)),
          shift_claims('cpu-memory-sum', 'memory-memory-sum'))
    logup('global closure rejects a forged program lookup', staged(False, closing={'program sums close'}),
          lambda c, r: None, forged(replaced(MEMORY_PROGRAM, 6, ('add-immediate', 3)), MEMORY_PROGRAM, 1))

    def other_challenge(index):
        def edit(case, reduction):
            case[5][2][0][0][index] = encode(reduction.field, scalar(12345))
        return edit

    logup('shift challenge changed',
          staged(True, *[(t, 'program interaction 0 inverts its denominator', row)
                         for t in ('cpu', 'program') for row in range(8)]),
          other_challenge(0))
    active = [('cpu', 'memory interaction 1 inverts its denominator', row) for row in (1, 2, 4, 5)]
    active += [('memory', 'memory interaction 0 inverts its denominator', row) for row in (2, 5, 9, 10)]
    logup('compression challenge changed', staged(True, *active), other_challenge(3))

    # Grand-product column order: cpu = [program pull, memory push]; program
    # = [program push]; memory = [memory pull].
    def grand(name, expected, edit, rows=None):
        reduction, case = honest(PRODUCT, rows or rows_of(MEMORY_PROGRAM, 1))
        edit(case, reduction)
        cases.append((f'{PRODUCT}: {name}', case, reduction, expected))

    grand('interior running product changed',
          staged(True, ('cpu', 'program pull product accumulates each row', 3),
                 ('cpu', 'program pull product accumulates each row', 4)),
          lambda c, r: change(c, r, 'cpu', 3, 0, plus_one))
    grand('last running product changed',
          staged(True, ('cpu', 'program pull product accumulates each row', 7),
                 ('cpu', 'program pull product ends at its claim', 7)),
          lambda c, r: change(c, r, 'cpu', 7, 0, plus_one))
    grand('first memory push product changed',
          staged(True, ('cpu', 'memory push product starts with the first row', 0),
                 ('cpu', 'memory push product accumulates each row', 1)),
          lambda c, r: change(c, r, 'cpu', 0, 1, plus_one))
    grand('first program push product changed',
          staged(True, ('program', 'program push product starts with the first row', 0),
                 ('program', 'program push product accumulates each row', 1)),
          lambda c, r: change(c, r, 'program', 0, 0, plus_one))
    grand('first memory pull product changed',
          staged(True, ('memory', 'memory pull product starts with the first row', 0),
                 ('memory', 'memory pull product accumulates each row', 1)),
          lambda c, r: change(c, r, 'memory', 0, 0, plus_one))

    def product_without_first_row(case, reduction):
        values, index = cell(case, reduction, 'cpu', 0, 0)
        (inverse,) = inverses([decode(reduction.field, values[index])], 'test')
        for row in range(8):
            change(case, reduction, 'cpu', row, 0, lambda v: mul(v, inverse))
        change_claim(case, reduction, 'cpu-program-pull-product', lambda v: mul(v, inverse))

    grand('product starts without the first row',
          staged(True, ('cpu', 'program pull product starts with the first row', 0),
                 closing={'program products agree'}),
          product_without_first_row)
    grand('push claim changed',
          staged(True, ('program', 'program push product ends at its claim', 7),
                 closing={'program products agree', 'program product is nonzero'}),
          lambda c, r: change_claim(c, r, 'program-program-push-product', plus_one))
    grand('pull claim changed',
          staged(True, ('memory', 'memory pull product ends at its claim', 15), closing={'memory products agree'}),
          lambda c, r: change_claim(c, r, 'memory-memory-pull-product', plus_one))
    grand('program inverse claim changed', staged(True, closing={'program product is nonzero'}),
          lambda c, r: change_claim(c, r, 'program-product-inverse', plus_one))
    grand('memory inverse claim changed', staged(True, closing={'memory product is nonzero'}),
          lambda c, r: change_claim(c, r, 'memory-product-inverse', plus_one))

    def scale_claims(case, reduction):
        two, (half,) = scalar(2), inverses([scalar(2)], 'test')
        change_claim(case, reduction, 'cpu-memory-push-product', lambda v: mul(v, two))
        change_claim(case, reduction, 'memory-memory-pull-product', lambda v: mul(v, two))
        change_claim(case, reduction, 'memory-product-inverse', lambda v: mul(v, half))

    grand('memory claims scaled consistently',
          staged(True, ('cpu', 'memory push product ends at its claim', 7),
                 ('memory', 'memory pull product ends at its claim', 15)),
          scale_claims)
    grand('global closure rejects a forged program lookup', staged(False, closing={'program products agree'}),
          lambda c, r: None, forged(replaced(MEMORY_PROGRAM, 6, ('add-immediate', 3)), MEMORY_PROGRAM, 1))
    changed = [('cpu', 'memory push product accumulates each row', row) for row in (1, 2, 4, 5)]
    changed += [('memory', 'memory pull product accumulates each row', row) for row in (2, 5, 9, 10)]
    grand('shift challenge changed', staged(True, *changed), other_challenge(2))

    # A challenge that compresses two different tuples to the same value: the
    # staged predicate holds although the Bundle's memory multiset does not.
    for kind, closing in [(LOGUP, 'memory sums close'), (PRODUCT, 'memory products agree')]:
        bad = list(CHALLENGES[kind])
        bad[3] = ONE
        reduction, case = honest(kind, collision_rows(), challenges=bad)
        cases.append((f'{kind}: compression collision', case, reduction, staged(False)))
        reduction, case = honest(kind, collision_rows())
        cases.append((f'{kind}: collision rejected at another challenge', case, reduction,
                      staged(False, closing={closing})))

    # A shift equal to an active fingerprint: the honest builder refuses (see
    # the refusal test); a prover's assignment then still fails.
    for kind, expected in [
            (LOGUP, staged(True, ('cpu', 'memory interaction 1 inverts its denominator', 1),
                           ('memory', 'memory interaction 0 inverts its denominator', 2))),
            (PRODUCT, staged(True, closing={'memory product is nonzero'}))]:
        reduction, case = honest(kind, rows_of(MEMORY_PROGRAM, 1), challenges=zero_shift(kind),
                                 refuse_zero=False)
        cases.append((f'{kind}: shift equals an active fingerprint', case, reduction, expected))

    # Presence: the verifier must evaluate the program instantiated for the
    # instance's presence. The program for a present memory table, given an
    # instance without it, leaves the memory claim free.
    for kind, closing in [(LOGUP, 'memory sums close'), (PRODUCT, 'memory products agree')]:
        reduction, case = honest(kind, rows_of(MEMORY_PROGRAM, 1))
        case[2][3][2], case[3][2][2], case[5][2][0][2][2] = ['absent'], None, None
        cases.append((f'{kind}: program for another presence accepts a free claim', case, reduction,
                      staged(False)))
        reduction, case = honest(kind, rows_of(MEMORY_PROGRAM, 1, memory_present=False), WITHOUT_MEMORY)
        cases.append((f'{kind}: presence-matched program rejects absent memory', case, reduction,
                      staged(False, closing={closing})))
    # Base-field challenges are a supported parameter, shown on one fixture.
    reduction = reductions.Reduction(LOGUP, BUNDLE, WITH_MEMORY, BASE)
    base = fixture('store-load')
    assignment = reduction.assign(*base[1:], reductions.fixture_challenges('base', 4, BASE))
    cases.append((f'{LOGUP}: base-field challenges', [*base, reduction.program, assignment], reduction, staged()))
    return cases


def zero_shift(kind):
    """Challenges whose memory shift equals the fingerprint of event (1,0,5,1)."""
    values = list(CHALLENGES[kind])
    delta = values[3]
    fingerprint = scalar(1)
    for coordinate in reversed([1, 0, 5, 1][:-1]):
        fingerprint = add(mul(fingerprint, delta), scalar(coordinate))
    values[2] = fingerprint
    return values


def test_machine_reductions_agree(toolchain, journal):
    cases = machine_staged_cases()
    reports = replies(toolchain, journal, [c for _, c, _, _ in cases])
    covered = {LOGUP: set(), PRODUCT: set()}
    for (name, case, reduction, expected), report in zip(cases, reports):
        found = staged_outcome(report, reduction)
        journal.check(name, found == expected, {'found': repr(found), 'expected': repr(expected)})
        if not isinstance(found, str) and reduction.presence == WITH_MEMORY:
            covered[reduction.kind] |= {(t, a) for t, a, _ in found[1]} | found[2]
    for kind, seen in covered.items():
        reduction = reductions.Reduction(kind, BUNDLE, WITH_MEMORY)
        declared = {(t[0], a) for t, names in zip(reduction.tables, reduction.assertion_names) for a in names}
        declared |= set(reduction.global_names)
        journal.check(f'{kind}: every staged check detects a mutation', seen == declared,
                      sorted(map(str, declared - seen)))


def counting_bundle(kind):
    """One table whose tuple 5 appears on both rows with arbitrary counts."""
    if kind == 'multiset':
        interactions = [['multiset', 0, ['global'], ['all'], 'push', [0], 1, 1],
                        ['multiset', 0, ['global'], ['all'], 'pull', [0], 2, 1]]
    else:
        interactions = [['field-balance', 0, ['global'], ['all'], [0], 1, None],
                        ['field-balance', 0, ['global'], ['all'], [0], 2, None]]
    return ['zkc.relation-bundle/0', [], [['pairs', kind, [BASE], BASE]], [[
        'counts', 'required', ['fixed', 2], 'finite', [['values', 'witness', BASE, 3]],
        ['zkc.ring/0', [BASE] * 3, [['input', 0], ['input', 1], ['input', 2]], [0, 1, 2]],
        [['read', 0, '0', 0], ['read', 0, '0', 1], ['read', 0, '0', 2]], [], interactions]]]


def counting_case(kind, reduction_kind, rows, **options):
    bundle = counting_bundle(kind)
    relation = machine.identity(bundle)
    carriers = [['zkc.relation-configuration/0', relation, [[None, []]]],
                ['zkc.relation-instance/0', relation, [], [['present', None, []]]],
                ['zkc.relation-witness/0', relation, [[[str(v % P) for row in rows for v in row]]]]]
    reduction = reductions.Reduction(reduction_kind, bundle, [True])
    challenges = reductions.fixture_challenges(f'counts/{kind}/{reduction_kind}', 2)
    assignment = reduction.assign(*carriers, challenges, **options)
    return bundle, reduction, [bundle, *carriers, reduction.program, assignment]


def test_field_balance_and_natural_counts_differ(toolchain, journal):
    """Counts 2 and p-1 sum to 1 in the field but are not natural Boolean counts."""
    malformed = [[5, 2, 1], [5, -1, 0]]
    cases = []
    bundle, reduction, case = counting_case('multiset', LOGUP, malformed, check_premises=False)
    cases.append(('LogUp sums of malformed natural counts', bundle, reduction, case,
                  fails(unbalanced={('pairs', (5,))}, ranges={('counts', 0, 0), ('counts', 0, 1)}),
                  staged()[1:]))
    bundle, reduction, case = counting_case('multiset', PRODUCT, malformed, check_premises=False)
    cases.append(('grand product of malformed natural counts', bundle, reduction, case,
                  fails(unbalanced={('pairs', (5,))}, ranges={('counts', 0, 0), ('counts', 0, 1)}),
                  staged(True, closing={'pairs products agree'})[1:]))
    # Field-weighted counts: 2 and p-2 against no pull balance in the field.
    bundle, reduction, case = counting_case('field-balance', LOGUP, [[5, 2, 0], [5, -2, 0]])
    cases.append(('LogUp of a field-weighted balance', bundle, reduction, case, HOLDS, staged()[1:]))
    bundle, reduction, case = counting_case('field-balance', LOGUP, [[5, 2, 0], [5, -1, 0]])
    cases.append(('LogUp of an unbalanced field weight', bundle, reduction, case,
                  fails(unbalanced={('pairs', (5,))}), staged(True, closing={'pairs sums close'})[1:]))
    reports = replies(toolchain, journal, [c for _, _, _, c, _, _ in cases])
    for (name, bundle, reduction, _, base, expected), report in zip(cases, reports):
        found = bundle_outcome(report, bundle, {'counts': []})
        journal.check(f'{name}: bundle', found == base, repr(found))
        journal.check(f'{name}: staged', staged_outcome(report, reduction)[1:] == expected,
                      repr(staged_outcome(report, reduction)))
    with pytest.raises(Refusal) as refused:
        counting_case('multiset', LOGUP, malformed)
    assert refused.value.code == 'reduction-boolean-count'


def test_reductions_refuse_unsupported_shapes():
    def refusal(code, build):
        with pytest.raises(Refusal) as refused:
            build()
        assert refused.value.code == code, (code, refused.value)

    multiset = counting_bundle('multiset')
    refusal('reduction-presence', lambda: reductions.Reduction(LOGUP, BUNDLE, [False, True, True]))
    refusal('reduction-presence', lambda: reductions.Reduction(LOGUP, BUNDLE, [True, True]))
    refusal('reduction-kind', lambda: reductions.Reduction('permutation', BUNDLE, WITH_MEMORY))
    refusal('reduction-field', lambda: reductions.Reduction(LOGUP, BUNDLE, WITH_MEMORY, 'unknown-field'))
    extension = deepcopy(counting_bundle('field-balance'))
    extension[2][0][2] = [EXTENSION]
    refusal('reduction-field', lambda: reductions.Reduction(LOGUP, extension, [True], BASE))
    refusal('reduction-channel-kind', lambda: reductions.Reduction(PRODUCT, counting_bundle('field-balance'), [True]))
    for position, value, code in [(3, ['first'], 'reduction-scope'), (2, ['local', 0], 'reduction-locality'),
                                  (7, 2, 'reduction-multiplicity-bound')]:
        changed = deepcopy(multiset)
        changed[3][0][8][0][position] = value
        refusal(code, lambda: reductions.Reduction(LOGUP, changed, [True]))
    # 2048 Boolean records on a table of up to 2^20 rows can count 2^31 >= p.
    changed = deepcopy(multiset)
    changed[3][0][2] = ['instance', 1, 1 << 20, False]
    changed[3][0][8] = [['multiset', 0, ['global'], ['all'], 'push', [0], 1, 1]] * 2048
    refusal('reduction-characteristic', lambda: reductions.Reduction(LOGUP, changed, [True]))
    reductions.Reduction(PRODUCT, changed, [True])

    base = fixture('store-load')
    reduction = reductions.Reduction(LOGUP, BUNDLE, WITHOUT_MEMORY)
    refusal('reduction-presence', lambda: reduction.assign(*base[1:], CHALLENGES[LOGUP]))
    reduction = reductions.Reduction(LOGUP, BUNDLE, WITH_MEMORY)
    refusal('reduction-challenge-count', lambda: reduction.assign(*base[1:], CHALLENGES[LOGUP][:3]))
    carriers = machine.carriers(BUNDLE, rows_of(MEMORY_PROGRAM, 1))
    for kind, code in [(LOGUP, 'reduction-zero-denominator'), (PRODUCT, 'reduction-zero-factor')]:
        reduction = reductions.Reduction(kind, BUNDLE, WITH_MEMORY)
        refusal(code, lambda: reduction.assign(*carriers, zero_shift(kind)))
    rows = rows_of(MEMORY_PROGRAM, 1)
    rows.set('memory', 5, 'event', 2)
    for kind in (LOGUP, PRODUCT):
        reduction = reductions.Reduction(kind, BUNDLE, WITH_MEMORY)
        refusal('reduction-boolean-count',
                lambda: reduction.assign(*machine.carriers(BUNDLE, rows), CHALLENGES[kind]))
