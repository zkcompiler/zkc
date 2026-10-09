"""A small accumulator machine, its reference interpreter and its relation Bundle.

The machine has one KoalaBear accumulator, two memory cells that start at
zero, and a linear program of SetImmediate, AddImmediate, Load, Store and Halt
instructions. Execution starts at pc 0 and clock 0, advances both by one per
instruction, and ends at the first Halt.

`execute` is an imperative interpreter; it never evaluates the relation. The
Bundle built by `machine_bundle` is the deterministic statement about such an
execution, and the carrier builders lay the interpreter's records out as its
configuration, instance and witness. The README states the relation and the
choices behind it.
"""

from dataclasses import dataclass, field

from ring_arena import BASE, P, Arena, Refusal, identity

RUN_FORMAT = 'zkc.accumulator-machine-run/0'
OPCODES = {'set-immediate': 1, 'add-immediate': 2, 'load': 3, 'store': 4, 'halt': 5}
SELECTOR = {'set-immediate': 'select_set', 'add-immediate': 'select_add',
            'load': 'select_load', 'store': 'select_store', 'halt': 'select_halt'}
MEMORY_CELLS = 2
CPU_HEIGHTS = (4, 16)
MEMORY_HEIGHTS = (8, 32)

CPU_COLUMNS = ('pc', 'clock', 'opcode', 'operand', 'accumulator_before', 'accumulator_after',
               'select_set', 'select_add', 'select_load', 'select_store', 'select_halt')
PROGRAM_COLUMNS = ('pc', 'opcode', 'operand')
SCHEDULE_COLUMNS = ('clock', 'address')
CELL_COLUMNS = ('before', 'after', 'event', 'write', 'value')
TABLES = ('cpu', 'program', 'memory')
CHANNELS = ('program', 'memory')


def power_of_two(n, bounds):
    return bounds[0] <= n <= bounds[1] and n & (n - 1) == 0


def validate_program(program):
    """Refuse programs whose configured table or execution length is not exact.

    A program is a power-of-two list of 4 to 16 instructions. Execution runs to
    the first Halt, and its length must itself be a CPU height (4, 8 or 16).
    Instructions after the first Halt are unreachable configured rows.
    """
    if not power_of_two(len(program), CPU_HEIGHTS):
        raise Refusal('machine-program-length', str(len(program)))
    for pc, (mnemonic, operand) in enumerate(program):
        if mnemonic not in OPCODES:
            raise Refusal('machine-opcode', f'pc {pc}: {mnemonic}')
        if not 0 <= operand < P:
            raise Refusal('machine-operand', f'pc {pc}: {operand}')
        if mnemonic in ('load', 'store') and operand >= MEMORY_CELLS:
            raise Refusal('machine-address', f'pc {pc}: {operand}')
    halts = [pc for pc, (mnemonic, _) in enumerate(program) if mnemonic == 'halt']
    if not halts:
        raise Refusal('machine-program-halt')
    if not power_of_two(halts[0] + 1, CPU_HEIGHTS):
        raise Refusal('machine-execution-length', str(halts[0] + 1))


@dataclass
class Step:
    pc: int
    clock: int
    mnemonic: str
    operand: int
    before: int
    after: int
    memory_before: tuple
    memory_after: tuple
    event: tuple = None  # (address, value, write) for Load and Store


@dataclass
class Execution:
    program: list
    initial: int
    steps: list = field(default_factory=list)

    @property
    def result(self):
        return self.steps[-1].after

    @property
    def has_memory_events(self):
        return any(step.event for step in self.steps)


def execute(program, initial):
    """Run the program from `initial` with zeroed memory, one step per instruction."""
    validate_program(program)
    if not 0 <= initial < P:
        raise Refusal('machine-operand', f'initial {initial}')
    run = Execution(program, initial)
    accumulator, memory = initial, [0] * MEMORY_CELLS
    pc = clock = 0
    while True:
        mnemonic, operand = program[pc]
        before, memory_before, event = accumulator, tuple(memory), None
        if mnemonic == 'set-immediate':
            accumulator = operand
        elif mnemonic == 'add-immediate':
            accumulator = (accumulator + operand) % P
        elif mnemonic == 'load':
            accumulator = memory[operand]
            event = (operand, accumulator, 0)
        elif mnemonic == 'store':
            memory[operand] = accumulator
            event = (operand, accumulator, 1)
        run.steps.append(Step(pc, clock, mnemonic, operand, before, accumulator,
                              memory_before, tuple(memory), event))
        if mnemonic == 'halt':
            return run
        pc, clock = pc + 1, clock + 1


def cpu_row(step):
    selectors = {name: 0 for name in SELECTOR.values()}
    selectors[SELECTOR[step.mnemonic]] = 1
    values = {'pc': step.pc, 'clock': step.clock, 'opcode': OPCODES[step.mnemonic],
              'operand': step.operand, 'accumulator_before': step.before,
              'accumulator_after': step.after, **selectors}
    return [values[c] for c in CPU_COLUMNS]


def memory_rows(steps, clocks):
    """Two rows per scheduled clock, address 0 then 1; idle clocks keep state."""
    rows = []
    for clock in range(clocks):
        if clock < len(steps):
            step = steps[clock]
            before, after, event = step.memory_before, step.memory_after, step.event
        else:
            before = after = steps[-1].memory_after
            event = None
        for address in range(MEMORY_CELLS):
            if event and event[0] == address:
                rows.append([before[address], after[address], 1, event[2], event[1]])
            else:
                rows.append([before[address], after[address], 0, 0, 0])
    return rows


@dataclass
class Rows:
    """Row-major configuration, instance and witness data with explicit presence.

    Tests change individual cells through `set` before emitting carriers, so
    every mutation names its table, column and row.
    """
    instructions: list
    schedule: list
    initial: int
    result: int
    cpu: list
    use: list
    memory: list
    memory_present: bool
    cpu_height: int = None

    def set(self, table, row, column, value):
        rows, columns = {
            'cpu': (self.cpu, CPU_COLUMNS), 'use': (self.use, ('use',)),
            'memory': (self.memory, CELL_COLUMNS),
            'instructions': (self.instructions, PROGRAM_COLUMNS),
            'schedule': (self.schedule, SCHEDULE_COLUMNS)}[table]
        rows[row][columns.index(column)] = value % P


def layout(run, memory_clocks=None, memory_present=None):
    """The canonical rows of an execution.

    The configured program table is the whole program, one row per pc; rows
    after the first Halt have use 0. The memory schedule covers the
    execution's clocks unless a longer schedule is configured. The optional
    memory table is present exactly when the execution has memory events
    unless `memory_present` overrides it.
    """
    clocks = len(run.steps) if memory_clocks is None else memory_clocks
    present = run.has_memory_events if memory_present is None else memory_present
    used = len(run.steps)
    return Rows(instructions=[[pc, OPCODES[m], operand] for pc, (m, operand) in enumerate(run.program)],
                schedule=[[clock, address] for clock in range(clocks) for address in range(MEMORY_CELLS)],
                initial=run.initial, result=run.result,
                cpu=[cpu_row(s) for s in run.steps],
                use=[[1 if pc < used else 0] for pc in range(len(run.program))],
                memory=memory_rows(run.steps, clocks), memory_present=present)


def total(terms):
    terms = list(terms)
    result = terms[0]
    for term in terms[1:]:
        result = result + term
    return result


@dataclass
class Table:
    name: str
    presence: str
    height: list
    groups: list
    assertions: list  # (name, scope, expression)
    interactions: list  # (channel, side, tuple expressions, multiplicity expression)


def machine_tables():
    """The three tables with their arenas; each assertion has a descriptive name."""
    cpu = Arena()

    def state(column, offset=0):
        return cpu.input(BASE, ['read', 0, str(offset), CPU_COLUMNS.index(column)])

    initial = cpu.input(BASE, ['public', 0])
    final = cpu.input(BASE, ['public', 1])
    pc, clock, opcode, operand = (state(c) for c in CPU_COLUMNS[:4])
    before, after = state('accumulator_before'), state('accumulator_after')
    select = {c: state(c) for c in CPU_COLUMNS[6:]}
    s_set, s_add, s_load, s_store, s_halt = select.values()
    decoded = total(OPCODES[m] * select[s] for m, s in SELECTOR.items())
    transition = ['interior', 0, 1]
    cpu_assertions = [
        ('pc starts at zero', ['first'], pc),
        ('clock starts at zero', ['first'], clock),
        ('accumulator starts at the public initial value', ['first'], before - initial),
        ('pc advances', transition, state('pc', 1) - pc - 1),
        ('clock advances', transition, state('clock', 1) - clock - 1),
        ('accumulator carries to the next step', transition, state('accumulator_before', 1) - after),
        ('set selector is Boolean', ['all'], s_set * (s_set - 1)),
        ('add selector is Boolean', ['all'], s_add * (s_add - 1)),
        ('load selector is Boolean', ['all'], s_load * (s_load - 1)),
        ('store selector is Boolean', ['all'], s_store * (s_store - 1)),
        ('exactly one selector is active', ['all'], total(select.values()) - 1),
        ('opcode decodes the selectors', ['all'], opcode - decoded),
        ('set-immediate replaces the accumulator', ['all'], s_set * (after - operand)),
        ('add-immediate adds the operand', ['all'], s_add * (after - before - operand)),
        ('store keeps the accumulator', ['all'], s_store * (after - before)),
        ('halt keeps the accumulator', ['all'], s_halt * (after - before)),
        ('no halt before the last step', transition, s_halt),
        ('last step halts', ['last'], s_halt - 1),
        ('final accumulator is the public result', ['last'], after - final),
    ]
    cpu_interactions = [
        ('program', 'pull', [pc, opcode, operand], cpu.constant(BASE, 1)),
        ('memory', 'push', [clock, operand, s_load * after + s_store * before, s_store],
         s_load + s_store),
    ]

    program = Arena()

    def instruction(column, offset=0):
        return program.input(BASE, ['read', 0, str(offset), PROGRAM_COLUMNS.index(column)])

    use = program.input(BASE, ['read', 1, '0', 0])
    program_assertions = [
        ('configured pc starts at zero', ['first'], instruction('pc')),
        ('configured pc advances', transition, instruction('pc', 1) - instruction('pc') - 1),
        ('use is Boolean', ['all'], use * (use - 1)),
    ]
    program_interactions = [
        ('program', 'push', [instruction(c) for c in PROGRAM_COLUMNS], use),
    ]

    memory = Arena()

    def schedule(column, offset=0):
        return memory.input(BASE, ['read', 0, str(offset), SCHEDULE_COLUMNS.index(column)])

    def cell(column, offset=0):
        return memory.input(BASE, ['read', 1, str(offset), CELL_COLUMNS.index(column)])

    m_before, m_after, event, write, value = (cell(c) for c in CELL_COLUMNS)
    address = schedule('address')
    memory_assertions = [
        ('schedule starts at clock zero', ['first'], schedule('clock')),
        ('schedule starts at address zero', ['first'], address),
        ('schedule alternates addresses', transition, schedule('address', 1) + address - 1),
        ('schedule advances the clock after address one', transition,
         schedule('clock', 1) - schedule('clock') - address),
        ('address zero starts at zero', ['first'], m_before),
        ('address one starts at zero', ['first'], cell('before', 1)),
        ('cell state carries to the next clock', ['interior', 0, 2], cell('before', 2) - m_after),
        ('event is Boolean', ['all'], event * (event - 1)),
        ('write requires an event', ['all'], write * (1 - event)),
        ('no write keeps the cell', ['all'], (1 - write) * (m_after - m_before)),
        ('read returns the cell', ['all'], event * (1 - write) * (value - m_before)),
        ('write stores the value', ['all'], write * (m_after - value)),
    ]
    memory_interactions = [
        ('memory', 'pull', [schedule('clock'), address, value, write], event),
    ]

    def tables():
        yield Table('cpu', 'required', ['instance', *CPU_HEIGHTS, True],
                    [['state', 'witness', BASE, len(CPU_COLUMNS)]],
                    cpu_assertions, cpu_interactions), cpu
        yield Table('program', 'required', ['config', *CPU_HEIGHTS, True],
                    [['instructions', 'config', BASE, len(PROGRAM_COLUMNS)],
                     ['use', 'witness', BASE, 1]],
                    program_assertions, program_interactions), program
        yield Table('memory', 'optional', ['config', *MEMORY_HEIGHTS, True],
                    [['schedule', 'config', BASE, len(SCHEDULE_COLUMNS)],
                     ['cells', 'witness', BASE, len(CELL_COLUMNS)]],
                    memory_assertions, memory_interactions), memory

    return list(tables())


def table_carrier(table, arena):
    outputs = [e for _, _, e in table.assertions]
    for _, _, tuple_values, multiplicity in table.interactions:
        outputs += tuple_values + [multiplicity]
    ring, bindings = arena.finish(outputs)
    assertions = [[i, scope] for i, (_, scope, _) in enumerate(table.assertions)]
    interactions, position = [], len(table.assertions)
    for channel, side, tuple_values, _ in table.interactions:
        width = len(tuple_values)
        interactions.append(['multiset', CHANNELS.index(channel), ['global'], ['all'], side,
                             list(range(position, position + width)), position + width, 1])
        position += width + 1
    return [table.name, table.presence, table.height, 'finite', table.groups, ring, bindings,
            assertions, interactions]


def machine_bundle():
    """The Bundle carrier and, per table, its assertion names in order."""
    tables = machine_tables()
    bundle = ['zkc.relation-bundle/0',
              [['initial-accumulator', BASE], ['final-result', BASE]],
              [['program', 'multiset', [BASE] * 3, BASE],
               ['memory', 'multiset', [BASE] * 4, BASE]],
              [table_carrier(t, a) for t, a in tables]]
    names = {t.name: [n for n, _, _ in t.assertions] for t, _ in tables}
    return bundle, names


def flat(rows):
    return [str(v % P) for row in rows for v in row]


def carriers(bundle, rows):
    """Configuration, instance and witness carriers for laid-out rows.

    The CPU height is the instance's authority and defaults to the number of
    CPU rows; the program and memory heights come from the configuration.
    """
    relation = identity(bundle)
    configuration = ['zkc.relation-configuration/0', relation, [
        [None, []],
        [len(rows.instructions), [flat(rows.instructions)]],
        [len(rows.schedule), [flat(rows.schedule)]]]]
    memory = ['present', None, []] if rows.memory_present else ['absent']
    height = len(rows.cpu) if rows.cpu_height is None else rows.cpu_height
    instance = ['zkc.relation-instance/0', relation, [str(rows.initial % P), str(rows.result % P)], [
        ['present', height, []],
        ['present', None, []],
        memory]]
    witness = ['zkc.relation-witness/0', relation, [
        [flat(rows.cpu)],
        [flat(rows.use)],
        [flat(rows.memory)] if rows.memory_present else None]]
    return configuration, instance, witness


def read_run(document):
    if not (isinstance(document, list) and len(document) == 3 and document[0] == RUN_FORMAT):
        raise Refusal('machine-run-schema')
    _, program, initial = document
    return [(m, int(o)) for m, o in program], int(initial)


def run_document(program, initial):
    return [RUN_FORMAT, [[m, str(o)] for m, o in program], str(initial)]
