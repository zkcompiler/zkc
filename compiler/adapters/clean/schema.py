"""Decode the Clean adapter's source and input contracts at their JSON boundary."""

from dataclasses import dataclass

from ring_arena import P, Refusal


LIMIT = 1 << 20
MAX_EXPRESSION_DEPTH = 256


def fields(value, required, path, optional=()):
    if not isinstance(value, dict):
        raise Refusal('clean-schema', f'{path}: expected object')
    missing = set(required) - value.keys()
    unexpected = value.keys() - set(required) - set(optional)
    if missing or unexpected:
        raise Refusal('clean-schema', f'{path}: missing {sorted(missing)}, '
                      f'unexpected {sorted(map(str, unexpected))}')


def array(value, path):
    if not isinstance(value, list) or len(value) > LIMIT:
        raise Refusal('clean-schema', f'{path}: expected array of at most {LIMIT} elements')
    return value


def natural(value, path, maximum=LIMIT):
    if type(value) is not int or not 0 <= value <= maximum:
        raise Refusal('clean-shape', f'{path}: expected integer in [0, {maximum}]')
    return value


def text(value, path):
    if not isinstance(value, str) or not value:
        raise Refusal('clean-schema', f'{path}: expected nonempty string')
    return value


def residues(value, path):
    return tuple(natural(v, f'{path}[{i}]', P - 1) for i, v in enumerate(array(value, path)))


@dataclass(frozen=True)
class Constant:
    value: int

    def apply(self, variable, constant, reduce):
        return constant(self.value)


@dataclass(frozen=True)
class Variable:
    index: int

    def apply(self, variable, constant, reduce):
        return variable(self.index)


@dataclass(frozen=True)
class Binary:
    kind: str
    left: 'Expression'
    right: 'Expression'

    def apply(self, variable, constant, reduce):
        left = self.left.apply(variable, constant, reduce)
        right = self.right.apply(variable, constant, reduce)
        return reduce(left + right if self.kind == 'add' else left * right)


Expression = Constant | Variable | Binary


def expression(value, variables, path, depth=0):
    if depth > MAX_EXPRESSION_DEPTH:
        raise Refusal('clean-expression-depth', f'{path}: maximum depth {MAX_EXPRESSION_DEPTH}')
    fields(value, ('type',), path, ('index', 'value', 'lhs', 'rhs'))
    kind = value['type']
    if kind == 'var':
        fields(value, ('type', 'index'), path)
        index = natural(value['index'], f'{path}.index')
        if index >= variables:
            raise Refusal('clean-variable', f'{path}: {index}')
        return Variable(index)
    if kind == 'const':
        fields(value, ('type', 'value'), path)
        return Constant(natural(value['value'], f'{path}.value', P - 1))
    if kind in ('add', 'mul'):
        fields(value, ('type', 'lhs', 'rhs'), path)
        return Binary(kind, expression(value['lhs'], variables, f'{path}.lhs', depth + 1),
                      expression(value['rhs'], variables, f'{path}.rhs', depth + 1))
    raise Refusal('clean-expression', path)


@dataclass(frozen=True)
class Registration:
    definition: str
    name: str
    arity: int


@dataclass(frozen=True)
class LookupTable:
    source: Registration
    height: int
    values: tuple[int, ...] | None


@dataclass(frozen=True)
class Binding:
    column: int
    slot: int
    row: str


@dataclass(frozen=True)
class Assertion:
    value: Expression


@dataclass(frozen=True)
class Lookup:
    name: str
    entry: tuple[Expression, ...]


@dataclass(frozen=True)
class Interaction:
    name: str
    multiplicity: Expression
    message: tuple[Expression, ...]
    assume_guarantees: bool


@dataclass(frozen=True)
class Context:
    scope: tuple
    active: range
    cells: tuple[tuple[int, int], ...]
    operations: tuple[Assertion | Lookup | Interaction, ...]


@dataclass(frozen=True)
class Source:
    origin: str
    model: str
    height: int
    width: int
    public_origin: str
    public_size: int
    bindings: tuple[Binding, ...]
    lookups: tuple[LookupTable, ...]
    channels: tuple[Registration, ...]
    contexts: tuple[Context, ...]


def registration(value, path):
    fields(value, ('definition', 'name', 'arity'), path)
    return Registration(text(value['definition'], f'{path}.definition'),
                        text(value['name'], f'{path}.name'), natural(value['arity'], f'{path}.arity'))


def lookup_table(value, path):
    fields(value, ('source', 'interpretation'), path)
    source = registration(value['source'], f'{path}.source')
    if source.arity != 2:
        raise Refusal('clean-lookup-arity', path)
    meaning = value['interpretation']
    fields(meaning, ('kind',), f'{path}.interpretation', ('values', 'height'))
    kind = meaning['kind']
    if kind == 'fixed-indexed':
        fields(meaning, ('kind', 'values'), f'{path}.interpretation')
        values = residues(meaning['values'], f'{path}.interpretation.values')
        height = len(values)
    elif kind == 'witness-indexed':
        fields(meaning, ('kind', 'height'), f'{path}.interpretation')
        values = None
        height = natural(meaning['height'], f'{path}.interpretation.height')
    else:
        raise Refusal('clean-lookup-interpretation', path)
    if not height:
        raise Refusal('clean-lookup-shape', path)
    return LookupTable(source, height, values)


def operations(value, variables, lookups, channels, is_component, path):
    for i, op in enumerate(array(value, path)):
        loc = f'{path}[{i}]'
        if not isinstance(op, dict):
            raise Refusal('clean-operation', loc)
        if set(op) == {'witness'}:
            natural(op['witness'], f'{loc}.witness')
        elif set(op) == {'assert'}:
            yield Assertion(expression(op['assert'], variables, f'{loc}.assert'))
        elif set(op) == {'lookup'}:
            item = op['lookup']
            fields(item, ('table', 'entry'), f'{loc}.lookup')
            name = text(item['table'], f'{loc}.lookup.table')
            if name not in lookups:
                raise Refusal('clean-lookup-unregistered', f'{loc}: {name}')
            entry = array(item['entry'], f'{loc}.lookup.entry')
            if len(entry) != 2:
                raise Refusal('clean-lookup-arity', loc)
            yield Lookup(name, tuple(expression(e, variables, f'{loc}.lookup.entry[{j}]')
                                     for j, e in enumerate(entry)))
        elif set(op) == {'interact'}:
            if not is_component:
                raise Refusal('clean-interaction', f'{loc}: table has no ensemble balance semantics')
            item = op['interact']
            loc = f'{loc}.interact'
            fields(item, ('channel', 'arity', 'multiplicity', 'message', 'assume_guarantees'), loc)
            name = text(item['channel'], f'{loc}.channel')
            if name not in channels:
                raise Refusal('clean-channel-unregistered', f'{loc}: {name}')
            message = array(item['message'], f'{loc}.message')
            if (natural(item['arity'], f'{loc}.arity') != channels[name].arity
                    or len(message) != channels[name].arity):
                raise Refusal('clean-channel-arity', loc)
            if type(item['assume_guarantees']) is not bool:
                raise Refusal('clean-schema', f'{loc}.assume_guarantees: expected boolean')
            yield Interaction(name, expression(item['multiplicity'], variables, f'{loc}.multiplicity'),
                              tuple(expression(e, variables, f'{loc}.message[{j}]')
                                    for j, e in enumerate(message)), item['assume_guarantees'])
        else:
            raise Refusal('clean-operation', loc)


def context(value, height, width, lookups, channels, is_component, path):
    fields(value, ('type', 'context'), path, ('row',))
    kind = value['type']
    fields(value, ('type', 'context', 'row') if kind == 'Boundary' else ('type', 'context'), path)
    if kind == 'EveryRow':
        scope, active, window = ('all',), range(height), 1
    elif kind == 'EveryRowExceptLast':
        scope, active, window = ('interior', 0, 1), range(height - 1), 2
    elif kind == 'Boundary':
        row = value['row']
        if type(row) is not int or not -height <= row < height:
            raise Refusal('clean-boundary', path)
        row %= height
        scope, active, window = ('interval', row, row + 1), range(row, row + 1), 1
    else:
        raise Refusal('clean-scope', path)
    ctx = value['context']
    fields(ctx, ('window', 'vars', 'circuit'), f'{path}.context')
    if type(ctx['window']) is not int or ctx['window'] != window:
        raise Refusal('clean-window', path)
    cells = []
    for i, cell in enumerate(array(ctx['vars'], f'{path}.context.vars')):
        loc = f'{path}.context.vars[{i}]'
        fields(cell, ('row', 'column'), loc)
        row, column = natural(cell['row'], f'{loc}.row'), natural(cell['column'], f'{loc}.column')
        if row >= window or column >= width:
            raise Refusal('clean-cell', loc)
        cells.append((row, column))
    return Context(scope, active, tuple(cells), tuple(operations(ctx['circuit'], len(cells),
        lookups, channels, is_component, f'{path}.context.circuit')))


def decode_source(value):
    fields(value, ('format', 'field', 'table', 'public', 'lookups', 'channels'), 'source')
    if value['format'] != 'zkc.clean-export/0' or type(value['field']) is not int or value['field'] != P:
        raise Refusal('clean-format', 'source')
    table = value['table']
    fields(table, ('origin', 'model', 'height', 'width', 'operations'), 'source.table')
    height, width = natural(table['height'], 'source.table.height'), natural(table['width'], 'source.table.width')
    if not height or not width:
        raise Refusal('clean-shape', 'source.table: empty table')
    origin = text(table['origin'], 'source.table.origin')
    model = table['model']
    if model not in ('table', 'component'):
        raise Refusal('clean-model', 'source.table.model')
    channels = []
    for i, item in enumerate(array(value['channels'], 'source.channels')):
        path = f'source.channels[{i}]'
        fields(item, ('source', 'interpretation'), path)
        if model != 'component' or item['interpretation'] != 'field-balance':
            raise Refusal('clean-interaction', path)
        channel = registration(item['source'], f'{path}.source')
        if channel.name in {c.name for c in channels}:
            raise Refusal('clean-channel-duplicate', path)
        channels.append(channel)
    lookups = tuple(lookup_table(item, f'source.lookups[{i}]')
                    for i, item in enumerate(array(value['lookups'], 'source.lookups')))
    names = {channel.name for channel in channels} | {'trace'}
    for i, lookup in enumerate(lookups):
        if lookup.source.name in names:
            raise Refusal('clean-lookup-duplicate', f'source.lookups[{i}]: {lookup.source.name}')
        names.add(lookup.source.name)
    public = value['public']
    fields(public, ('origin', 'size', 'bindings'), 'source.public')
    public_origin = text(public['origin'], 'source.public.origin')
    public_size = natural(public['size'], 'source.public.size')
    bindings = []
    for i, binding in enumerate(array(public['bindings'], 'source.public.bindings')):
        path = f'source.public.bindings[{i}]'
        fields(binding, ('column', 'slot', 'row'), path)
        column, slot = natural(binding['column'], f'{path}.column'), natural(binding['slot'], f'{path}.slot')
        if column >= width or slot >= public_size or binding['row'] not in ('first', 'last'):
            raise Refusal('clean-public-binding', path)
        bindings.append(Binding(column, slot, binding['row']))
    lookup_names = {item.source.name for item in lookups}
    channel_map = {item.name: item for item in channels}
    if model == 'component':
        contexts = (Context(('all',), range(height), tuple((0, i) for i in range(width)),
            tuple(operations(table['operations'], width, lookup_names, channel_map, True,
                             'source.table.operations'))),)
    else:
        contexts = tuple(context(op, height, width, lookup_names, channel_map, False,
            f'source.table.operations[{i}]')
            for i, op in enumerate(array(table['operations'], 'source.table.operations')))
    return Source(origin, model, height, width, public_origin, public_size, tuple(bindings),
                  lookups, tuple(channels), contexts)


def decode_public(value, size):
    public = residues(value, 'inputs.public')
    if len(public) != size:
        raise Refusal('clean-public-shape', f'inputs.public: expected {size} values')
    return public


def decode_witness(trace, tables, source):
    rows = array(trace, 'inputs.trace')
    if len(rows) != source.height:
        raise Refusal('clean-trace-shape', f'inputs.trace: expected {source.height} rows')
    rows = tuple(array(row, f'inputs.trace[{i}]') for i, row in enumerate(rows))
    if any(len(row) != source.width for row in rows):
        raise Refusal('clean-trace-shape', f'inputs.trace: expected {source.width} columns')
    rows = tuple(tuple(natural(v, f'inputs.trace[{i}][{j}]', P - 1)
                       for j, v in enumerate(row)) for i, row in enumerate(rows))
    fields(tables, tuple(t.source.name for t in source.lookups if t.values is None), 'inputs.witness_tables')
    values = []
    for table in source.lookups:
        data = table.values
        if data is None:
            path = f'inputs.witness_tables.{table.source.name}'
            data = residues(tables[table.source.name], path)
            if len(data) != table.height:
                raise Refusal('clean-lookup-shape', path)
        values.append(data)
    return rows, tuple(values)
