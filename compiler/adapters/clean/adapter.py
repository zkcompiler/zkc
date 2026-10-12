"""Translate explicit Clean extraction plans to ordinary relation Bundles.

This adapter handles arithmetic table constraints and indexed immutable lookup
tables. It does not infer a Lean proposition's meaning from a table name.
Configuration, instance and witness carriers are separate outputs.
"""

from collections import Counter
from dataclasses import dataclass, field

from ring_arena import Arena, BASE, P, Refusal, identity


def fields(value, required, optional=()):
    """The extraction format has one exact schema, with no compatibility fields."""
    if not isinstance(value, dict) or not set(required) <= value.keys() <= set(required) | set(optional):
        raise Refusal('clean-schema', str(required))


def natural(value, label, maximum=1 << 20):
    if type(value) is not int or not 0 <= value <= maximum:
        raise Refusal('clean-shape', label)
    return value


def residue(value):
    return natural(value, 'noncanonical field value', P - 1)


def scalar(value):
    return str(residue(value))


def flatten(operations):
    for operation in operations:
        if set(operation) == {'subcircuit'}:
            yield from flatten(operation['subcircuit'])
        elif set(operation) == {'name', 'operations'}:
            yield from flatten(operation['operations'])
        elif set(operation) in ({'witness'}, {'assert'}, {'lookup'}, {'interact'}):
            yield operation
        else:
            raise Refusal('clean-operation', str(operation.keys()))


def expression(source, variable, constant):
    """Interpret the extracted expression through the caller's arithmetic."""
    kind = source['type']
    if kind == 'var' and set(source) == {'type', 'index'}:
        return variable(natural(source['index'], 'variable'))
    if kind == 'const' and set(source) == {'type', 'value'}:
        return constant(residue(source['value']))
    if kind in ('add', 'mul') and set(source) == {'type', 'lhs', 'rhs'}:
        left = expression(source['lhs'], variable, constant)
        right = expression(source['rhs'], variable, constant)
        return left + right if kind == 'add' else left * right
    raise Refusal('clean-expression', kind)


@dataclass
class Table:
    name: str
    height: int
    groups: list
    arena: Arena = field(default_factory=Arena)
    assertions: list = field(default_factory=list)
    records: list = field(default_factory=list)
    configuration: list = field(default_factory=list)
    witness: list = field(default_factory=list)

    def read(self, group, column, offset=0):
        return self.arena.input(BASE, ['read', group, str(offset), column])

    def fixed_column(self, group, column, values):
        """Pin a column to extraction-time data, grouping equal runs."""
        start = 0
        while start < len(values):
            end = start + 1
            while end < len(values) and values[end] == values[start]:
                end += 1
            self.assertions.append((self.read(group, column) - values[start], ['interval', start, end]))
            start = end

    def encode(self):
        outputs = [value for value, _ in self.assertions]
        records = []
        for channel, values, count in self.records:
            start = len(outputs)
            outputs.extend([*values, count])
            records.append(['field-balance', channel, ['global'], ['all'],
                            list(range(start, start + len(values))), len(outputs) - 1, None])
        arena, inputs = self.arena.finish(outputs)
        assertions = [[i, scope] for i, (_, scope) in enumerate(self.assertions)]
        return [self.name, 'required', ['fixed', self.height], 'cyclic',
                self.groups, arena, inputs, assertions, records]


@dataclass
class Export:
    bundle: list
    configuration: list
    instance: list
    witness: list

    def documents(self):
        return {'bundle.json': self.bundle, 'configuration.json': self.configuration,
                'instance.json': self.instance, 'witness.json': self.witness}


def scoped_context(operation, height):
    kind = operation['type']
    if kind == 'EveryRow':
        return ['all'], range(height)
    if kind == 'EveryRowExceptLast':
        return ['interior', 0, 1], range(height - 1)
    if kind == 'Boundary':
        row = operation['row']
        if type(row) is not int:
            raise Refusal('clean-boundary', str(row))
        row = row if row >= 0 else height + row
        if not 0 <= row < height:
            raise Refusal('clean-boundary', str(row))
        return ['interval', row, row + 1], range(row, row + 1)
    raise Refusal('clean-scope', kind)


def check_cardinality(tables, channels):
    """Check structural record counts, including records with zero weights."""
    for channel, declaration in enumerate(channels):
        count = sum(table.height * sum(record[0] == channel for record in table.records)
                    for table in tables)
        if count >= P:
            raise Refusal('clean-channel-characteristic', declaration[0])


def export(document):
    fields(document, ('format', 'field', 'table', 'public_bindings', 'public',
                      'lookups', 'trace', 'witness_tables'), ('channels', 'reference'))
    if document['format'] != 'zkc.clean-export/0' or document['field'] != P:
        raise Refusal('clean-format')
    source = document['table']
    fields(source, ('model', 'height', 'width', 'operations'))
    height = natural(source['height'], 'height')
    width = natural(source['width'], 'width')
    if not height or not width:
        raise Refusal('clean-shape', 'empty source table')
    is_component = source['model'] == 'component'
    if is_component:
        source = {**source, 'model': 'table', 'operations': [{
            'type': 'EveryRow', 'context': {'window': 1,
                'vars': [{'row': 0, 'column': i} for i in range(width)],
                'circuit': source['operations']}}]}
    if source['model'] != 'table':
        raise Refusal('clean-model', source['model'])
    if not is_component and document.get('channels'):
        raise Refusal('clean-interaction', 'TableOperation has no ensemble balance semantics')
    trace = document['trace']
    if len(trace) != height or any(len(row) != width for row in trace):
        raise Refusal('clean-trace-shape')
    trace = [[residue(value) for value in row] for row in trace]
    if not isinstance(document['witness_tables'], dict):
        raise Refusal('clean-schema', 'witness_tables')
    public = [scalar(value) for value in document['public']]
    main = Table('trace', height, [['trace', 'witness', BASE, width]],
                 witness=[[scalar(value) for row in trace for value in row]])

    tables, channels, lookup_tables, queries = [main], [], {}, {}
    declared_channels = {}
    for channel in document.get('channels', []):
        fields(channel, ('name', 'arity'))
        name, arity = channel['name'], natural(channel['arity'], 'channel arity')
        if name in declared_channels:
            raise Refusal('clean-channel-duplicate', name)
        declared_channels[name] = (len(channels), arity)
        channels.append([name, 'field-balance', [BASE] * arity, BASE])
    for declaration in document['lookups']:
        fields(declaration, ('name', 'interpretation'), ('values', 'height'))
        name, interpretation = declaration['name'], declaration['interpretation']
        if name in lookup_tables or name in declared_channels:
            raise Refusal('clean-lookup-duplicate', name)
        if interpretation == 'fixed-indexed':
            fields(declaration, ('name', 'interpretation', 'values'))
            values = [residue(value) for value in declaration['values']]
        elif interpretation == 'witness-indexed':
            fields(declaration, ('name', 'interpretation', 'height'))
            if name not in document['witness_tables']:
                raise Refusal('clean-lookup-shape', name)
            values = [residue(value) for value in document['witness_tables'][name]]
            if len(values) != natural(declaration['height'], 'lookup height'):
                raise Refusal('clean-lookup-shape', name)
        else:
            raise Refusal('clean-lookup-interpretation', interpretation)
        if not values or len(values) >= P:
            raise Refusal('clean-lookup-shape', name)
        channel = len(channels)
        channels.append([name, 'field-balance', [BASE, BASE], BASE])
        fixed = interpretation == 'fixed-indexed'
        groups = ([['indexed', 'config', BASE, 2], ['counts', 'witness', BASE, 1]]
                  if fixed else [['indexed_counts', 'witness', BASE, 3]])
        table = Table(name, len(values), groups)
        if fixed:
            table.configuration = [[scalar(v) for i, value in enumerate(values) for v in [i, value]]]
        address, value = table.read(0, 0), table.read(0, 1)
        count = table.read(1 if fixed else 0, 0 if fixed else 2)
        table.assertions.extend([(address, ['first']),
            (table.read(0, 0, 1) - address - 1, ['interior', 0, 1])])
        if fixed:
            table.fixed_column(0, 1, values)
        table.records.append((channel, [address, value], count))
        tables.append(table)
        lookup_tables[name] = (channel, table, values, fixed)
        queries[name] = Counter()

    fields(document['witness_tables'], [name for name, (_, _, _, fixed) in lookup_tables.items() if not fixed])

    selectors = []
    for operation in source['operations']:
        fields(operation, ('type', 'context'), ('row',))
        fields(operation, ('type', 'context', 'row') if operation['type'] == 'Boundary' else ('type', 'context'))
        scope, active = scoped_context(operation, height)
        ctx = operation['context']
        fields(ctx, ('window', 'vars', 'circuit'))
        window = natural(ctx['window'], 'window', 2)
        if window != (2 if operation['type'] == 'EveryRowExceptLast' else 1):
            raise Refusal('clean-window')
        cells = ctx['vars']
        for cell in cells:
            fields(cell, ('row', 'column'))
            if natural(cell['row'], 'cell row', 1) >= window or natural(cell['column'], 'column') >= width:
                raise Refusal('clean-cell')
        if any(row + cell['row'] >= height for row in active for cell in cells):
            raise Refusal('clean-window')

        def variable(index):
            if index >= len(cells):
                raise Refusal('clean-variable', str(index))
            return main.read(0, cells[index]['column'], cells[index]['row'])

        def term(value):
            return expression(value, variable, lambda n: main.arena.constant(BASE, n))

        selector = None
        for flat in flatten(ctx['circuit']):
            if 'witness' in flat:
                continue
            if 'assert' in flat:
                main.assertions.append((term(flat['assert']), scope))
            elif 'lookup' in flat:
                lookup = flat['lookup']
                fields(lookup, ('table', 'entry'))
                name = lookup['table']
                if name not in lookup_tables:
                    raise Refusal('clean-lookup-unregistered', name)
                if len(lookup['entry']) != 2:
                    raise Refusal('clean-lookup-arity', name)
                if len(active) != height and selector is None:
                    selector = main.read(0, width + len(selectors))
                    selectors.append([int(row in active) for row in range(height)])
                channel = lookup_tables[name][0]
                values = [term(e) for e in lookup['entry']]
                count = -selector if selector is not None else main.arena.constant(BASE, -1)
                main.records.append((channel, values, count))
                for row in active:
                    def fetch(index):
                        if index >= len(cells):
                            raise Refusal('clean-variable', str(index))
                        cell = cells[index]
                        return trace[row + cell['row']][cell['column']]
                    pair = tuple(expression(e, fetch, int) % P for e in lookup['entry'])
                    queries[name][pair] += 1
            else:
                if not is_component:
                    raise Refusal('clean-interaction', 'TableOperation has no ensemble balance semantics')
                interaction = flat['interact']
                fields(interaction, ('channel', 'arity', 'multiplicity', 'message', 'assume_guarantees'))
                name = interaction['channel']
                if name not in declared_channels:
                    raise Refusal('clean-channel-unregistered', name)
                channel, arity = declared_channels[name]
                if (len(interaction['message']) != arity or interaction['arity'] != arity
                        or type(interaction['assume_guarantees']) is not bool):
                    raise Refusal('clean-channel-arity', name)
                count = term(interaction['multiplicity'])
                main.records.append((channel, [term(e) for e in interaction['message']], count))

    if selectors:
        main.groups[0][3] += len(selectors)
        main.witness = [[scalar(value) for row, values in enumerate(trace)
                         for value in values + [selector[row] for selector in selectors]]]
        for column, values in enumerate(selectors):
            main.fixed_column(0, width + column, values)
    for binding in document['public_bindings']:
        fields(binding, ('column', 'slot', 'row'))
        column, slot = natural(binding['column'], 'boundary column'), natural(binding['slot'], 'public slot')
        if column >= width or slot >= len(public) or binding['row'] not in ('first', 'last'):
            raise Refusal('clean-public-binding')
        main.assertions.append((main.read(0, column) - main.arena.input(BASE, ['public', slot]), [binding['row']]))
    for name, (_, table, values, fixed) in lookup_tables.items():
        counts = queries[name]
        unknown = set(counts) - {(i, value) for i, value in enumerate(values)}
        if unknown:
            raise Refusal('clean-witness-lookup', f'{name}: {sorted(unknown)}')
        table.witness = [[scalar(v) for i, value in enumerate(values)
                          for v in ([counts[i, value]] if fixed else [i, value, counts[i, value]])]]
    bundle = ['zkc.relation-bundle/0', [[f'public_{i}', BASE] for i in range(len(public))],
              channels, [table.encode() for table in tables]]
    # Clean's flat Balance counts records even when their weight is zero.
    # For lookup membership this is our encoding's non-cancellation premise.
    check_cardinality(tables, channels)
    digest = identity(bundle)
    return Export(bundle,
        ['zkc.relation-configuration/0', digest, [[None, table.configuration] for table in tables]],
        ['zkc.relation-instance/0', digest, public, [['present', None, []] for table in tables]],
        ['zkc.relation-witness/0', digest, [table.witness for table in tables]])
