"""Compile Clean declarations, then encode instances and prepare witnesses.

Only static declarations reach the relation compiler. The compiled layout is
immutable; its JSON carrier properties return independent values for callers.
"""

from collections import Counter
from dataclasses import dataclass, field
import json

from ring_arena import Arena, BASE, P, Refusal, compact, identity
from clean.schema import (Assertion, Interaction, Lookup, Source,
                    decode_public, decode_source, decode_witness, fields)


@dataclass
class Table:
    name: str
    height: int
    groups: list
    arena: Arena = field(default_factory=Arena)
    assertions: list = field(default_factory=list)
    records: list = field(default_factory=list)

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


def check_cardinality(tables, channels):
    """Check structural record counts, including records with zero weights."""
    for channel, declaration in enumerate(channels):
        count = sum(table.height * sum(record[0] == channel for record in table.records)
                    for table in tables)
        if count >= P:
            raise Refusal('clean-channel-characteristic', declaration[0])


@dataclass(frozen=True)
class CompiledRelation:
    source: Source = field(repr=False)
    selectors: tuple[range, ...]
    digest: str
    _bundle: str = field(repr=False)
    _configuration: str = field(repr=False)

    @property
    def bundle(self):
        return json.loads(self._bundle)

    @property
    def configuration(self):
        return json.loads(self._configuration)

    def encode_instance(self, public):
        values = decode_public(public, self.source.public_size)
        return ['zkc.relation-instance/0', self.digest, list(map(str, values)),
                [['present', None, []] for _ in range(1 + len(self.source.lookups))]]

    def prepare_witness(self, trace, witness_tables):
        rows, lookup_values = decode_witness(trace, witness_tables, self.source)
        queries = {table.source.name: Counter() for table in self.source.lookups}
        for context in self.source.contexts:
            for lookup in context.operations:
                if not isinstance(lookup, Lookup):
                    continue
                for row in context.active:
                    def fetch(index):
                        offset, column = context.cells[index]
                        return rows[row + offset][column]
                    pair = tuple(e.apply(fetch, int, lambda v: v % P) for e in lookup.entry)
                    queries[lookup.name][pair] += 1
        main = [[str(value) for row, values in enumerate(rows)
                 for value in (*values, *(int(row in active) for active in self.selectors))]]
        witness = [main]
        for table, values in zip(self.source.lookups, lookup_values):
            counts = queries[table.source.name]
            unknown = set(counts) - set(enumerate(values))
            if unknown:
                raise Refusal('clean-witness-lookup', f'{table.source.name}: {sorted(unknown)}')
            witness.append([[str(v) for i, value in enumerate(values)
                for v in ([counts[i, value]] if table.values is not None else [i, value, counts[i, value]])]])
        return ['zkc.relation-witness/0', self.digest, witness]


def compile_relation(document):
    """Compile a static extraction plan without any execution's input values."""
    source = decode_source(document)
    main = Table('trace', source.height, [['trace', 'witness', BASE, source.width]])
    tables, configuration, selectors = [main], [[None, []]], []
    channels = [[channel.name, 'field-balance', [BASE] * channel.arity, BASE]
                for channel in source.channels]
    channel_indices = {channel.name: i for i, channel in enumerate(source.channels)}
    lookup_indices = {}
    for declaration in source.lookups:
        name, height, values = declaration.source.name, declaration.height, declaration.values
        channel = len(channels)
        lookup_indices[name] = channel
        channels.append([name, 'field-balance', [BASE, BASE], BASE])
        fixed = values is not None
        groups = ([['indexed', 'config', BASE, 2], ['counts', 'witness', BASE, 1]]
                  if fixed else [['indexed_counts', 'witness', BASE, 3]])
        table = Table(name, height, groups)
        configuration.append([None, [[str(v) for i, value in enumerate(values) for v in (i, value)]]
                              if fixed else []])
        address, value = table.read(0, 0), table.read(0, 1)
        count = table.read(1 if fixed else 0, 0 if fixed else 2)
        table.assertions.extend([(address, ['first']),
            (table.read(0, 0, 1) - address - 1, ['interior', 0, 1])])
        if fixed:
            table.fixed_column(0, 1, values)
        table.records.append((channel, [address, value], count))
        tables.append(table)

    for context in source.contexts:
        def variable(index):
            row, column = context.cells[index]
            return main.read(0, column, row)

        def term(value):
            return value.apply(variable, lambda n: main.arena.constant(BASE, n), lambda v: v)

        selector = None
        for operation in context.operations:
            match operation:
                case Assertion(value):
                    main.assertions.append((term(value), list(context.scope)))
                case Lookup(name, entry):
                    if len(context.active) != source.height and selector is None:
                        selector = main.read(0, source.width + len(selectors))
                        selectors.append(context.active)
                    values = [term(e) for e in entry]
                    count = -selector if selector is not None else main.arena.constant(BASE, -1)
                    main.records.append((lookup_indices[name], values, count))
                case Interaction(name, multiplicity, message, _):
                    count = term(multiplicity)
                    main.records.append((channel_indices[name], [term(e) for e in message], count))

    main.groups[0][3] += len(selectors)
    for column, active in enumerate(selectors):
        main.fixed_column(0, source.width + column, [int(row in active) for row in range(source.height)])
    for binding in source.bindings:
        main.assertions.append((main.read(0, binding.column)
            - main.arena.input(BASE, ['public', binding.slot]), [binding.row]))
    # Clean counts even zero-weight records. Lookup membership also relies on
    # the number of requests being below the characteristic (no cancellation).
    check_cardinality(tables, channels)
    bundle = ['zkc.relation-bundle/0', [[f'public_{i}', BASE] for i in range(source.public_size)],
              channels, [table.encode() for table in tables]]
    digest = identity(bundle)
    return CompiledRelation(source, tuple(selectors), digest, compact(bundle),
        compact(['zkc.relation-configuration/0', digest, configuration]))


def export(source, inputs):
    """Compose the independent stages for fixture producers and small clients."""
    fields(inputs, ('format', 'public', 'trace', 'witness_tables'), 'inputs')
    if inputs['format'] != 'zkc.clean-inputs/0':
        raise Refusal('clean-format', 'inputs')
    compiled = compile_relation(source)
    return {'bundle.json': compiled.bundle, 'configuration.json': compiled.configuration,
            'instance.json': compiled.encode_instance(inputs['public']),
            'witness.json': compiled.prepare_witness(inputs['trace'], inputs['witness_tables'])}
